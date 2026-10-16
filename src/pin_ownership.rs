//! Stationary storage obligations are independent of reference-handle liveness.
//! Heap owners carry allocation identities through ordinary value transfers;
//! releasing an allocation is distinct from moving or leaking its owner.

use std::collections::{HashMap, HashSet};

use crate::linearcheck::LinearTypes;
use crate::typed_body::{BindingId, Body, NodeKind, ParameterLoanSummary, PlaceRoot};
use crate::typed_borrow::BorrowConflict;
use crate::typed_flow::{FlowAction, FlowGraph, FlowLoanOrigins, FlowNodeId};
use crate::typed_ir::{Declarations, FunctionId};
use crate::typed_place::Place;

fn allocation_overlaps(
    left: &crate::typed_flow::LoanOrigin,
    right: &crate::typed_flow::LoanOrigin,
) -> bool {
    // Symbolic parameter storage distinguishes the allocation carried by an
    // owning-pointer slot from the ordinary reference to its containing box.
    // Caller substitution replaces this slot with a concrete allocation ID.
    if matches!(left.place.root, PlaceRoot::Parameter(_))
        && left.place.root == right.place.root
        && left.parameter_storage != right.parameter_storage
    {
        return false;
    }
    left.referent_place().overlaps(&right.referent_place())
}

pub(crate) fn check(
    declarations: &Declarations,
    types: &LinearTypes,
    caches: &HashMap<&str, std::cell::OnceCell<FlowLoanOrigins>>,
) -> Result<(), BorrowConflict> {
    let mut relevant = declarations.bodies.iter().filter_map(|(name, body)| {
        let needed = body.parameter_loan_slots.iter().chain(&body.parameter_referent_loan_slots).flatten().any(|slot| slot.owned_allocation)
            || body.nodes.iter().any(|node| matches!(&node.kind, NodeKind::Form { head, callee: None, .. }
                if matches!(head.as_str(), "pin" | "pin-shared" | "pin-borrow" | "pin-borrow-mut" | "pin-own-of" | "pin-own-borrow" | "pin-shared-borrow" | "pin-own-borrow-mut" | "pin-shared-borrow-mut" | "pin-release" | "pin-shared-release")))
            || body.nodes.iter().any(|node| matches!(node.ty, Some(crate::Type::PinOwned(_) | crate::Type::PinShared(_))));
        needed.then_some(name)
    }).collect::<HashSet<_>>();
    if relevant.is_empty() {
        return Ok(());
    }
    loop {
        let mut additions = Vec::new();
        for (name, body) in &declarations.bodies {
            if !relevant.contains(name)
                && body.nodes.iter().any(|node| match &node.kind {
                    NodeKind::Form {
                        callee: Some(callee),
                        ..
                    } => declarations.function_name(*callee).is_some_and(|name| {
                        relevant.iter().any(|candidate| candidate.as_str() == name)
                    }),
                    _ => false,
                })
            {
                additions.push(name);
            }
        }
        if additions.is_empty() {
            break;
        }
        relevant.extend(additions);
    }
    let origins_by_name = relevant
        .iter()
        .map(|name| {
            (
                *name,
                caches[name.as_str()].get_or_init(|| {
                    declarations.flows[*name].loan_origins(&declarations.bodies[*name])
                }),
            )
        })
        .collect::<HashMap<_, _>>();
    let mut effects: HashMap<FunctionId, Vec<ParameterLoanSummary>> = HashMap::new();
    // Calls are acyclic, but declaration order need not be topological.
    // Each round only adds may-access footprints; no result is permission.
    // Owning footprints invalidate storage; borrowed footprints access it.
    for _ in 0..=declarations.bodies.len() {
        let mut changed = false;
        for name in &relevant {
            let body = &declarations.bodies[*name];
            let flow = &declarations.flows[*name];
            let origins = &origins_by_name[*name];
            let id = declarations.function_id(name).expect("checked function");
            for (index, _) in flow.nodes.iter().enumerate() {
                for released in allocation_accesses(
                    body,
                    flow,
                    origins,
                    FlowNodeId(index),
                    &effects,
                    declarations,
                ) {
                    if !matches!(released.place.root, PlaceRoot::Parameter(_)) {
                        continue;
                    }
                    let mut summary = released.parameter_summary().expect("parameter origin");
                    summary.storage.clear();
                    summary.storage_inputs.clear();
                    let output = effects.entry(id).or_default();
                    if !output.contains(&summary) {
                        output.push(summary);
                        changed = true;
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }
    let mut names = relevant.into_iter().collect::<Vec<_>>();
    names.sort();
    for name in names {
        let body = &declarations.bodies[name];
        let flow = &declarations.flows[name];
        let origins = origins_by_name[name];
        check_stack(body, flow, types, origins)?;
        let active = flow.active_bindings_before(body);
        let consumed = flow.consumptions(body, types);
        for (index, node) in flow.nodes.iter().enumerate() {
            let event = FlowNodeId(index);
            if let FlowAction::Borrow { value, .. } | FlowAction::Evaluate(value) = node.action {
                if matches!(&body.nodes[value.0].kind, NodeKind::Form { head, callee: None, .. } if matches!(head.as_str(), "pin-own-borrow" | "pin-shared-borrow" | "pin-own-borrow-mut" | "pin-shared-borrow-mut"))
                    && active[index].is_some()
                    && !origins
                        .value_before(body, flow, event, value)
                        .iter()
                        .any(|origin| !origin.lifetime_only)
                {
                    return Err(BorrowConflict {
                        message: "cannot establish allocation identity for an owning-pin view"
                            .into(),
                        span: node.span,
                        labels: Vec::new(),
                    });
                }
            }
            for released in allocation_accesses(body, flow, origins, event, &effects, declarations)
            {
                for binding in active[index].iter().flatten() {
                    if consumed
                        .definitely_consumed_before(event, &Place::root(PlaceRoot::Local(*binding)))
                    {
                        continue;
                    }
                    for held in origins.before(event, *binding) {
                        if held.owned_allocation
                            || !allocation_overlaps(&released, held)
                            || (!released.owned_allocation && !released.mutable && !held.mutable)
                        {
                            continue;
                        }
                        // Retained references must be retired explicitly before
                        // invalidating heap storage, even if never read again.
                        return Err(BorrowConflict {
                            message: format!("cannot {} pinned allocation while '{}' retains a conflicting borrow", if released.owned_allocation { "release" } else { "access" }, body.bindings[binding.0].name),
                            span: node.span,
                            labels: held.span.into_iter().map(|span| (span, "allocation borrowed here".into())).collect(),
                        });
                    }
                }
                // A moved exclusive argument may already be consumed as a
                // local, but its loan is still active inside this call.
                if let FlowAction::Evaluate(value) = node.action {
                    if let NodeKind::Form {
                        callee: Some(_),
                        children,
                        ..
                    } = &body.nodes[value.0].kind
                    {
                        for argument in children.iter().skip(1) {
                            for held in origins.value_before(body, flow, event, *argument) {
                                if !held.owned_allocation
                                    && allocation_overlaps(&released, &held)
                                    && (released.owned_allocation
                                        || released.mutable
                                        || held.mutable)
                                {
                                    return Err(BorrowConflict { message: "call accesses a pinned allocation while also passing a conflicting pointee borrow".into(), span: node.span, labels: held.span.into_iter().map(|span| (span, "allocation borrowed here".into())).collect() });
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    Ok(())
}

fn allocation_accesses(
    body: &Body,
    flow: &FlowGraph,
    origins: &FlowLoanOrigins,
    event: FlowNodeId,
    effects: &HashMap<FunctionId, Vec<ParameterLoanSummary>>,
    declarations: &Declarations,
) -> Vec<crate::typed_flow::LoanOrigin> {
    let value = match flow.nodes[event.0].action {
        FlowAction::Evaluate(value)
        | FlowAction::Release { value, .. }
        | FlowAction::Borrow { value, .. } => value,
        _ => return Vec::new(),
    };
    let NodeKind::Form {
        head,
        children,
        callee,
        ..
    } = &body.nodes[value.0].kind
    else {
        return Vec::new();
    };
    if callee.is_none()
        && matches!(
            head.as_str(),
            "pin-own-borrow" | "pin-shared-borrow" | "pin-own-borrow-mut" | "pin-shared-borrow-mut"
        )
    {
        return origins
            .value_before(body, flow, event, value)
            .into_iter()
            .filter(|origin| !origin.lifetime_only && origin.storage.is_empty())
            .collect();
    }
    if callee.is_none() && matches!(head.as_str(), "pin-release" | "pin-shared-release") {
        return origins
            .value_before(body, flow, event, children[1])
            .into_iter()
            .filter(|origin| origin.owned_allocation)
            .collect();
    }
    let Some(callee) = callee else {
        return Vec::new();
    };
    let mut result = Vec::new();
    if let Some(effects) = effects.get(callee) {
        for effect in effects {
            if let Some(argument) = children.get(effect.parameter + 1) {
                result.extend(
                    origins
                        .apply_summary_before(body, flow, event, *argument, effect)
                        .into_iter()
                        .filter(|origin| origin.storage.is_empty()),
                );
            }
        }
    } else if !declarations
        .bodies
        .contains_key(declarations.function_name(*callee).expect("checked callee"))
    {
        // An unavailable body cannot promise to preserve owned allocations.
        for argument in children.iter().skip(1) {
            result.extend(
                origins
                    .value_before(body, flow, event, *argument)
                    .into_iter()
                    .filter(|origin| origin.owned_allocation),
            );
        }
    }
    result
}

fn check_stack(
    body: &Body,
    flow: &FlowGraph,
    types: &LinearTypes,
    origins: &FlowLoanOrigins,
) -> Result<(), BorrowConflict> {
    let active = flow.active_bindings_before(body);
    let transfers = flow.consumptions(body, types);
    // Pinning is a property of storage, not a live handle. Union facts at
    // branches: a place pinned on either path cannot be moved on the join.
    let mut frozen = vec![HashSet::<BindingId>::new(); flow.nodes.len()];
    let mut ended = frozen.clone();
    let mut reached = vec![false; flow.nodes.len()];
    reached[flow.entry.0] = true;
    let mut pending = std::collections::VecDeque::from([flow.entry]);
    while let Some(event) = pending.pop_front() {
        let node = &flow.nodes[event.0];
        let mut next = frozen[event.0].clone();
        let mut retired = ended[event.0].clone();
        match node.action {
            FlowAction::Bind { binding, .. } => {
                // A loop iteration introduces new storage for this binding.
                next.remove(&binding);
                retired.remove(&binding);
            }
            FlowAction::Borrow { value, .. }
                if matches!(&body.nodes[value.0].kind,
                NodeKind::Form { head, .. } if matches!(head.as_str(), "pin" | "pin-shared" | "pin-borrow" | "pin-borrow-mut"))
                    && (matches!(&body.nodes[value.0].kind,
                        NodeKind::Form { head, .. } if matches!(head.as_str(), "pin" | "pin-shared"))
                        || matches!(&body.nodes[value.0].ty, Some(crate::Type::PinnedReference { target, .. }) if types.is_linear(target))) =>
            {
                for origin in origins.value_before(body, flow, event, value) {
                    if let PlaceRoot::Local(binding) = origin.place.root {
                        next.insert(binding);
                    }
                }
            }
            FlowAction::Release { ref place, .. } => {
                if let PlaceRoot::Local(binding) = place.root {
                    if next.contains(&binding) {
                        retired.insert(binding);
                    }
                }
            }
            _ => {}
        }
        for successor in &node.successors {
            let before = (frozen[successor.0].len(), ended[successor.0].len());
            frozen[successor.0].extend(&next);
            ended[successor.0].extend(&retired);
            if !reached[successor.0]
                || before != (frozen[successor.0].len(), ended[successor.0].len())
            {
                reached[successor.0] = true;
                pending.push_back(*successor);
            }
        }
    }
    for (index, node) in flow.nodes.iter().enumerate() {
        if active[index].is_none() {
            continue;
        }
        let event = FlowNodeId(index);
        let violation = match &node.action {
            FlowAction::Borrow { value, place, .. } if matches!(&body.nodes[value.0].kind, NodeKind::Form { head, callee: None, .. } if matches!(head.as_str(), "pin" | "pin-shared" | "pin-borrow" | "pin-borrow-mut"))
                && matches!(&body.nodes[value.0].ty, Some(crate::Type::PinnedReference { target, .. }) if types.is_linear(target))
                && matches!(&body.nodes[value.0].kind, NodeKind::Form { children, .. }
                    if crate::typed_place::reads_through_reference(body, children[1])
                        && origins.address_before(body, flow, event, children[1]).iter()
                            .any(|origin| origin.storage.is_empty() && !origin.lifetime_only && !origin.pinned && !origin.owned_allocation)) => Some((place.clone(), "cannot create a permanent pin through an ordinary reference; pass a pinned reference instead")),
            FlowAction::Read { place, place_base: false, .. }
                if matches!(place.root, PlaceRoot::Local(binding) if frozen[index].contains(&binding) && transfers.consumes_at(event, place)) => Some((place.clone(), "cannot move or copy stationary storage; access it through a pinned reference")),
            FlowAction::Clone { place, value }
                if matches!(place.root, PlaceRoot::Local(binding) if frozen[index].contains(&binding) && body.nodes[value.0].ty.as_ref().is_some_and(|ty| types.is_linear(ty))) => Some((place.clone(), "cannot move or copy stationary storage; access it through a pinned reference")),
            FlowAction::Assign { place, value } if matches!(place.root, PlaceRoot::Local(binding) if frozen[index].contains(&binding) && (place.segments.is_empty() || body.nodes[value.0].ty.as_ref().is_some_and(|ty| types.is_linear(ty)))) => Some((place.clone(), "cannot replace stationary storage; use checked pinned field access")),
            FlowAction::Borrow { value, place, mutable: true } if matches!(place.root, PlaceRoot::Local(binding) if frozen[index].contains(&binding))
                && matches!(body.nodes[value.0].ty, Some(crate::Type::Reference { .. })) => Some((place.clone(), "cannot obtain an ordinary mutable reference to stationary storage")),
            _ => None,
        };
        if let Some((place, message)) = violation {
            let PlaceRoot::Local(binding) = place.root else {
                unreachable!()
            };
            return Err(BorrowConflict {
                message: format!("{message}: '{}'", body.bindings[binding.0].name),
                span: node.span.or(body.bindings[binding.0].span),
                labels: body.bindings[binding.0]
                    .span
                    .into_iter()
                    .map(|span| (span, "stationary storage declared here".into()))
                    .collect(),
            });
        }
        let accessed = match &node.action {
            FlowAction::Borrow { place, .. }
            | FlowAction::Read { place, .. }
            | FlowAction::Assign { place, .. }
            | FlowAction::Write { place, .. }
            | FlowAction::Clone { place, .. }
            | FlowAction::Release { place, .. } => Some(place),
            _ => None,
        };
        if let Some(place) = accessed {
            if matches!(place.root, PlaceRoot::Local(binding) if ended[index].contains(&binding)) {
                return Err(BorrowConflict {
                    message:
                        "stationary storage has already ended; it cannot be reused or re-pinned"
                            .into(),
                    span: node.span,
                    labels: Vec::new(),
                });
            }
        }
        if let FlowAction::Write { value, .. } = node.action {
            if let NodeKind::Form { head, children, .. } = &body.nodes[value.0].kind {
                if head == "deref-set" {
                    for origin in origins.value_before(body, flow, event, children[1]) {
                        if matches!(origin.place.root, PlaceRoot::Local(binding) if frozen[index].contains(&binding))
                        {
                            return Err(BorrowConflict { message: "cannot replace stationary storage through an ordinary mutable reference".into(), span: node.span, labels: Vec::new() });
                        }
                    }
                }
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    fn check(source: &str) -> Result<(), String> {
        crate::check_types(&crate::parse_program(source)?)
    }

    #[test]
    fn stationary_storage_syntax_is_replaced_by_the_generated_api() {
        for body in ["(#let-pin value #u64 42u64)", "(#pin-end value)"] {
            assert!(check(&format!("(#fn main () () {body} (#return ()))")).is_err());
        }
    }

    const HEAP: &str = "(#fn create () (#pin-own #u64)
        (#return (#unsafe (#pin-own-of (#ptr-null (#ptr-mut #u64)) 42u64))))
      (#fn forward (: owner (#pin-own #u64)) (#pin-own #u64) (#return owner))
      (#fn destroy (: owner (#pin-own #u64)) ()
        (#let pointer (#ptr-mut #u64) (#unsafe (#pin-release owner))) (#forget pointer) (#return ()))
      (#fn main () #u64
        (#let owner (#pin-own #u64) (#call create (:)))
        (#let view (#pin-ref #u64) (#pin-own-borrow owner))
        (#let moved (#pin-own #u64) (#call forward (: owner owner)))
        (#let result #u64 (#deref view)) (#forget view)
        (#call destroy (: owner moved)) (#return result))";

    #[test]
    fn heap_owner_moves_through_calls_without_changing_allocation() {
        check(HEAP).unwrap();
    }

    #[test]
    fn heap_release_through_a_callee_cannot_invalidate_retained_views() {
        let bad = HEAP.replace(
            "(#let result #u64 (#deref view)) (#forget view)",
            "(#let result #u64 42u64)",
        );
        assert!(check(&bad).unwrap_err().contains("pinned allocation"));
    }

    #[test]
    fn heap_owner_cannot_be_duplicated() {
        assert!(check(&HEAP.replace("(: owner owner)))", "(: owner (#clone owner))))")).is_err());
    }

    #[test]
    fn an_ordinary_pin_does_not_make_a_linear_owner_movable_again() {
        let source = "(#struct Frame (#linear) ((value #u64)))
          (#fn main () () (#let-mut frame Frame (#struct-literal Frame (: value 42u64)))
          (#let pin (#pin-ref-mut Frame) (#pin-borrow-mut frame)) (#forget pin)
          (#let moved Frame frame) (#forget moved) (#return ()))";
        assert!(check(source).unwrap_err().contains("stationary"));
    }

    #[test]
    fn heap_views_obey_exclusive_borrow_rules_after_owner_moves() {
        let source = HEAP.replace("(#let owner (#pin-own #u64)", "(#let-mut owner (#pin-own #u64)")
            .replace("(#let moved (#pin-own #u64)", "(#let-mut moved (#pin-own #u64)")
            .replace("(#let result #u64 (#deref view))", "(#let exclusive (#pin-ref-mut #u64) (#pin-own-borrow-mut moved)) (#let result #u64 (#deref view)) (#forget exclusive)");
        let error = check(&source).unwrap_err();
        assert!(error.contains("borrow"), "{error}");
    }

    #[test]
    fn independent_allocations_do_not_share_call_site_identity() {
        let source = HEAP.replace("(#let view (#pin-ref #u64)", "(#let other (#pin-own #u64) (#call create (:))) (#call destroy (: owner other)) (#let view (#pin-ref #u64)");
        check(&source).unwrap();
    }

    #[test]
    fn heap_adoption_preserves_the_initializers_external_reference() {
        let source = "(#struct Held () (: value (#ref #u64)))
          (#fn adopt (: pointer (#ptr-mut Held) : source (#ref #u64)) (#pin-own Held)
          (#return (#unsafe (#pin-own-of pointer (#struct-literal Held (: value source))))))";
        check(source).unwrap();
    }

    #[test]
    fn leaking_an_owner_does_not_end_the_allocation_lifetime() {
        let source = HEAP
            .replace(
                "(#let moved (#pin-own #u64) (#call forward (: owner owner)))",
                "(#forget owner)",
            )
            .replace("(#call destroy (: owner moved))", "()");
        check(&source).unwrap();
    }

    #[test]
    fn aggregate_forwarding_preserves_allocation_identity_for_release() {
        let source = HEAP.replace(
            "(#let moved (#pin-own #u64) (#call forward (: owner owner)))",
            "(#let wrapped (#tuple (#pin-own #u64)) (#tuple (#tuple (#pin-own #u64)) owner))
             (#let returned (#tuple (#pin-own #u64)) (#call pass (: item wrapped)))
             (#let moved (#pin-own #u64) (#get returned 0))",
        );
        let source = format!("(#fn pass (: item (#tuple (#pin-own #u64))) (#tuple (#pin-own #u64)) (#return item)) {source}");
        check(&source).unwrap();
        assert!(check(&source.replace("(#forget view)", "()"))
            .unwrap_err()
            .contains("pinned allocation"));
    }

    #[test]
    fn a_fresh_owner_and_view_returned_together_have_the_same_identity() {
        let source = "(#fn pair () (#tuple (#pin-own #u64) (#pin-ref #u64))
          (#let owner (#pin-own #u64) (#unsafe (#pin-own-of (#ptr-null (#ptr-mut #u64)) 42u64)))
          (#let view (#pin-ref #u64) (#pin-own-borrow owner))
          (#return (#tuple (#tuple (#pin-own #u64) (#pin-ref #u64)) owner view)))
          (#fn main () ()
          (#let returned (#tuple (#pin-own #u64) (#pin-ref #u64)) (#call pair (:)))
          (#let owner (#pin-own #u64) (#get returned 0))
          (#let pointer (#ptr-mut #u64) (#unsafe (#pin-release owner)))
          (#let result #u64 (#deref (#get returned 1)))
          (#forget returned) (#forget pointer) (#return ()))";
        assert!(check(source).unwrap_err().contains("pinned allocation"));
    }

    #[test]
    fn pinning_a_linear_parameter_requires_a_pinned_input() {
        let source = "(#struct Frame (#linear) (: value #u64))
          (#struct Container () (: frame Frame))
          (#fn view (: container (#ref Container)) (#pin-ref Frame)
          (#return (#pin-borrow (#get container frame))))";
        assert!(check(source).unwrap_err().contains("ordinary reference"));
        check(&source.replace("(#ref Container)", "(#pin-ref Container)")).unwrap();
    }

    #[test]
    fn a_callee_cannot_mutably_access_an_owner_with_a_retained_pointee_view() {
        let source = "(#struct Data () (: value #u64))
          (#fn mutate (: #mut owner (#pin-own Data) : view (#pin-ref Data)) (#pin-own Data)
          (#let exclusive (#pin-ref-mut Data) (#pin-own-borrow-mut owner))
          (#pin-set-field exclusive value 99u64)
          (#let observed #u64 (#get view value)) (#forget exclusive) (#return owner))
          (#fn main () ()
          (#let owner (#pin-own Data) (#unsafe (#pin-own-of (#ptr-null (#ptr-mut Data)) (#struct-literal Data (: value 42u64)))))
          (#let view (#pin-ref Data) (#pin-own-borrow owner))
          (#let returned (#pin-own Data) (#call mutate (: owner owner : view view)))
          (#forget returned) (#forget view) (#return ()))";
        let error = check(source).unwrap_err();
        assert!(
            error.contains("pinned allocation") && error.contains("borrow"),
            "{error}"
        );
    }

    #[test]
    fn thread_transfer_cannot_outlive_a_retained_pointee_view() {
        let functions = HEAP.split("(#fn main").next().unwrap();
        let source = format!(
            "{functions}
          (#thread-task Task destroy)
          (#fn main () ()
          (#let owner (#pin-own #u64) (#call create (:)))
          (#let view (#pin-ref #u64) (#pin-own-borrow owner))
          (#let spawned Task-spawn-result (#call Task-spawn (: owner owner)))
          (#unreachable) (#return ()))"
        );
        let error = check(&source).unwrap_err();
        assert!(
            error.contains("pinned allocation") && error.contains("borrow"),
            "{error}"
        );
    }

    #[test]
    fn an_owning_pin_cannot_be_bitwise_cloned_inside_an_aggregate() {
        let source = HEAP.replace("(#let moved (#pin-own #u64) (#call forward (: owner owner)))", "(#let wrapped (#tuple (#pin-own #u64)) (#tuple (#tuple (#pin-own #u64)) owner)) (#let duplicate (#tuple (#pin-own #u64)) (#clone wrapped)) (#let moved (#pin-own #u64) (#get wrapped 0)) (#forget duplicate)");
        assert!(check(&source)
            .unwrap_err()
            .contains("owning pin cannot be cloned"));
    }
}
