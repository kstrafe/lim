//! Checks simultaneous call-argument loans and live direct-loan conflicts
//! using resolved places. Pure constructors preserve direct borrows through
//! aggregates, conditional results, and reference-returning calls. Loop break
//! values are transferred from their checked control-flow instructions.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use crate::linearcheck::LinearTypes;
use crate::typed_body::{BindingId, Body, Control, NodeId, NodeKind, PlaceRoot};
use crate::typed_flow::{FlowAction, FlowGraph, FlowNodeId, LoanOrigin};
use crate::typed_ir::{DeclarationId, FieldId};
use crate::typed_place::{reads_through_reference, Place};
use crate::{Span, Type};

const MAX_BORROW_ALTERNATIVES: usize = 1024;
const MAX_ALIAS_CHAIN_DEPTH: usize = 128;

#[derive(Debug)]
pub(crate) struct BorrowConflict {
    pub message: String,
    pub span: Option<Span>,
    pub labels: Vec<(Span, String)>,
}

#[derive(Clone, Copy, Debug)]
enum AccessKind {
    Read,
    Borrow { mutable: bool },
    Clone,
    Move,
    Write,
    Release,
}

/// Check loans retained by live bindings at checked access events. Projected
/// accesses through a reference are rebased onto the original referent so a
/// live child reborrow conflicts with parent access while disjoint fields stay
/// independent.
#[cfg(test)]
pub(crate) fn check_live_direct_loans(body: &Body, flow: &FlowGraph) -> Result<(), BorrowConflict> {
    check_live_direct_loans_with_types(body, flow, &LinearTypes::default())
}

pub(crate) fn check_live_direct_loans_with_types(
    body: &Body,
    flow: &FlowGraph,
    types: &LinearTypes,
) -> Result<(), BorrowConflict> {
    if !flow
        .nodes
        .iter()
        .any(|node| matches!(node.action, FlowAction::Borrow { .. }))
    {
        return Ok(());
    }
    let origins = flow.loan_origins(body);
    let consumptions = flow.consumptions(body, types);
    let live = flow.liveness(body);
    let scoped_ids = flow
        .nodes
        .iter()
        .filter_map(|node| match node.action {
            FlowAction::BorrowScopeEnd { scope } => Some(scope),
            _ => None,
        })
        .collect::<HashSet<_>>();
    let scoped_places = flow
        .nodes
        .iter()
        .enumerate()
        .filter_map(|(index, node)| match node.action {
            FlowAction::Borrow {
                value,
                ref place,
                mutable,
            } if scoped_ids.contains(&value) => {
                let projected = match place.root {
                    PlaceRoot::Local(binding) => {
                        origins.projected_referents(FlowNodeId(index), binding, &place.segments)
                    }
                    _ => Vec::new(),
                };
                let places = if projected.is_empty() {
                    vec![place.clone()]
                } else {
                    projected
                };
                Some((value, (places, mutable, node.span)))
            }
            _ => None,
        })
        .collect::<HashMap<_, _>>();
    let scoped_before = scoped_borrows_before(flow, &scoped_ids);
    for (index, node) in flow.nodes.iter().enumerate() {
        // Computed reference operands have no syntactic place, so lowering
        // represents their write as Evaluate. Resolve the evaluated target
        // rather than silently omitting the write from conflict checking.
        let computed_targets = match node.action {
            FlowAction::Evaluate(value) => match &body.nodes[value.0].kind {
                NodeKind::Form { head, children, .. }
                    if head == "deref-set" && children.len() == 3 =>
                {
                    origins.value_before(body, flow, FlowNodeId(index), children[1])
                }
                _ => Vec::new(),
            },
            _ => Vec::new(),
        };
        let (place, access) = match &node.action {
            FlowAction::Evaluate(_) if !computed_targets.is_empty() => {
                (&computed_targets[0].place, AccessKind::Write)
            }
            FlowAction::Read {
                place,
                place_base: false,
                ..
            } => {
                let event = FlowNodeId(index);
                let access = if consumptions.consumes_at(event, place) {
                    AccessKind::Move
                } else {
                    AccessKind::Read
                };
                (place, access)
            }
            FlowAction::Borrow { place, mutable, .. } => {
                (place, AccessKind::Borrow { mutable: *mutable })
            }
            FlowAction::Clone { place, .. } => (place, AccessKind::Clone),
            FlowAction::Assign { place, .. } => (place, AccessKind::Write),
            FlowAction::Write { place, .. } => (place, AccessKind::Write),
            FlowAction::Release { place, .. } => (place, AccessKind::Release),
            _ => continue,
        };
        let reference_value_access = match node.action {
            FlowAction::Read { value, .. } | FlowAction::Clone { value, .. } => {
                reads_through_reference(body, value)
            }
            _ => false,
        };
        let event = FlowNodeId(index);
        let mut projected = computed_targets
            .iter()
            .map(|origin| origin.place.clone())
            .collect::<Vec<_>>();
        let mut reborrow_parent = computed_targets
            .first()
            .and_then(|origin| origin.borrowed_from);
        if computed_targets.is_empty() && !matches!(access, AccessKind::Move) {
            if let PlaceRoot::Local(binding) = &place.root {
                projected = origins.projected_referents(event, *binding, &place.segments);
                if !projected.is_empty() {
                    reborrow_parent = Some(*binding);
                } else if matches!(access, AccessKind::Borrow { .. })
                    && matches!(
                        body.bindings[binding.0].ty,
                        Type::Reference { .. } | Type::PinnedReference { .. }
                    )
                {
                    // Borrowing the reference handle itself is not an access to
                    // the referent; its existing loan is the parent of a direct
                    // reborrow and is handled when a place is projected through it.
                    continue;
                }
            }
        }
        let access_places = if projected.is_empty() {
            vec![place.clone()]
        } else {
            projected
        };
        let mut suspended_parents = HashSet::new();
        let mut pending_parents = reborrow_parent.into_iter().collect::<Vec<_>>();
        while let Some(parent) = pending_parents.pop() {
            if !suspended_parents.insert(parent) {
                continue;
            }
            pending_parents.extend(
                origins
                    .before(event, parent)
                    .iter()
                    .filter_map(|origin| origin.borrowed_from),
            );
        }
        for binding in live.before(event) {
            if suspended_parents.contains(&binding) {
                continue;
            }
            if consumptions
                .definitely_consumed_before(event, &Place::root(PlaceRoot::Local(binding)))
            {
                continue;
            }
            for held in origins.before(event, binding) {
                let releasing_reborrow_parent =
                    match (&place.root, place.segments.is_empty(), access) {
                        (
                            PlaceRoot::Local(parent),
                            true,
                            AccessKind::Write | AccessKind::Release,
                        ) => held.borrowed_from == Some(*parent),
                        _ => false,
                    };
                if releasing_reborrow_parent {
                    let parent = match &place.root {
                        PlaceRoot::Local(parent) => body.bindings[parent.0].name.as_str(),
                        _ => unreachable!(),
                    };
                    return Err(BorrowConflict {
                        message: crate::analysis_error::failure!(
                            "cannot move or destroy reference '{parent}' while a derived reference is stored"
                        )
                        .message,
                        span: node.span,
                        labels: held
                            .span
                            .map(|span| (span, "derived reference originates here".into()))
                            .into_iter()
                            .collect(),
                    });
                }
                let forbidden_pinned_access = held.pinned
                    && !reference_value_access
                    && access_places.iter().any(|place| {
                        held.place.overlaps(place)
                            && match access {
                                AccessKind::Read => held.place == *place,
                                AccessKind::Clone => true,
                                _ => false,
                            }
                    });
                if forbidden_pinned_access {
                    let owner = match &held.place.root {
                        PlaceRoot::Local(binding) | PlaceRoot::Parameter(binding) => {
                            body.bindings[binding.0].name.as_str()
                        }
                        PlaceRoot::Global(_) => "static",
                    };
                    return Err(BorrowConflict {
                        message: crate::analysis_error::failure!(
                            "cannot copy pinned referent '{owner}' while its pinned reference is live"
                        )
                        .message,
                        span: node.span,
                        labels: held
                            .span
                            .into_iter()
                            .map(|span| (span, "referent pinned here".into()))
                            .collect(),
                    });
                }
                let conflicts = match access {
                    AccessKind::Read | AccessKind::Clone => held.mutable,
                    AccessKind::Borrow { mutable } => held.mutable || mutable,
                    AccessKind::Move | AccessKind::Write | AccessKind::Release => true,
                };
                if conflicts && access_places.iter().any(|place| held.place.overlaps(place)) {
                    let owner = match &held.place.root {
                        PlaceRoot::Local(binding) | PlaceRoot::Parameter(binding) => {
                            body.bindings[binding.0].name.as_str()
                        }
                        PlaceRoot::Global(_) => "static",
                    };
                    let message = match access {
                        AccessKind::Read => {
                            format!("cannot access '{owner}' while it is mutably borrowed")
                        }
                        AccessKind::Borrow { mutable: true } if held.mutable => {
                            format!("cannot borrow '{owner}' mutably because it is already borrowed mutably")
                        }
                        AccessKind::Borrow { mutable: true } => {
                            format!("cannot borrow '{owner}' mutably while a live reference exists")
                        }
                        AccessKind::Borrow { mutable: false } => {
                            format!(
                                "cannot borrow '{owner}' because it is already borrowed mutably"
                            )
                        }
                        AccessKind::Clone => {
                            format!("cannot clone '{owner}' while it is mutably borrowed")
                        }
                        AccessKind::Move => {
                            format!("cannot move '{owner}' while it is borrowed")
                        }
                        AccessKind::Write if held.mutable => {
                            format!("cannot mutate '{owner}' while it is mutably borrowed")
                        }
                        AccessKind::Write => {
                            format!("cannot mutate '{owner}' while it is immutably borrowed")
                        }
                        AccessKind::Release => {
                            format!("cannot destroy '{owner}' while it is borrowed")
                        }
                    };
                    return Err(BorrowConflict {
                        message: crate::analysis_error::failure!("{message}").message,
                        span: node.span,
                        labels: held
                            .span
                            .map(|span| (span, "borrow begins here".into()))
                            .into_iter()
                            .collect(),
                    });
                }
            }
        }
        let mut active_scopes = scoped_before[index].iter().copied().collect::<Vec<_>>();
        active_scopes.sort_by_key(|scope| scope.0);
        for scope in active_scopes {
            let Some((held_places, held_mutable, held_span)) = scoped_places.get(&scope) else {
                continue;
            };
            // A temporary borrow normally ends with its expression scope.
            // If a returned value carries that borrow, its precise lifetime
            // is instead governed by the live binding that owns the loan.
            // This matters for async start/poll calls: Pending retains the
            // returned frame, while Ready can consume it and release the
            // captured external borrow before the lexical block ends.
            let carried_by_live_value = held_span.is_some_and(|span| {
                let scoped_node = body.nodes[scope.0].kind.clone();
                let is_temporary_reference = matches!(
                    scoped_node,
                    NodeKind::Form { ref head, ref children, .. }
                        if matches!(head.as_str(), "borrow" | "borrow-mut" | "pin-borrow" | "pin-borrow-mut")
                            && children.len() == 2
                );
                if !is_temporary_reference {
                    return true;
                }
                live.before(event).iter().any(|binding| {
                    !consumptions.definitely_consumed_before(
                        event,
                        &Place::root(PlaceRoot::Local(*binding)),
                    ) && origins
                        .before(event, *binding)
                        .iter()
                        .any(|origin| origin.span == Some(span))
                })
            });
            if !carried_by_live_value {
                continue;
            }
            let mutable_scope_access = *held_mutable
                && matches!(
                    access,
                    AccessKind::Read | AccessKind::Clone | AccessKind::Write
                )
                && held_places.iter().any(|held_place| {
                    access_places.iter().any(|access| {
                        held_place.root == access.root
                            && access.segments.starts_with(&held_place.segments)
                    })
                });
            let held_is_parent_ancestor = matches!(access, AccessKind::Borrow { .. })
                && reborrow_parent.is_some()
                && *held_mutable
                && held_places.iter().any(|held_place| {
                    access_places.iter().any(|access| {
                        held_place.root == access.root
                            && access.segments.len() > held_place.segments.len()
                            && access.segments.starts_with(&held_place.segments)
                    })
                });
            if mutable_scope_access || held_is_parent_ancestor {
                continue;
            }
            let Some(held_place) = held_places
                .iter()
                .find(|held| access_places.iter().any(|place| held.overlaps(place)))
            else {
                continue;
            };
            let conflicts = match access {
                AccessKind::Read | AccessKind::Clone => *held_mutable,
                AccessKind::Borrow { mutable } => *held_mutable || mutable,
                AccessKind::Move | AccessKind::Write | AccessKind::Release => true,
            };
            if !conflicts {
                continue;
            }
            let owner = match &held_place.root {
                PlaceRoot::Local(binding) | PlaceRoot::Parameter(binding) => {
                    body.bindings[binding.0].name.as_str()
                }
                PlaceRoot::Global(_) => "static",
            };
            let message = match access {
                AccessKind::Read => format!("cannot access '{owner}' while it is mutably borrowed"),
                AccessKind::Borrow { mutable: true } if *held_mutable => {
                    format!(
                        "cannot borrow '{owner}' mutably because it is already borrowed mutably"
                    )
                }
                AccessKind::Borrow { mutable: true } => {
                    format!("cannot borrow '{owner}' mutably while a live reference exists")
                }
                AccessKind::Borrow { mutable: false } => {
                    format!("cannot borrow '{owner}' because it is already borrowed mutably")
                }
                AccessKind::Clone => format!("cannot clone '{owner}' while it is mutably borrowed"),
                AccessKind::Move => format!("cannot move '{owner}' while it is borrowed"),
                AccessKind::Write if *held_mutable => {
                    format!("cannot mutate '{owner}' while it is mutably borrowed")
                }
                AccessKind::Write => {
                    format!("cannot mutate '{owner}' while it is immutably borrowed")
                }
                AccessKind::Release => format!("cannot destroy '{owner}' while it is borrowed"),
            };
            return Err(BorrowConflict {
                message: crate::analysis_error::failure!("{message}").message,
                span: node.span,
                labels: held_span
                    .map(|span| (span, "borrow begins here".into()))
                    .into_iter()
                    .collect(),
            });
        }
    }
    Ok(())
}

fn scoped_borrows_before(flow: &FlowGraph, scoped_ids: &HashSet<NodeId>) -> Vec<HashSet<NodeId>> {
    let mut predecessors = vec![Vec::new(); flow.nodes.len()];
    for (index, node) in flow.nodes.iter().enumerate() {
        for successor in &node.successors {
            predecessors[successor.0].push(index);
        }
    }
    let mut before = vec![HashSet::new(); flow.nodes.len()];
    let mut after = before.clone();
    loop {
        let mut changed = false;
        for (index, node) in flow.nodes.iter().enumerate() {
            let mut incoming = HashSet::new();
            for predecessor in &predecessors[index] {
                incoming.extend(after[*predecessor].iter().copied());
            }
            let mut outgoing = incoming.clone();
            match node.action {
                FlowAction::Borrow { value, .. } if scoped_ids.contains(&value) => {
                    outgoing.insert(value);
                }
                FlowAction::BorrowScopeEnd { scope } => {
                    outgoing.remove(&scope);
                }
                _ => {}
            }
            if before[index] != incoming || after[index] != outgoing {
                before[index] = incoming;
                after[index] = outgoing;
                changed = true;
            }
        }
        if !changed {
            return before;
        }
    }
}

#[derive(Clone)]
struct DirectBorrow {
    place: Place,
    mutable: bool,
    span: Option<Span>,
    storage: Vec<crate::typed_place::Segment>,
}

pub(crate) fn check_call_arguments(body: &Body, flow: &FlowGraph) -> Result<(), BorrowConflict> {
    let calls = body
        .nodes
        .iter()
        .enumerate()
        .filter(|(_, node)| {
            matches!(
                node.kind,
                NodeKind::Form {
                    callee: Some(_),
                    ..
                }
            )
        })
        .collect::<Vec<_>>();
    if calls.is_empty() {
        return Ok(());
    }
    let call_events = flow
        .nodes
        .iter()
        .enumerate()
        .filter_map(|(index, node)| match node.action {
            FlowAction::Evaluate(id) => Some((id, FlowNodeId(index))),
            _ => None,
        })
        .collect::<HashMap<_, _>>();
    let origins = flow.loan_origins(body);
    let active = flow.definitely_active_bindings_before(body);
    for (index, node) in calls {
        let NodeKind::Form {
            head,
            children,
            callee: Some(_),
            ..
        } = &node.kind
        else {
            continue;
        };
        let mut bindings = BoundBorrows::new();
        let call_event = call_events.get(&NodeId(index)).copied();
        if let Some(event) = call_event {
            for index in 0..body.bindings.len() {
                let held = origins.before(event, BindingId(index));
                if let Some(alternatives) = origin_alternatives(held, node.span)? {
                    bindings.insert(BindingId(index), alternatives);
                }
            }
        }
        let mut prior = vec![Vec::<DirectBorrow>::new()];
        for argument in children.iter().skip(1) {
            let alternatives = returned_borrows_with_bindings(body, *argument, head, &bindings)?;
            if let Some(event) = call_event {
                if let Some(active) = active[event.0].as_ref() {
                    for borrow in alternatives.iter().flatten() {
                        let PlaceRoot::Local(binding) = &borrow.place.root else {
                            continue;
                        };
                        if !active.contains(&binding) {
                            let name = &body.bindings[binding.0].name;
                            return Err(BorrowConflict {
                                message: format!(
                                    "reference to block-local variable '{name}' escapes its scope"
                                ),
                                span: body.nodes[argument.0].span.or(node.span),
                                labels: borrow
                                    .span
                                    .map(|span| (span, "reference originates here".into()))
                                    .into_iter()
                                    .collect(),
                            });
                        }
                    }
                }
            }
            prior = combine(prior, alternatives, head, node.span)?;
        }
    }
    Ok(())
}

/// Enforce return-reference lifetimes from checked places and loan origins.
/// Function parameters are the only local roots permitted to outlive the body;
/// globals are represented as global places and do not enter this condition.
pub(crate) fn check_return_escapes(
    body: &Body,
    flow: &FlowGraph,
    parameter_count: usize,
) -> Result<(), BorrowConflict> {
    let origins = flow.loan_origins(body);
    for (index, node) in flow.nodes.iter().enumerate() {
        let FlowAction::Return(Some(value)) = &node.action else {
            continue;
        };
        for origin in origins.value_before(body, flow, FlowNodeId(index), *value) {
            let PlaceRoot::Local(binding) = origin.place.root else {
                continue;
            };
            if binding.0 < parameter_count {
                continue;
            }
            let name = &body.bindings[binding.0].name;
            return Err(BorrowConflict {
                message: format!("cannot return a value retaining a reference to local '{name}'"),
                span: node.span,
                labels: origin
                    .span
                    .map(|span| (span, "reference originates here".into()))
                    .into_iter()
                    .collect(),
            });
        }
    }
    Ok(())
}

/// Reject reference-bearing values transferred out of a lexical scope that
/// owns one of their referents. The source value may be nested in a block,
/// branch, match arm, or aggregate; typed loan origins resolve those forms
/// without reconstructing ownership from syntax names.
pub(crate) fn check_scope_escapes(body: &Body, flow: &FlowGraph) -> Result<(), BorrowConflict> {
    let origins = flow.loan_origins(body);
    let active = flow.definitely_active_bindings_before(body);
    for (index, node) in flow.nodes.iter().enumerate() {
        let value = match node.action {
            FlowAction::Bind { value, .. } | FlowAction::Pattern { value, .. } => value,
            _ => continue,
        };
        let Some(active) = active[index].as_ref() else {
            continue;
        };
        for origin in origins.value_before(body, flow, FlowNodeId(index), value) {
            let PlaceRoot::Local(binding) = origin.place.root else {
                continue;
            };
            if active.contains(&binding) {
                continue;
            }
            let name = &body.bindings[binding.0].name;
            return Err(BorrowConflict {
                message: format!("reference to block-local variable '{name}' escapes its scope"),
                span: body.nodes[value.0].span.or(node.span),
                labels: origin
                    .span
                    .map(|span| (span, "reference originates here".into()))
                    .into_iter()
                    .collect(),
            });
        }
    }
    Ok(())
}

type BoundBorrows = HashMap<BindingId, Vec<Vec<DirectBorrow>>>;

fn origin_alternatives(
    held: &[LoanOrigin],
    span: Option<Span>,
) -> Result<Option<Vec<Vec<DirectBorrow>>>, BorrowConflict> {
    if held.is_empty() {
        return Ok(None);
    }
    if held.iter().all(|origin| origin.storage.is_empty()) {
        let alternatives = held
            .iter()
            .map(|origin| {
                vec![DirectBorrow {
                    place: origin.place.clone(),
                    mutable: origin.mutable,
                    span: origin.span,
                    storage: Vec::new(),
                }]
            })
            .collect();
        return bounded(alternatives, span).map(Some);
    }
    use crate::typed_place::Segment;
    let mut variants = BTreeMap::<crate::typed_ir::AggregateId, BTreeSet<usize>>::new();
    for origin in held {
        for segment in &origin.storage {
            if let Segment::Payload(variant, _) = segment {
                variants
                    .entry(variant.owner)
                    .or_default()
                    .insert(variant.index);
            }
        }
    }
    let split_variants = variants
        .into_iter()
        .filter(|(_, indices)| indices.len() > 1)
        .collect::<Vec<_>>();
    let mut assignments = vec![HashMap::<crate::typed_ir::AggregateId, usize>::new()];
    for (owner, indices) in split_variants {
        let mut expanded = Vec::new();
        for assignment in &assignments {
            for index in &indices {
                let mut next = assignment.clone();
                next.insert(owner, *index);
                expanded.push(next);
            }
        }
        assignments = expanded;
    }
    let alternatives = assignments
        .into_iter()
        .map(|assignment| {
            held.iter()
                .filter(|origin| {
                    origin.storage.iter().all(|segment| match segment {
                        Segment::Payload(variant, _) => assignment
                            .get(&variant.owner)
                            .is_none_or(|index| *index == variant.index),
                        _ => true,
                    })
                })
                .map(|origin| DirectBorrow {
                    place: origin.place.clone(),
                    mutable: origin.mutable,
                    span: origin.span,
                    storage: origin.storage.clone(),
                })
                .collect()
        })
        .collect();
    bounded(alternatives, span).map(Some)
}

/// Each alternative is one execution path through the value expression.
/// Borrows within one alternative coexist; different alternatives do not.
fn returned_borrows_with_bindings(
    body: &Body,
    id: NodeId,
    callee: &str,
    bindings: &BoundBorrows,
) -> Result<Vec<Vec<DirectBorrow>>, BorrowConflict> {
    if let Some(borrow) = direct_borrow(body, id) {
        if let Some(resolved) = resolve_projected_borrow(body, &borrow, bindings)? {
            return bounded(resolved, body.nodes[id.0].span);
        }
        return Ok(vec![vec![borrow]]);
    }
    let node = &body.nodes[id.0];
    match &node.kind {
        NodeKind::Symbol {
            binding: Some(binding),
            ..
        } => Ok(bindings
            .get(binding)
            .cloned()
            .unwrap_or_else(|| vec![Vec::new()])),
        NodeKind::Form { head, children, .. }
            if matches!(
                head.as_str(),
                "get" | "get-payload" | "pin-get-payload" | "pin-get-payload-mut" | "index"
            ) =>
        {
            let Some(slot) =
                Place::from_expression(body, id).and_then(|place| place.segments.last().cloned())
            else {
                return Ok(vec![Vec::new()]);
            };
            let Some(parent) = children.get(1) else {
                return Ok(vec![Vec::new()]);
            };
            let mut alternatives = returned_borrows_with_bindings(body, *parent, callee, bindings)?;
            for alternative in &mut alternatives {
                alternative.retain_mut(|origin| {
                    if !origin
                        .storage
                        .first()
                        .is_some_and(|held| storage_segment_matches(&slot, held))
                    {
                        return false;
                    }
                    origin.storage.remove(0);
                    true
                });
            }
            alternatives.retain(|alternative| !alternative.is_empty());
            Ok(alternatives)
        }
        NodeKind::If {
            then_value,
            else_value,
            ..
        } => {
            let mut alternatives =
                returned_borrows_with_bindings(body, *then_value, callee, bindings)?;
            if let Some(otherwise) = else_value {
                alternatives.extend(returned_borrows_with_bindings(
                    body, *otherwise, callee, bindings,
                )?);
            } else {
                alternatives.push(Vec::new());
            }
            bounded(alternatives, node.span)
        }
        NodeKind::Match { value, arms, .. } => {
            let sources = returned_borrows_with_bindings(body, *value, callee, bindings)?;
            let mut alternatives = Vec::new();
            for arm in arms {
                let NodeKind::MatchArm { pattern, values } = &body.nodes[arm.0].kind else {
                    continue;
                };
                if let Some(value) = values.last() {
                    for source in &sources {
                        let mut local = bindings.clone();
                        let mut distributed = HashMap::new();
                        distribute_pattern_borrows(body, *pattern, source, &mut distributed);
                        for (binding, borrows) in distributed {
                            local.insert(binding, vec![borrows]);
                        }
                        alternatives.extend(returned_borrows_with_bindings(
                            body, *value, callee, &local,
                        )?);
                    }
                }
            }
            bounded(alternatives, node.span)
        }
        NodeKind::Loop(instructions) => {
            returned_loop_borrows(body, instructions, None, callee, bindings, node.span)
        }
        NodeKind::Block(instructions) => {
            let mut local = bindings.clone();
            for instruction in instructions {
                match &instruction.control {
                    Control::Bind(binding, value, _) => {
                        let loans = returned_borrows_with_bindings(body, *value, callee, &local)?;
                        local.insert(*binding, loans);
                    }
                    Control::Destructure { pattern, value, .. } => {
                        let alternatives =
                            returned_borrows_with_bindings(body, *value, callee, &local)?;
                        let mut distributed = HashMap::<BindingId, Vec<Vec<DirectBorrow>>>::new();
                        for alternative in alternatives {
                            let mut path = HashMap::new();
                            distribute_pattern_borrows(body, *pattern, &alternative, &mut path);
                            for (binding, borrows) in path {
                                distributed.entry(binding).or_default().push(borrows);
                            }
                        }
                        for (binding, alternatives) in distributed {
                            local.insert(binding, alternatives);
                        }
                    }
                    Control::Assign(PlaceRoot::Local(binding), _, _) => {
                        local.remove(binding);
                    }
                    _ => {}
                }
            }
            match instructions.last().map(|item| &item.control) {
                Some(Control::Evaluate(value)) => {
                    returned_borrows_with_bindings(body, *value, callee, &local)
                }
                _ => Ok(vec![Vec::new()]),
            }
        }
        NodeKind::Labeled(label, inner) => {
            if let NodeKind::Loop(instructions) = &body.nodes[inner.0].kind {
                returned_loop_borrows(body, instructions, Some(label), callee, bindings, node.span)
            } else {
                returned_borrows_with_bindings(body, *inner, callee, bindings)
            }
        }
        NodeKind::Form { head, children, .. } if head == "unsafe" && children.len() == 2 => {
            returned_borrows_with_bindings(body, children[1], callee, bindings)
        }
        NodeKind::Form { head, children, .. } if head == "clone" && children.len() == 2 => {
            returned_borrows_with_bindings(body, children[1], callee, bindings)
        }
        NodeKind::Form {
            children,
            callee: Some(_),
            ..
        } if matches!(
            node.ty,
            Some(
                Type::Reference { .. }
                    | Type::PinnedReference { .. }
                    | Type::Slice(_)
                    | Type::MutableSlice(_)
            )
        ) =>
        {
            let mut alternatives = Vec::new();
            for argument in children.iter().skip(1) {
                for mut alternative in
                    returned_borrows_with_bindings(body, *argument, callee, bindings)?
                {
                    for mut borrow in alternative.drain(..) {
                        borrow.storage.clear();
                        alternatives.push(vec![borrow]);
                    }
                }
            }
            bounded(alternatives, node.span)
        }
        NodeKind::Form { head, .. }
            if head == "array-repeat" && matches!(node.ty, Some(Type::Array(_, 0))) =>
        {
            Ok(vec![Vec::new()])
        }
        NodeKind::Form { head, children, .. }
            if matches!(
                head.as_str(),
                "tuple" | "array" | "array-of" | "array-repeat" | "struct-literal"
            ) || matches!(
                children.first().map(|child| &body.nodes[child.0].kind),
                Some(NodeKind::Declaration(
                    DeclarationId::Variant(_) | DeclarationId::Aggregate(_)
                ))
            ) =>
        {
            if head == "struct-literal" {
                return combine_children(
                    body,
                    children.iter().skip(1).copied(),
                    callee,
                    node.span,
                    bindings,
                );
            }
            let start = if matches!(
                children.first().map(|child| &body.nodes[child.0].kind),
                Some(NodeKind::Declaration(
                    DeclarationId::Variant(_) | DeclarationId::Aggregate(_)
                ))
            ) {
                1
            } else {
                constructor_values_start(node.ty.as_ref(), children.len())
            };
            let mut alternatives = vec![Vec::new()];
            for (index, child) in children.iter().skip(start).enumerate() {
                let slot = constructor_slot(body, head, children, index);
                let mut values = returned_borrows_with_bindings(body, *child, callee, bindings)?;
                if let Some(slot) = slot {
                    for alternative in &mut values {
                        for borrow in alternative {
                            borrow.storage.insert(0, slot.clone());
                        }
                    }
                }
                alternatives = combine(alternatives, values, callee, node.span)?;
            }
            Ok(alternatives)
        }
        NodeKind::Syntax(children) => {
            combine_children(body, children.iter().copied(), callee, node.span, bindings)
        }
        _ => Ok(vec![Vec::new()]),
    }
}

fn constructor_values_start(ty: Option<&Type>, child_count: usize) -> usize {
    let arity = match ty {
        Some(Type::Array(_, length)) => *length,
        Some(Type::Tuple(fields)) => fields.len(),
        _ => return 2,
    };
    if child_count == arity + 1 {
        1
    } else {
        2
    }
}

fn returned_loop_borrows(
    body: &Body,
    instructions: &[crate::typed_body::Instruction],
    label: Option<&str>,
    callee: &str,
    bindings: &BoundBorrows,
    span: Option<Span>,
) -> Result<Vec<Vec<DirectBorrow>>, BorrowConflict> {
    fn expression_breaks(
        body: &Body,
        expression: NodeId,
        label: Option<&str>,
        nested_loops: usize,
        values: &mut Vec<NodeId>,
    ) {
        match &body.nodes[expression.0].kind {
            NodeKind::If {
                condition,
                then_value,
                else_value,
                ..
            } => {
                expression_breaks(body, *condition, label, nested_loops, values);
                expression_breaks(body, *then_value, label, nested_loops, values);
                if let Some(value) = else_value {
                    expression_breaks(body, *value, label, nested_loops, values);
                }
            }
            NodeKind::Match { value, arms, .. } => {
                expression_breaks(body, *value, label, nested_loops, values);
                for arm in arms {
                    if let NodeKind::MatchArm { values: arms, .. } = &body.nodes[arm.0].kind {
                        for value in arms {
                            expression_breaks(body, *value, label, nested_loops, values);
                        }
                    }
                }
            }
            NodeKind::Block(instructions) => {
                instruction_breaks(body, instructions, label, nested_loops, values);
            }
            NodeKind::Loop(instructions) => {
                instruction_breaks(body, instructions, label, nested_loops + 1, values);
            }
            NodeKind::Labeled(loop_label, inner) => {
                if let NodeKind::Loop(instructions) = &body.nodes[inner.0].kind {
                    instruction_breaks(
                        body,
                        instructions,
                        Some(loop_label),
                        nested_loops + 1,
                        values,
                    );
                } else {
                    expression_breaks(body, *inner, label, nested_loops, values);
                }
            }
            NodeKind::Form { children, .. } | NodeKind::Syntax(children) => {
                for child in children {
                    expression_breaks(body, *child, label, nested_loops, values);
                }
            }
            NodeKind::Quoted(_, inner) => {
                expression_breaks(body, *inner, label, nested_loops, values);
            }
            NodeKind::Declaration(_) | NodeKind::Symbol { .. } | NodeKind::Literal(_) => {}
            NodeKind::MatchArm {
                pattern,
                values: arms,
            } => {
                expression_breaks(body, *pattern, label, nested_loops, values);
                for value in arms {
                    expression_breaks(body, *value, label, nested_loops, values);
                }
            }
        }
    }

    fn instruction_breaks(
        body: &Body,
        instructions: &[crate::typed_body::Instruction],
        label: Option<&str>,
        nested_loops: usize,
        values: &mut Vec<NodeId>,
    ) {
        for instruction in instructions {
            match &instruction.control {
                Control::Break(target, Some(value))
                    if (label.is_some() && target.as_deref() == label)
                        || (target.is_none() && nested_loops == 0) =>
                {
                    values.push(*value);
                    expression_breaks(body, *value, label, nested_loops, values);
                }
                Control::Break(_, Some(value))
                | Control::Bind(_, value, _)
                | Control::Assign(_, _, value)
                | Control::Evaluate(value) => {
                    expression_breaks(body, *value, label, nested_loops, values);
                }
                Control::Destructure { value, .. } => {
                    expression_breaks(body, *value, label, nested_loops, values);
                }
                Control::Loop(loop_body) => {
                    instruction_breaks(body, loop_body, label, nested_loops + 1, values);
                }
                Control::While(condition, loop_body) => {
                    expression_breaks(body, *condition, label, nested_loops + 1, values);
                    instruction_breaks(body, loop_body, label, nested_loops + 1, values);
                }
                Control::For(init, condition, step, loop_body) => {
                    instruction_breaks(
                        body,
                        std::slice::from_ref(init.as_ref()),
                        label,
                        nested_loops + 1,
                        values,
                    );
                    expression_breaks(body, *condition, label, nested_loops + 1, values);
                    instruction_breaks(
                        body,
                        std::slice::from_ref(step.as_ref()),
                        label,
                        nested_loops + 1,
                        values,
                    );
                    instruction_breaks(body, loop_body, label, nested_loops + 1, values);
                }
                Control::Labeled(_, nested) => {
                    instruction_breaks(
                        body,
                        std::slice::from_ref(nested.as_ref()),
                        label,
                        nested_loops,
                        values,
                    );
                }
                _ => {}
            }
        }
    }

    let mut values = Vec::new();
    instruction_breaks(body, instructions, label, 0, &mut values);
    let mut alternatives = Vec::new();
    for value in values {
        alternatives.extend(returned_borrows_with_bindings(
            body, value, callee, bindings,
        )?);
    }
    bounded(alternatives, span)
}

fn constructor_slot(
    body: &Body,
    head: &str,
    children: &[NodeId],
    index: usize,
) -> Option<crate::typed_place::Segment> {
    use crate::typed_place::Segment;
    match children.first().map(|child| &body.nodes[child.0].kind) {
        Some(NodeKind::Declaration(DeclarationId::Aggregate(owner))) => {
            Some(Segment::Field(FieldId {
                owner: *owner,
                index,
            }))
        }
        Some(NodeKind::Declaration(DeclarationId::Variant(variant))) => {
            Some(Segment::Payload(*variant, index))
        }
        _ => match head {
            "tuple" => Some(Segment::Tuple(index)),
            "array" | "array-of" => Some(Segment::Index(index as u128)),
            _ => None,
        },
    }
}

fn resolve_projected_borrow(
    body: &Body,
    borrow: &DirectBorrow,
    bindings: &BoundBorrows,
) -> Result<Option<Vec<Vec<DirectBorrow>>>, BorrowConflict> {
    let PlaceRoot::Local(binding) = borrow.place.root else {
        return Ok(None);
    };
    if borrow.place.segments.is_empty()
        || !matches!(
            body.bindings[binding.0].ty,
            Type::Reference { .. } | Type::PinnedReference { .. }
        )
    {
        return Ok(None);
    }
    let Some(places) = resolve_alias_places(
        body,
        &borrow.place,
        bindings,
        &mut HashSet::new(),
        borrow.span,
    )?
    else {
        return Ok(None);
    };
    Ok(Some(
        places
            .into_iter()
            .map(|place| {
                vec![DirectBorrow {
                    place,
                    mutable: borrow.mutable,
                    span: borrow.span,
                    storage: Vec::new(),
                }]
            })
            .collect(),
    ))
}

fn resolve_alias_places(
    body: &Body,
    place: &Place,
    bindings: &BoundBorrows,
    seen: &mut HashSet<BindingId>,
    span: Option<Span>,
) -> Result<Option<Vec<Place>>, BorrowConflict> {
    let PlaceRoot::Local(binding) = place.root else {
        return Ok(Some(vec![place.clone()]));
    };
    if place.segments.is_empty()
        || !matches!(
            body.bindings[binding.0].ty,
            Type::Reference { .. } | Type::PinnedReference { .. }
        )
    {
        return Ok(Some(vec![place.clone()]));
    }
    let Some(origins) = bindings.get(&binding) else {
        return Ok(None);
    };
    if seen.len() >= MAX_ALIAS_CHAIN_DEPTH {
        return Err(BorrowConflict {
            message: format!(
                "call argument reference chain exceeds {MAX_ALIAS_CHAIN_DEPTH} bindings"
            ),
            span,
            labels: Vec::new(),
        });
    }
    if !seen.insert(binding) {
        return Ok(None);
    }
    let mut resolved = Vec::new();
    for alternative in origins {
        let [origin] = alternative.as_slice() else {
            seen.remove(&binding);
            return Ok(None);
        };
        let mut next = origin.place.clone();
        next.segments.extend(place.segments.iter().cloned());
        let Some(places) = resolve_alias_places(body, &next, bindings, seen, span)? else {
            seen.remove(&binding);
            return Ok(None);
        };
        resolved.extend(places);
        if resolved.len() > MAX_BORROW_ALTERNATIVES {
            seen.remove(&binding);
            return Err(complexity_error(span));
        }
    }
    seen.remove(&binding);
    Ok(Some(resolved))
}

fn combine_children(
    body: &Body,
    children: impl Iterator<Item = NodeId>,
    callee: &str,
    span: Option<Span>,
    bindings: &BoundBorrows,
) -> Result<Vec<Vec<DirectBorrow>>, BorrowConflict> {
    let mut alternatives = vec![Vec::new()];
    for child in children {
        alternatives = combine(
            alternatives,
            returned_borrows_with_bindings(body, child, callee, bindings)?,
            callee,
            span,
        )?;
    }
    Ok(alternatives)
}

fn combine(
    left: Vec<Vec<DirectBorrow>>,
    right: Vec<Vec<DirectBorrow>>,
    callee: &str,
    span: Option<Span>,
) -> Result<Vec<Vec<DirectBorrow>>, BorrowConflict> {
    let mut result = Vec::new();
    let mut seen = HashSet::new();
    for existing in &left {
        for incoming in &right {
            let mut combined = existing.clone();
            for borrow in incoming {
                if borrow.mutable
                    && combined.iter().any(|first| {
                        first.mutable
                            && first.place == borrow.place
                            && first.span == borrow.span
                            && first.storage == borrow.storage
                    })
                {
                    continue;
                }
                if let Some(first) = combined.iter().find(|first| {
                    (first.mutable || borrow.mutable) && first.place.overlaps(&borrow.place)
                }) {
                    return Err(BorrowConflict {
                        message: format!(
                            "call to '{callee}' passes overlapping borrows; at most one may be mutable"
                        ),
                        span: borrow.span.or(span),
                        labels: first
                            .span
                            .map(|span| (span, "first borrow is passed here".into()))
                            .into_iter()
                            .collect(),
                    });
                }
                combined.push(borrow.clone());
            }
            let key = borrow_key(&combined);
            if seen.insert(key) {
                result.push(combined);
                if result.len() > MAX_BORROW_ALTERNATIVES {
                    return Err(complexity_error(span));
                }
            }
        }
    }
    Ok(result)
}

fn bounded(
    alternatives: Vec<Vec<DirectBorrow>>,
    span: Option<Span>,
) -> Result<Vec<Vec<DirectBorrow>>, BorrowConflict> {
    let mut unique = Vec::new();
    let mut seen = HashSet::new();
    for alternative in alternatives {
        if seen.insert(borrow_key(&alternative)) {
            unique.push(alternative);
            if unique.len() > MAX_BORROW_ALTERNATIVES {
                return Err(complexity_error(span));
            }
        }
    }
    Ok(unique)
}

fn borrow_key(borrows: &[DirectBorrow]) -> Vec<(Place, bool, Vec<crate::typed_place::Segment>)> {
    borrows
        .iter()
        .map(|borrow| (borrow.place.clone(), borrow.mutable, borrow.storage.clone()))
        .collect()
}

fn complexity_error(span: Option<Span>) -> BorrowConflict {
    BorrowConflict {
        message: format!(
            "call argument has more than {MAX_BORROW_ALTERNATIVES} borrow paths; split the expression"
        ),
        span,
        labels: Vec::new(),
    }
}

fn direct_borrow(body: &Body, id: NodeId) -> Option<DirectBorrow> {
    let node = body.nodes.get(id.0)?;
    let NodeKind::Form { head, children, .. } = &node.kind else {
        return None;
    };
    if head == "unsafe" && children.len() == 2 {
        return direct_borrow(body, children[1]);
    }
    if !matches!(
        head.as_str(),
        "borrow" | "borrow-mut" | "pin-borrow" | "pin-borrow-mut"
    ) || children.len() != 2
    {
        return None;
    }
    Some(DirectBorrow {
        place: Place::from_expression(body, children[1])?,
        mutable: matches!(head.as_str(), "borrow-mut" | "pin-borrow-mut"),
        span: node.span,
        storage: Vec::new(),
    })
}

fn storage_segment_matches(
    wanted: &crate::typed_place::Segment,
    held: &crate::typed_place::Segment,
) -> bool {
    use crate::typed_place::Segment;
    wanted == held
        || matches!(
            (wanted, held),
            (Segment::DynamicIndex, Segment::Index(_)) | (Segment::Index(_), Segment::DynamicIndex)
        )
        || matches!((wanted, held), (Segment::Tuple(wanted), Segment::SliceHalf(found)) if wanted == found)
}

fn distribute_pattern_borrows(
    body: &Body,
    pattern: NodeId,
    origins: &[DirectBorrow],
    output: &mut HashMap<BindingId, Vec<DirectBorrow>>,
) {
    match &body.nodes[pattern.0].kind {
        NodeKind::Symbol {
            binding: Some(binding),
            ..
        } => {
            output.insert(
                *binding,
                origins
                    .iter()
                    .filter(|origin| origin.storage.is_empty())
                    .cloned()
                    .collect(),
            );
        }
        NodeKind::Form { head, children, .. } => {
            let declaration = children.first().map(|child| &body.nodes[child.0].kind);
            for (index, child) in children.iter().skip(1).enumerate() {
                let slot = match declaration {
                    Some(NodeKind::Declaration(DeclarationId::Aggregate(owner))) => {
                        Some(crate::typed_place::Segment::Field(FieldId {
                            owner: *owner,
                            index,
                        }))
                    }
                    Some(NodeKind::Declaration(DeclarationId::Variant(variant))) => {
                        Some(crate::typed_place::Segment::Payload(*variant, index))
                    }
                    _ => match head.as_str() {
                        "tuple" => Some(crate::typed_place::Segment::Tuple(index)),
                        "array" | "array-of" => {
                            Some(crate::typed_place::Segment::Index(index as u128))
                        }
                        _ => None,
                    },
                };
                let Some(slot) = slot else { continue };
                let nested = origins
                    .iter()
                    .filter_map(|origin| {
                        if !origin
                            .storage
                            .first()
                            .is_some_and(|held| storage_segment_matches(&slot, held))
                        {
                            return None;
                        }
                        let mut origin = origin.clone();
                        origin.storage.remove(0);
                        Some(origin)
                    })
                    .collect::<Vec<_>>();
                distribute_pattern_borrows(body, *child, &nested, output);
            }
        }
        _ => {}
    }
}

#[cfg(test)]
mod tests {
    use super::{
        bounded, check_call_arguments, check_live_direct_loans, check_scope_escapes, combine,
        origin_alternatives, returned_borrows_with_bindings, BoundBorrows, DirectBorrow,
        MAX_BORROW_ALTERNATIVES,
    };
    use crate::typed_body::{BindingId, NodeId, NodeKind, PlaceRoot};
    use crate::typed_flow::{FlowAction, FlowGraph, FlowNode, FlowNodeId, LoanOrigin};
    use crate::typed_place::Place;
    use crate::Type;

    fn source(args: &str) -> String {
        format!(
            "(#fn inspect ((left (#ref-mut u64)) (right (#ref u64))) u64
               (#forget left) (#forget right) (#return 0u64))
             (#fn main () u64
               (#let-mut value u64 1u64)
               (#return (#call inspect ( {args}))))"
        )
    }

    #[test]
    fn scope_escape_analysis_accepts_references_that_stay_with_their_owner() {
        let source = "(#fn main () u64
          (#let result u64
            (#block
              (#let owner u64 41u64)
              (#let view (#ref u64) (#borrow owner))
              (#deref view)))
          (#return result))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let flow = &checked.declarations().flows["main"];
        check_scope_escapes(body, flow).unwrap();
    }

    #[test]
    fn call_scope_analysis_accepts_arguments_borrowed_from_live_locals() {
        let source = "(#fn read ((input (#ref u64))) u64 (#return (#deref input)))
          (#fn main () u64
            (#let owner u64 42u64)
            (#return (#call read (: input (#borrow owner)))))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let flow = &checked.declarations().flows["main"];
        check_call_arguments(body, flow).unwrap();
    }

    #[test]
    fn live_reference_conflict_uses_checked_places_and_origin_spans() {
        let source = "(#fn main () u64
            (#let-mut left u64 1u64)
            (#let-mut right u64 2u64)
            (#let view (#ref-mut u64) (#borrow-mut left))
            (#let other (#ref u64) (#borrow right))
            (#return (#deref view)))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let mut flow = FlowGraph::lower(body).unwrap();
        check_live_direct_loans(body, &flow).unwrap();

        let left = BindingId(body.bindings.iter().position(|b| b.name == "left").unwrap());
        let right = BindingId(
            body.bindings
                .iter()
                .position(|b| b.name == "right")
                .unwrap(),
        );
        let second = flow
            .nodes
            .iter_mut()
            .find(|node| {
                matches!(&node.action, FlowAction::Borrow { place, .. }
                    if place.root == PlaceRoot::Local(right))
            })
            .unwrap();
        let FlowAction::Borrow { place, .. } = &mut second.action else {
            unreachable!()
        };
        place.root = PlaceRoot::Local(left);
        let error = check_live_direct_loans(body, &flow).unwrap_err();
        let span = error.span.unwrap();
        assert_eq!(&source[span.start..span.end], "(#borrow right)");
        let first = error.labels[0].0;
        assert_eq!(&source[first.start..first.end], "(#borrow-mut left)");
    }

    #[test]
    fn moving_a_borrowed_owner_into_a_by_value_call_is_rejected() {
        let source = "(#struct Token ((value u64)))
          (#linear Token)
          (#fn consume ((token Token)) () (#drop token) (#return ()))
          (#fn main () ()
            (#let-mut owner Token (#struct-literal Token ((value 1u64))))
            (#let view (#ref Token) (#borrow owner))
            (#call consume (: token owner))
            (#forget view)
            (#return ()))";
        let program = crate::parse_program(source).unwrap();
        let error = match crate::CheckedProgram::validate(&program) {
            Ok(_) => panic!("moving a borrowed linear owner must fail"),
            Err(error) => error,
        };
        assert!(error.contains("cannot move 'owner' while it is borrowed"));
    }

    #[test]
    fn enum_returned_reference_payload_remains_a_live_borrow() {
        let source = "(#struct Token ((value u64)))
          (#struct RefBox ((value (#ref Token))))
          (#opaque RefBox)
          (#enum Maybe ((Some RefBox) None))
          (#fn wrap ((input (#ref Token))) Maybe
            (#return (Some (#struct-literal RefBox ((value input))))))
          (#fn main () ()
            (#let-mut owner Token (#struct-literal Token ((value 1u64))))
            (#let option Maybe (#call wrap (: input (#borrow owner))))
            (#let result RefBox
              (#match option
                (#case (Some box) box)
                (#case None (#unreachable))))
            (#drop owner)
            (#forget result)
            (#return ()))";
        let program = crate::parse_program(source).unwrap();
        let error = match crate::CheckedProgram::validate(&program) {
            Ok(_) => panic!("dropping an owner retained by an enum payload must fail"),
            Err(error) => error,
        };
        assert!(
            error.contains("cannot destroy 'owner' while it is borrowed"),
            "{error}"
        );
    }

    #[test]
    fn dereference_reads_rebase_to_the_referent() {
        let source = "(#fn main () u64
            (#let-mut value u64 1u64)
            (#let parent (#ref u64) (#borrow value))
            (#let observed u64 (#deref parent))
            (#return 0u64))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let flow = FlowGraph::lower(body).unwrap();
        let origins = flow.loan_origins(body);
        let read = flow
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| match &node.action {
                FlowAction::Read { place, .. }
                    if place
                        .segments
                        .contains(&crate::typed_place::Segment::Dereference) =>
                {
                    Some((FlowNodeId(index), place))
                }
                _ => None,
            })
            .unwrap();
        let parent = BindingId(
            body.bindings
                .iter()
                .position(|binding| binding.name == "parent")
                .unwrap(),
        );
        let value = BindingId(
            body.bindings
                .iter()
                .position(|binding| binding.name == "value")
                .unwrap(),
        );
        assert_eq!(read.1.root, PlaceRoot::Local(parent));
        assert_eq!(
            origins.projected_referents(read.0, parent, &read.1.segments),
            vec![Place::root(PlaceRoot::Local(value))]
        );
    }

    #[test]
    fn reference_returning_call_writes_conflict_with_live_child_borrows() {
        let source = "(#struct Point ((x u64) (y u64)))
            (#fn identity ((value (#ref-mut Point))) (#ref-mut Point)
              (#return value))
            (#fn main () u64
              (#let-mut point Point (#struct-literal Point ((x 1u64) (y 2u64))))
              (#let parent (#ref-mut Point) (#borrow-mut point))
              (#let child (#ref u64) (#borrow (#get parent x)))
              (#forget child)
              (#deref-set (#call identity (: value parent))
                (#struct-literal Point ((x 3u64) (y 4u64))))
              (#return 0u64))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let mut flow = FlowGraph::lower(body).unwrap();
        check_live_direct_loans(body, &flow).unwrap();
        let release = flow
            .nodes
            .iter()
            .position(|node| matches!(node.action, FlowAction::Release { .. }))
            .unwrap();
        let action = flow
            .nodes
            .iter()
            .find_map(|node| match node.action {
                FlowAction::Evaluate(value)
                    if matches!(&body.nodes[value.0].kind,
                NodeKind::Form { head, .. } if head == "deref-set") =>
                {
                    Some(node.action.clone())
                }
                _ => None,
            })
            .expect("computed target must lower as Evaluate");
        let write = FlowNodeId(flow.nodes.len());
        let predecessor = flow
            .nodes
            .iter_mut()
            .find(|node| node.successors.contains(&FlowNodeId(release)))
            .unwrap();
        for successor in &mut predecessor.successors {
            if *successor == FlowNodeId(release) {
                *successor = write;
            }
        }
        flow.nodes.push(FlowNode {
            action,
            successors: vec![FlowNodeId(release)],
            span: None,
        });
        let error = check_live_direct_loans(body, &flow).unwrap_err();
        assert!(
            error.message.contains("cannot mutate 'point'"),
            "{}",
            error.message
        );
    }

    #[test]
    fn dereference_writes_conflict_with_live_child_borrows() {
        let source = "(#struct Point ((x u64) (y u64)))
            (#fn main () u64
              (#let-mut point Point (#struct-literal Point ((x 1u64) (y 2u64))))
              (#let parent (#ref-mut Point) (#borrow-mut point))
              (#let child (#ref u64) (#borrow (#get parent x)))
              (#forget child)
              (#deref-set parent (#struct-literal Point ((x 3u64) (y 4u64))))
              (#return 0u64))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let mut flow = FlowGraph::lower(body).unwrap();
        let parent = BindingId(
            body.bindings
                .iter()
                .position(|binding| binding.name == "parent")
                .unwrap(),
        );
        let child = BindingId(
            body.bindings
                .iter()
                .position(|binding| binding.name == "child")
                .unwrap(),
        );
        let release = flow
            .nodes
            .iter()
            .position(|node| {
                matches!(&node.action, FlowAction::Release { place, .. }
                    if place.root == PlaceRoot::Local(child))
            })
            .unwrap();
        let (place, value) = flow
            .nodes
            .iter()
            .find_map(|node| match &node.action {
                FlowAction::Write { place, value } => Some((place.clone(), *value)),
                _ => None,
            })
            .unwrap();
        assert_eq!(place.root, PlaceRoot::Local(parent));
        assert_eq!(
            place.segments,
            vec![crate::typed_place::Segment::Dereference]
        );
        let write = FlowNodeId(flow.nodes.len());
        flow.nodes.push(FlowNode {
            action: FlowAction::Write { place, value },
            successors: vec![FlowNodeId(release)],
            span: None,
        });
        let predecessor = flow
            .nodes
            .iter_mut()
            .find(|node| node.successors.contains(&FlowNodeId(release)))
            .unwrap();
        for successor in &mut predecessor.successors {
            if *successor == FlowNodeId(release) {
                *successor = write;
            }
        }
        let error = check_live_direct_loans(body, &flow).unwrap_err();
        assert!(error.message.contains("cannot mutate 'point'"));
        // Exercise the event representation used when the reference target
        // cannot be represented by a syntactic place.
        flow.nodes[write.0].action = FlowAction::Evaluate(value);
        let error = check_live_direct_loans(body, &flow).unwrap_err();
        assert!(error.message.contains("cannot mutate 'point'"));
    }

    #[test]
    fn split_slice_writes_use_distinct_typed_half_places() {
        let source = "(#fn main () u64
            (#let-mut values (#array u64 4)
              (#array-of (#array u64 4) 1u64 2u64 3u64 4u64))
            (#let view (#slice-mut u64) (#slice-mut-of (#borrow-mut values)))
            (#let (#tuple left right) (#tuple (#slice-mut u64) (#slice-mut u64))
              (#slice-mut-split view 2usize))
            (#deref-set (#slice-mut-idx left 0usize) 10u64)
            (#deref-set (#slice-mut-idx right 0usize) 20u64)
            (#forget left) (#forget right)
            (#return 0u64))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let flow = FlowGraph::lower(body).unwrap();
        let origins = flow.loan_origins(body);
        let writes = flow
            .nodes
            .iter()
            .enumerate()
            .filter_map(|(index, node)| match &node.action {
                FlowAction::Write { place, .. } => Some((FlowNodeId(index), place.clone())),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(writes.len(), 2);
        let split_places = writes
            .iter()
            .map(|(_, place)| {
                let event = writes
                    .iter()
                    .find(|(_, candidate)| candidate == place)
                    .unwrap()
                    .0;
                let PlaceRoot::Local(binding) = place.root else {
                    unreachable!()
                };
                origins.projected_referents(event, binding, &place.segments)
            })
            .collect::<Vec<_>>();
        assert_ne!(split_places[0], split_places[1]);
        check_live_direct_loans(body, &flow).unwrap();
    }

    #[test]
    fn nested_split_slice_writes_keep_the_full_partition_path() {
        let source = "(#fn main () u64
            (#let-mut values (#array u64 8)
              (#array-of (#array u64 8) 1u64 2u64 3u64 4u64 5u64 6u64 7u64 8u64))
            (#let view (#slice-mut u64) (#slice-mut-of (#borrow-mut values)))
            (#let (#tuple left right) (#tuple (#slice-mut u64) (#slice-mut u64))
              (#slice-mut-split view 4usize))
            (#let (#tuple first second) (#tuple (#slice-mut u64) (#slice-mut u64))
              (#slice-mut-split left 2usize))
            (#deref-set (#slice-mut-idx first 0usize) 10u64)
            (#deref-set (#slice-mut-idx second 0usize) 20u64)
            (#deref-set (#slice-mut-idx right 0usize) 30u64)
            (#forget first) (#forget second) (#forget right)
            (#return 0u64))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let flow = FlowGraph::lower(body).unwrap();
        let origins = flow.loan_origins(body);
        let writes = flow
            .nodes
            .iter()
            .enumerate()
            .filter_map(|(index, node)| match &node.action {
                FlowAction::Write { place, .. } => Some((FlowNodeId(index), place.clone())),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(writes.len(), 3);
        let referents = writes
            .iter()
            .map(|(event, place)| {
                let PlaceRoot::Local(binding) = place.root else {
                    unreachable!()
                };
                origins.projected_referents(*event, binding, &place.segments)
            })
            .collect::<Vec<_>>();
        assert!(referents.iter().all(|places| places.len() == 1));
        assert!(referents[0][0].overlaps(&referents[1][0]) == false);
        assert!(referents[0][0].overlaps(&referents[2][0]) == false);
        assert!(referents[1][0].overlaps(&referents[2][0]) == false);
        check_live_direct_loans(body, &flow).unwrap();
    }

    #[test]
    fn scoped_borrow_conflicts_are_checked_on_typed_control_flow() {
        let source = "(#fn main () u64
            (#let-mut value u64 1u64)
            (#return (#borrow value (#borrow-mut value 2u64))))";
        let program = crate::parse_program(source).unwrap();
        let error = crate::CheckedProgram::validate(&program).err().unwrap();
        assert!(error.contains("cannot borrow 'value' mutably while a live reference exists"));
    }

    #[test]
    fn typed_scoped_borrow_ends_before_following_accesses() {
        let source = "(#fn main () u64
            (#let-mut value u64 1u64)
            (#borrow value 2u64)
            (#borrow-mut value 3u64)
            (#return value))";
        let program = crate::parse_program(source).unwrap();
        crate::CheckedProgram::validate(&program).unwrap();
    }

    #[test]
    fn mutable_scoped_borrow_authorizes_access_within_its_region() {
        let source = "(#fn main () u64
            (#let-mut value u64 1u64)
            (#borrow-mut value (#block (#set value 2u64) value))
            (#return value))";
        let program = crate::parse_program(source).unwrap();
        crate::CheckedProgram::validate(&program).unwrap();
    }

    #[test]
    fn scoped_loan_remains_active_on_each_branch() {
        let source = "(#fn main () u64
            (#let-mut value u64 1u64)
            (#return (#borrow value
              (#if true (#borrow-mut value 2u64) 3u64))))";
        let program = crate::parse_program(source).unwrap();
        let error = crate::CheckedProgram::validate(&program).err().unwrap();
        assert!(error.contains("cannot borrow 'value' mutably while a live reference exists"));
    }

    #[test]
    fn scoped_loan_is_ended_at_a_branch_join() {
        let source = "(#fn main () u64
            (#let-mut value u64 1u64)
            (#if true (#borrow value 2u64) 3u64)
            (#borrow-mut value 4u64)
            (#return value))";
        let program = crate::parse_program(source).unwrap();
        crate::CheckedProgram::validate(&program).unwrap();
    }

    #[test]
    fn scoped_field_reborrow_conflicts_on_the_referent_projection() {
        let source = "(#struct Pair ((left u64) (right u64)))
          (#fn main () u64
            (#let-mut pair Pair (#struct-literal Pair ((left 1u64) (right 2u64))))
            (#let parent (#ref-mut Pair) (#borrow-mut pair))
            (#borrow-mut (#get parent left)
              (#block
                (#let view (#ref u64) (#borrow (#get parent left)))
                3u64))
            (#return 0u64))";
        let program = crate::parse_program(source).unwrap();
        let error = crate::CheckedProgram::validate(&program).err().unwrap();
        assert!(error.contains("cannot borrow 'pair'"), "{error}");
    }

    #[test]
    fn scoped_field_reborrow_keeps_disjoint_siblings_available() {
        let source = "(#struct Pair ((left u64) (right u64)))
          (#fn main () u64
            (#let-mut pair Pair (#struct-literal Pair ((left 1u64) (right 2u64))))
            (#let parent (#ref-mut Pair) (#borrow-mut pair))
            (#borrow-mut (#get parent left)
              (#block
                (#let view (#ref u64) (#borrow (#get parent right)))
                (#drop view)
                3u64))
            (#return 0u64))";
        let program = crate::parse_program(source).unwrap();
        crate::CheckedProgram::validate(&program).unwrap();
    }

    #[test]
    fn escaping_loop_exit_ends_the_scoped_loan() {
        let source = "(#fn main () u64
            (#let-mut value u64 1u64)
            (#label outer
              (#loop (#borrow-mut value (#block (#break-to outer) ()))))
            (#borrow-mut value 2u64)
            (#return value))";
        let program = crate::parse_program(source).unwrap();
        crate::CheckedProgram::validate(&program).unwrap();
    }

    #[test]
    fn return_inside_scoped_borrow_runs_typed_scope_cleanup() {
        let source = "(#fn main () ()
            (#let-mut value u64 1u64)
            (#borrow-mut value (#block (#return ())))
            (#return ()))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let flow = FlowGraph::lower(body).unwrap();
        assert!(flow.nodes.iter().any(|node| {
            if !matches!(node.action, FlowAction::Return(Some(_)))
                || !node
                    .span
                    .is_some_and(|span| source[span.start..span.end].contains("#return ()"))
            {
                return false;
            }
            let mut next = node.successors.first().copied();
            for _ in 0..flow.nodes.len() {
                let Some(successor) = next else { break };
                if matches!(
                    flow.nodes[successor.0].action,
                    FlowAction::BorrowScopeEnd { .. }
                ) {
                    return true;
                }
                next = flow.nodes[successor.0].successors.first().copied();
            }
            false
        }));
    }

    #[test]
    fn scoped_loan_is_released_on_every_loop_iteration() {
        let source = "(#fn main () u64
            (#let-mut value u64 1u64)
            (#for-range (iteration u64) 0u64 3u64
              (#borrow value 2u64))
            (#borrow-mut value 4u64)
            (#return value))";
        let program = crate::parse_program(source).unwrap();
        crate::CheckedProgram::validate(&program).unwrap();
    }

    #[test]
    fn projected_reborrow_suspends_parent_access_but_preserves_disjoint_fields() {
        let overlapping = "(#struct Inner ((value u64)))
          (#struct Outer ((inner Inner) (other u64)))
          (#fn main () u64
            (#let-mut owner Outer (#struct-literal Outer
              ((inner (#struct-literal Inner ((value 7u64)))) (other 9u64))))
            (#let outer-ref (#ref-mut Outer) (#borrow-mut owner))
            (#let inner-ref (#ref-mut Inner) (#borrow-mut (#get outer-ref inner)))
            (#let observed u64 (#get outer-ref other))
            (#drop inner-ref)
            (#drop outer-ref)
            (#forget owner)
            (#return observed))";
        let program = crate::parse_program(overlapping).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let mut flow = checked.declarations().flows["main"].clone();
        check_live_direct_loans(body, &flow).unwrap();
        let declarations = checked.declarations();
        let outer = Type::Named("Outer".into());
        let inner = Type::Named("Inner".into());
        let inner_field = declarations.field_id(&outer, "inner").unwrap();
        let value_field = declarations.field_id(&inner, "value").unwrap();
        let other_field = declarations.field_id(&outer, "other").unwrap();
        let outer_ref = BindingId(
            body.bindings
                .iter()
                .position(|binding| binding.name == "outer-ref")
                .unwrap(),
        );
        let access = flow
            .nodes
            .iter_mut()
            .find_map(|node| match &mut node.action {
                FlowAction::Read { place, .. }
                    if place.root == PlaceRoot::Local(outer_ref)
                        && place.segments == [crate::typed_place::Segment::Field(other_field)] =>
                {
                    place.segments = vec![
                        crate::typed_place::Segment::Field(inner_field),
                        crate::typed_place::Segment::Field(value_field),
                    ];
                    Some(())
                }
                _ => None,
            });
        assert!(access.is_some());
        let error = check_live_direct_loans(body, &flow).unwrap_err();
        let span = error.span.unwrap();
        assert_eq!(&overlapping[span.start..span.end], "(#get outer-ref other)");

        let disjoint = "(#struct Outer ((left u64) (right u64)))
          (#fn main () u64
            (#let-mut owner Outer (#struct-literal Outer ((left 7u64) (right 9u64))))
            (#let outer-ref (#ref-mut Outer) (#borrow-mut owner))
            (#let left-ref (#ref-mut u64) (#borrow-mut (#get outer-ref left)))
            (#let right u64 (#get outer-ref right))
            (#drop left-ref)
            (#drop outer-ref)
            (#forget owner)
            (#return right))";
        let program = crate::parse_program(disjoint).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        check_live_direct_loans(body, &checked.declarations().flows["main"]).unwrap();
    }

    #[test]
    fn aggregate_held_loan_conflicts_with_checked_borrow_event() {
        let source = "(#struct Holder ((view (#ref-mut u64))))
          (#fn main () u64
            (#let-mut left u64 1u64)
            (#let-mut right u64 2u64)
            (#let holder Holder
              (#struct-literal Holder ((view (#borrow-mut left)))))
            (#let other (#ref u64) (#borrow right))
            (#let result u64 (#deref (#get holder view)))
            (#forget holder)
            (#return result))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let mut flow = FlowGraph::lower(body).unwrap();
        check_live_direct_loans(body, &flow).unwrap();

        let left = BindingId(body.bindings.iter().position(|b| b.name == "left").unwrap());
        let right = BindingId(
            body.bindings
                .iter()
                .position(|b| b.name == "right")
                .unwrap(),
        );
        let second = flow
            .nodes
            .iter_mut()
            .find(|node| {
                matches!(&node.action, FlowAction::Borrow { place, .. }
                if place.root == PlaceRoot::Local(right))
            })
            .unwrap();
        let FlowAction::Borrow { place, .. } = &mut second.action else {
            unreachable!()
        };
        place.root = PlaceRoot::Local(left);
        let error = check_live_direct_loans(body, &flow).unwrap_err();
        let span = error.span.unwrap();
        assert_eq!(&source[span.start..span.end], "(#borrow right)");
        let first = error.labels[0].0;
        assert_eq!(&source[first.start..first.end], "(#borrow-mut left)");
    }

    #[test]
    fn explicit_release_keeps_aggregate_loan_live() {
        let source = "(#struct Holder ((view (#ref-mut u64))))
          (#fn main () u64
            (#let-mut left u64 1u64)
            (#let-mut right u64 2u64)
            (#let holder Holder
              (#struct-literal Holder ((view (#borrow-mut left)))))
            (#let other (#ref u64) (#borrow right))
            (#forget holder)
            (#return 0u64))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let mut flow = FlowGraph::lower(body).unwrap();
        check_live_direct_loans(body, &flow).unwrap();
        let left = BindingId(body.bindings.iter().position(|b| b.name == "left").unwrap());
        let holder = BindingId(
            body.bindings
                .iter()
                .position(|b| b.name == "holder")
                .unwrap(),
        );
        let right = BindingId(
            body.bindings
                .iter()
                .position(|b| b.name == "right")
                .unwrap(),
        );
        let event = flow
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| {
                matches!(&node.action, FlowAction::Borrow { place, .. }
                if place.root == PlaceRoot::Local(right))
                .then_some(FlowNodeId(index))
            })
            .unwrap();
        assert!(flow.liveness(body).before(event).contains(&holder));
        let FlowAction::Borrow { place, .. } = &mut flow.nodes[event.0].action else {
            unreachable!()
        };
        place.root = PlaceRoot::Local(left);
        let error = check_live_direct_loans(body, &flow).unwrap_err();
        let span = error.labels[0].0;
        assert_eq!(&source[span.start..span.end], "(#borrow-mut left)");
    }

    #[test]
    fn write_conflict_uses_checked_place_and_loan_origin() {
        let source = "(#fn main () u64
            (#let-mut left u64 1u64)
            (#let-mut right u64 2u64)
            (#let view (#ref u64) (#borrow left))
            (#set right 3u64)
            (#return (#deref view)))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let mut flow = FlowGraph::lower(body).unwrap();
        check_live_direct_loans(body, &flow).unwrap();
        let left = BindingId(body.bindings.iter().position(|b| b.name == "left").unwrap());
        let right = BindingId(
            body.bindings
                .iter()
                .position(|b| b.name == "right")
                .unwrap(),
        );
        let write = flow
            .nodes
            .iter_mut()
            .find(|node| {
                matches!(&node.action, FlowAction::Assign { place, .. }
                if place.root == PlaceRoot::Local(right))
            })
            .unwrap();
        let FlowAction::Assign { place, .. } = &mut write.action else {
            unreachable!()
        };
        place.root = PlaceRoot::Local(left);
        let error = check_live_direct_loans(body, &flow).unwrap_err();
        assert!(error.message.contains("cannot mutate"));
        let span = error.span.unwrap();
        assert_eq!(&source[span.start..span.end], "(#set right 3u64)");
        let first = error.labels[0].0;
        assert_eq!(&source[first.start..first.end], "(#borrow left)");
    }

    #[test]
    fn explicit_release_conflict_uses_checked_place_and_loan_origin() {
        let source = "(#fn main () u64
            (#let left u64 1u64)
            (#let right u64 2u64)
            (#let view (#ref u64) (#borrow left))
            (#forget right)
            (#return (#deref view)))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let mut flow = FlowGraph::lower(body).unwrap();
        check_live_direct_loans(body, &flow).unwrap();
        let left = BindingId(body.bindings.iter().position(|b| b.name == "left").unwrap());
        let right = BindingId(
            body.bindings
                .iter()
                .position(|b| b.name == "right")
                .unwrap(),
        );
        let release = flow
            .nodes
            .iter_mut()
            .find(|node| {
                matches!(&node.action, FlowAction::Release { place, .. }
                if place.root == PlaceRoot::Local(right))
            })
            .unwrap();
        let FlowAction::Release { place, .. } = &mut release.action else {
            unreachable!()
        };
        place.root = PlaceRoot::Local(left);
        let error = check_live_direct_loans(body, &flow).unwrap_err();
        assert!(error.message.contains("cannot destroy"));
        let span = error.span.unwrap();
        assert_eq!(&source[span.start..span.end], "(#forget right)");
        let first = error.labels[0].0;
        assert_eq!(&source[first.start..first.end], "(#borrow left)");
    }

    #[test]
    fn clone_conflict_uses_checked_place_and_mutable_loan_origin() {
        let source = "(#fn main () u64
            (#let-mut left u64 1u64)
            (#let-mut right u64 2u64)
            (#let view (#ref-mut u64) (#borrow-mut left))
            (#let copy u64 (#clone right))
            (#return (#u64.+.wrap (#deref view) copy)))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let mut flow = FlowGraph::lower(body).unwrap();
        check_live_direct_loans(body, &flow).unwrap();
        let left = BindingId(body.bindings.iter().position(|b| b.name == "left").unwrap());
        let right = BindingId(
            body.bindings
                .iter()
                .position(|b| b.name == "right")
                .unwrap(),
        );
        let clone = flow
            .nodes
            .iter_mut()
            .find(|node| {
                matches!(&node.action, FlowAction::Clone { place, .. }
                if place.root == PlaceRoot::Local(right))
            })
            .unwrap();
        let FlowAction::Clone { place, .. } = &mut clone.action else {
            unreachable!()
        };
        place.root = PlaceRoot::Local(left);
        let error = check_live_direct_loans(body, &flow).unwrap_err();
        assert!(error.message.contains("cannot clone"));
        let span = error.span.unwrap();
        assert_eq!(&source[span.start..span.end], "(#clone right)");
        let first = error.labels[0].0;
        assert_eq!(&source[first.start..first.end], "(#borrow-mut left)");
    }

    #[test]
    fn symbol_read_conflict_uses_checked_binding_identity() {
        let source = "(#fn main () u64
            (#let-mut left u64 1u64)
            (#let-mut right u64 2u64)
            (#let view (#ref-mut u64) (#borrow-mut left))
            (#let value u64 right)
            (#return (#deref view)))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let mut flow = FlowGraph::lower(body).unwrap();
        check_live_direct_loans(body, &flow).unwrap();
        let left = BindingId(body.bindings.iter().position(|b| b.name == "left").unwrap());
        let right_read = flow.nodes.iter_mut().find(|node| {
            matches!(node.action, FlowAction::Read { value: id, .. }
                if matches!(&body.nodes[id.0].kind, NodeKind::Symbol { name, .. } if name == "right"))
        }).unwrap();
        let FlowAction::Read { place, .. } = &mut right_read.action else {
            unreachable!()
        };
        place.root = PlaceRoot::Local(left);
        let error = check_live_direct_loans(body, &flow).unwrap_err();
        assert!(error.message.contains("cannot access"));
        let span = error.span.unwrap();
        assert_eq!(&source[span.start..span.end], "right");
        let first = error.labels[0].0;
        assert_eq!(&source[first.start..first.end], "(#borrow-mut left)");
    }

    #[test]
    fn disjoint_field_read_does_not_read_entire_base() {
        let source = "(#struct Pair ((left u64) (right u64)))
          (#fn main () u64
            (#let-mut pair Pair (#struct-literal Pair ((left 1u64) (right 2u64))))
            (#let pair-ref (#ref-mut Pair) (#borrow-mut pair))
            (#let view (#ref-mut u64) (#borrow-mut (#get pair-ref left)))
            (#let right u64 (#get pair-ref right))
            (#return (#u64.+.wrap (#deref view) right)))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        check_live_direct_loans(body, &checked.declarations().flows["main"]).unwrap();
    }

    #[test]
    fn overlapping_direct_borrows_have_two_exact_source_sites() {
        let source = source("(left (#borrow-mut value)) (right (#borrow value))");
        let program = crate::parse_program(&source).unwrap();
        let error = crate::CheckedProgram::validate_with_span(&program)
            .err()
            .unwrap();
        assert!(error.0.contains("overlapping borrows"), "{}", error.0);
        assert_eq!(error.1, crate::DiagnosticCode::Borrow);
        let second = error.2.unwrap();
        assert_eq!(&source[second.start..second.end], "(#borrow value)");
        let first = error.3[0].0;
        assert_eq!(&source[first.start..first.end], "#borrow-mut");
    }

    #[test]
    fn two_shared_direct_borrows_are_allowed() {
        let source = "(#fn inspect ((left (#ref u64)) (right (#ref u64))) u64
            (#return (#u64.+.wrap (#deref left) (#deref right))))
          (#fn main () u64
            (#let value u64 1u64)
            (#return (#call inspect (: left (#borrow value) : right (#borrow value)))))";
        let program = crate::parse_program(source).unwrap();
        crate::CheckedProgram::validate(&program).unwrap_or_else(|error| panic!("{error}"));
    }

    #[test]
    fn disjoint_struct_fields_can_be_borrowed_together() {
        let source = "(#struct Pair ((left u64) (right u64)))
          (#fn inspect ((left (#ref-mut u64)) (right (#ref u64))) u64
            (#forget left) (#forget right) (#return 0u64))
          (#fn main () u64
            (#let-mut pair Pair (#struct-literal Pair ((left 1u64) (right 2u64))))
            (#let pair-ref (#ref-mut Pair) (#borrow-mut pair))
            (#return (#call inspect (: left (#borrow-mut (#get pair-ref left)) : right (#borrow (#get pair-ref right))))))";
        let program = crate::parse_program(source).unwrap();
        crate::CheckedProgram::validate(&program).unwrap_or_else(|error| panic!("{error}"));

        let overlapping = source.replace(
            ": right (#borrow (#get pair-ref right))",
            ": right (#borrow (#get pair-ref left))",
        );
        let program = crate::parse_program(&overlapping).unwrap();
        let error = crate::CheckedProgram::validate(&program).err().unwrap();
        assert!(error.contains("overlapping borrows"), "{error}");
    }

    #[test]
    fn borrow_inside_struct_argument_conflicts_with_another_argument() {
        let source = "(#struct Holder ((item (#ref u64))))
          (#fn inspect ((holder Holder) (right (#ref-mut u64))) u64
            (#let (Holder item) Holder holder)
            (#drop item) (#drop right) (#return 0u64))
          (#fn main () u64
            (#let-mut value u64 1u64)
            (#return (#call inspect (: holder (#struct-literal Holder ((item (#borrow value)))) : right (#borrow-mut value)))))";
        let program = crate::parse_program(source).unwrap();
        let error = crate::CheckedProgram::validate_with_span(&program)
            .err()
            .unwrap();
        assert!(error.0.contains("overlapping borrows"), "{}", error.0);
        let second = error.2.unwrap();
        assert_eq!(&source[second.start..second.end], "(#borrow-mut value)");
    }

    #[test]
    fn bound_reference_aggregate_conflicts_with_another_call_argument() {
        let source = "(#struct Holder ((item (#ref u64))))
          (#fn inspect ((holder Holder) (right (#ref-mut u64))) u64
            (#forget holder) (#forget right) (#return 0u64))
          (#fn main () u64
            (#let-mut value u64 1u64)
            (#let holder Holder (#struct-literal Holder ((item (#borrow value)))))
            (#return (#call inspect (: holder holder : right (#borrow-mut value)))))";
        let program = crate::parse_program(source).unwrap();
        let error = crate::CheckedProgram::validate_with_span(&program)
            .err()
            .unwrap();
        assert!(error.0.contains("overlapping borrows"), "{}", error.0);
        let conflict = error.2.unwrap();
        assert_eq!(&source[conflict.start..conflict.end], "(#borrow-mut value)");
        let first = error.3[0].0;
        assert_eq!(&source[first.start..first.end], "#borrow");
    }

    #[test]
    fn projected_bound_reference_aggregate_conflicts_with_call_argument() {
        let source = "(#struct Holder ((item (#ref u64)) (other (#ref u64))))
          (#fn inspect ((item (#ref u64)) (right (#ref-mut u64))) u64
            (#forget item) (#forget right) (#return 0u64))
          (#fn main () u64
            (#let-mut value u64 1u64)
            (#let-mut other u64 2u64)
            (#let holder Holder (#struct-literal Holder
              ((item (#borrow value)) (other (#borrow other)))))
            (#let result u64 (#call inspect
              (: item (#get holder item) : right (#borrow-mut value))))
            (#return result))";
        let program = crate::parse_program(source).unwrap();
        let error = crate::CheckedProgram::validate_with_span(&program)
            .err()
            .unwrap();
        assert!(error.0.contains("overlapping borrows"), "{}", error.0);
        let conflict = error.2.unwrap();
        assert_eq!(&source[conflict.start..conflict.end], "(#borrow-mut value)");
        let first = error.3[0].0;
        assert_eq!(&source[first.start..first.end], "#borrow");

        let disjoint = source
            .replace(
                "(#struct Holder ((item (#ref u64)) (other (#ref u64))))",
                "(#struct Holder ((item (#ref u64)) (other u64)))",
            )
            .replace("(other (#borrow other))", "(other other)")
            .replace("(#borrow-mut value))))", "(#borrow-mut other))))");
        let program = crate::parse_program(&disjoint).unwrap();
        crate::CheckedProgram::validate(&program)
            .unwrap_or_else(|error| panic!("disjoint projection: {error}"));
    }

    #[test]
    fn array_constructors_expose_borrowed_call_arguments() {
        for constructor in [
            "(#array-of (#array (#ref u64) 1) (#borrow value))",
            "(#array-repeat (#borrow value))",
        ] {
            let source = format!(
                "(#fn inspect ((values (#array (#ref u64) 1)) (other (#ref-mut u64))) u64
                   (#forget values) (#forget other) (#return 0u64))
                 (#fn main () u64
                   (#let-mut value u64 1u64)
                   (#return (#call inspect (: values {constructor} : other (#borrow-mut value)))))"
            );
            let program = crate::parse_program(&source).unwrap();
            let error = crate::CheckedProgram::validate_with_span(&program)
                .err()
                .unwrap();
            assert!(
                error.0.contains("overlapping borrows"),
                "{constructor}: {}",
                error.0
            );
            let conflict = error.2.unwrap();
            assert_eq!(&source[conflict.start..conflict.end], "(#borrow-mut value)");
        }
    }

    #[test]
    fn empty_repeated_array_does_not_retain_a_call_argument_borrow() {
        let source = "(#fn inspect ((values (#array (#ref u64) 0)) (other (#ref-mut u64))) u64
             (#forget values) (#forget other) (#return 0u64))
          (#fn main () u64
             (#let-mut value u64 1u64)
             (#return (#call inspect
               (: values (#array-repeat (#borrow value))
                : other (#borrow-mut value)))))";
        let program = crate::parse_program(source).unwrap();
        crate::CheckedProgram::validate(&program).unwrap();
    }

    #[test]
    fn conditional_alternatives_do_not_conflict_with_each_other() {
        let source = "(#fn inspect ((left (#ref-mut u64)) (right (#ref u64))) u64
            (#forget left) (#forget right) (#return 0u64))
          (#fn main () u64
            (#let-mut first u64 1u64)
            (#let-mut second u64 2u64)
            (#return (#call inspect (: left (#if true (#borrow-mut first) (#borrow-mut second)) : right (#borrow second)))))";
        let program = crate::parse_program(source).unwrap();
        let error = crate::CheckedProgram::validate(&program).err().unwrap();
        assert!(error.contains("overlapping borrows"), "{error}");

        let disjoint = source
            .replace(
                "(#let-mut second u64 2u64)",
                "(#let-mut second u64 2u64) (#let-mut third u64 3u64)",
            )
            .replace(": right (#borrow second)", ": right (#borrow third)");
        let program = crate::parse_program(&disjoint).unwrap();
        crate::CheckedProgram::validate(&program).unwrap_or_else(|error| panic!("{error}"));
    }

    #[test]
    fn borrow_inside_tuple_argument_conflicts_with_another_argument() {
        let source = "(#fn inspect ((left (#tuple (#ref u64))) (right (#ref-mut u64))) u64
            (#let (#tuple item) (#tuple (#ref u64)) left)
            (#drop item) (#drop right) (#return 0u64))
          (#fn main () u64
            (#let-mut value u64 1u64)
            (#return (#call inspect (: left (#tuple (#borrow value)) : right (#borrow-mut value)))))";
        let program = crate::parse_program(source).unwrap();
        let error = crate::CheckedProgram::validate_with_span(&program)
            .err()
            .unwrap();
        assert!(error.0.contains("overlapping borrows"), "{}", error.0);
        let second = error.2.unwrap();
        assert_eq!(&source[second.start..second.end], "(#borrow-mut value)");
        let first = error.3[0].0;
        assert_eq!(&source[first.start..first.end], "#borrow");

        let disjoint = source
            .replace(
                "(#let-mut value u64 1u64)",
                "(#let-mut value u64 1u64) (#let-mut other u64 2u64)",
            )
            .replace(": right (#borrow-mut value)", ": right (#borrow-mut other)");
        let program = crate::parse_program(&disjoint).unwrap();
        crate::CheckedProgram::validate(&program).unwrap_or_else(|error| panic!("{error}"));
    }

    #[test]
    fn borrow_inside_array_argument_conflicts_with_another_argument() {
        let source = "(#fn inspect ((left (#array (#ref u64) 1)) (right (#ref-mut u64))) u64
            (#let (#array item) (#array (#ref u64) 1) left)
            (#drop item) (#drop right) (#return 0u64))
          (#fn main () u64
            (#let-mut value u64 1u64)
            (#return (#call inspect (: left (#array (#array (#ref u64) 1) (#borrow value)) : right (#borrow-mut value)))))";
        let program = crate::parse_program(source).unwrap();
        let error = crate::CheckedProgram::validate_with_span(&program)
            .err()
            .unwrap();
        assert!(error.0.contains("overlapping borrows"), "{}", error.0);
        let second = error.2.unwrap();
        assert_eq!(&source[second.start..second.end], "(#borrow-mut value)");
        let first = error.3[0].0;
        assert_eq!(&source[first.start..first.end], "#borrow");

        let disjoint = source
            .replace(
                "(#let-mut value u64 1u64)",
                "(#let-mut value u64 1u64) (#let-mut other u64 2u64)",
            )
            .replace(": right (#borrow-mut value)", ": right (#borrow-mut other)");
        let program = crate::parse_program(&disjoint).unwrap();
        crate::CheckedProgram::validate(&program).unwrap_or_else(|error| panic!("{error}"));
    }

    #[test]
    fn borrow_inside_enum_argument_conflicts_with_another_argument() {
        let source = "(#enum Holder ((Has (#ref u64))))
          (#fn inspect ((left Holder) (right (#ref-mut u64))) u64
            (#let-else (Has item) Holder left (#return 0u64))
            (#drop item) (#drop right) (#return 0u64))
          (#fn main () u64
            (#let-mut value u64 1u64)
            (#return (#call inspect (: left (Has (#borrow value)) : right (#borrow-mut value)))))";
        let program = crate::parse_program(source).unwrap();
        let error = crate::CheckedProgram::validate(&program).err().unwrap();
        assert!(error.contains("overlapping borrows"), "{error}");
    }

    #[test]
    fn match_result_borrows_are_checked_per_arm() {
        let source = "(#fn inspect ((left (#ref u64)) (right (#ref-mut u64))) u64
            (#drop left) (#drop right) (#return 0u64))
          (#fn main () u64
            (#let-mut first u64 1u64)
            (#let-mut second u64 2u64)
            (#return (#call inspect (: left (#match true
                (#case true (#borrow first))
                (#case false (#borrow second))) : right (#borrow-mut first)))))";
        let program = crate::parse_program(source).unwrap();
        let error = crate::CheckedProgram::validate(&program).err().unwrap();
        assert!(error.contains("overlapping borrows"), "{error}");
    }

    #[test]
    fn immutable_block_binding_retains_borrow_origin() {
        let source = "(#fn inspect ((left (#ref u64)) (right (#ref-mut u64))) u64
            (#drop left) (#drop right) (#return 0u64))
          (#fn main () u64
            (#let-mut value u64 1u64)
            (#return (#call inspect (: left (#block (#let view (#ref u64) (#borrow value)) view) : right (#borrow-mut value)))))";
        let program = crate::parse_program(source).unwrap();
        let error = crate::CheckedProgram::validate_with_span(&program)
            .err()
            .unwrap();
        assert!(error.0.contains("overlapping borrows"), "{}", error.0);
        let second = error.2.unwrap();
        assert_eq!(&source[second.start..second.end], "(#borrow-mut value)");
        let first = error.3[0].0;
        assert_eq!(&source[first.start..first.end], "#borrow");

        let disjoint = source
            .replace(
                "(#let-mut value u64 1u64)",
                "(#let-mut value u64 1u64) (#let-mut other u64 2u64)",
            )
            .replace(": right (#borrow-mut value)", ": right (#borrow-mut other)");
        let program = crate::parse_program(&disjoint).unwrap();
        crate::CheckedProgram::validate(&program).unwrap_or_else(|error| panic!("{error}"));
    }

    #[test]
    fn destructured_block_reference_retains_aggregate_loan_origin() {
        let source = "(#fn inspect ((left (#ref u64)) (right (#ref-mut u64))) u64
            (#drop left) (#drop right) (#return 0u64))
          (#fn main () u64
            (#let-mut value u64 1u64)
            (#return (#call inspect
              (: left (#block
                  (#let (#tuple view) (#tuple (#ref u64))
                    (#tuple (#tuple (#ref u64)) (#borrow value)))
                  view)
               : right (#borrow-mut value)))))";
        let program = crate::parse_program(source).unwrap();
        let error = crate::CheckedProgram::validate_with_span(&program)
            .err()
            .unwrap();
        assert!(error.0.contains("overlapping borrows"), "{}", error.0);
        let second = error.2.unwrap();
        assert_eq!(&source[second.start..second.end], "(#borrow-mut value)");
        let first = error.3[0].0;
        assert_eq!(&source[first.start..first.end], "#borrow");
    }

    #[test]
    fn destructured_sibling_references_keep_distinct_loan_origins() {
        let source = "(#fn inspect ((left (#ref u64)) (right (#ref-mut u64))) u64
            (#drop left) (#drop right) (#return 0u64))
          (#fn main () u64
            (#let-mut first u64 1u64)
            (#let-mut second u64 2u64)
            (#let pair (#tuple (#ref u64) (#ref-mut u64))
              (#tuple (#tuple (#ref u64) (#ref-mut u64))
                (#borrow first) (#borrow-mut second)))
            (#let (#tuple left right)
              (#tuple (#ref u64) (#ref-mut u64))
              pair)
            (#return (#call inspect (: left left : right right))))";
        let program = crate::parse_program(source).unwrap();
        crate::CheckedProgram::validate(&program).unwrap_or_else(|error| panic!("{error}"));
    }

    #[test]
    fn array_destructuring_retains_element_loan_paths() {
        let source = "(#fn inspect ((left (#ref u64)) (right (#ref-mut u64))) u64
            (#drop left) (#drop right) (#return 0u64))
          (#fn main () u64
            (#let-mut first u64 1u64)
            (#let-mut second u64 2u64)
            (#let pair (#array (#ref u64) 2)
              (#array (#array (#ref u64) 2)
                (#borrow first) (#borrow second)))
            (#let (#array left right) (#array (#ref u64) 2) pair)
            (#return (#call inspect (: left left : right (#borrow-mut second)))))";
        let program = crate::parse_program(source).unwrap();
        crate::CheckedProgram::validate(&program).unwrap_or_else(|error| panic!("{error}"));

        let overlapping = source.replace(
            ": right (#borrow-mut second)",
            ": right (#borrow-mut first)",
        );
        let program = crate::parse_program(&overlapping).unwrap();
        let error = crate::CheckedProgram::validate(&program).err().unwrap();
        assert!(error.contains("overlapping borrows"), "{error}");
    }

    #[test]
    fn struct_destructuring_retains_field_loan_paths() {
        let source = "(#struct Pair ((left (#ref u64)) (right (#ref u64))))
          (#fn inspect ((left (#ref u64)) (right (#ref-mut u64))) u64
            (#drop left) (#drop right) (#return 0u64))
          (#fn main () u64
            (#let-mut first u64 1u64)
            (#let-mut second u64 2u64)
            (#let pair Pair (#struct-literal Pair
              ((left (#borrow first)) (right (#borrow second)))))
            (#let (Pair left right) Pair pair)
            (#return (#call inspect
              (: left left : right (#borrow-mut first)))))";
        let program = crate::parse_program(source).unwrap();
        let error = crate::CheckedProgram::validate(&program).err().unwrap();
        assert!(error.contains("overlapping borrows"), "{error}");

        let disjoint = source.replace(": left left", ": left right");
        let program = crate::parse_program(&disjoint).unwrap();
        crate::CheckedProgram::validate(&program).unwrap_or_else(|error| panic!("{error}"));
    }

    #[test]
    fn enum_payload_destructuring_retains_loan_paths() {
        let source = "(#enum Holder ((Held (#ref u64)) (Empty)))
          (#fn inspect ((left (#ref u64)) (right (#ref-mut u64))) u64
            (#drop left) (#drop right) (#return 0u64))
          (#fn main () u64
            (#let-mut value u64 1u64)
            (#let-mut other u64 2u64)
            (#let holder Holder (Held (#borrow value)))
            (#let-else (Held left) Holder holder (#return 0u64))
            (#return (#call inspect
              (: left left : right (#borrow-mut value)))))";
        let program = crate::parse_program(source).unwrap();
        let error = crate::CheckedProgram::validate(&program).err().unwrap();
        assert!(error.contains("overlapping borrows"), "{error}");

        let disjoint = source.replace(": right (#borrow-mut value)", ": right (#borrow-mut other)");
        let program = crate::parse_program(&disjoint).unwrap();
        crate::CheckedProgram::validate(&program).unwrap_or_else(|error| panic!("{error}"));
    }

    #[test]
    fn enum_match_binding_retains_payload_loan_path() {
        let source = "(#enum Holder ((Held (#ref u64)) (Empty)))
          (#fn inspect ((left (#ref u64)) (right (#ref-mut u64))) u64
            (#drop left) (#drop right) (#return 0u64))
          (#fn main () u64
            (#let-mut value u64 1u64)
            (#let-mut other u64 2u64)
            (#let holder Holder (Held (#borrow value)))
            (#return (#match holder
              (#case (Held left)
                (#call inspect (: left left : right (#borrow-mut value))))
              (#case Empty 0u64))))";
        let program = crate::parse_program(source).unwrap();
        let error = crate::CheckedProgram::validate(&program).err().unwrap();
        assert!(error.contains("overlapping borrows"), "{error}");

        let disjoint = source.replace(": right (#borrow-mut value)", ": right (#borrow-mut other)");
        let program = crate::parse_program(&disjoint).unwrap();
        crate::CheckedProgram::validate(&program).unwrap_or_else(|error| panic!("{error}"));
    }

    #[test]
    fn nested_struct_patterns_retain_full_loan_path() {
        let source = "(#struct Inner ((item (#ref u64))))
          (#struct Outer ((inner Inner)))
          (#fn inspect ((left (#ref u64)) (right (#ref-mut u64))) u64
            (#drop left) (#drop right) (#return 0u64))
          (#fn main () u64
            (#let-mut value u64 1u64)
            (#let-mut other u64 2u64)
            (#let inner Inner (#struct-literal Inner ((item (#borrow value)))))
            (#let outer Outer (#struct-literal Outer ((inner inner))))
            (#let (Outer (Inner left)) Outer outer)
            (#return (#call inspect
              (: left left : right (#borrow-mut value)))))";
        let program = crate::parse_program(source).unwrap();
        let error = crate::CheckedProgram::validate(&program).err().unwrap();
        assert!(error.contains("overlapping borrows"), "{error}");

        let disjoint = source.replace(": right (#borrow-mut value)", ": right (#borrow-mut other)");
        let program = crate::parse_program(&disjoint).unwrap();
        crate::CheckedProgram::validate(&program).unwrap_or_else(|error| panic!("{error}"));
    }

    #[test]
    fn loop_break_reference_retains_call_argument_origin() {
        let source = "(#fn inspect ((left (#ref u64)) (right (#ref-mut u64))) u64
            (#drop left) (#drop right) (#return 0u64))
          (#fn main () u64
            (#let-mut value u64 1u64)
            (#return (#call inspect
              (: left (#loop (#break (#borrow value)))
               : right (#borrow-mut value)))))";
        let program = crate::parse_program(source).unwrap();
        let error = crate::CheckedProgram::validate_with_span(&program)
            .err()
            .unwrap();
        assert!(error.0.contains("overlapping borrows"), "{}", error.0);
        let second = error.2.unwrap();
        assert_eq!(&source[second.start..second.end], "(#borrow-mut value)");
        let first = error.3[0].0;
        assert_eq!(&source[first.start..first.end], "#borrow");

        let disjoint = source
            .replace(
                "(#let-mut value u64 1u64)",
                "(#let-mut value u64 1u64) (#let-mut other u64 2u64)",
            )
            .replace(": right (#borrow-mut value)", ": right (#borrow-mut other)");
        let program = crate::parse_program(&disjoint).unwrap();
        crate::CheckedProgram::validate(&program).unwrap_or_else(|error| panic!("{error}"));

        let labeled = source.replace(
            "(#loop (#break (#borrow value)))",
            "(#label outer (#loop (#break-to outer (#borrow value))))",
        );
        let program = crate::parse_program(&labeled).unwrap();
        let error = crate::CheckedProgram::validate(&program).err().unwrap();
        assert!(error.contains("overlapping borrows"), "{error}");
    }

    #[test]
    fn mutable_block_binding_retains_initial_borrow_origin() {
        let source = "(#fn inspect ((left (#ref u64)) (right (#ref-mut u64))) u64
            (#drop left) (#drop right) (#return 0u64))
          (#fn main () u64
            (#let-mut value u64 1u64)
            (#return (#call inspect (: left (#block
                (#let-mut view (#ref u64) (#borrow value))
                view) : right (#borrow-mut value)))))";
        let program = crate::parse_program(source).unwrap();
        let error = crate::CheckedProgram::validate_with_span(&program)
            .err()
            .unwrap();
        assert!(error.0.contains("overlapping borrows"), "{}", error.0);
        let first = error.3[0].0;
        assert_eq!(&source[first.start..first.end], "#borrow");

        let disjoint = source
            .replace(
                "(#let-mut value u64 1u64)",
                "(#let-mut value u64 1u64) (#let-mut other u64 2u64)",
            )
            .replace(": right (#borrow-mut value)", ": right (#borrow-mut other)");
        let program = crate::parse_program(&disjoint).unwrap();
        crate::CheckedProgram::validate(&program).unwrap_or_else(|error| panic!("{error}"));

        let branched = source.replace(
            "(#loop (#break (#borrow value)))",
            "(#loop (#if true
              (#block (#break (#borrow value)))
              (#block (#break (#borrow value)))))",
        );
        let program = crate::parse_program(&branched).unwrap();
        let error = crate::CheckedProgram::validate(&program).err().unwrap();
        assert!(error.contains("overlapping borrows"), "{error}");

        let matched = source.replace(
            "(#loop (#break (#borrow value)))",
            "(#loop (#match true
              (#case true (#block (#break (#borrow value))))
              (#case false (#block (#break (#borrow value))))))",
        );
        let program = crate::parse_program(&matched).unwrap();
        let error = crate::CheckedProgram::validate(&program).err().unwrap();
        assert!(error.contains("overlapping borrows"), "{error}");
    }

    #[test]
    fn equivalent_borrow_paths_do_not_exhaust_the_path_budget() {
        let shared = DirectBorrow {
            place: Place::root(PlaceRoot::Local(BindingId(0))),
            mutable: false,
            span: None,
            storage: Vec::new(),
        };
        let repeated = vec![vec![shared.clone()]; MAX_BORROW_ALTERNATIVES + 1];
        assert_eq!(bounded(repeated, None).unwrap().len(), 1);

        // The Cartesian product has 33 * 33 paths, but only 65 distinct
        // loan sequences after equivalent alternatives are folded together.
        let alternatives = (0..33).map(|count| vec![shared.clone(); count]).collect();
        assert_eq!(
            combine(
                alternatives,
                (0..33).map(|count| vec![shared.clone(); count]).collect(),
                "inspect",
                None
            )
            .unwrap()
            .len(),
            65
        );

        let distinct = (0..=MAX_BORROW_ALTERNATIVES)
            .map(|index| {
                vec![DirectBorrow {
                    place: Place::root(PlaceRoot::Local(BindingId(index))),
                    mutable: false,
                    span: None,
                    storage: Vec::new(),
                }]
            })
            .collect();
        assert!(bounded(distinct, None).is_err());
    }

    #[test]
    fn reference_binding_as_call_argument_retains_its_direct_origin() {
        let source = "(#fn inspect ((left (#ref u64)) (right (#ref-mut u64))) u64
            (#drop left) (#drop right) (#return 0u64))
          (#fn main () u64
            (#let-mut value u64 1u64)
            (#let view (#ref u64) (#borrow value))
            (#return (#call inspect (: left view : right (#borrow-mut value)))))";
        let program = crate::parse_program(source).unwrap();
        let error = crate::CheckedProgram::validate_with_span(&program)
            .err()
            .unwrap();
        assert!(error.0.contains("overlapping borrows"), "{}", error.0);
        let second = error.2.unwrap();
        assert_eq!(&source[second.start..second.end], "(#borrow-mut value)");
        let first = error.3[0].0;
        assert_eq!(&source[first.start..first.end], "#borrow");

        let disjoint = source
            .replace(
                "(#let-mut value u64 1u64)",
                "(#let-mut value u64 1u64) (#let-mut other u64 2u64)",
            )
            .replace(": right (#borrow-mut value)", ": right (#borrow-mut other)");
        let program = crate::parse_program(&disjoint).unwrap();
        crate::CheckedProgram::validate(&program).unwrap_or_else(|error| panic!("{error}"));
    }

    #[test]
    fn reference_returning_call_preserves_argument_origin() {
        let source = "(#fn identity ((source (#ref u64))) (#ref u64)
            (#return source))
          (#fn inspect ((left (#ref u64)) (right (#ref-mut u64))) u64
            (#drop left) (#drop right) (#return 0u64))
          (#fn main () u64
            (#let-mut value u64 1u64)
            (#return (#call inspect
              (: left (#call identity (: source (#borrow value)))
               : right (#borrow-mut value)))))";
        let program = crate::parse_program(source).unwrap();
        let error = crate::CheckedProgram::validate_with_span(&program)
            .err()
            .unwrap();
        assert!(error.0.contains("overlapping borrows"), "{}", error.0);
        let second = error.2.unwrap();
        assert_eq!(&source[second.start..second.end], "(#borrow-mut value)");
        let first = error.3[0].0;
        assert_eq!(&source[first.start..first.end], "#borrow");
    }

    #[test]
    fn joined_reference_origins_are_checked_as_alternatives() {
        let held = [
            LoanOrigin {
                place: Place::root(PlaceRoot::Local(BindingId(0))),
                mutable: true,
                pinned: false,
                span: None,
                borrowed_from: None,
                storage: Vec::new(),
                parameter_storage: None,
            },
            LoanOrigin {
                place: Place::root(PlaceRoot::Local(BindingId(1))),
                mutable: true,
                pinned: false,
                span: None,
                borrowed_from: None,
                storage: Vec::new(),
                parameter_storage: None,
            },
        ];
        let alternatives = origin_alternatives(&held, None).unwrap().unwrap();
        assert_eq!(alternatives.len(), 2);
        let shared = |binding| {
            vec![vec![DirectBorrow {
                place: Place::root(PlaceRoot::Local(BindingId(binding))),
                mutable: false,
                span: None,
                storage: Vec::new(),
            }]]
        };
        assert!(combine(alternatives.clone(), shared(0), "inspect", None).is_err());
        assert!(combine(alternatives, shared(2), "inspect", None).is_ok());

        let source = "(#enum Choice ((First (#ref-mut u64)) (Second (#ref-mut u64))))
            (#fn inspect ((choice Choice)) u64
              (#return (#match choice
                (#case (First first) (#block (#drop first) 0u64))
                (#case (Second second) (#block (#drop second) 0u64)))))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["inspect"];
        let mut variants = body
            .nodes
            .iter()
            .filter_map(|node| match &node.kind {
                NodeKind::Declaration(crate::typed_ir::DeclarationId::Variant(variant)) => {
                    Some(*variant)
                }
                _ => None,
            })
            .collect::<Vec<_>>();
        variants.sort();
        variants.dedup();
        let first = variants[0];
        let second = variants[1];
        let variant = |variant, field| LoanOrigin {
            place: Place::root(PlaceRoot::Local(BindingId(0))),
            mutable: true,
            pinned: false,
            span: None,
            borrowed_from: None,
            storage: vec![crate::typed_place::Segment::Payload(variant, field)],
            parameter_storage: None,
        };
        let mutually_exclusive =
            origin_alternatives(&[variant(first, 0), variant(second, 0)], None)
                .unwrap()
                .unwrap();
        assert_eq!(mutually_exclusive.len(), 2);
        assert!(mutually_exclusive.iter().all(|path| path.len() == 1));

        let coexisting = origin_alternatives(&[variant(first, 0), variant(first, 1)], None)
            .unwrap()
            .unwrap();
        assert_eq!(coexisting.len(), 1);
        assert_eq!(coexisting[0].len(), 2);

        let source = "(#fn inspect ((first (#ref-mut u64)) (second (#ref u64))) u64
            (#drop first) (#drop second) (#return 0u64))
          (#fn main () u64
            (#let-mut left u64 1u64)
            (#let-mut right u64 2u64)
            (#let flag bool true)
            (#let view (#ref-mut u64)
              (#if flag (#borrow-mut left) (#borrow-mut right)))
            (#let-mut third u64 3u64)
            (#return (#call inspect (: first view : second (#borrow third)))))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let graph = &checked.declarations().flows["main"];
        let view = BindingId(body.bindings.iter().position(|b| b.name == "view").unwrap());
        let call = body
            .nodes
            .iter()
            .position(|node| {
                matches!(&node.kind, NodeKind::Form { head, callee: Some(_), .. } if head == "inspect")
            })
            .map(NodeId)
            .unwrap();
        let event = graph
            .nodes
            .iter()
            .position(|node| matches!(node.action, FlowAction::Evaluate(id) if id == call))
            .map(FlowNodeId)
            .unwrap();
        assert_eq!(graph.loan_origins(body).before(event, view).len(), 2);
    }

    #[test]
    fn projected_borrow_uses_reference_bindings_referent_place() {
        let source = "(#struct Pair ((left u64) (right u64)))
          (#fn main () u64
            (#let-mut pair Pair (#struct-literal Pair ((left 1u64) (right 2u64))))
            (#let pair-ref (#ref-mut Pair) (#borrow-mut pair))
            (#let field-ref (#ref u64) (#borrow (#get pair-ref left)))
            (#drop field-ref)
            (#drop pair-ref)
            (#forget pair)
            (#return 0u64))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let pair = BindingId(body.bindings.iter().position(|b| b.name == "pair").unwrap());
        let pair_ref = BindingId(
            body.bindings
                .iter()
                .position(|b| b.name == "pair-ref")
                .unwrap(),
        );
        let borrow = body
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| match &node.kind {
                NodeKind::Form { head, children, .. } if head == "borrow" => {
                    matches!(&body.nodes[children[1].0].kind, NodeKind::Form { head, .. } if head == "get")
                        .then_some(NodeId(index))
                }
                _ => None,
            })
            .unwrap();
        let mut bindings = BoundBorrows::new();
        bindings.insert(
            pair_ref,
            vec![vec![DirectBorrow {
                place: Place::root(PlaceRoot::Local(pair)),
                mutable: true,
                span: None,
                storage: Vec::new(),
            }]],
        );
        let projected = returned_borrows_with_bindings(body, borrow, "inspect", &bindings)
            .unwrap()
            .pop()
            .unwrap()
            .pop()
            .unwrap();
        assert_eq!(projected.place.root, PlaceRoot::Local(pair));
        assert_eq!(projected.place.segments.len(), 1);
        let overlapping = DirectBorrow {
            place: projected.place.clone(),
            mutable: true,
            span: None,
            storage: Vec::new(),
        };
        assert!(combine(
            vec![vec![projected]],
            vec![vec![overlapping]],
            "inspect",
            None,
        )
        .is_err());
    }

    #[test]
    fn projected_borrow_follows_two_known_reference_bindings() {
        let source = "(#struct Inner ((x u64)))
          (#struct Outer ((inner Inner)))
          (#fn main () u64
            (#let-mut owner Outer (#struct-literal Outer
              ((inner (#struct-literal Inner ((x 3u64)))))))
            (#let outer-ref (#ref-mut Outer) (#borrow-mut owner))
            (#let inner-ref (#ref-mut Inner)
              (#borrow-mut (#get outer-ref inner)))
            (#let value-ref (#ref u64) (#borrow (#get inner-ref x)))
            (#drop value-ref)
            (#drop inner-ref)
            (#drop outer-ref)
            (#forget owner)
            (#return 0u64))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let id = |name: &str| {
            BindingId(
                body.bindings
                    .iter()
                    .position(|binding| binding.name == name)
                    .unwrap(),
            )
        };
        let owner = id("owner");
        let outer_ref = id("outer-ref");
        let inner_ref = id("inner-ref");
        let projection = |base: BindingId| {
            body.nodes
                .iter()
                .enumerate()
                .find_map(|(index, node)| match &node.kind {
                    NodeKind::Form { head, children, .. } if head == "get" => {
                        matches!(&body.nodes[children[1].0].kind,
                            NodeKind::Symbol { binding: Some(binding), .. } if *binding == base)
                        .then_some(NodeId(index))
                    }
                    _ => None,
                })
                .unwrap()
        };
        let inner_place = Place::from_expression(body, projection(outer_ref)).unwrap();
        let value_get = projection(inner_ref);
        let value_borrow = body
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| match &node.kind {
                NodeKind::Form { head, children, .. }
                    if head == "borrow" && children.get(1) == Some(&value_get) =>
                {
                    Some(NodeId(index))
                }
                _ => None,
            })
            .unwrap();
        let mut bindings = BoundBorrows::new();
        bindings.insert(
            outer_ref,
            vec![vec![DirectBorrow {
                place: Place::root(PlaceRoot::Local(owner)),
                mutable: true,
                span: None,
                storage: Vec::new(),
            }]],
        );
        bindings.insert(
            inner_ref,
            vec![vec![DirectBorrow {
                place: inner_place,
                mutable: true,
                span: None,
                storage: Vec::new(),
            }]],
        );
        let resolved =
            returned_borrows_with_bindings(body, value_borrow, "inspect", &bindings).unwrap();
        assert_eq!(resolved.len(), 1);
        assert_eq!(resolved[0][0].place.root, PlaceRoot::Local(owner));
        assert_eq!(resolved[0][0].place.segments.len(), 2);

        bindings.insert(
            outer_ref,
            vec![vec![DirectBorrow {
                place: Place::root(PlaceRoot::Local(inner_ref)),
                mutable: true,
                span: None,
                storage: Vec::new(),
            }]],
        );
        let unresolved =
            returned_borrows_with_bindings(body, value_borrow, "inspect", &bindings).unwrap();
        assert_eq!(unresolved[0][0].place.root, PlaceRoot::Local(inner_ref));
    }
}
