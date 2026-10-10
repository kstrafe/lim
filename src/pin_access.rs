//! Accesses through direct pinned pointer fields in borrowed wrappers.
//!
//! Borrowing a wrapper's stack address does not itself access its pointee.
//! Callee footprints cross that pointer boundary using checked input slots.
//! This is an additional rejection gate, never a new pin/borrow permission.
//! Enum-payload state cells are not wrapper entry points: their conditional
//! internal loans remain governed by the separate state-sensitive checks.

use crate::linearcheck::LinearTypes;
use crate::typed_body::{Body, NodeId, NodeKind, ParameterLoanSummary, PlaceRoot};
use crate::typed_borrow::BorrowConflict;
use crate::typed_flow::{FlowAction, FlowLoanOrigins, FlowNodeId, LoanOrigin};
use crate::typed_ir::{Declarations, FunctionId};
use crate::typed_place::{Place, Segment};
use crate::{Span, Type};
use std::cell::OnceCell;
use std::collections::{HashMap, HashSet};

#[derive(Clone)]
struct Access {
    input: ParameterLoanSummary,
    span: Option<Span>,
}

fn same_pointer(left: &LoanOrigin, right: &LoanOrigin) -> bool {
    left.place.root == right.place.root
        && (!matches!(left.place.root, PlaceRoot::Parameter(_))
            || left.parameter_storage == right.parameter_storage)
        && left.place.overlaps(&right.place)
}

fn calls(body: &Body) -> impl Iterator<Item = (NodeId, FunctionId)> + '_ {
    body.nodes
        .iter()
        .enumerate()
        .filter_map(|(index, node)| match node.kind {
            NodeKind::Form {
                callee: Some(id), ..
            } => Some((NodeId(index), id)),
            _ => None,
        })
}

fn infer(
    id: FunctionId,
    declarations: &Declarations,
    caches: &HashMap<&str, OnceCell<FlowLoanOrigins>>,
    effects: &mut HashMap<FunctionId, Vec<Access>>,
    visiting: &mut HashSet<FunctionId>,
) {
    if effects.contains_key(&id) {
        return;
    }
    let name = declarations.function_name(id).expect("checked callee");
    let Some(body) = declarations.bodies.get(name) else {
        effects.insert(id, Vec::new());
        return;
    };
    assert!(visiting.insert(id), "checked call graph must be acyclic");
    for (_, dependency) in calls(body) {
        infer(dependency, declarations, caches, effects, visiting);
    }
    let flow = &declarations.flows[name];
    let origins = caches[name].get_or_init(|| flow.loan_origins(body));
    let mut accesses = Vec::<Access>::new();
    for (index, node) in flow.nodes.iter().enumerate() {
        let event = FlowNodeId(index);
        let mut physical = Vec::new();
        match node.action {
            FlowAction::Borrow { value, .. } => {
                if matches!(body.nodes[value.0].ty, Some(Type::PinnedReference { .. })) {
                    physical.extend(origins.value_before(body, flow, event, value));
                }
            }
            FlowAction::Read {
                value,
                place_base: false,
                ..
            } => {
                if crate::typed_place::reads_through_reference(body, value) {
                    physical.extend(
                        origins
                            .address_before(body, flow, event, value)
                            .into_iter()
                            .map(|mut origin| {
                                origin.mutable = false;
                                origin
                            }),
                    );
                }
            }
            FlowAction::Write { .. } | FlowAction::Evaluate(_) => {
                physical.extend(origins.stores_before(body, flow, event).into_iter().map(
                    |store| {
                        let mut target = store.destination;
                        target.mutable = true;
                        target
                    },
                ));
            }
            _ => {}
        }
        if let FlowAction::Evaluate(value) = node.action {
            if let NodeKind::Form {
                callee: Some(callee),
                children,
                ..
            } = &body.nodes[value.0].kind
            {
                for access in &effects[callee] {
                    if let Some(argument) = children.get(access.input.parameter + 1) {
                        physical.extend(origins.apply_summary_before(
                            body,
                            flow,
                            event,
                            *argument,
                            &access.input,
                        ));
                    }
                }
            }
        }
        for origin in physical {
            if !origin.pinned
                || origin.owned_allocation
                || origin.lifetime_only
                || !origin.storage.is_empty()
            {
                continue;
            }
            let Some(mut input) = origin.parameter_summary() else {
                continue;
            };
            if input.fresh_allocation.is_some() || input.global.is_some() {
                continue;
            }
            input.storage.clear();
            input.storage_inputs.clear();
            if !accesses.iter().any(|access| access.input == input) {
                accesses.push(Access {
                    input,
                    span: node.span,
                });
            }
        }
    }
    visiting.remove(&id);
    effects.insert(id, accesses);
}

/// An argument can lend one exact stored pointer. Lending a wrapper address
/// does not grant every pointer contained in its pointee or every sibling.
fn granted_slots(body: &Body, argument: NodeId, input: &ParameterLoanSummary) -> Vec<Place> {
    if let NodeKind::Form {
        head,
        children,
        callee: None,
        ..
    } = &body.nodes[argument.0].kind
    {
        if matches!(
            head.as_str(),
            "borrow" | "borrow-mut" | "pin" | "pin-shared" | "pin-borrow" | "pin-borrow-mut"
        ) && input.input_storage.first() == Some(&Segment::Dereference)
            && !input.input_storage[1..].contains(&Segment::Dereference)
            && !crate::typed_place::reads_through_reference(body, children[1])
        {
            if let Some(mut slot) = Place::from_expression(body, children[1]) {
                slot.segments.extend_from_slice(&input.input_storage[1..]);
                return vec![slot];
            }
        }
    }
    if input
        .input_storage
        .iter()
        .all(|part| *part != Segment::Dereference)
    {
        if let Some(mut slot) = Place::from_expression(body, argument) {
            slot.segments.extend_from_slice(&input.input_storage);
            return vec![slot];
        }
    }
    Vec::new()
}

pub(crate) fn check(
    declarations: &Declarations,
    types: &LinearTypes,
    caches: &HashMap<&str, OnceCell<FlowLoanOrigins>>,
) -> Result<(), BorrowConflict> {
    let mut relevant = declarations
        .bodies
        .iter()
        .filter_map(|(name, body)| {
            body.parameter_loan_slots
                .iter()
                .chain(&body.parameter_referent_loan_slots)
                .flatten()
                .any(|slot| {
                    slot.pinned
                        && slot
                            .storage
                            .iter()
                            .all(|slot| matches!(slot, Segment::Field(_) | Segment::Dereference))
                        && slot
                            .storage
                            .iter()
                            .any(|slot| matches!(slot, Segment::Field(_)))
                })
                .then(|| declarations.function_id(name).unwrap())
        })
        .collect::<HashSet<_>>();
    if relevant.is_empty() {
        return Ok(());
    }
    // A forwarding/helper function must not hide its callee's access just
    // because its own public parameter is a plain pinned reference.
    let mut callers = HashMap::<FunctionId, Vec<FunctionId>>::new();
    for (name, body) in &declarations.bodies {
        let caller = declarations.function_id(name).unwrap();
        for (_, callee) in calls(body) {
            callers.entry(callee).or_default().push(caller);
        }
    }
    let mut pending = relevant.iter().copied().collect::<Vec<_>>();
    while let Some(callee) = pending.pop() {
        for caller in callers.get(&callee).into_iter().flatten() {
            if relevant.insert(*caller) {
                pending.push(*caller);
            }
        }
    }
    let mut effects = HashMap::new();
    for id in &relevant {
        infer(*id, declarations, caches, &mut effects, &mut HashSet::new());
    }
    let mut names = declarations.bodies.keys().collect::<Vec<_>>();
    names.sort();
    for name in names {
        let body = &declarations.bodies[name];
        if !calls(body).any(|(_, callee)| relevant.contains(&callee)) {
            continue;
        }
        let flow = &declarations.flows[name];
        let origins = caches[name.as_str()].get_or_init(|| flow.loan_origins(body));
        let live = flow.liveness(body);
        let unread = crate::typed_borrow::unread_loan_bindings(body, flow, types, origins);
        let consumed = flow.consumptions(body, types);
        let mut events = (0..flow.nodes.len()).collect::<Vec<_>>();
        events.sort_by_key(|index| {
            (
                flow.nodes[*index]
                    .span
                    .map(|span| span.start)
                    .unwrap_or(usize::MAX),
                std::cmp::Reverse(*index),
            )
        });
        for index in events {
            let node = &flow.nodes[index];
            let FlowAction::Evaluate(value) = node.action else {
                continue;
            };
            let NodeKind::Form {
                callee: Some(callee),
                children,
                ..
            } = &body.nodes[value.0].kind
            else {
                continue;
            };
            if !relevant.contains(callee) {
                continue;
            }
            let event = FlowNodeId(index);
            for access in &effects[callee] {
                let argument = children[access.input.parameter + 1];
                let mut grants = granted_slots(body, argument, &access.input);
                grants.extend(origins.summary_slots_before(
                    body,
                    flow,
                    event,
                    argument,
                    &access.input,
                ));
                let granted_loans = grants
                    .iter()
                    .flat_map(|slot| match slot.root {
                        PlaceRoot::Local(binding) => origins
                            .before(event, binding)
                            .iter()
                            .filter(|held| held.storage == slot.segments)
                            .cloned()
                            .collect::<Vec<_>>(),
                        _ => Vec::new(),
                    })
                    .collect::<Vec<_>>();
                for target in
                    origins.apply_summary_before(body, flow, event, argument, &access.input)
                {
                    if target.lifetime_only || !target.storage.is_empty() {
                        continue;
                    }
                    // Ownership transfer retires a caller binding, not the
                    // loan currently passed into another callee parameter.
                    for (parameter, other) in children.iter().skip(1).enumerate() {
                        if parameter == access.input.parameter {
                            continue;
                        }
                        for held in origins.value_before(body, flow, event, *other) {
                            if held.owned_allocation
                                || held.lifetime_only
                                || !(target.mutable || held.mutable)
                                || !same_pointer(&target, &held)
                            {
                                continue;
                            }
                            return Err(BorrowConflict {
                                message: "callee accesses a pinned pointee while another argument retains a conflicting borrow".into(),
                                span: body.nodes[argument.0].span.or(node.span),
                                labels: body.nodes[other.0].span.map(|span| (span, "conflicting pointee loan is passed here".into()))
                                    .into_iter().chain(access.span.map(|span| (span, "callee accesses the pointee here".into()))).collect(),
                            });
                        }
                    }
                    for binding in crate::typed_borrow::visible_loan_bindings(
                        &live,
                        &unread,
                        event,
                        body.bindings.len(),
                    ) {
                        for held in origins.before(event, binding) {
                            let slot = Place {
                                root: PlaceRoot::Local(binding),
                                segments: held.storage.clone(),
                            };
                            if held.owned_allocation
                                || !(target.mutable || held.mutable)
                                || !same_pointer(&target, held)
                                || grants.contains(&slot)
                                || granted_loans.iter().any(|grant| {
                                    same_pointer(held, grant)
                                        && held.place.segments.len() < grant.place.segments.len()
                                        && grant.place.segments.starts_with(&held.place.segments)
                                })
                                || consumed.definitely_consumed_before(event, &slot)
                                || consumed.definitely_consumed_before(
                                    event,
                                    &Place::root(slot.root.clone()),
                                )
                            {
                                continue;
                            }
                            return Err(BorrowConflict {
                                message: format!("callee accesses a pinned pointee while '{}' retains a conflicting borrow", body.bindings[binding.0].name),
                                span: body.nodes[argument.0].span.or(node.span),
                                labels: held.span.into_iter().map(|span| (span, "pointee borrowed here".into()))
                                    .chain(access.span.map(|span| (span, "callee accesses the pointee here".into()))).collect(),
                            });
                        }
                    }
                }
            }
        }
    }
    Ok(())
}
