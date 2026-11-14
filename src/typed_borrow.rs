//! Checks simultaneous call-argument loans and live direct-loan conflicts
//! using resolved places. Pure constructors preserve direct borrows through
//! aggregates, conditional results, and reference-returning calls. Loop break
//! values are transferred from their checked control-flow instructions.

use std::cell::OnceCell;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use crate::linearcheck::LinearTypes;
use crate::typed_body::{BindingId, Body, Control, NodeId, NodeKind, PlaceRoot};
use crate::typed_flow::{FlowAction, FlowGraph, FlowLoanOrigins, FlowNodeId, LoanOrigin};
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

#[cfg(test)]
pub(crate) fn check_live_direct_loans_with_types(
    body: &Body,
    flow: &FlowGraph,
    types: &LinearTypes,
) -> Result<(), BorrowConflict> {
    check_live_direct_loans_cached(body, flow, types, &OnceCell::new())
}

#[cfg(test)]
pub(crate) fn check_live_direct_loans_cached(
    body: &Body,
    flow: &FlowGraph,
    types: &LinearTypes,
    cache: &OnceCell<FlowLoanOrigins>,
) -> Result<(), BorrowConflict> {
    check_live_direct_loans_cached_with_permissions(body, flow, types, cache, &[])
}

pub(crate) fn check_live_direct_loans_cached_with_permissions(
    body: &Body,
    flow: &FlowGraph,
    types: &LinearTypes,
    cache: &OnceCell<FlowLoanOrigins>,
    permissions: &[crate::call_self_loans::InternalReborrowPermission],
) -> Result<(), BorrowConflict> {
    if !flow
        .nodes
        .iter()
        .any(|node| matches!(node.action, FlowAction::Borrow { .. }))
        && body.parameter_loan_slots.iter().all(Vec::is_empty)
        && !body.nodes.iter().any(|node| match &node.kind {
            NodeKind::Form {
                callee: Some(callee),
                ..
            } => body
                .call_return_origins
                .get(callee)
                .is_some_and(|summary| summary.iter().any(|origin| origin.global.is_some())),
            NodeKind::Form { head, .. }
                if matches!(
                    head.as_str(),
                    "pin-own-borrow"
                        | "pin-own-borrow-mut"
                        | "pin-shared-borrow"
                        | "pin-shared-borrow-mut"
                ) =>
            {
                true
            }
            _ => false,
        })
    {
        return Ok(());
    }
    let origins = cache.get_or_init(|| flow.loan_origins(body));
    let consumptions = flow.consumptions(body, types);
    let live = flow.liveness(body);
    let unread = unread_loan_bindings(body, flow, types, origins);
    let returned_loans = flow
        .nodes
        .iter()
        .enumerate()
        .filter_map(|(index, node)| match node.action {
            FlowAction::Return(Some(value)) => {
                Some(origins.value_before(body, flow, FlowNodeId(index), value))
            }
            _ => None,
        })
        .flatten()
        .collect::<Vec<_>>();
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
                // This property is invariant across accesses to the scope.
                // Inspect the node once without cloning its owned syntax.
                let is_temporary_reference = matches!(
                    &body.nodes[value.0].kind,
                    NodeKind::Form { head, children, .. }
                        if matches!(head.as_str(), "borrow" | "borrow-mut" | "pin" | "pin-shared" | "pin-borrow" | "pin-borrow-mut")
                            && children.len() == 2
                );
                Some((value, (places, mutable, node.span, is_temporary_reference)))
            }
            _ => None,
        })
        .collect::<HashMap<_, _>>();
    let scoped_before = scoped_borrows_before(flow, &scoped_ids);
    // Nodes are allocated backwards while constructing continuations. Report
    // the first offending source access, not a later cleanup that happens to
    // have a smaller allocation index. Loan snapshots remain CFG fixed points.
    let mut accesses = (0..flow.nodes.len()).collect::<Vec<_>>();
    accesses.sort_by_key(|index| {
        (
            flow.nodes[*index]
                .span
                .map(|span| span.start)
                .unwrap_or(usize::MAX),
            std::cmp::Reverse(*index),
        )
    });
    for index in accesses {
        let node = &flow.nodes[index];
        // Computed reference operands have no syntactic place, so lowering
        // represents their write or tag read as Evaluate. Resolve the actual
        // evaluated target instead of omitting the access from loan checks.
        let tag_receiver = match node.action {
            FlowAction::Evaluate(value) => match &body.nodes[value.0].kind {
                NodeKind::Form { head, children, .. }
                    if head == "#variant-is" && children.len() == 3 =>
                {
                    Some(children[1])
                }
                _ => None,
            },
            _ => None,
        };
        let computed_targets = match node.action {
            FlowAction::Read { value, .. } | FlowAction::Write { value, .. } => {
                match &body.nodes[value.0].kind {
                    NodeKind::Form { head, children, .. }
                        if matches!(head.as_str(), "deref" | "deref-set") =>
                    {
                        let targets =
                            origins.value_before(body, flow, FlowNodeId(index), children[1]);
                        if targets.iter().any(|origin| origin.reborrow_slot.is_some()) {
                            targets
                                .into_iter()
                                .filter(|origin| !origin.lifetime_only && origin.storage.is_empty())
                                .collect()
                        } else {
                            Vec::new()
                        }
                    }
                    _ => Vec::new(),
                }
            }
            FlowAction::Borrow { value, .. } => match &body.nodes[value.0].kind {
                NodeKind::Form { head, .. }
                    if matches!(
                        head.as_str(),
                        "pin-own-borrow"
                            | "pin-own-borrow-mut"
                            | "pin-shared-borrow"
                            | "pin-shared-borrow-mut"
                            | "borrow-slice"
                            | "borrow-slice-mut"
                            | "slice-mut-range"
                            | "slice-mut-idx"
                    ) =>
                {
                    origins
                        .value_before(body, flow, FlowNodeId(index), value)
                        .into_iter()
                        .filter(|origin| !origin.lifetime_only && origin.storage.is_empty())
                        .collect()
                }
                _ => Vec::new(),
            },
            FlowAction::Evaluate(value) => match &body.nodes[value.0].kind {
                NodeKind::Form { head, .. }
                    if matches!(
                        head.as_str(),
                        "pin-own-borrow"
                            | "pin-own-borrow-mut"
                            | "pin-shared-borrow"
                            | "pin-shared-borrow-mut"
                    ) =>
                {
                    origins
                        .value_before(body, flow, FlowNodeId(index), value)
                        .into_iter()
                        .filter(|origin| !origin.lifetime_only && origin.storage.is_empty())
                        .collect()
                }
                NodeKind::Form { head, children, .. }
                    if matches!(head.as_str(), "deref-set" | "#variant-is")
                        && children.len() == 3 =>
                {
                    origins.value_before(body, flow, FlowNodeId(index), children[1])
                }
                _ => Vec::new(),
            },
            _ => Vec::new(),
        };
        let computed_borrow = match node.action {
            FlowAction::Evaluate(value) => match &body.nodes[value.0].kind {
                NodeKind::Form { head, .. }
                    if matches!(
                        head.as_str(),
                        "pin-own-borrow"
                            | "pin-own-borrow-mut"
                            | "pin-shared-borrow"
                            | "pin-shared-borrow-mut"
                    ) =>
                {
                    Some(matches!(
                        head.as_str(),
                        "pin-own-borrow-mut" | "pin-shared-borrow-mut"
                    ))
                }
                _ => None,
            },
            _ => None,
        };
        let (place, access) = match &node.action {
            FlowAction::Evaluate(_) if !computed_targets.is_empty() => (
                &computed_targets[0].place,
                if let Some(mutable) = computed_borrow {
                    AccessKind::Borrow { mutable }
                } else if tag_receiver.is_some() {
                    AccessKind::Read
                } else {
                    AccessKind::Write
                },
            ),
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
            FlowAction::Evaluate(_) if tag_receiver.is_some() => true,
            _ => false,
        };
        let event = FlowNodeId(index);
        let mut projected = computed_targets
            .iter()
            .map(|origin| origin.referent_place())
            .collect::<Vec<_>>();
        let mut reborrow_parent = computed_targets
            .first()
            .and_then(|origin| origin.borrowed_from);
        let mut access_origins = computed_targets.clone();
        if computed_targets.is_empty() && !matches!(access, AccessKind::Move) {
            if let PlaceRoot::Local(binding) = &place.root {
                access_origins = origins.projected_origins(event, *binding, &place.segments);
                projected = access_origins
                    .iter()
                    .map(LoanOrigin::referent_place)
                    .collect();
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
        let mut tag_sources = Vec::new();
        if let Some(receiver) = tag_receiver {
            // Reuse ordinary argument-result slot permissions. A reference
            // stored in an owned field grants access from that exact slot,
            // not from every other reference stored in the same aggregate.
            call_argument_slots(body, receiver, &mut tag_sources);
        }
        let mut write_sources = Vec::new();
        if let FlowAction::Write { value, .. } | FlowAction::Evaluate(value) = node.action {
            if let NodeKind::Form { head, children, .. } = &body.nodes[value.0].kind {
                if head == "deref-set" && children.len() == 3 {
                    call_argument_slots(body, children[1], &mut write_sources);
                }
            }
        }
        let mut suspended_parents = HashSet::new();
        let mut suspended_slots = access_origins
            .iter()
            .filter_map(|origin| origin.reborrow_slot.clone())
            .collect::<Vec<_>>();
        let mut pending_parents = reborrow_parent.into_iter().collect::<Vec<_>>();
        if tag_receiver.is_some() {
            pending_parents.extend(
                computed_targets
                    .iter()
                    .filter_map(|origin| origin.borrowed_from),
            );
        }
        while let Some(parent) = pending_parents.pop() {
            if !suspended_parents.insert(parent) {
                continue;
            }
            for origin in origins.before(event, parent) {
                if let Some(slot) = &origin.reborrow_slot {
                    if !suspended_slots.contains(slot) {
                        suspended_slots.push(slot.clone());
                    }
                }
                pending_parents.extend(origin.borrowed_from);
            }
        }
        for binding in visible_loan_bindings(&live, &unread, event, body.bindings.len()) {
            if suspended_parents.contains(&binding)
                && (matches!(
                    body.bindings[binding.0].ty,
                    Type::Reference { .. }
                        | Type::PinnedReference { .. }
                        | Type::Slice(_)
                        | Type::MutableSlice(_)
                ) || !suspended_slots
                    .iter()
                    .any(|slot| slot.root == PlaceRoot::Local(binding)))
            {
                continue;
            }
            if consumptions
                .definitely_consumed_before(event, &Place::root(PlaceRoot::Local(binding)))
            {
                continue;
            }
            for held in origins.before(event, binding) {
                if matches!(access, AccessKind::Release)
                    && place.root == PlaceRoot::Local(binding)
                    && !held.storage.is_empty()
                    && held.storage.starts_with(&place.segments)
                    && !held
                        .storage
                        .contains(&crate::typed_place::Segment::Dereference)
                {
                    // Releasing owned storage ends its contained handles as
                    // well. An internal loan in that same released subtree
                    // cannot survive the release; other bindings and sibling
                    // slots still undergo the ordinary conflict checks.
                    continue;
                }
                if suspended_slots.iter().any(|slot| {
                    slot.root == PlaceRoot::Local(binding) && slot.segments == held.storage
                }) {
                    continue;
                }
                if held.owned_allocation {
                    continue;
                }
                if tag_sources.iter().any(|source| {
                    source.root == PlaceRoot::Local(binding) && source.segments == held.storage
                }) {
                    continue;
                }
                let slot = Place {
                    root: PlaceRoot::Local(binding),
                    segments: held.storage.clone(),
                };
                if consumptions.definitely_consumed_before(event, &slot) {
                    continue;
                }
                let held_place = held.referent_place();
                let overlaps_access = if access_origins.is_empty() {
                    access_places.iter().any(|place| held_place.overlaps(place))
                } else {
                    access_origins
                        .iter()
                        .any(|origin| call_referents_overlap(held, origin))
                };
                if let FlowAction::Read { value, .. } = &node.action {
                    let argument_origins = origins.value_before(body, flow, event, *value);
                    if internal_reborrow_argument_matches(
                        body,
                        permissions,
                        *value,
                        &held_place,
                        &argument_origins,
                    ) {
                        continue;
                    }
                }
                if access_is_through_child_of_held_parent(origins, event, place, held) {
                    continue;
                }
                // A retained slice operation can borrow the descriptor itself.
                // A checked call instead lends its pointee: exact slot ancestry
                // supplies permission, while ordinary overlap checks below
                // still reject conflicting pointee access or destruction.
                if !held.call_reborrow
                    && held
                        .reborrow_slot
                        .as_ref()
                        .is_some_and(|slot| slot.overlaps(place))
                    && !matches!(&node.action,
                        FlowAction::Read { value, .. } if is_mutable_slice_index_base(body, *value))
                {
                    return Err(BorrowConflict {
                        message: "cannot access or release a slice handle while its derived reference is active".into(),
                        span: node.span,
                        labels: held.span.into_iter().map(|span|
                            (span, "derived reference originates here".into())).collect(),
                    });
                }
                let resumes_suspended_parent =
                    accesses_suspended_exclusive_parent(body, origins, event, place, held);
                if matches!(node.action, FlowAction::Evaluate(value)
                if internal_reborrow_access_matches(
                    permissions,
                    value,
                    &held_place,
                    &computed_targets,
                )) {
                    // Returning a reference to this owner is not itself an
                    // access to every referent stored inside it. The call's
                    // exact child slot and callee effects were checked by
                    // `check_calls_cached`; let that proof authorize the
                    // disjoint call while keeping ordinary accesses checked.
                    continue;
                }
                if matches!(access, AccessKind::Read)
                    && place.segments.is_empty()
                    && !matches!(&node.action,
                        FlowAction::Read { value, .. }
                            if is_mutable_slice_index_base(body, *value))
                {
                    if let PlaceRoot::Local(parent) = place.root {
                        if held.borrowed_from == Some(parent)
                            && matches!(body.bindings[parent.0].ty, Type::MutableSlice(_))
                        {
                            let parent = &body.bindings[parent.0].name;
                            return Err(BorrowConflict {
                                message: format!("cannot use reference '{parent}' while a derived field reference is active"),
                                span: node.span,
                                labels: held.span.into_iter().map(|span|
                                    (span, "derived reference originates here".into())).collect(),
                            });
                        }
                    }
                }
                let releasing_reborrow_parent =
                    match (&place.root, place.segments.is_empty(), access) {
                        (
                            PlaceRoot::Local(parent),
                            true,
                            AccessKind::Write | AccessKind::Release,
                        ) => {
                            let transfers_returned_loan = !held.lifetime_only
                                && returned_loans.iter().any(|returned| {
                                    returned.borrowed_from == Some(*parent)
                                        && returned.referent_place() == held.referent_place()
                                        && returned.mutable == held.mutable
                                        && returned.pinned == held.pinned
                                        && returned.owned_allocation == held.owned_allocation
                                        && !returned.lifetime_only
                                });
                            let is_non_owning_handle = matches!(
                                body.bindings[parent.0].ty,
                                Type::Reference { .. }
                                    | Type::PinnedReference { .. }
                                    | Type::Slice(_)
                                    | Type::MutableSlice(_)
                            );
                            held.borrowed_from == Some(*parent)
                                && !held.call_reborrow
                                && !(is_non_owning_handle && transfers_returned_loan)
                        }
                        _ => false,
                    };
                if releasing_reborrow_parent {
                    let parent = match &place.root {
                        PlaceRoot::Local(parent) => body.bindings[parent.0].name.as_str(),
                        _ => unreachable!(),
                    };
                    return Err(BorrowConflict {
                        message: crate::analysis_error::failure!(
                            "cannot move or destroy reference '{parent}' while a stored derived reference borrows it"
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
                if matches!(access, AccessKind::Read)
                    && !held.storage.is_empty()
                    && place.root == PlaceRoot::Local(binding)
                    && matches!(&node.action, FlowAction::Read { value, .. }
                        if matches!(body.nodes[value.0].ty,
                            Some(Type::Reference { .. } | Type::PinnedReference { .. }
                                | Type::MutableSlice(_))))
                    && (place.segments == held.storage
                        || place
                            .segments
                            .strip_suffix(&[crate::typed_place::Segment::Dereference])
                            == Some(held.storage.as_slice()))
                {
                    // Loading this exact stored handle is not a read of its
                    // pointee through an independent alias. Derived-child
                    // restrictions above still suspend the handle itself.
                    continue;
                }
                if matches!(access, AccessKind::Write)
                    && held.mutable
                    && !held.lifetime_only
                    && write_sources.iter().any(|source| {
                        source.root == PlaceRoot::Local(binding) && source.segments == held.storage
                    })
                    && access_origins.iter().any(|origin| {
                        origin.mutable
                            && !origin.lifetime_only
                            && origin.referent_place() == held.referent_place()
                    })
                {
                    // Writing through this exact stored mutable handle uses
                    // its own capability, not an independent alias. Child
                    // suspension above and all other live loans still apply.
                    continue;
                }
                let forbidden_pinned_access = held.pinned
                    && !reference_value_access
                    && overlaps_access
                    && access_places.iter().any(|place| {
                        held_place.overlaps(place)
                            && match access {
                                AccessKind::Read => held_place == *place,
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
                        PlaceRoot::Allocation(_, _) => "pinned allocation",
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
                let conflicts = resumes_suspended_parent
                    || match access {
                        AccessKind::Read | AccessKind::Clone => held.mutable,
                        AccessKind::Borrow { mutable } => held.mutable || mutable,
                        AccessKind::Move | AccessKind::Write | AccessKind::Release => true,
                    };
                if conflicts && overlaps_access {
                    let owner = if matches!(access, AccessKind::Read) {
                        diagnostic_place_name(
                            body,
                            access_places
                                .iter()
                                .find(|place| held_place.overlaps(place))
                                .unwrap(),
                        )
                    } else {
                        match held.place.root {
                            PlaceRoot::Local(binding) | PlaceRoot::Parameter(binding) => {
                                body.bindings[binding.0].name.clone()
                            }
                            PlaceRoot::Global(_) => "static".into(),
                            PlaceRoot::Allocation(_, _) => "pinned allocation".into(),
                        }
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
            let Some((held_places, held_mutable, held_span, is_temporary_reference)) =
                scoped_places.get(&scope)
            else {
                continue;
            };
            // A temporary borrow normally ends with its expression scope.
            // If a returned value carries that borrow, its precise lifetime
            // is instead governed by the live binding that owns the loan.
            // This matters for async start/poll calls: Pending retains the
            // returned frame, while Ready can consume it and release the
            // captured external borrow before the lexical block ends.
            let carried_by_live_value = held_span.is_some_and(|span| {
                if !*is_temporary_reference {
                    return true;
                }
                live.before(event).iter().any(|binding| {
                    !consumptions
                        .definitely_consumed_before(event, &Place::root(PlaceRoot::Local(*binding)))
                        && origins
                            .before(event, *binding)
                            .iter()
                            .any(|origin| origin.span == Some(span))
                })
            });
            if !carried_by_live_value {
                continue;
            }
            let mutable_scope_access = *held_mutable
                && reborrow_parent.is_none()
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
            let owner = if matches!(access, AccessKind::Read) {
                diagnostic_place_name(
                    body,
                    access_places
                        .iter()
                        .find(|place| held_place.overlaps(place))
                        .unwrap(),
                )
            } else {
                match &held_place.root {
                    PlaceRoot::Local(binding) | PlaceRoot::Parameter(binding) => {
                        body.bindings[binding.0].name.clone()
                    }
                    PlaceRoot::Global(_) => "static".into(),
                    PlaceRoot::Allocation(_, _) => "pinned allocation".into(),
                }
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
    check_call_reborrow_parents(
        body,
        flow,
        origins,
        &live,
        &unread,
        &consumptions,
        permissions,
    )
}

/// A mutable-slice handle read used only as the receiver of an element/range borrow
/// is not an access to the suspended slice contents. The resulting indexed
/// borrow event checks overlap against existing element loans precisely.
fn is_mutable_slice_index_base(body: &Body, value: NodeId) -> bool {
    body.nodes.iter().any(|node| {
        matches!(&node.kind,
            NodeKind::Form { head, children, .. }
                if matches!(head.as_str(), "slice-mut-idx" | "slice-mut-range") && children.get(1) == Some(&value))
    })
}

fn diagnostic_place_name(body: &Body, place: &Place) -> String {
    use crate::typed_ir::DeclarationId;
    use crate::typed_place::Segment;
    let mut name = match place.root {
        PlaceRoot::Local(binding) | PlaceRoot::Parameter(binding) => {
            body.bindings[binding.0].name.clone()
        }
        PlaceRoot::Global(_) => "static".into(),
        PlaceRoot::Allocation(_, _) => "pinned allocation".into(),
    };
    for segment in &place.segments {
        match segment {
            Segment::Field(field) => {
                name.push('.');
                if let Some(field) = body.declaration_name(DeclarationId::Field(*field)) {
                    name.push_str(field);
                } else {
                    name.push_str(&field.index.to_string());
                }
            }
            Segment::Tuple(index) => name.push_str(&format!(".{index}")),
            Segment::Index(index) | Segment::SliceIndex(index) => {
                name.push_str(&format!(".{index}"))
            }
            Segment::DynamicIndex | Segment::SliceDynamicIndex => name.push_str(".*"),
            Segment::SliceRange { start, end } => {
                name.push_str(&format!("[{start}..{end}]"));
            }
            Segment::SliceRangeUnknown => name.push_str("[range?]"),
            Segment::Payload(variant, index) => {
                name.push('.');
                if let Some(variant) = body.declaration_name(DeclarationId::Variant(*variant)) {
                    name.push_str(variant);
                }
                name.push_str(&format!(".{index}"));
            }
            Segment::Dereference => name.push_str(".*"),
            Segment::SliceHalf(index) => name.push_str(&format!("[half {index}]")),
            Segment::ThreadCapture(_, index) => name.push_str(&format!(".capture[{index}]")),
        }
    }
    name
}

/// A freshly bound reference-bearing value retains its loans before its first
/// owned value use. Ordinary use liveness then determines visibility; merely
/// borrowing the container's address or copying through a pin does not use up
/// the original holder. Parameters and pattern-produced copies use ordinary
/// liveness from the outset. Slot consumption remains authoritative for moves
/// and explicit release, including moves through a local pinned reference.
pub(crate) fn unread_loan_bindings(
    body: &Body,
    flow: &FlowGraph,
    types: &LinearTypes,
    origins: &FlowLoanOrigins,
) -> Vec<Vec<u64>> {
    use std::collections::VecDeque;
    let words = body.bindings.len().div_ceil(64);
    let mut before = vec![None::<Vec<u64>>; flow.nodes.len()];
    before[flow.entry.0] = Some(vec![0; words]);
    let mut pending = VecDeque::from([flow.entry]);
    let mut queued = vec![false; flow.nodes.len()];
    queued[flow.entry.0] = true;
    while let Some(event) = pending.pop_front() {
        queued[event.0] = false;
        let mut state = before[event.0].as_ref().unwrap().clone();
        let set = |state: &mut [u64], binding: BindingId, active: bool| {
            let mask = 1u64 << (binding.0 % 64);
            if active {
                state[binding.0 / 64] |= mask;
            } else {
                state[binding.0 / 64] &= !mask;
            }
        };
        match &flow.nodes[event.0].action {
            FlowAction::Bind { binding, .. } => {
                set(
                    &mut state,
                    *binding,
                    types.contains_reference(&body.bindings[binding.0].ty),
                );
            }
            FlowAction::Assign { place, .. } if place.segments.is_empty() => {
                if let PlaceRoot::Local(binding) = place.root {
                    set(
                        &mut state,
                        binding,
                        types.contains_reference(&body.bindings[binding.0].ty),
                    );
                }
            }
            FlowAction::Read {
                place,
                place_base: false,
                ..
            } if place.segments.is_empty() => {
                if let PlaceRoot::Local(binding) = place.root {
                    set(&mut state, binding, false);
                }
            }
            FlowAction::Borrow { place, .. } if !place.segments.is_empty() => {
                if let PlaceRoot::Local(binding) = place.root {
                    if matches!(
                        body.bindings[binding.0].ty,
                        Type::Reference { .. } | Type::PinnedReference { .. }
                    ) {
                        set(&mut state, binding, false);
                    }
                }
            }
            FlowAction::Evaluate(value) => {
                if let NodeKind::Form {
                    children,
                    callee: Some(_),
                    ..
                } = &body.nodes[value.0].kind
                {
                    for argument in children.iter().skip(1) {
                        for origin in origins.value_before(body, flow, event, *argument) {
                            if !origin.pinned
                                && !origin.lifetime_only
                                && origin.storage.is_empty()
                                && origin.place.segments.is_empty()
                            {
                                if let PlaceRoot::Local(binding) = origin.place.root {
                                    set(&mut state, binding, false);
                                }
                            }
                        }
                    }
                }
            }
            FlowAction::Release { place, .. } if place.segments.is_empty() => {
                if let PlaceRoot::Local(binding) = place.root {
                    set(&mut state, binding, false);
                }
            }
            FlowAction::ScopeExit(bindings) => {
                for binding in bindings {
                    set(&mut state, *binding, false);
                }
            }
            _ => {}
        }
        for successor in &flow.nodes[event.0].successors {
            let changed = if let Some(existing) = &mut before[successor.0] {
                let mut changed = false;
                for (held, incoming) in existing.iter_mut().zip(&state) {
                    let joined = *held | incoming;
                    changed |= joined != *held;
                    *held = joined;
                }
                changed
            } else {
                before[successor.0] = Some(state.clone());
                true
            };
            if changed && !queued[successor.0] {
                queued[successor.0] = true;
                pending.push_back(*successor);
            }
        }
    }
    before
        .into_iter()
        .map(|state| state.unwrap_or_default())
        .collect()
}

pub(crate) fn visible_loan_bindings(
    live: &crate::typed_flow::FlowLiveness,
    unread: &[Vec<u64>],
    event: FlowNodeId,
    count: usize,
) -> Vec<BindingId> {
    let mut visible = live.before(event);
    visible.extend((0..count).filter_map(|index| {
        unread[event.0]
            .get(index / 64)
            .is_some_and(|word| word & (1 << (index % 64)) != 0)
            .then_some(BindingId(index))
    }));
    visible.sort_unstable_by_key(|binding| binding.0);
    visible.dedup();
    visible
}

/// A reference argument grants callee access to its referent, even when the
/// argument expression only reads the pointer slot. Check that access against
/// retained child reborrows; the argument's own slot and reborrow ancestors
/// supply its permission, rather than conflicting with themselves. Independent
/// argument aliasing and opaque/borrowed-storage lifetimes have separate checks.
fn check_call_reborrow_parents(
    body: &Body,
    flow: &FlowGraph,
    origins: &FlowLoanOrigins,
    live: &crate::typed_flow::FlowLiveness,
    unread: &[Vec<u64>],
    consumptions: &crate::typed_flow::FlowConsumptions,
    permissions: &[crate::call_self_loans::InternalReborrowPermission],
) -> Result<(), BorrowConflict> {
    for (index, node) in flow.nodes.iter().enumerate() {
        let FlowAction::Evaluate(value) = node.action else {
            continue;
        };
        let NodeKind::Form {
            children,
            callee: Some(callee),
            ..
        } = &body.nodes[value.0].kind
        else {
            continue;
        };
        let head = body
            .declaration_name(crate::typed_ir::DeclarationId::Function(*callee))
            .expect("checked call declaration");
        let event = FlowNodeId(index);
        for argument in children.iter().skip(1) {
            // References stored inside a borrowed pointee describe its
            // contents, not additional references lent by this argument.
            let incoming = origins
                .value_before(body, flow, event, *argument)
                .into_iter()
                .filter(|origin| {
                    !origin
                        .storage
                        .contains(&crate::typed_place::Segment::Dereference)
                })
                .collect::<Vec<_>>();
            if incoming.is_empty() {
                continue;
            }
            let mut sources = Vec::new();
            call_argument_slots(body, *argument, &mut sources);
            if let NodeKind::Form { head, children, .. } = &body.nodes[argument.0].kind {
                if head == "deref"
                    && children.len() == 2
                    && matches!(&body.nodes[children[1].0].ty,
                        Some(Type::Reference { target, .. } | Type::PinnedReference { target, .. })
                        if matches!(target.as_ref(), Type::Reference { .. } | Type::PinnedReference { .. }))
                {
                    // Loading a reference through a checked reference holder
                    // lends that exact holder's loan, not an independent alias.
                    // Opaque lifetime anchors cannot identify typed holders.
                    sources.extend(
                        origins
                            .value_before(body, flow, event, children[1])
                            .into_iter()
                            .filter(|origin| !origin.lifetime_only && origin.storage.is_empty())
                            .map(|origin| origin.referent_place()),
                    );
                }
            }
            let mut parents = HashSet::new();
            let mut suspended_slots = incoming
                .iter()
                .filter_map(|origin| origin.reborrow_slot.clone())
                .collect::<Vec<_>>();
            let mut pending = incoming
                .iter()
                .filter_map(|origin| origin.borrowed_from)
                .collect::<Vec<_>>();
            while let Some(parent) = pending.pop() {
                if parents.insert(parent) {
                    for origin in origins.before(event, parent) {
                        if let Some(slot) = &origin.reborrow_slot {
                            if !suspended_slots.contains(slot) {
                                suspended_slots.push(slot.clone());
                            }
                        }
                    }
                    pending.extend(
                        origins
                            .before(event, parent)
                            .iter()
                            .filter_map(|origin| origin.borrowed_from),
                    );
                }
            }
            for binding in visible_loan_bindings(live, unread, event, body.bindings.len()) {
                if parents.contains(&binding)
                    && (matches!(
                        body.bindings[binding.0].ty,
                        Type::Reference { .. }
                            | Type::PinnedReference { .. }
                            | Type::Slice(_)
                            | Type::MutableSlice(_)
                    ) || !suspended_slots
                        .iter()
                        .any(|slot| slot.root == PlaceRoot::Local(binding)))
                {
                    continue;
                }
                for held in origins.before(event, binding) {
                    if suspended_slots.iter().any(|slot| {
                        slot.root == PlaceRoot::Local(binding) && slot.segments == held.storage
                    }) {
                        continue;
                    }
                    if held.borrowed_from.is_none() {
                        continue;
                    }
                    let slot = Place {
                        root: PlaceRoot::Local(binding),
                        segments: held.storage.clone(),
                    };
                    if consumptions.definitely_consumed_before(event, &slot)
                        || consumptions
                            .definitely_consumed_before(event, &Place::root(slot.root.clone()))
                        || sources.iter().any(|source: &Place| {
                            source.root == slot.root && slot.segments.starts_with(&source.segments)
                        })
                    {
                        continue;
                    }
                    if !incoming.iter().any(|argument| {
                        (argument.mutable || held.mutable) && call_referents_overlap(argument, held)
                    }) {
                        continue;
                    }
                    if internal_reborrow_permission_matches(
                        permissions,
                        value,
                        &held.referent_place(),
                    ) {
                        continue;
                    }
                    let source = sources
                        .first()
                        .map(|source| &source.root)
                        .unwrap_or(&held.place.root);
                    let name = match source {
                        PlaceRoot::Local(binding) | PlaceRoot::Parameter(binding) => {
                            body.bindings[binding.0].name.as_str()
                        }
                        PlaceRoot::Global(_) => "static",
                        PlaceRoot::Allocation(_, _) => "pinned allocation",
                    };
                    return Err(BorrowConflict {
                        message: crate::analysis_error::failure!(
                            "cannot borrow '{name}' for call to '{head}' while another reference is live"
                        ).message,
                        span: body.nodes[argument.0].span.or(node.span),
                        labels: held.span.into_iter().map(|span| (span, "conflicting reference originates here".into())).collect(),
                    });
                }
            }
        }
    }
    Ok(())
}

fn internal_reborrow_permission_matches(
    permissions: &[crate::call_self_loans::InternalReborrowPermission],
    call: NodeId,
    referent: &Place,
) -> bool {
    // The permission retains the exact stored child slot whose internal
    // access was checked. A copied local holder has a different storage slot,
    // so apply that proof by the call identity and exact physical referent.
    permissions
        .iter()
        .any(|permission| permission.call == call && &permission.referent == referent)
}

fn internal_reborrow_access_matches(
    permissions: &[crate::call_self_loans::InternalReborrowPermission],
    call: NodeId,
    held_referent: &Place,
    accessed_referents: &[LoanOrigin],
) -> bool {
    permissions.iter().any(|permission| {
        permission.call == call
            && &permission.referent == held_referent
            && accessed_referents
                .iter()
                .any(|access| access.referent_place().overlaps(&permission.referent))
    })
}

fn internal_reborrow_argument_matches(
    body: &Body,
    permissions: &[crate::call_self_loans::InternalReborrowPermission],
    argument: NodeId,
    held_referent: &Place,
    argument_origins: &[LoanOrigin],
) -> bool {
    permissions.iter().any(|permission| {
        if &permission.referent != held_referent
            || !argument_origins
                .iter()
                .any(|origin| origin.referent_place().overlaps(&permission.referent))
        {
            return false;
        }
        matches!(
            &body.nodes[permission.call.0].kind,
            NodeKind::Form { children, callee: Some(_), .. }
                if children.iter().skip(1).any(|child| *child == argument)
        )
    })
}

fn access_is_through_child_of_held_parent(
    origins: &FlowLoanOrigins,
    event: FlowNodeId,
    place: &Place,
    held: &LoanOrigin,
) -> bool {
    let Some(parent) = held.borrowed_from else {
        return false;
    };
    let binding = match place.root {
        PlaceRoot::Local(binding) | PlaceRoot::Parameter(binding) => binding,
        _ => return false,
    };
    if binding == parent {
        return false;
    }
    let held_referent = held.referent_place();
    origins.before(event, binding).iter().any(|access| {
        let access_referent = access.referent_place();
        access.borrowed_from == Some(parent)
            && access_referent.root == held_referent.root
            && access_referent != held_referent
            && access_referent
                .segments
                .starts_with(&held_referent.segments)
    })
}

fn accesses_suspended_exclusive_parent(
    body: &Body,
    origins: &FlowLoanOrigins,
    event: FlowNodeId,
    place: &Place,
    held: &LoanOrigin,
) -> bool {
    let Some(parent) = held.borrowed_from else {
        return false;
    };
    if place.segments.is_empty() {
        return false;
    }
    let exclusive = |binding: BindingId| {
        matches!(
            body.bindings[binding.0].ty,
            Type::Reference { mutable: true, .. }
                | Type::PinnedReference { mutable: true, .. }
                | Type::MutableSlice(_)
        )
    };
    let access_binding = match place.root {
        PlaceRoot::Local(binding) | PlaceRoot::Parameter(binding) => binding,
        _ => return false,
    };
    if access_binding == parent {
        return exclusive(access_binding);
    }
    if exclusive(access_binding) {
        let held_referent = held.referent_place();
        origins.before(event, access_binding).iter().any(|access| {
            let access_referent = access.referent_place();
            access.borrowed_from == Some(parent)
                && access_referent.root == held_referent.root
                && access_referent != held_referent
                && held_referent
                    .segments
                    .starts_with(&access_referent.segments)
        })
    } else {
        false
    }
}

fn call_referents_overlap(left: &LoanOrigin, right: &LoanOrigin) -> bool {
    // Different pointer slots in one parameter denote different symbolic
    // referents, not nested physical fields of the outer pointer's referent.
    // Call-site provenance maps those slots to actual caller places, where
    // real aliasing is checked. A derived field keeps the same input slot and
    // adds its physical projection separately.
    if left.place.root == right.place.root && matches!(left.place.root, PlaceRoot::Parameter(_)) {
        if let (Some(left_slot), Some(right_slot)) =
            (&left.parameter_storage, &right.parameter_storage)
        {
            if left_slot.len() != right_slot.len() {
                return false;
            }
            let left_slot = Place {
                root: left.place.root.clone(),
                segments: left_slot.clone(),
            };
            let right_slot = Place {
                root: right.place.root.clone(),
                segments: right_slot.clone(),
            };
            if !left_slot.overlaps(&right_slot) {
                return false;
            }
        }
    }
    left.referent_place().overlaps(&right.referent_place())
}

/// Owned slots supplying an argument's result. Borrow expressions are not
/// owned slots: their parent permission is carried by loan provenance instead.
fn call_argument_slots(body: &Body, value: NodeId, output: &mut Vec<Place>) {
    let node = &body.nodes[value.0];
    match &node.kind {
        NodeKind::Symbol { .. } => {
            if let Some(place) = Place::from_expression(body, value) {
                output.push(place);
            }
        }
        NodeKind::Form { head, .. }
            if matches!(
                head.as_str(),
                "get" | "get-payload" | "index" | "index-proven"
            ) && !reads_through_reference(body, value) =>
        {
            if let Some(place) = Place::from_expression(body, value) {
                output.push(place);
            }
        }
        NodeKind::If {
            then_value,
            else_value,
            ..
        } => {
            call_argument_slots(body, *then_value, output);
            if let Some(value) = else_value {
                call_argument_slots(body, *value, output);
            }
        }
        NodeKind::Match { arms, .. } => {
            for arm in arms {
                if let NodeKind::MatchArm { values, .. } = &body.nodes[arm.0].kind {
                    if let Some(value) = values.last() {
                        call_argument_slots(body, *value, output);
                    }
                }
            }
        }
        NodeKind::Block(instructions) => {
            if let Some(crate::typed_body::Instruction {
                control: Control::Evaluate(value),
                ..
            }) = instructions.last()
            {
                call_argument_slots(body, *value, output);
            }
        }
        NodeKind::Loop(instructions) => {
            for value in loop_result_values(body, instructions, None) {
                call_argument_slots(body, value, output);
            }
        }
        NodeKind::Labeled(label, value) => {
            if let NodeKind::Loop(instructions) = &body.nodes[value.0].kind {
                for value in loop_result_values(body, instructions, Some(label)) {
                    call_argument_slots(body, value, output);
                }
            } else {
                call_argument_slots(body, *value, output);
            }
        }
        NodeKind::Form { head, children, .. } if head == "unsafe" => {
            if let Some(value) = children.get(1) {
                call_argument_slots(body, *value, output);
            }
        }
        _ => {}
    }
}

pub(crate) fn scoped_borrows_before(
    flow: &FlowGraph,
    scoped_ids: &HashSet<NodeId>,
) -> Vec<HashSet<NodeId>> {
    // Without a scoped loan, every transfer preserves the empty set. Avoid
    // constructing predecessors and iterating the fixed point in that case.
    if scoped_ids.is_empty() {
        return vec![HashSet::new(); flow.nodes.len()];
    }
    let mut predecessors = vec![Vec::new(); flow.nodes.len()];
    for (index, node) in flow.nodes.iter().enumerate() {
        for successor in &node.successors {
            predecessors[successor.0].push(index);
        }
    }
    let mut before = vec![HashSet::new(); flow.nodes.len()];
    let mut after = before.clone();
    // Keep two scratch sets across visits. Swapping changed snapshots also
    // retains their old allocation for the next transfer instead of dropping
    // it and allocating a fresh incoming set and outgoing clone each time.
    let mut incoming = HashSet::new();
    let mut outgoing = HashSet::new();
    // Seed every node, as the original whole-graph solver did, including
    // disconnected nodes. Only a changed outgoing set can affect successors.
    let mut pending = (0..flow.nodes.len()).collect::<std::collections::VecDeque<_>>();
    let mut queued = vec![true; flow.nodes.len()];
    while let Some(index) = pending.pop_front() {
        queued[index] = false;
        let node = &flow.nodes[index];
        incoming.clear();
        for predecessor in &predecessors[index] {
            incoming.extend(after[*predecessor].iter().copied());
        }
        outgoing.clear();
        outgoing.extend(incoming.iter().copied());
        match node.action {
            FlowAction::Borrow { value, .. } if scoped_ids.contains(&value) => {
                outgoing.insert(value);
            }
            FlowAction::BorrowScopeEnd { scope } => {
                outgoing.remove(&scope);
            }
            _ => {}
        }
        if before[index] != incoming {
            std::mem::swap(&mut before[index], &mut incoming);
        }
        if after[index] != outgoing {
            std::mem::swap(&mut after[index], &mut outgoing);
            for successor in &node.successors {
                if !queued[successor.0] {
                    queued[successor.0] = true;
                    pending.push_back(successor.0);
                }
            }
        }
    }
    before
}

#[derive(Clone)]
struct DirectBorrow {
    place: Place,
    mutable: bool,
    span: Option<Span>,
    storage: Vec<crate::typed_place::Segment>,
}

fn is_value_constructor(body: &Body, kind: &NodeKind) -> bool {
    matches!(kind, NodeKind::Form { head, children, callee: None, .. }
        if matches!(head.as_str(), "tuple" | "array" | "array-of" | "array-repeat" | "struct-literal")
        || matches!(children.first().map(|child| &body.nodes[child.0].kind),
            Some(NodeKind::Declaration(DeclarationId::Variant(_) | DeclarationId::Aggregate(_)))))
}

#[cfg(test)]
pub(crate) fn check_call_arguments(body: &Body, flow: &FlowGraph) -> Result<(), BorrowConflict> {
    check_call_arguments_cached(body, flow, &OnceCell::new())
}

pub(crate) fn check_call_arguments_cached(
    body: &Body,
    flow: &FlowGraph,
    cache: &OnceCell<FlowLoanOrigins>,
) -> Result<(), BorrowConflict> {
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
            ) || is_value_constructor(body, &node.kind)
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
    let symbol_events = flow
        .nodes
        .iter()
        .enumerate()
        .filter_map(|(index, event)| {
            let FlowAction::Read { value, .. } = event.action else {
                return None;
            };
            matches!(body.nodes[value.0].kind, NodeKind::Symbol { .. })
                .then_some((value, FlowNodeId(index)))
        })
        .collect::<Vec<_>>();
    let origins = cache.get_or_init(|| flow.loan_origins(body));
    let active = flow.definitely_active_bindings_before(body);
    let predecessors = OnceCell::new();
    let mut argument_writes = HashMap::<NodeId, Vec<FlowNodeId>>::new();
    for event in flow.reachable() {
        let node = &flow.nodes[event.0];
        let (FlowAction::Write { value, .. } | FlowAction::Evaluate(value)) = node.action else {
            continue;
        };
        if matches!(&body.nodes[value.0].kind,
            NodeKind::Form { head, callee: None, .. }
                if matches!(head.as_str(), "deref-set" | "pin-write"))
        {
            argument_writes.entry(value).or_default().push(event);
        }
    }
    // Capture operand values at their reads, not after later operands have
    // reassigned their bindings. Share these immutable snapshots across all
    // uses and path alternatives in this function.
    let mut value_snapshots = HashMap::new();
    for (value, read) in &symbol_events {
        let held = origins.value_before(body, flow, *read, *value);
        let ambiguous = held.iter().enumerate().any(|(index, origin)| {
            origin.mutable
                && !origin.storage.is_empty()
                && held[index + 1..].iter().any(|other| {
                    other.mutable && origin.referent_place().overlaps(&other.referent_place())
                })
        });
        if ambiguous {
            if let NodeKind::Symbol {
                binding: Some(binding),
                ..
            } = &body.nodes[value.0].kind
            {
                if let Some(paths) = origins.incoming_binding_paths(
                    body,
                    flow,
                    predecessors.get_or_init(|| {
                        let mut predecessors = vec![Vec::new(); flow.nodes.len()];
                        for (index, node) in flow.nodes.iter().enumerate() {
                            for successor in &node.successors {
                                predecessors[successor.0].push(FlowNodeId(index));
                            }
                        }
                        predecessors
                    }),
                    *read,
                    *binding,
                    &held,
                ) {
                    let mut alternatives = Vec::new();
                    for path in paths {
                        alternatives.extend(
                            origin_alternatives(path, body.nodes[value.0].span)?
                                .unwrap_or_else(|| vec![Vec::new()]),
                        );
                    }
                    value_snapshots
                        .insert(*value, bounded(alternatives, body.nodes[value.0].span)?);
                    continue;
                }
            }
        }
        if let Some(alternatives) = origin_alternatives(&held, body.nodes[value.0].span)? {
            value_snapshots.insert(*value, alternatives);
        }
    }
    let value_snapshots = std::sync::Arc::new(value_snapshots);
    for (index, node) in calls {
        let NodeKind::Form {
            head,
            children,
            callee,
            ..
        } = &node.kind
        else {
            continue;
        };
        let mut bindings = BoundBorrows::new();
        bindings.values = std::sync::Arc::clone(&value_snapshots);
        let call_event = call_events.get(&NodeId(index)).copied();
        if let Some(event) = call_event {
            for index in 0..body.bindings.len() {
                let held = origins.before(event, BindingId(index));
                if let Some(alternatives) = origin_alternatives(held, node.span)? {
                    bindings.insert(BindingId(index), alternatives);
                }
            }
        }
        if callee.is_none() {
            // Fresh borrows in aggregate operands coexist before any local
            // owns the completed value. Check them with the same path-aware
            // alternatives as call operands, rather than waiting for liveness
            // of a destination that may never be read.
            returned_borrows_with_bindings(body, NodeId(index), &format!("#{head}"), &bindings)?;
            continue;
        }
        let head = body
            .declaration_name(crate::typed_ir::DeclarationId::Function(callee.unwrap()))
            .expect("checked call declaration");
        if let Some(event) = call_event {
            if !argument_writes.is_empty() {
                check_argument_writes(body, flow, origins, event, children, &argument_writes)?;
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

/// Evaluated reference operands remain lent while subsequent operands run.
/// Simultaneous argument checks alone miss writes hidden in a later operand.
fn check_argument_writes(
    body: &Body,
    flow: &FlowGraph,
    origins: &FlowLoanOrigins,
    call: FlowNodeId,
    children: &[NodeId],
    write_events: &HashMap<NodeId, Vec<FlowNodeId>>,
) -> Result<(), BorrowConflict> {
    fn instructions(values: &[crate::typed_body::Instruction], pending: &mut Vec<NodeId>) {
        for instruction in values {
            match &instruction.control {
                Control::Bind(_, value, _)
                | Control::Assign(_, _, value)
                | Control::Evaluate(value) => pending.push(*value),
                Control::Destructure {
                    value, otherwise, ..
                } => {
                    pending.push(*value);
                    if let Some(otherwise) = otherwise {
                        instructions(otherwise, pending);
                    }
                }
                Control::While(condition, values) => {
                    pending.push(*condition);
                    instructions(values, pending);
                }
                Control::Loop(values) => instructions(values, pending),
                Control::For(initial, condition, step, values) => {
                    pending.push(*condition);
                    instructions(std::slice::from_ref(initial.as_ref()), pending);
                    instructions(std::slice::from_ref(step.as_ref()), pending);
                    instructions(values, pending);
                }
                Control::Labeled(_, instruction) => {
                    instructions(std::slice::from_ref(instruction.as_ref()), pending)
                }
                Control::Return(value) | Control::Break(_, value) => pending.extend(value),
                Control::Continue(_) => {}
            }
        }
    }
    let mut held = Vec::<LoanOrigin>::new();
    for argument in children.iter().skip(1) {
        if !held.is_empty() {
            let mut pending = vec![*argument];
            let mut writes = HashSet::new();
            while let Some(value) = pending.pop() {
                match &body.nodes[value.0].kind {
                    NodeKind::Form {
                        head,
                        children,
                        callee,
                        ..
                    } => {
                        if callee.is_none() && matches!(head.as_str(), "deref-set" | "pin-write") {
                            writes.insert(value);
                        }
                        pending.extend(children.iter().skip(1));
                    }
                    NodeKind::If {
                        condition,
                        then_value,
                        else_value,
                        ..
                    } => {
                        pending.extend([*condition, *then_value]);
                        pending.extend(else_value);
                    }
                    NodeKind::Match { value, arms, .. } => {
                        pending.push(*value);
                        pending.extend(arms);
                    }
                    NodeKind::MatchArm { values, .. } => pending.extend(values),
                    NodeKind::Block(values) | NodeKind::Loop(values) => {
                        instructions(values, &mut pending)
                    }
                    NodeKind::Labeled(_, value) => pending.push(*value),
                    _ => {}
                }
            }
            let mut events = writes
                .iter()
                .filter_map(|value| write_events.get(value))
                .flatten()
                .copied()
                .collect::<Vec<_>>();
            events.sort_by_key(|event| {
                (
                    flow.nodes[event.0]
                        .span
                        .map(|span| span.start)
                        .unwrap_or(usize::MAX),
                    event.0,
                )
            });
            for event in events {
                let node = &flow.nodes[event.0];
                let (FlowAction::Write { value, .. } | FlowAction::Evaluate(value)) = node.action
                else {
                    unreachable!()
                };
                let NodeKind::Form { children, .. } = &body.nodes[value.0].kind else {
                    continue;
                };
                let targets = origins.value_before(body, flow, event, children[1]);
                if let Some(loan) = held.iter().find(|loan| {
                    targets.iter().any(|target| {
                        !target.lifetime_only
                            && target.storage.is_empty()
                            && call_referents_overlap(loan, target)
                    })
                }) {
                    return Err(BorrowConflict {
                        message: "cannot write through a reference while an earlier call argument retains its loan".into(),
                        span: node.span,
                        labels: loan.span.map(|span| (span, "earlier argument retains this reference".into())).into_iter().collect(),
                    });
                }
            }
        }
        held.extend(
            origins
                .value_before(body, flow, call, *argument)
                .into_iter()
                .filter(|loan| !loan.lifetime_only && loan.storage.is_empty()),
        );
    }
    Ok(())
}

/// Enforce return-reference lifetimes from checked places and loan origins.
/// Incoming referents have Parameter roots and globals have Global roots. Local
/// roots always name this function's storage, including by-value parameter
/// slots: their addresses cannot outlive the body. Loading a reference stored in
/// a parameter must preserve its incoming referent, not the slot's address.
#[cfg(test)]
pub(crate) fn check_return_escapes(body: &Body, flow: &FlowGraph) -> Result<(), BorrowConflict> {
    check_return_escapes_cached(body, flow, &OnceCell::new())
}

pub(crate) fn check_return_escapes_cached(
    body: &Body,
    flow: &FlowGraph,
    cache: &OnceCell<FlowLoanOrigins>,
) -> Result<(), BorrowConflict> {
    let origins = cache.get_or_init(|| flow.loan_origins(body));
    for (index, node) in flow.nodes.iter().enumerate() {
        let FlowAction::Return(Some(value)) = &node.action else {
            continue;
        };
        for origin in origins.value_before(body, flow, FlowNodeId(index), *value) {
            let PlaceRoot::Local(binding) = origin.place.root else {
                continue;
            };
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
#[cfg(test)]
pub(crate) fn check_scope_escapes(body: &Body, flow: &FlowGraph) -> Result<(), BorrowConflict> {
    check_scope_escapes_cached(body, flow, &OnceCell::new())
}

pub(crate) fn check_scope_escapes_cached(
    body: &Body,
    flow: &FlowGraph,
    cache: &OnceCell<FlowLoanOrigins>,
) -> Result<(), BorrowConflict> {
    let origins = cache.get_or_init(|| flow.loan_origins(body));
    let active = flow.definitely_active_bindings_before(body);
    for (index, node) in flow.nodes.iter().enumerate() {
        let Some(active) = active[index].as_ref() else {
            continue;
        };
        let store = match node.action {
            FlowAction::Write { value, .. } | FlowAction::Evaluate(value) => {
                match &body.nodes[value.0].kind {
                    NodeKind::Form { head, children, .. }
                        if matches!(head.as_str(), "deref-set" | "pin-write")
                            && children.len() == 3 =>
                    {
                        Some((children[1], children[2]))
                    }
                    NodeKind::Form { head, children, .. }
                        if head == "pin-set-field" && children.len() == 4 =>
                    {
                        Some((children[1], children[3]))
                    }
                    NodeKind::Form { head, children, .. }
                        if head == "word-write" && children.len() == 4 =>
                    {
                        Some((children[2], children[3]))
                    }
                    _ => None,
                }
            }
            _ => None,
        };
        if let Some((target, value)) = store {
            let event = FlowNodeId(index);
            let targets = origins
                .value_before(body, flow, event, target)
                .into_iter()
                .filter(|origin| !origin.lifetime_only && origin.storage.is_empty())
                .collect::<Vec<_>>();
            let local_storage = !targets.is_empty()
                && targets.iter().all(|origin| match origin.place.root {
                    PlaceRoot::Local(binding) => active.contains(&binding),
                    PlaceRoot::Allocation(..) => active.iter().any(|binding| {
                        origins.before(event, *binding).iter().any(|held| {
                            held.owned_allocation && held.place.root == origin.place.root
                        })
                    }),
                    _ => false,
                });
            for origin in origins.value_before(body, flow, event, value) {
                let PlaceRoot::Local(binding) = origin.place.root else {
                    continue;
                };
                if active.contains(&binding) && local_storage {
                    continue;
                }
                let name = &body.bindings[binding.0].name;
                let message = if !active.contains(&binding) {
                    format!("reference to block-local variable '{name}' escapes its scope")
                } else {
                    format!(
                        "cannot store a reference to local variable '{name}' in non-local storage"
                    )
                };
                return Err(BorrowConflict {
                    message,
                    span: body.nodes[value.0].span.or(node.span).or(origin.span),
                    labels: origin
                        .span
                        .into_iter()
                        .map(|span| (span, "reference originates here".into()))
                        .collect(),
                });
            }
        }
        if let FlowAction::ScopeExit(exiting) = &node.action {
            if exiting.is_empty() {
                continue;
            }
            let event = FlowNodeId(index);
            // Stable binding order keeps the chosen diagnostic deterministic
            // when several outer holders retain references to dying locals.
            for holder in (0..body.bindings.len())
                .map(BindingId)
                .filter(|holder| active.contains(holder))
            {
                if exiting.contains(&holder) {
                    continue;
                }
                for origin in origins.before(event, holder) {
                    let PlaceRoot::Local(binding) = origin.place.root else {
                        continue;
                    };
                    if !exiting.contains(&binding) {
                        continue;
                    }
                    return Err(BorrowConflict {
                        message: format!(
                            "reference to block-local variable '{}' escapes its scope",
                            body.bindings[binding.0].name
                        ),
                        span: node.span.or(origin.span).or(body.bindings[binding.0].span),
                        labels: origin
                            .span
                            .into_iter()
                            .map(|span| (span, "reference originates here".into()))
                            .collect(),
                    });
                }
            }
        }
        let value = match node.action {
            FlowAction::Bind { value, .. } | FlowAction::Pattern { value, .. } => value,
            _ => continue,
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

#[derive(Clone, Default)]
struct BoundBorrows {
    bindings: HashMap<BindingId, Vec<Vec<DirectBorrow>>>,
    values: std::sync::Arc<HashMap<NodeId, Vec<Vec<DirectBorrow>>>>,
}

impl BoundBorrows {
    fn new() -> Self {
        Self::default()
    }

    fn get(&self, binding: &BindingId) -> Option<&Vec<Vec<DirectBorrow>>> {
        self.bindings.get(binding)
    }

    fn insert(&mut self, binding: BindingId, alternatives: Vec<Vec<DirectBorrow>>) {
        self.bindings.insert(binding, alternatives);
    }

    fn remove(&mut self, binding: &BindingId) {
        self.bindings.remove(binding);
    }
}

fn origin_alternatives(
    held: &[LoanOrigin],
    span: Option<Span>,
) -> Result<Option<Vec<Vec<DirectBorrow>>>, BorrowConflict> {
    if held.iter().any(|origin| origin.owned_allocation) {
        let borrowed = held
            .iter()
            .filter(|origin| !origin.owned_allocation)
            .cloned()
            .collect::<Vec<_>>();
        return origin_alternatives(&borrowed, span);
    }
    if held.is_empty() {
        return Ok(None);
    }
    if held.iter().all(|origin| origin.storage.is_empty()) {
        let alternatives = held
            .iter()
            .map(|origin| {
                vec![DirectBorrow {
                    place: origin.referent_place(),
                    mutable: origin.mutable,
                    span: origin.span,
                    storage: Vec::new(),
                }]
            })
            .collect();
        return bounded(alternatives, span).map(Some);
    }
    use crate::typed_place::Segment;
    // A discriminant belongs to a stored enum instance, not its type. Reusing
    // one enum type in sibling slots does not correlate those slots' tags.
    let mut variants =
        BTreeMap::<(Vec<Segment>, crate::typed_ir::AggregateId), BTreeSet<usize>>::new();
    for origin in held {
        for (depth, segment) in origin.storage.iter().enumerate() {
            if let Segment::Payload(variant, _) = segment {
                variants
                    .entry((origin.storage[..depth].to_vec(), variant.owner))
                    .or_default()
                    .insert(variant.index);
            }
        }
    }
    let split_variants = variants
        .into_iter()
        .filter(|(_, indices)| indices.len() > 1)
        .collect::<Vec<_>>();
    let mut assignments =
        vec![HashMap::<(Vec<Segment>, crate::typed_ir::AggregateId), usize>::new()];
    for (owner, indices) in split_variants {
        if assignments.len() > MAX_BORROW_ALTERNATIVES / indices.len() {
            return Err(complexity_error(span));
        }
        let mut expanded = Vec::new();
        for assignment in &assignments {
            for index in &indices {
                let mut next = assignment.clone();
                next.insert(owner.clone(), *index);
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
                    origin
                        .storage
                        .iter()
                        .enumerate()
                        .all(|(depth, segment)| match segment {
                            Segment::Payload(variant, _) => assignment
                                .get(&(origin.storage[..depth].to_vec(), variant.owner))
                                .is_none_or(|index| *index == variant.index),
                            _ => true,
                        })
                })
                .map(|origin| DirectBorrow {
                    place: origin.referent_place(),
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
            .values
            .get(&id)
            .or_else(|| bindings.get(binding))
            .cloned()
            .unwrap_or_else(|| vec![Vec::new()])),
        NodeKind::Form { head, children, .. }
            if matches!(
                head.as_str(),
                "get"
                    | "get-payload"
                    | "pin-get-payload"
                    | "pin-get-payload-mut"
                    | "pin-get-payload-unchecked"
                    | "pin-get-payload-unchecked-mut"
                    | "index"
                    | "index-proven"
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
        NodeKind::Form { head, children, .. } if head == "word-view" && children.len() == 3 => {
            let mut alternatives =
                returned_borrows_with_bindings(body, children[2], callee, bindings)?;
            let mutable = matches!(
                node.ty,
                Some(
                    Type::Reference { mutable: true, .. }
                        | Type::PinnedReference { mutable: true, .. }
                        | Type::MutableSlice(_)
                )
            );
            for alternative in &mut alternatives {
                for borrow in alternative {
                    borrow.mutable = mutable;
                }
            }
            Ok(alternatives)
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

fn loop_result_values(
    body: &Body,
    instructions: &[crate::typed_body::Instruction],
    label: Option<&str>,
) -> Vec<NodeId> {
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
                Control::Destructure {
                    value, otherwise, ..
                } => {
                    expression_breaks(body, *value, label, nested_loops, values);
                    if let Some(otherwise) = otherwise {
                        instruction_breaks(body, otherwise, label, nested_loops, values);
                    }
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
    values
}

fn returned_loop_borrows(
    body: &Body,
    instructions: &[crate::typed_body::Instruction],
    label: Option<&str>,
    callee: &str,
    bindings: &BoundBorrows,
    span: Option<Span>,
) -> Result<Vec<Vec<DirectBorrow>>, BorrowConflict> {
    let mut alternatives = Vec::new();
    for value in loop_result_values(body, instructions, label) {
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
                        message: if let Some(constructor) = callee.strip_prefix('#') {
                            format!("constructor '{constructor}' contains overlapping borrows; at most one may be mutable")
                        } else {
                            format!("call to '{callee}' passes overlapping borrows; at most one may be mutable")
                        },
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
        "borrow" | "borrow-mut" | "pin" | "pin-shared" | "pin-borrow" | "pin-borrow-mut"
    ) || children.len() != 2
    {
        return None;
    }
    Some(DirectBorrow {
        place: Place::from_expression(body, children[1])?,
        mutable: matches!(head.as_str(), "pin" | "borrow-mut" | "pin-borrow-mut"),
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
        || matches!(
            (wanted, held),
            (
                Segment::DynamicIndex | Segment::SliceDynamicIndex,
                Segment::SliceRange { .. } | Segment::SliceRangeUnknown
            ) | (
                Segment::SliceRange { .. } | Segment::SliceRangeUnknown,
                Segment::DynamicIndex | Segment::SliceDynamicIndex
            ) | (
                Segment::Index(_) | Segment::SliceIndex(_),
                Segment::SliceRange { .. } | Segment::SliceRangeUnknown
            ) | (
                Segment::SliceRange { .. } | Segment::SliceRangeUnknown,
                Segment::Index(_) | Segment::SliceIndex(_)
            )
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
            "(#fn inspect ((left (#ref-mut #u64)) (right (#ref #u64))) #u64
               (#forget left) (#forget right) (#return 0u64))
             (#fn main () #u64
               (#let-mut value #u64 1u64)
               (#return (#call inspect ( {args}))))"
        )
    }

    #[test]
    fn borrow_checks_share_one_function_local_provenance_result() {
        let program = crate::parse_program(
            "(#fn read ((input (#ref #u64))) #u64 (#return (#deref input)))
             (#fn main () #u64
               (#let owner #u64 42u64)
               (#return (#call read (: input (#borrow owner)))))",
        )
        .unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let flow = &checked.declarations().flows["main"];
        let cache = std::cell::OnceCell::new();
        assert!(cache.get().is_none());
        super::check_scope_escapes_cached(body, flow, &cache).unwrap();
        let first = cache.get().unwrap() as *const _;
        super::check_return_escapes_cached(body, flow, &cache).unwrap();
        super::check_live_direct_loans_cached(
            body,
            flow,
            &crate::linearcheck::LinearTypes::from_program(&program),
            &cache,
        )
        .unwrap();
        super::check_call_arguments_cached(body, flow, &cache).unwrap();
        assert_eq!(first, cache.get().unwrap() as *const _);
        check_scope_escapes(body, flow).unwrap();
        super::check_return_escapes(body, flow).unwrap();
        check_live_direct_loans(body, flow).unwrap();
        check_call_arguments(body, flow).unwrap();
    }

    #[test]
    fn symbolic_pointer_boundaries_preserve_aliasing_within_the_same_input_slot() {
        use crate::typed_place::Segment;
        let origin = |root, slot, projection| LoanOrigin {
            owned_allocation: false,
            place: Place {
                root,
                segments: projection,
            },
            mutable: true,
            pinned: false,
            lifetime_only: false,
            maybe_absent: false,
            word_stored: false,
            word_view_address: false,
            span: None,
            borrowed_from: None,
            reborrow_slot: None,
            call_reborrow: false,
            entry_loan: None,
            storage: Vec::new(),
            parameter_storage: Some(slot),
            storage_inputs: Vec::new(),
        };
        let parameter = PlaceRoot::Parameter(BindingId(0));
        let outer = origin(parameter.clone(), vec![], vec![]);
        let first = origin(
            parameter.clone(),
            vec![Segment::Index(0)],
            vec![Segment::Tuple(0)],
        );
        assert!(!super::call_referents_overlap(&outer, &first));
        assert!(super::call_referents_overlap(&first, &first));
        let disjoint_leaf = origin(
            parameter.clone(),
            vec![Segment::Index(0)],
            vec![Segment::Tuple(1)],
        );
        assert!(!super::call_referents_overlap(&first, &disjoint_leaf));
        let distinct_input = origin(
            parameter.clone(),
            vec![Segment::Index(1)],
            vec![Segment::Tuple(0)],
        );
        assert!(!super::call_referents_overlap(&first, &distinct_input));
        let selected_input = origin(
            parameter,
            vec![Segment::DynamicIndex],
            vec![Segment::Tuple(0)],
        );
        assert!(super::call_referents_overlap(&first, &selected_input));
        // At the caller, slot identities are substituted with real places.
        // Different symbolic slots never excuse aliasing of actual storage.
        let actual = PlaceRoot::Local(BindingId(0));
        let left = origin(
            actual.clone(),
            vec![Segment::Index(0)],
            vec![Segment::Tuple(0)],
        );
        let right = origin(actual, vec![Segment::Index(1)], vec![Segment::Tuple(0)]);
        assert!(super::call_referents_overlap(&left, &right));
    }

    #[test]
    fn stored_input_reference_is_not_storage_inside_its_container() {
        for (handle, borrow) in [
            ("#ref-mut", "#borrow-mut"),
            ("#pin-ref-mut", "#pin-borrow-mut"),
        ] {
            let source = format!(
                "(#struct Source () (: amount #u64))
              (#struct Holder () (: view (#ref Source)))
              (#fn project (: input (#ref Source)) (#ref #u64)
                (#return (#borrow (#get input amount))))
              (#fn read (: holder ({handle} Holder)) #u64
                (#let selected (#ref #u64) (#call project (: input (#get holder view))))
                (#return (#deref selected)))
              (#fn main () #u64
                (#let-mut owner Source (#struct-literal Source (: amount 42u64)))
                (#let-mut holder Holder (#struct-literal Holder (: view (#borrow owner))))
                (#let answer #u64 (#call read (: holder ({borrow} holder))))
                (#forget holder) (#forget owner) (#return answer))"
            );
            let program = crate::parse_program(&source).unwrap();
            crate::CheckedProgram::validate(&program)
                .unwrap_or_else(|error| panic!("{error}\n{source}"));

            let bad = source
                .replace("(#let answer", "(#forget owner) (#let answer")
                .replace("(#forget holder) (#forget owner)", "(#forget holder)");
            let program = crate::parse_program(&bad).unwrap();
            let error = crate::CheckedProgram::validate_with_span(&program)
                .err()
                .unwrap();
            assert_eq!(error.1, crate::DiagnosticCode::Borrow, "{}", error.0);
            let span = error.2.unwrap();
            assert_eq!(&bad[span.start..span.end], "#forget");
        }
    }

    #[test]
    fn input_slot_identity_does_not_hide_physical_reborrow_conflicts() {
        for (handle, shared, exclusive) in [
            ("#ref-mut", "#ref", "#ref-mut"),
            ("#pin-ref-mut", "#pin-ref", "#pin-ref-mut"),
        ] {
            let source = format!(
                "(#struct Source () (: amount #u64 : other #u64))
              (#fn read (: input ({handle} Source)) #u64
                (#let selected ({shared} #u64) (#borrow (#get input amount)))
                (#let conflicting ({exclusive} #u64) (#borrow-mut (#get input amount)))
                (#return (#deref selected)))"
            );
            let program = crate::parse_program(&source).unwrap();
            let error = crate::CheckedProgram::validate_with_span(&program)
                .err()
                .unwrap();
            assert_eq!(error.1, crate::DiagnosticCode::Borrow, "{}", error.0);
            let span = error.2.unwrap();
            assert_eq!(&source[span.start..span.end], "#borrow-mut");
            let disjoint = source.replace(
                "(#borrow-mut (#get input amount))",
                "(#borrow-mut (#get input other))",
            );
            let program = crate::parse_program(&disjoint).unwrap();
            crate::CheckedProgram::validate(&program)
                .unwrap_or_else(|error| panic!("{error}\n{disjoint}"));
        }
    }

    #[test]
    fn loaded_reference_origins_distinguish_incoming_referents_from_parameter_slots() {
        for (operator, handle) in [("#borrow", "#ref"), ("#pin-borrow", "#pin-ref")] {
            for external in [true, false] {
                let (parameter, initializer) = if external {
                    ("(outside (#ref #u64))", "outside")
                } else {
                    ("(seed #u64)", "(#borrow seed)")
                };
                let source = format!(
                    "(#struct Holder () ((view (#ref #u64))))
                     (#fn read ({parameter}) (#ref #u64)
                       (#let owner Holder (#struct-literal Holder (: view {initializer})))
                       (#let view ({handle} (#ref #u64)) ({operator} (#get owner view)))
                       (#return (#deref view)))"
                );
                let program = crate::parse_program(&source).unwrap();
                let declarations =
                    crate::typecheck::resolve_program_for_analysis(&program, false).unwrap();
                let body = &declarations.bodies["read"];
                let flow = &declarations.flows["read"];
                let origins = flow.loan_origins(body);
                let (event, value) = flow
                    .nodes
                    .iter()
                    .enumerate()
                    .find_map(|(index, node)| match node.action {
                        FlowAction::Return(Some(value)) => Some((FlowNodeId(index), value)),
                        _ => None,
                    })
                    .unwrap();
                let returned = origins.value_before(body, flow, event, value);
                let expected = if external {
                    PlaceRoot::Parameter(BindingId(0))
                } else {
                    PlaceRoot::Local(BindingId(0))
                };
                assert!(
                    !returned.is_empty(),
                    "missing loaded reference origin: {source}"
                );
                assert!(
                    returned.iter().all(|origin| origin.place.root == expected),
                    "{returned:?}\n{source}"
                );
                let result = super::check_return_escapes(body, flow);
                assert_eq!(result.is_ok(), external, "{result:?}\n{source}");
                if let Err(error) = result {
                    let span = error.span.unwrap();
                    assert_eq!(&source[span.start..span.end], "(#return (#deref view))");
                    assert!(error.message.contains("local 'seed'"), "{error:?}");
                }
            }
        }
    }

    #[test]
    fn earlier_reference_argument_blocks_writes_in_later_operands() {
        let source = "(#struct Holder () (: value (#ref-mut #u64) : other (#ref-mut #u64)))
          (#fn read (: view (#ref-mut #u64) : amount #u64) #u64
            (#return (#u64::add-wrap (#deref view) amount)))
          (#fn work (: held Holder) #u64
            (#let answer #u64 (#call read
              (: view (#get held value)
               : amount (#block (#deref-set (#get held value) 99u64) 2u64))))
            (#forget held) (#return answer))";
        let error =
            crate::CheckedProgram::validate_with_span(&crate::parse_program(source).unwrap())
                .err()
                .unwrap();
        assert_eq!(error.1, crate::DiagnosticCode::Borrow, "{}", error.0);
        let span = error.2.unwrap();
        assert!(source[span.start..span.end].contains("#deref-set"));
        for expression in [
            "(#block (#deref-set (#get held other) 99u64) 2u64)",
            "(#block (#unreachable) (#deref-set (#get held value) 99u64) 2u64)",
        ] {
            let valid = source.replace(
                "(#block (#deref-set (#get held value) 99u64) 2u64)",
                expression,
            );
            crate::CheckedProgram::validate(&crate::parse_program(&valid).unwrap())
                .unwrap_or_else(|error| panic!("{error}\n{valid}"));
        }
    }

    #[test]
    fn skipped_borrow_checks_do_not_solve_provenance() {
        let program = crate::parse_program("(#fn main () #u64 (#return 42u64))").unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let flow = &checked.declarations().flows["main"];
        let cache = std::cell::OnceCell::new();
        super::check_live_direct_loans_cached(
            body,
            flow,
            &crate::linearcheck::LinearTypes::from_program(&program),
            &cache,
        )
        .unwrap();
        super::check_call_arguments_cached(body, flow, &cache).unwrap();
        assert!(cache.get().is_none());
    }

    #[test]
    fn reused_scoped_sets_match_allocating_solver_on_cycles_and_joins() {
        use crate::typed_body::{BindingId, NodeId, PlaceRoot};
        use std::collections::HashSet;

        fn reference(flow: &FlowGraph, ids: &HashSet<NodeId>) -> Vec<HashSet<NodeId>> {
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
                        FlowAction::Borrow { value, .. } if ids.contains(&value) => {
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

        for count in [1, 2, 65, 130] {
            let mut nodes = Vec::new();
            for index in 0..count {
                nodes.push(FlowNode {
                    action: FlowAction::Borrow {
                        value: NodeId(index),
                        place: Place {
                            root: PlaceRoot::Local(BindingId(0)),
                            segments: vec![],
                        },
                        mutable: false,
                    },
                    successors: vec![FlowNodeId(index + 1)],
                    span: None,
                });
            }
            // One edge ends the first scope, the other retains it. A back
            // edge feeds their joined facts through the allocation swap.
            nodes[count - 1].successors.push(FlowNodeId(count + 1));
            nodes.push(FlowNode {
                action: FlowAction::BorrowScopeEnd { scope: NodeId(0) },
                successors: vec![FlowNodeId(count + 1)],
                span: None,
            });
            nodes.push(FlowNode {
                action: FlowAction::Exit,
                successors: vec![FlowNodeId(0)],
                span: None,
            });
            let flow = FlowGraph {
                variant_pruned_edges: Default::default(),
                nodes,
                entry: FlowNodeId(0),
                exit: FlowNodeId(count + 1),
            };
            let ids = (0..count).map(NodeId).collect();
            assert_eq!(
                super::scoped_borrows_before(&flow, &ids),
                reference(&flow, &ids)
            );
            // Lowering commonly puts successors before their predecessors.
            // Reverse node IDs to exercise that scheduling order as well.
            let mut reversed = flow.clone();
            reversed.nodes.reverse();
            let length = reversed.nodes.len();
            for node in &mut reversed.nodes {
                for successor in &mut node.successors {
                    successor.0 = length - successor.0 - 1;
                }
            }
            reversed.entry = FlowNodeId(reversed.nodes.len() - flow.entry.0 - 1);
            reversed.exit = FlowNodeId(reversed.nodes.len() - flow.exit.0 - 1);
            assert_eq!(
                super::scoped_borrows_before(&reversed, &ids),
                reference(&reversed, &ids)
            );
        }
    }

    #[test]
    fn absent_scoped_loans_have_empty_facts_at_every_event() {
        let program =
            crate::parse_program("(#fn main () #u64 (#let value #u64 1u64) (#return value))")
                .unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let flow = &checked.declarations().flows["main"];
        let facts = super::scoped_borrows_before(flow, &std::collections::HashSet::new());
        assert_eq!(facts.len(), flow.nodes.len());
        assert!(facts.iter().all(std::collections::HashSet::is_empty));
    }

    #[test]
    fn scope_escape_analysis_accepts_references_that_stay_with_their_owner() {
        let source = "(#fn main () #u64
          (#let result #u64
            (#block
              (#let owner #u64 41u64)
              (#let view (#ref #u64) (#borrow owner))
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
        let source = "(#fn read ((input (#ref #u64))) #u64 (#return (#deref input)))
          (#fn main () #u64
            (#let owner #u64 42u64)
            (#return (#call read (: input (#borrow owner)))))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let flow = &checked.declarations().flows["main"];
        check_call_arguments(body, flow).unwrap();
    }

    #[test]
    fn live_reference_conflict_uses_checked_places_and_origin_spans() {
        let source = "(#fn main () #u64
            (#let-mut left #u64 1u64)
            (#let-mut right #u64 2u64)
            (#let view (#ref-mut #u64) (#borrow-mut left))
            (#let other (#ref #u64) (#borrow right))
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
        let source = "(#struct Token (#linear) ((value #u64)))

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
        let source = "(#struct Token () ((value #u64)))
          (#struct RefBox () ((value (#ref Token))))
          (#opaque RefBox)
          (#enum Maybe () ((Maybe.Some RefBox) Maybe.None))
          (#fn wrap ((input (#ref Token))) Maybe
            (#return (Maybe.Some (#struct-literal RefBox ((value input))))))
          (#fn main () ()
            (#let-mut owner Token (#struct-literal Token ((value 1u64))))
            (#let option Maybe (#call wrap (: input (#borrow owner))))
            (#let result RefBox
              (#match option
                (#case (Maybe.Some box) box)
                (#case Maybe.None (#unreachable))))
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
        let source = "(#fn main () #u64
            (#let-mut value #u64 1u64)
            (#let parent (#ref #u64) (#borrow value))
            (#let observed #u64 (#deref parent))
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
    fn static_returned_loans_are_checked_without_local_borrow_events() {
        let source = "(#static vALUE #u64 1u64)
          (#fn obtain () (#ref #u64) (#return (#unsafe (#borrow vALUE))))
          (#fn inspect () #u64
            (#let view (#ref #u64) (#call obtain ()))
            (#forget view)
            (#let observed #u64 (#unsafe vALUE)) (#return observed))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["inspect"];
        let mut flow = FlowGraph::lower(body).unwrap();
        assert!(!flow
            .nodes
            .iter()
            .any(|node| matches!(node.action, FlowAction::Borrow { .. })));
        check_live_direct_loans(body, &flow).unwrap();
        let release = flow
            .nodes
            .iter()
            .position(|node| matches!(node.action, FlowAction::Release { .. }))
            .unwrap();
        let action = flow
            .nodes
            .iter()
            .find(|node| {
                matches!(&node.action,
            FlowAction::Read { place, .. } if matches!(place.root, PlaceRoot::Global(_)))
            })
            .unwrap()
            .action
            .clone();
        let FlowAction::Read { place, value, .. } = action else {
            unreachable!()
        };
        let action = FlowAction::Release { place, value };
        let read = FlowNodeId(flow.nodes.len());
        for node in &mut flow.nodes {
            for successor in &mut node.successors {
                if *successor == FlowNodeId(release) {
                    *successor = read;
                }
            }
        }
        flow.nodes.push(FlowNode {
            action,
            successors: vec![FlowNodeId(release)],
            span: None,
        });
        let error = check_live_direct_loans(body, &flow).unwrap_err();
        assert!(error.message.contains("borrow"), "{}", error.message);
    }

    #[test]
    fn parameter_loans_are_checked_without_local_borrow_events() {
        let source = "(#struct Point () ((x #u64) (y #u64)))
          (#fn field ((parent (#ref-mut Point))) (#ref #u64)
            (#return (#borrow (#get parent x))))
          (#fn inspect ((parent (#ref-mut Point))) ()
            (#let child (#ref #u64) (#call field (: parent parent)))
            (#forget child)
            (#deref-set parent (#struct-literal Point ((x 3u64) (y 4u64))))
            (#return ()))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["inspect"];
        let mut flow = FlowGraph::lower(body).unwrap();
        assert!(!flow
            .nodes
            .iter()
            .any(|node| matches!(node.action, FlowAction::Borrow { .. })));
        check_live_direct_loans(body, &flow).unwrap();
        let release = flow
            .nodes
            .iter()
            .position(|node| matches!(node.action, FlowAction::Release { .. }))
            .unwrap();
        let action = flow
            .nodes
            .iter()
            .find(|node| matches!(node.action, FlowAction::Write { .. }))
            .unwrap()
            .action
            .clone();
        let write = FlowNodeId(flow.nodes.len());
        for node in &mut flow.nodes {
            for successor in &mut node.successors {
                if *successor == FlowNodeId(release) {
                    *successor = write;
                }
            }
        }
        flow.nodes.push(FlowNode {
            action,
            successors: vec![FlowNodeId(release)],
            span: None,
        });
        let error = check_live_direct_loans(body, &flow).unwrap_err();
        assert!(error.message.contains("cannot mutate"), "{}", error.message);
    }

    #[test]
    fn reference_returning_call_writes_conflict_with_live_child_borrows() {
        let source = "(#struct Point () ((x #u64) (y #u64)))
            (#fn identity ((value (#ref-mut Point))) (#ref-mut Point)
              (#return value))
            (#fn main () #u64
              (#let-mut point Point (#struct-literal Point ((x 1u64) (y 2u64))))
              (#let parent (#ref-mut Point) (#borrow-mut point))
              (#let child (#ref #u64) (#borrow (#get parent x)))
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
        let source = "(#struct Point () ((x #u64) (y #u64)))
            (#fn main () #u64
              (#let-mut point Point (#struct-literal Point ((x 1u64) (y 2u64))))
              (#let parent (#ref-mut Point) (#borrow-mut point))
              (#let child (#ref #u64) (#borrow (#get parent x)))
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
        let source = "(#fn main () #u64
            (#let-mut values (#array #u64 4)
              (#array-of (#array #u64 4) 1u64 2u64 3u64 4u64))
            (#let view (#slice-mut #u64) (#slice-mut-of (#borrow-mut values)))
            (#let (#tuple left right) (#tuple (#slice-mut #u64) (#slice-mut #u64))
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
        let source = "(#fn main () #u64
            (#let-mut values (#array #u64 8)
              (#array-of (#array #u64 8) 1u64 2u64 3u64 4u64 5u64 6u64 7u64 8u64))
            (#let view (#slice-mut #u64) (#slice-mut-of (#borrow-mut values)))
            (#let (#tuple left right) (#tuple (#slice-mut #u64) (#slice-mut #u64))
              (#slice-mut-split view 4usize))
            (#let (#tuple first second) (#tuple (#slice-mut #u64) (#slice-mut #u64))
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
        let source = "(#fn main () #u64
            (#let-mut value #u64 1u64)
            (#return (#borrow value (#borrow-mut value 2u64))))";
        let program = crate::parse_program(source).unwrap();
        let error = crate::CheckedProgram::validate(&program).err().unwrap();
        assert!(error.contains("cannot borrow 'value' mutably while a live reference exists"));
    }

    #[test]
    fn typed_scoped_borrow_ends_before_following_accesses() {
        let source = "(#fn main () #u64
            (#let-mut value #u64 1u64)
            (#borrow value 2u64)
            (#borrow-mut value 3u64)
            (#return value))";
        let program = crate::parse_program(source).unwrap();
        crate::CheckedProgram::validate(&program).unwrap();
    }

    #[test]
    fn mutable_scoped_borrow_authorizes_access_within_its_region() {
        let source = "(#fn main () #u64
            (#let-mut value #u64 1u64)
            (#borrow-mut value (#block (#set value 2u64) value))
            (#return value))";
        let program = crate::parse_program(source).unwrap();
        crate::CheckedProgram::validate(&program).unwrap();
    }

    #[test]
    fn scoped_loan_remains_active_on_each_branch() {
        let source = "(#fn main () #u64
            (#let-mut value #u64 1u64)
            (#return (#borrow value
              (#if true (#borrow-mut value 2u64) 3u64))))";
        let program = crate::parse_program(source).unwrap();
        let error = crate::CheckedProgram::validate(&program).err().unwrap();
        assert!(error.contains("cannot borrow 'value' mutably while a live reference exists"));
    }

    #[test]
    fn scoped_loan_is_ended_at_a_branch_join() {
        let source = "(#fn main () #u64
            (#let-mut value #u64 1u64)
            (#if true (#borrow value 2u64) 3u64)
            (#borrow-mut value 4u64)
            (#return value))";
        let program = crate::parse_program(source).unwrap();
        crate::CheckedProgram::validate(&program).unwrap();
    }

    #[test]
    fn scoped_field_reborrow_conflicts_on_the_referent_projection() {
        let source = "(#struct Pair () ((left #u64) (right #u64)))
          (#fn main () #u64
            (#let-mut pair Pair (#struct-literal Pair ((left 1u64) (right 2u64))))
            (#let parent (#ref-mut Pair) (#borrow-mut pair))
            (#borrow-mut (#get parent left)
              (#block
                (#let view (#ref #u64) (#borrow (#get parent left)))
                3u64))
            (#return 0u64))";
        let program = crate::parse_program(source).unwrap();
        let error = crate::CheckedProgram::validate(&program).err().unwrap();
        assert!(error.contains("cannot borrow 'pair'"), "{error}");
    }

    #[test]
    fn scoped_field_reborrow_keeps_disjoint_siblings_available() {
        let source = "(#struct Pair () ((left #u64) (right #u64)))
          (#fn main () #u64
            (#let-mut pair Pair (#struct-literal Pair ((left 1u64) (right 2u64))))
            (#let parent (#ref-mut Pair) (#borrow-mut pair))
            (#borrow-mut (#get parent left)
              (#block
                (#let view (#ref #u64) (#borrow (#get parent right)))
                (#drop view)
                3u64))
            (#return 0u64))";
        let program = crate::parse_program(source).unwrap();
        crate::CheckedProgram::validate(&program).unwrap();
    }

    #[test]
    fn escaping_loop_exit_ends_the_scoped_loan() {
        let source = "(#fn main () #u64
            (#let-mut value #u64 1u64)
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
            (#let-mut value #u64 1u64)
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
        let source = "(#fn main () #u64
            (#let-mut value #u64 1u64)
            (#for-range (iteration #u64) 0u64 3u64
              (#borrow value 2u64))
            (#borrow-mut value 4u64)
            (#return value))";
        let program = crate::parse_program(source).unwrap();
        crate::CheckedProgram::validate(&program).unwrap();
    }

    #[test]
    fn projected_reborrow_suspends_parent_access_but_preserves_disjoint_fields() {
        let overlapping = "(#struct Inner () ((value #u64)))
          (#struct Outer () ((inner Inner) (other #u64)))
          (#fn main () #u64
            (#let-mut owner Outer (#struct-literal Outer
              ((inner (#struct-literal Inner ((value 7u64)))) (other 9u64))))
            (#let outer-ref (#ref-mut Outer) (#borrow-mut owner))
            (#let inner-ref (#ref-mut Inner) (#borrow-mut (#get outer-ref inner)))
            (#let observed #u64 (#get outer-ref other))
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

        let disjoint = "(#struct Outer () ((left #u64) (right #u64)))
          (#fn main () #u64
            (#let-mut owner Outer (#struct-literal Outer ((left 7u64) (right 9u64))))
            (#let outer-ref (#ref-mut Outer) (#borrow-mut owner))
            (#let left-ref (#ref-mut #u64) (#borrow-mut (#get outer-ref left)))
            (#let right #u64 (#get outer-ref right))
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
    fn reference_parameter_reborrows_distinguish_overlapping_and_disjoint_fields() {
        let prefix = "(#struct Pair () (: left #u64 : right #u64))\n";
        let overlapping = format!(
            "{prefix}(#fn bad (: target (#ref-mut Pair)) ()
              (#let left (#ref-mut #u64) (#borrow-mut (#get target left)))
              (#let child (#ref #u64) (#borrow (#get target left)))
              (#drop child) (#drop left) (#return ()))"
        );
        let error =
            match crate::CheckedProgram::validate(&crate::parse_program(&overlapping).unwrap()) {
                Ok(_) => panic!("a parameter's active exclusive field reborrow must block overlap"),
                Err(error) => error,
            };
        assert!(
            error.contains("already borrowed mutably") || error.contains("live reference exists"),
            "{error}"
        );

        let disjoint = format!(
            "{prefix}(#fn valid (: target (#ref-mut Pair)) ()
              (#let left (#ref-mut #u64) (#borrow-mut (#get target left)))
              (#let child (#ref #u64) (#borrow (#get target right)))
              (#drop child) (#drop left) (#return ()))"
        );
        crate::CheckedProgram::validate(&crate::parse_program(&disjoint).unwrap())
            .expect("disjoint parameter fields remain independently borrowable");
    }

    #[test]
    fn aggregate_held_loan_conflicts_with_checked_borrow_event() {
        let source = "(#struct Holder () ((view (#ref-mut #u64))))
          (#fn main () #u64
            (#let-mut left #u64 1u64)
            (#let-mut right #u64 2u64)
            (#let holder Holder
              (#struct-literal Holder ((view (#borrow-mut left)))))
            (#let other (#ref #u64) (#borrow right))
            (#let result #u64 (#deref (#get holder view)))
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
        let source = "(#struct Holder () ((view (#ref-mut #u64))))
          (#fn main () #u64
            (#let-mut left #u64 1u64)
            (#let-mut right #u64 2u64)
            (#let holder Holder
              (#struct-literal Holder ((view (#borrow-mut left)))))
            (#let other (#ref #u64) (#borrow right))
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
        let source = "(#fn main () #u64
            (#let-mut left #u64 1u64)
            (#let-mut right #u64 2u64)
            (#let view (#ref #u64) (#borrow left))
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
        let source = "(#fn main () #u64
            (#let left #u64 1u64)
            (#let right #u64 2u64)
            (#let view (#ref #u64) (#borrow left))
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
        let source = "(#fn main () #u64
            (#let-mut left #u64 1u64)
            (#let-mut right #u64 2u64)
            (#let view (#ref-mut #u64) (#borrow-mut left))
            (#let copy #u64 (#clone right))
            (#return (#u64::add-wrap (#deref view) copy)))";
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
        let source = "(#fn main () #u64
            (#let-mut left #u64 1u64)
            (#let-mut right #u64 2u64)
            (#let view (#ref-mut #u64) (#borrow-mut left))
            (#let value #u64 right)
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
        let source = "(#struct Pair () ((left #u64) (right #u64)))
          (#fn main () #u64
            (#let-mut pair Pair (#struct-literal Pair ((left 1u64) (right 2u64))))
            (#let pair-ref (#ref-mut Pair) (#borrow-mut pair))
            (#let view (#ref-mut #u64) (#borrow-mut (#get pair-ref left)))
            (#let right #u64 (#get pair-ref right))
            (#return (#u64::add-wrap (#deref view) right)))";
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
    fn caller_loop_preserves_initial_and_resumed_exclusive_aggregate_slots() {
        let source = "
          (#enum LeftSlot () ((LeftSlot.LeftEmpty) (LeftSlot.LeftFull (#ref-mut #u64))))
          (#enum RightSlot () ((RightSlot.RightEmpty) (RightSlot.RightFull (#ref-mut #u64))))
          (#struct Frame () (: left LeftSlot : right RightSlot))
          (#fn shift (: frame Frame) Frame
            (#let left LeftSlot (#get frame left))
            (#let right RightSlot (#get frame right))
            (#forget frame)
            (#return (#match left
              (#case (LeftSlot.LeftFull view) (#block (#forget right)
                (#struct-literal Frame (: left LeftSlot.LeftEmpty : right (RightSlot.RightFull view)))))
              (#case LeftSlot.LeftEmpty (#match right
                (#case (RightSlot.RightFull view)
                  (#struct-literal Frame (: left LeftSlot.LeftEmpty : right (RightSlot.RightFull view))))
                (#case RightSlot.RightEmpty
                  (#struct-literal Frame (: left LeftSlot.LeftEmpty : right RightSlot.RightEmpty))))))))
          (#fn run (: count #u64) #u64
            (#let-mut owner #u64 40u64)
            (#let-mut frame Frame (#struct-literal Frame
              (: left (LeftSlot.LeftFull (#borrow-mut owner)) : right RightSlot.RightEmpty)))
            (#for-range (turn #u64) 0u64 count
              (#let next Frame (#call shift (: frame frame)))
              (#set frame next))
            (#forget frame)
            (#set owner 42u64)
            (#return owner))
          (#fn main () #u64 (#return (#call run (: count 3u64))))";
        let program = crate::parse_program(source).unwrap();
        crate::CheckedProgram::validate(&program).unwrap_or_else(|error| panic!("{error}"));
        let invalid = source.replace(
            "(#forget frame)\n            (#set owner 42u64)",
            "(#set owner 99u64) (#forget frame)\n            (#set owner 42u64)",
        );
        assert_ne!(invalid, source);
        let program = crate::parse_program(&invalid).unwrap();
        let (message, code, span, _) = crate::CheckedProgram::validate_with_span(&program)
            .err()
            .expect("the looping frame still holds an exclusive external loan");
        assert_eq!(code, crate::DiagnosticCode::Borrow, "{message}");
        let span = span.unwrap();
        assert_eq!(&invalid[span.start..span.end], "#set", "{message}");
        assert_eq!(span.start, invalid.find("#set owner 99u64").unwrap());
    }

    #[test]
    fn two_shared_direct_borrows_are_allowed() {
        let source = "(#fn inspect ((left (#ref #u64)) (right (#ref #u64))) #u64
            (#return (#u64::add-wrap (#deref left) (#deref right))))
          (#fn main () #u64
            (#let value #u64 1u64)
            (#return (#call inspect (: left (#borrow value) : right (#borrow value)))))";
        let program = crate::parse_program(source).unwrap();
        crate::CheckedProgram::validate(&program).unwrap_or_else(|error| panic!("{error}"));
    }

    #[test]
    fn disjoint_struct_fields_can_be_borrowed_together() {
        let source = "(#struct Pair () ((left #u64) (right #u64)))
          (#fn inspect ((left (#ref-mut #u64)) (right (#ref #u64))) #u64
            (#forget left) (#forget right) (#return 0u64))
          (#fn main () #u64
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
        let source = "(#struct Holder () ((item (#ref #u64))))
          (#fn inspect ((holder Holder) (right (#ref-mut #u64))) #u64
            (#let (Holder item) Holder holder)
            (#drop item) (#drop right) (#return 0u64))
          (#fn main () #u64
            (#let-mut value #u64 1u64)
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
        let source = "(#struct Holder () ((item (#ref #u64))))
          (#fn inspect ((holder Holder) (right (#ref-mut #u64))) #u64
            (#forget holder) (#forget right) (#return 0u64))
          (#fn main () #u64
            (#let-mut value #u64 1u64)
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
        let source = "(#struct Holder () ((item (#ref #u64)) (other (#ref #u64))))
          (#fn inspect ((item (#ref #u64)) (right (#ref-mut #u64))) #u64
            (#forget item) (#forget right) (#return 0u64))
          (#fn main () #u64
            (#let-mut value #u64 1u64)
            (#let-mut other #u64 2u64)
            (#let holder Holder (#struct-literal Holder
              ((item (#borrow value)) (other (#borrow other)))))
            (#let result #u64 (#call inspect
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
                "(#struct Holder () ((item (#ref #u64)) (other (#ref #u64))))",
                "(#struct Holder () ((item (#ref #u64)) (other #u64)))",
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
            "(#array-of (#array (#ref #u64) 1) (#borrow value))",
            "(#array-repeat (#borrow value))",
        ] {
            let source = format!(
                "(#fn inspect ((values (#array (#ref #u64) 1)) (other (#ref-mut #u64))) #u64
                   (#forget values) (#forget other) (#return 0u64))
                 (#fn main () #u64
                   (#let-mut value #u64 1u64)
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
        let source = "(#fn inspect ((values (#array (#ref #u64) 0)) (other (#ref-mut #u64))) #u64
             (#forget values) (#forget other) (#return 0u64))
          (#fn main () #u64
             (#let-mut value #u64 1u64)
             (#return (#call inspect
               (: values (#array-repeat (#borrow value))
                : other (#borrow-mut value)))))";
        let program = crate::parse_program(source).unwrap();
        crate::CheckedProgram::validate(&program).unwrap();
    }

    #[test]
    fn conditional_alternatives_do_not_conflict_with_each_other() {
        let source = "(#fn inspect ((left (#ref-mut #u64)) (right (#ref #u64))) #u64
            (#forget left) (#forget right) (#return 0u64))
          (#fn main () #u64
            (#let-mut first #u64 1u64)
            (#let-mut second #u64 2u64)
            (#return (#call inspect (: left (#if true (#borrow-mut first) (#borrow-mut second)) : right (#borrow second)))))";
        let program = crate::parse_program(source).unwrap();
        let error = crate::CheckedProgram::validate(&program).err().unwrap();
        assert!(error.contains("overlapping borrows"), "{error}");

        let disjoint = source
            .replace(
                "(#let-mut second #u64 2u64)",
                "(#let-mut second #u64 2u64) (#let-mut third #u64 3u64)",
            )
            .replace(": right (#borrow second)", ": right (#borrow third)");
        let program = crate::parse_program(&disjoint).unwrap();
        crate::CheckedProgram::validate(&program).unwrap_or_else(|error| panic!("{error}"));
    }

    #[test]
    fn borrow_inside_tuple_argument_conflicts_with_another_argument() {
        let source = "(#fn inspect ((left (#tuple (#ref #u64))) (right (#ref-mut #u64))) #u64
            (#let (#tuple item) (#tuple (#ref #u64)) left)
            (#drop item) (#drop right) (#return 0u64))
          (#fn main () #u64
            (#let-mut value #u64 1u64)
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
                "(#let-mut value #u64 1u64)",
                "(#let-mut value #u64 1u64) (#let-mut other #u64 2u64)",
            )
            .replace(": right (#borrow-mut value)", ": right (#borrow-mut other)");
        let program = crate::parse_program(&disjoint).unwrap();
        crate::CheckedProgram::validate(&program).unwrap_or_else(|error| panic!("{error}"));
    }

    #[test]
    fn borrow_inside_array_argument_conflicts_with_another_argument() {
        let source = "(#fn inspect ((left (#array (#ref #u64) 1)) (right (#ref-mut #u64))) #u64
            (#let (#array item) (#array (#ref #u64) 1) left)
            (#drop item) (#drop right) (#return 0u64))
          (#fn main () #u64
            (#let-mut value #u64 1u64)
            (#return (#call inspect (: left (#array (#array (#ref #u64) 1) (#borrow value)) : right (#borrow-mut value)))))";
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
                "(#let-mut value #u64 1u64)",
                "(#let-mut value #u64 1u64) (#let-mut other #u64 2u64)",
            )
            .replace(": right (#borrow-mut value)", ": right (#borrow-mut other)");
        let program = crate::parse_program(&disjoint).unwrap();
        crate::CheckedProgram::validate(&program).unwrap_or_else(|error| panic!("{error}"));
    }

    #[test]
    fn borrow_inside_enum_argument_conflicts_with_another_argument() {
        let source = "(#enum Holder () ((Holder.Has (#ref #u64))))
          (#fn inspect ((left Holder) (right (#ref-mut #u64))) #u64
            (#let-else (Holder.Has item) Holder left (#return 0u64))
            (#drop item) (#drop right) (#return 0u64))
          (#fn main () #u64
            (#let-mut value #u64 1u64)
            (#return (#call inspect (: left (Holder.Has (#borrow value)) : right (#borrow-mut value)))))";
        let program = crate::parse_program(source).unwrap();
        let error = crate::CheckedProgram::validate(&program).err().unwrap();
        assert!(error.contains("overlapping borrows"), "{error}");
    }

    #[test]
    fn match_result_borrows_are_checked_per_arm() {
        let source = "(#fn inspect ((left (#ref #u64)) (right (#ref-mut #u64))) #u64
            (#drop left) (#drop right) (#return 0u64))
          (#fn main () #u64
            (#let-mut first #u64 1u64)
            (#let-mut second #u64 2u64)
            (#return (#call inspect (: left (#match true
                (#case true (#borrow first))
                (#case false (#borrow second))) : right (#borrow-mut first)))))";
        let program = crate::parse_program(source).unwrap();
        let error = crate::CheckedProgram::validate(&program).err().unwrap();
        assert!(error.contains("overlapping borrows"), "{error}");
    }

    #[test]
    fn immutable_block_binding_retains_borrow_origin() {
        let source = "(#fn inspect ((left (#ref #u64)) (right (#ref-mut #u64))) #u64
            (#drop left) (#drop right) (#return 0u64))
          (#fn main () #u64
            (#let-mut value #u64 1u64)
            (#return (#call inspect (: left (#block (#let view (#ref #u64) (#borrow value)) view) : right (#borrow-mut value)))))";
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
                "(#let-mut value #u64 1u64)",
                "(#let-mut value #u64 1u64) (#let-mut other #u64 2u64)",
            )
            .replace(": right (#borrow-mut value)", ": right (#borrow-mut other)");
        let program = crate::parse_program(&disjoint).unwrap();
        crate::CheckedProgram::validate(&program).unwrap_or_else(|error| panic!("{error}"));
    }

    #[test]
    fn destructured_block_reference_retains_aggregate_loan_origin() {
        let source = "(#fn inspect ((left (#ref #u64)) (right (#ref-mut #u64))) #u64
            (#drop left) (#drop right) (#return 0u64))
          (#fn main () #u64
            (#let-mut value #u64 1u64)
            (#return (#call inspect
              (: left (#block
                  (#let (#tuple view) (#tuple (#ref #u64))
                    (#tuple (#tuple (#ref #u64)) (#borrow value)))
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
        let source = "(#fn inspect ((left (#ref #u64)) (right (#ref-mut #u64))) #u64
            (#drop left) (#drop right) (#return 0u64))
          (#fn main () #u64
            (#let-mut first #u64 1u64)
            (#let-mut second #u64 2u64)
            (#let pair (#tuple (#ref #u64) (#ref-mut #u64))
              (#tuple (#tuple (#ref #u64) (#ref-mut #u64))
                (#borrow first) (#borrow-mut second)))
            (#let (#tuple left right)
              (#tuple (#ref #u64) (#ref-mut #u64))
              pair)
            (#return (#call inspect (: left left : right right))))";
        let program = crate::parse_program(source).unwrap();
        crate::CheckedProgram::validate(&program).unwrap_or_else(|error| panic!("{error}"));
    }

    #[test]
    fn array_destructuring_retains_element_loan_paths() {
        let source = "(#fn inspect ((left (#ref #u64)) (right (#ref-mut #u64))) #u64
            (#drop left) (#drop right) (#return 0u64))
          (#fn main () #u64
            (#let-mut first #u64 1u64)
            (#let-mut second #u64 2u64)
            (#let pair (#array (#ref #u64) 2)
              (#array (#array (#ref #u64) 2)
                (#borrow first) (#borrow second)))
            (#let (#array left right) (#array (#ref #u64) 2) pair)
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
        let source = "(#struct Pair () ((left (#ref #u64)) (right (#ref #u64))))
          (#fn inspect ((left (#ref #u64)) (right (#ref-mut #u64))) #u64
            (#drop left) (#drop right) (#return 0u64))
          (#fn main () #u64
            (#let-mut first #u64 1u64)
            (#let-mut second #u64 2u64)
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
        let source = "(#enum Holder () ((Holder.Held (#ref #u64)) (Holder.Empty)))
          (#fn inspect ((left (#ref #u64)) (right (#ref-mut #u64))) #u64
            (#drop left) (#drop right) (#return 0u64))
          (#fn main () #u64
            (#let-mut value #u64 1u64)
            (#let-mut other #u64 2u64)
            (#let holder Holder (Holder.Held (#borrow value)))
            (#let-else (Holder.Held left) Holder holder (#return 0u64))
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
        let source = "(#enum Holder () ((Holder.Held (#ref #u64)) (Holder.Empty)))
          (#fn inspect ((left (#ref #u64)) (right (#ref-mut #u64))) #u64
            (#drop left) (#drop right) (#return 0u64))
          (#fn main () #u64
            (#let-mut value #u64 1u64)
            (#let-mut other #u64 2u64)
            (#let holder Holder (Holder.Held (#borrow value)))
            (#return (#match holder
              (#case (Holder.Held left)
                (#call inspect (: left left : right (#borrow-mut value))))
              (#case Holder.Empty 0u64))))";
        let program = crate::parse_program(source).unwrap();
        let error = crate::CheckedProgram::validate(&program).err().unwrap();
        assert!(error.contains("overlapping borrows"), "{error}");

        let disjoint = source.replace(": right (#borrow-mut value)", ": right (#borrow-mut other)");
        let program = crate::parse_program(&disjoint).unwrap();
        crate::CheckedProgram::validate(&program).unwrap_or_else(|error| panic!("{error}"));
    }

    #[test]
    fn nested_struct_patterns_retain_full_loan_path() {
        let source = "(#struct Inner () ((item (#ref #u64))))
          (#struct Outer () ((inner Inner)))
          (#fn inspect ((left (#ref #u64)) (right (#ref-mut #u64))) #u64
            (#drop left) (#drop right) (#return 0u64))
          (#fn main () #u64
            (#let-mut value #u64 1u64)
            (#let-mut other #u64 2u64)
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
        let source = "(#fn inspect ((left (#ref #u64)) (right (#ref-mut #u64))) #u64
            (#drop left) (#drop right) (#return 0u64))
          (#fn main () #u64
            (#let-mut value #u64 1u64)
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
                "(#let-mut value #u64 1u64)",
                "(#let-mut value #u64 1u64) (#let-mut other #u64 2u64)",
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
        let source = "(#fn inspect ((left (#ref #u64)) (right (#ref-mut #u64))) #u64
            (#drop left) (#drop right) (#return 0u64))
          (#fn main () #u64
            (#let-mut value #u64 1u64)
            (#return (#call inspect (: left (#block
                (#let-mut view (#ref #u64) (#borrow value))
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
                "(#let-mut value #u64 1u64)",
                "(#let-mut value #u64 1u64) (#let-mut other #u64 2u64)",
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
        let source = "(#fn inspect ((left (#ref #u64)) (right (#ref-mut #u64))) #u64
            (#drop left) (#drop right) (#return 0u64))
          (#fn main () #u64
            (#let-mut value #u64 1u64)
            (#let view (#ref #u64) (#borrow value))
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
                "(#let-mut value #u64 1u64)",
                "(#let-mut value #u64 1u64) (#let-mut other #u64 2u64)",
            )
            .replace(": right (#borrow-mut value)", ": right (#borrow-mut other)");
        let program = crate::parse_program(&disjoint).unwrap();
        crate::CheckedProgram::validate(&program).unwrap_or_else(|error| panic!("{error}"));
    }

    #[test]
    fn reference_returning_call_preserves_argument_origin() {
        let source = "(#fn identity ((source (#ref #u64))) (#ref #u64)
            (#return source))
          (#fn inspect ((left (#ref #u64)) (right (#ref-mut #u64))) #u64
            (#drop left) (#drop right) (#return 0u64))
          (#fn main () #u64
            (#let-mut value #u64 1u64)
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
                owned_allocation: false,
                place: Place::root(PlaceRoot::Local(BindingId(0))),
                mutable: true,
                pinned: false,
                span: None,
                borrowed_from: None,
                reborrow_slot: None,
                call_reborrow: false,
                entry_loan: None,
                storage: Vec::new(),
                parameter_storage: None,
                storage_inputs: Vec::new(),
                lifetime_only: false,
                maybe_absent: false,
                word_stored: false,
                word_view_address: false,
            },
            LoanOrigin {
                owned_allocation: false,
                place: Place::root(PlaceRoot::Local(BindingId(1))),
                mutable: true,
                pinned: false,
                span: None,
                borrowed_from: None,
                reborrow_slot: None,
                call_reborrow: false,
                entry_loan: None,
                storage: Vec::new(),
                parameter_storage: None,
                storage_inputs: Vec::new(),
                lifetime_only: false,
                maybe_absent: false,
                word_stored: false,
                word_view_address: false,
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

        let source =
            "(#enum Choice () ((Choice.First (#ref-mut #u64)) (Choice.Second (#ref-mut #u64))))
            (#fn inspect ((choice Choice)) #u64
              (#return (#match choice
                (#case (Choice.First first) (#block (#drop first) 0u64))
                (#case (Choice.Second second) (#block (#drop second) 0u64)))))";
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
            owned_allocation: false,
            place: Place::root(PlaceRoot::Local(BindingId(0))),
            mutable: true,
            pinned: false,
            span: None,
            borrowed_from: None,
            reborrow_slot: None,
            call_reborrow: false,
            entry_loan: None,
            storage: vec![crate::typed_place::Segment::Payload(variant, field)],
            parameter_storage: None,
            storage_inputs: Vec::new(),
            lifetime_only: false,
            maybe_absent: false,
            word_stored: false,
            word_view_address: false,
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

        // Sibling instances of the same enum have independent tags. Same-tag
        // combinations are disjoint here, but opposite-tag combinations alias.
        let sibling = |position, tag, referent| {
            let mut origin = variant(tag, 0);
            origin
                .storage
                .insert(0, crate::typed_place::Segment::Tuple(position));
            origin.place = Place::root(PlaceRoot::Local(BindingId(referent)));
            origin
        };
        let independent = origin_alternatives(
            &[
                sibling(0, first, 0),
                sibling(0, second, 1),
                sibling(1, first, 1),
                sibling(1, second, 0),
            ],
            None,
        )
        .unwrap()
        .unwrap();
        assert_eq!(independent.len(), 4);
        assert!(combine(vec![Vec::new()], independent, "inspect", None).is_err());
        let separate_referents = origin_alternatives(
            &[
                sibling(0, first, 0),
                sibling(0, second, 1),
                sibling(1, first, 2),
                sibling(1, second, 3),
            ],
            None,
        )
        .unwrap()
        .unwrap();
        assert_eq!(separate_referents.len(), 4);
        assert!(combine(vec![Vec::new()], separate_referents, "inspect", None).is_ok());
        // A reference boundary is also part of instance identity. A directly
        // stored enum and one in its referent cannot share a discriminant.
        let mut indirect_first = variant(first, 0);
        indirect_first
            .storage
            .insert(0, crate::typed_place::Segment::Dereference);
        let mut indirect_second = variant(second, 0);
        indirect_second
            .storage
            .insert(0, crate::typed_place::Segment::Dereference);
        let distinct_boundaries = origin_alternatives(
            &[
                variant(first, 0),
                variant(second, 0),
                indirect_first,
                indirect_second,
            ],
            None,
        )
        .unwrap()
        .unwrap();
        assert_eq!(distinct_boundaries.len(), 4);
        let excessive = (0..11)
            .flat_map(|position| {
                [
                    sibling(position, first, position * 2),
                    sibling(position, second, position * 2 + 1),
                ]
            })
            .collect::<Vec<_>>();
        assert!(origin_alternatives(&excessive, None).is_err());

        let source = "(#fn inspect ((first (#ref-mut #u64)) (second (#ref #u64))) #u64
            (#drop first) (#drop second) (#return 0u64))
          (#fn main () #u64
            (#let-mut left #u64 1u64)
            (#let-mut right #u64 2u64)
            (#let flag #bool true)
            (#let view (#ref-mut #u64)
              (#if flag (#borrow-mut left) (#borrow-mut right)))
            (#let-mut third #u64 3u64)
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
                matches!(&node.kind, NodeKind::Form { callee: Some(id), .. }
                    if Some(*id) == checked.declarations().function_id("inspect"))
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
        let source = "(#struct Pair () ((left #u64) (right #u64)))
          (#fn main () #u64
            (#let-mut pair Pair (#struct-literal Pair ((left 1u64) (right 2u64))))
            (#let pair-ref (#ref-mut Pair) (#borrow-mut pair))
            (#let field-ref (#ref #u64) (#borrow (#get pair-ref left)))
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
        let source = "(#struct Inner () ((x #u64)))
          (#struct Outer () ((inner Inner)))
          (#fn main () #u64
            (#let-mut owner Outer (#struct-literal Outer
              ((inner (#struct-literal Inner ((x 3u64)))))))
            (#let outer-ref (#ref-mut Outer) (#borrow-mut owner))
            (#let inner-ref (#ref-mut Inner)
              (#borrow-mut (#get outer-ref inner)))
            (#let value-ref (#ref #u64) (#borrow (#get inner-ref x)))
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
