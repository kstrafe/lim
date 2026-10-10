//! Suspension storage facts from the existing checked ownership solution.
//!
//! Data reads, destruction, and address/lifetime retention are separate reasons
//! to retain storage. These are conservative facts, not permission to move a
//! self-referential frame or omit cancellation. The source suspension graph
//! still needs a checked-body mapping before general frame emission can use
//! these snapshots at original awaits.

use std::collections::{HashMap, HashSet};

use crate::linearcheck::LinearTypes;
use crate::typed_body::{BindingId, Body, NodeId, PlaceRoot};
use crate::typed_flow::{
    linear_obligation_place, place_covers, FlowAction, FlowConsumptions, FlowGraph, FlowLiveness,
    FlowLoanOrigins, FlowNodeId, LoanOrigin, StorageFacts,
};
use crate::typed_ir::{Declarations, VariantId};
use crate::typed_place::{Place, Segment};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Availability {
    Empty,
    Full,
    /// Branch-dependent, partly consumed, or an unknown enum alternative.
    /// This is not permission to load/store the entire value as initialized.
    Conditional,
}

#[derive(Debug)]
pub(crate) struct Obligation {
    pub place: Place,
    pub availability: Availability,
}

#[derive(Debug)]
pub(crate) struct Slot {
    pub binding: BindingId,
    pub data_needed: bool,
    pub address_needed: bool,
    pub lifetime_needed: bool,
    pub obligations: Vec<Obligation>,
    pub loans: Vec<LoanOrigin>,
}

impl Slot {
    pub(crate) fn cleanup_needed(&self) -> bool {
        self.obligations.iter().any(|obligation| {
            debug_assert_eq!(obligation.place.root, PlaceRoot::Local(self.binding));
            obligation.availability != Availability::Empty
        })
    }

    pub(crate) fn retain(&self) -> bool {
        self.data_needed
            || self.address_needed
            || self.lifetime_needed
            || self.cleanup_needed()
            || !self.loans.is_empty()
    }
}

#[derive(Debug)]
pub(crate) struct ValueSlot {
    /// An already-evaluated operand. It must not be reconstructed on resume.
    pub value: NodeId,
    #[cfg_attr(not(test), allow(dead_code))] // General frame emission consumes the checked type.
    pub ty: crate::Type,
    pub loans: Vec<LoanOrigin>,
}

#[derive(Debug)]
pub(crate) struct ScopedLoan {
    #[cfg_attr(not(test), allow(dead_code))]
    pub scope: NodeId,
    pub places: Vec<Place>,
    #[cfg_attr(not(test), allow(dead_code))]
    pub mutable: bool,
    pub handle: Place,
}

#[derive(Debug)]
pub(crate) struct Snapshot {
    pub slots: Vec<Slot>,
    #[cfg_attr(not(test), allow(dead_code))] // General frame emission consumes operand slots.
    pub values: Vec<ValueSlot>,
    #[cfg_attr(not(test), allow(dead_code))]
    pub scoped_loans: Vec<ScopedLoan>,
    /// Unresolved effects are never a proof that storage is initialized.
    pub unresolved_effects: bool,
}

/// Solve once per checked function, then query arbitrary suspension events.
/// The same loan retention and consumption solvers enforce ordinary borrowing.
pub(crate) struct Analysis<'a> {
    body: &'a Body,
    flow: &'a FlowGraph,
    origins: &'a FlowLoanOrigins,
    moves: &'a FlowConsumptions,
    live: FlowLiveness,
    unread: Vec<Vec<u64>>,
    active: Vec<Option<HashSet<BindingId>>>,
    definite_active: Vec<Option<HashSet<BindingId>>>,
    obligations: Vec<Vec<Place>>,
    unresolved_before: Vec<bool>,
    entry_only: bool,
    scoped_before: Vec<HashSet<NodeId>>,
    scoped_places: HashMap<NodeId, ScopedLoan>,
}

impl<'a> Analysis<'a> {
    pub(crate) fn new(
        body: &'a Body,
        facts: &'a StorageFacts,
        types: &LinearTypes,
        declarations: &Declarations,
    ) -> Self {
        let flow = &facts.flow;
        let origins = &facts.origins;
        let unread = crate::typed_borrow::unread_loan_bindings(body, flow, types, origins);
        let obligations = body
            .bindings
            .iter()
            .enumerate()
            .map(|(index, binding)| {
                types
                    .linear_obligation_paths(&binding.ty)
                    .iter()
                    .map(|path| {
                        linear_obligation_place(declarations, BindingId(index), &binding.ty, path)
                            .expect("checked linear obligation has a resolved place")
                    })
                    .collect()
            })
            .collect();
        let scopes = flow
            .nodes
            .iter()
            .filter_map(|node| match node.action {
                FlowAction::BorrowScopeEnd { scope } => Some(scope),
                _ => None,
            })
            .collect::<HashSet<_>>();
        let scoped_before = crate::typed_borrow::scoped_borrows_before(flow, &scopes);
        let scoped_places = flow
            .nodes
            .iter()
            .enumerate()
            .filter_map(|(index, node)| match &node.action {
                FlowAction::Borrow {
                    value,
                    place,
                    mutable,
                } if scopes.contains(value) => {
                    let projected = match place.root {
                        PlaceRoot::Local(binding) => {
                            origins.projected_referents(FlowNodeId(index), binding, &place.segments)
                        }
                        _ => Vec::new(),
                    };
                    Some((
                        *value,
                        ScopedLoan {
                            scope: *value,
                            places: if projected.is_empty() {
                                vec![place.clone()]
                            } else {
                                projected
                            },
                            mutable: *mutable,
                            handle: place.clone(),
                        },
                    ))
                }
                _ => None,
            })
            .collect();
        Self {
            body,
            flow,
            origins,
            unread,
            obligations,
            moves: &facts.moves,
            live: flow.liveness(body),
            active: flow.active_bindings_before(body),
            definite_active: flow.definitely_active_bindings_before(body),
            unresolved_before: facts.moves.unresolved_before(flow),
            entry_only: facts.entry_only,
            scoped_before,
            scoped_places,
        }
    }

    pub(crate) fn before(&self, event: FlowNodeId) -> Option<Snapshot> {
        self.before_with_values(event, &[])
    }

    /// `values` must be evaluated operands selected by the checked body's
    /// evaluation-order planner, not arbitrary source expressions or reads.
    pub(crate) fn before_with_values(
        &self,
        event: FlowNodeId,
        values: &[NodeId],
    ) -> Option<Snapshot> {
        if self.entry_only && event != self.flow.entry {
            return None;
        }
        let active = self.active.get(event.0)?.as_ref()?;
        let definite_active = self.definite_active[event.0].as_ref()?;
        let possible = self.moves.possible_regions_before(event)?;
        let definite = self.moves.definite_regions_before(event)?;
        let variants = self.origins.variants_before(self.body, self.flow, event);
        let unresolved_effects = self.unresolved_before[event.0] || self.moves.unresolved_at(event);
        let visible = crate::typed_borrow::visible_loan_bindings(
            &self.live,
            &self.unread,
            event,
            self.body.bindings.len(),
        )
        .into_iter()
        .collect::<HashSet<_>>();
        let data = self.live.before(event).into_iter().collect::<HashSet<_>>();
        let mut slots = Vec::new();
        // Dense binding order is stable; never let hash order affect frames.
        for index in 0..self.body.bindings.len() {
            let binding = BindingId(index);
            if !active.contains(&binding) {
                continue;
            }
            let availability = |place: &Place| {
                if unresolved_effects {
                    Availability::Conditional
                } else if inactive(place, variants)
                    || definite
                        .iter()
                        .any(|consumed| !dynamic(consumed) && place_covers(consumed, place))
                {
                    Availability::Empty
                } else if !definite_active.contains(&binding)
                    || has_unknown_variant(place, variants)
                    || possible.keys().any(|consumed| consumed.overlaps(place))
                {
                    Availability::Conditional
                } else {
                    Availability::Full
                }
            };
            let obligations = self.obligations[index]
                .iter()
                .map(|place| Obligation {
                    place: place.clone(),
                    availability: availability(place),
                })
                .collect();
            let loans = if visible.contains(&binding) {
                self.origins
                    .before(event, binding)
                    .iter()
                    .filter(|origin| {
                        let holder = Place {
                            root: PlaceRoot::Local(binding),
                            segments: origin.storage.clone(),
                        };
                        availability(&holder) != Availability::Empty
                    })
                    .cloned()
                    .collect()
            } else {
                Vec::new()
            };
            slots.push(Slot {
                binding,
                data_needed: data.contains(&binding),
                address_needed: false,
                lifetime_needed: false,
                obligations,
                loans,
            });
        }
        let mut captured = Vec::with_capacity(values.len());
        for &value in values {
            if captured.iter().any(|slot: &ValueSlot| slot.value == value) {
                continue;
            }
            captured.push(ValueSlot {
                value,
                ty: self.body.nodes.get(value.0)?.ty.clone()?,
                loans: self
                    .origins
                    .value_before(self.body, self.flow, event, value),
            });
        }
        let mut retain_owners = Vec::new();
        let mut scopes = self.scoped_before[event.0]
            .iter()
            .copied()
            .collect::<Vec<_>>();
        scopes.sort_by_key(|scope| scope.0);
        let scoped_loans = scopes
            .into_iter()
            .filter_map(|scope| self.scoped_places.get(&scope))
            .map(|loan| {
                for place in &loan.places {
                    if let PlaceRoot::Local(owner) = place.root {
                        retain_owners.push((owner, true));
                    }
                }
                if let PlaceRoot::Local(handle) = loan.handle.root {
                    retain_owners.push((handle, false));
                }
                ScopedLoan {
                    scope: loan.scope,
                    places: loan.places.clone(),
                    mutable: loan.mutable,
                    handle: loan.handle.clone(),
                }
            })
            .collect();
        for loans in slots
            .iter()
            .map(|slot| &slot.loans)
            .chain(captured.iter().map(|slot| &slot.loans))
        {
            for loan in loans {
                if let PlaceRoot::Local(owner) = loan.referent_place().root {
                    retain_owners.push((owner, !loan.lifetime_only));
                }
                // Handle dependencies are different from pointee provenance.
                // Call-duration reborrows do not retain temporary parent handles.
                if !loan.call_reborrow {
                    if let Some(parent) = loan.borrowed_from {
                        retain_owners.push((parent, false));
                    }
                }
            }
        }
        for (owner, address) in retain_owners {
            if let Some(slot) = slots.iter_mut().find(|slot| slot.binding == owner) {
                slot.address_needed |= address;
                slot.lifetime_needed = true;
            }
        }
        Some(Snapshot {
            slots,
            values: captured,
            scoped_loans,
            unresolved_effects,
        })
    }
}

fn dynamic(place: &Place) -> bool {
    place
        .segments
        .iter()
        .any(|segment| matches!(segment, Segment::DynamicIndex | Segment::SliceDynamicIndex))
}

fn inactive(place: &Place, variants: Option<&HashMap<Place, VariantId>>) -> bool {
    let Some(variants) = variants else {
        return false;
    };
    place.segments.iter().enumerate().any(|(index, segment)| {
        let Segment::Payload(wanted, _) = segment else {
            return false;
        };
        variants
            .get(&Place {
                root: place.root.clone(),
                segments: place.segments[..index].to_vec(),
            })
            .is_some_and(|actual| actual != wanted && actual.owner == wanted.owner)
    })
}

fn has_unknown_variant(place: &Place, variants: Option<&HashMap<Place, VariantId>>) -> bool {
    place.segments.iter().enumerate().any(|(index, segment)| {
        matches!(segment, Segment::Payload(_, _))
            && variants.is_none_or(|variants| {
                !variants.contains_key(&Place {
                    root: place.root.clone(),
                    segments: place.segments[..index].to_vec(),
                })
            })
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::typed_body::NodeKind;
    use crate::typed_flow::FlowAction;

    fn prepare(source: &str) -> (crate::Program, Declarations) {
        let program =
            crate::parse_program(&format!("(#fn checkpoint () () (#return ()))\n{source}"))
                .unwrap();
        // Invalid consumption is allowed here to inspect conservative states;
        // this type-only boundary cannot authorize emission of such a program.
        let declarations = crate::typecheck::resolve_program_for_analysis(&program, false).unwrap();
        (program, declarations)
    }

    fn checkpoint(body: &Body, flow: &FlowGraph, index: usize) -> FlowNodeId {
        let mut calls = flow
            .nodes
            .iter()
            .enumerate()
            .filter_map(|(index, node)| {
                let FlowAction::Evaluate(value) = node.action else {
                    return None;
                };
                let NodeKind::Form {
                    callee: Some(callee),
                    ..
                } = body.nodes[value.0].kind
                else {
                    return None;
                };
                (body.declaration_name(crate::typed_ir::DeclarationId::Function(callee))
                    == Some("checkpoint"))
                .then_some((node.span.unwrap().start, FlowNodeId(index)))
            })
            .collect::<Vec<_>>();
        calls.sort_by_key(|(start, _)| *start);
        calls[index].1
    }

    fn slot<'a>(body: &Body, snapshot: &'a Snapshot, name: &str) -> &'a Slot {
        snapshot
            .slots
            .iter()
            .find(|slot| body.bindings[slot.binding.0].name == name)
            .unwrap()
    }

    fn prepare_staged(source: &str) -> (crate::Program, Declarations, StorageFacts) {
        let (program, mut declarations) = prepare(source);
        let types = LinearTypes::from_program(&program);
        let mut facts = declarations
            .suspension_storage_facts(&types, &HashSet::from(["work".into()]))
            .unwrap();
        assert_eq!(
            facts.len(),
            1,
            "only requested bodies need storage snapshots"
        );
        (program, declarations, facts.remove("work").unwrap())
    }

    #[test]
    fn entry_only_facts_cannot_authorize_suspended_storage() {
        let (program, declarations) =
            prepare("(#fn work ((value #u64)) () (#call checkpoint (:)) (#return ()))");
        let body = &declarations.bodies["work"];
        let flow = &declarations.flows["work"];
        let types = LinearTypes::from_program(&program);
        let facts = StorageFacts::for_entry(body, flow, &types);
        let analysis = Analysis::new(body, &facts, &types, &declarations);
        assert!(analysis.before(flow.entry).is_some());
        assert!(analysis.before(checkpoint(body, flow, 0)).is_none());
    }

    #[test]
    fn scoped_borrow_retains_an_unread_copy_owners_address_until_scope_end() {
        let (program, declarations, facts) = prepare_staged(
            "(#fn work () ()
               (#let-mut owner #u64 1u64)
               (#borrow-mut owner (#block (#call checkpoint (:)) ()))
               (#call checkpoint (:)) (#return ()))",
        );
        crate::CheckedProgram::validate(&program).unwrap();
        let body = &declarations.bodies["work"];
        let types = LinearTypes::from_program(&program);
        let analysis = Analysis::new(body, &facts, &types, &declarations);
        let inside = analysis.before(checkpoint(body, &facts.flow, 0)).unwrap();
        let owner = slot(body, &inside, "owner");
        assert!(!owner.data_needed);
        assert!(!owner.cleanup_needed());
        assert!(owner.address_needed && owner.lifetime_needed && owner.retain());
        assert_eq!(inside.scoped_loans.len(), 1);
        assert!(inside.scoped_loans[0].mutable);
        assert_eq!(
            inside.scoped_loans[0].places[0].root,
            PlaceRoot::Local(owner.binding)
        );
        let outside = analysis.before(checkpoint(body, &facts.flow, 1)).unwrap();
        assert!(outside.scoped_loans.is_empty());
        assert!(!slot(body, &outside, "owner").retain());
    }

    #[test]
    fn scoped_reborrow_retains_the_referent_and_not_the_parent_handles_address() {
        let (program, declarations, facts) = prepare_staged(
            "(#struct Owner ((value #u64)))
             (#fn work () ()
               (#let-mut owner Owner (#struct-literal Owner (: value 1u64)))
               (#let view (#ref-mut Owner) (#borrow-mut owner))
               (#borrow (#get view value) (#block (#call checkpoint (:)) ()))
               (#drop view) (#call checkpoint (:)) (#return ()))",
        );
        crate::CheckedProgram::validate(&program).unwrap();
        let body = &declarations.bodies["work"];
        let types = LinearTypes::from_program(&program);
        let analysis = Analysis::new(body, &facts, &types, &declarations);
        let inside = analysis.before(checkpoint(body, &facts.flow, 0)).unwrap();
        let owner = slot(body, &inside, "owner");
        assert!(owner.address_needed && owner.lifetime_needed);
        let view = slot(body, &inside, "view");
        assert!(view.lifetime_needed);
        assert!(!view.address_needed);
        assert_eq!(inside.scoped_loans.len(), 1);
        assert!(!inside.scoped_loans[0].mutable);
        assert_eq!(
            inside.scoped_loans[0].places[0].root,
            PlaceRoot::Local(owner.binding)
        );
        assert_eq!(
            inside.scoped_loans[0].handle.root,
            PlaceRoot::Local(view.binding)
        );
        let outside = analysis.before(checkpoint(body, &facts.flow, 1)).unwrap();
        assert!(outside.scoped_loans.is_empty());
        assert!(!slot(body, &outside, "owner").retain());
    }

    #[test]
    fn callee_consumption_and_forwarded_initialization_change_cleanup() {
        let (program, declarations, facts) = prepare_staged(
            "(#struct Resource ((value #u64))) (#linear Resource)
             (#fn consume ((value (#ref-mut Resource))) ()
               (#forget (#deref value)) (#return ()))
             (#fn initialize ((value (#ref-mut Resource))) ()
               (#deref-set value (#struct-literal Resource (: value 42u64))) (#return ()))
             (#fn forward ((value (#ref-mut Resource))) ()
               (#call initialize (: value value)) (#return ()))
             (#fn work () ()
               (#let-mut owner Resource (#struct-literal Resource (: value 1u64)))
               (#let view (#ref-mut Resource) (#borrow-mut owner))
               (#call consume (: value view)) (#call checkpoint (:))
               (#call forward (: value view)) (#call checkpoint (:))
               (#drop view) (#forget owner) (#return ()))",
        );
        let body = &declarations.bodies["work"];
        let types = LinearTypes::from_program(&program);
        let analysis = Analysis::new(body, &facts, &types, &declarations);
        for (index, expected) in [(0, Availability::Empty), (1, Availability::Full)] {
            let snapshot = analysis
                .before(checkpoint(body, &facts.flow, index))
                .unwrap();
            assert!(!snapshot.unresolved_effects);
            assert_eq!(
                slot(body, &snapshot, "owner").obligations[0].availability,
                expected
            );
            assert_eq!(slot(body, &snapshot, "owner").cleanup_needed(), index == 1);
        }
        crate::CheckedProgram::validate(&program).unwrap();
    }

    #[test]
    fn callee_consumes_only_the_projected_linear_field() {
        let (program, declarations, facts) = prepare_staged(
            "(#struct Resource ((value #u64))) (#linear Resource)
             (#struct Pair (: left.part Resource : right Resource))
             (#fn consume ((value (#ref-mut Pair))) ()
               (#forget (#get value left.part)) (#return ()))
             (#fn work ((#mut owner Pair)) ()
               (#call consume (: value (#borrow-mut owner))) (#call checkpoint (:))
               (#return (#unreachable)))",
        );
        let body = &declarations.bodies["work"];
        let types = LinearTypes::from_program(&program);
        let analysis = Analysis::new(body, &facts, &types, &declarations);
        let snapshot = analysis.before(checkpoint(body, &facts.flow, 0)).unwrap();
        let owner = slot(body, &snapshot, "owner");
        assert_eq!(owner.obligations.len(), 2);
        assert_eq!(owner.obligations[0].availability, Availability::Empty);
        assert_eq!(owner.obligations[1].availability, Availability::Full);
        assert!(owner.cleanup_needed());
        // Divergence has no owned return obligation, but cancellation at the
        // earlier checkpoint must still consume the surviving right field.
        crate::CheckedProgram::validate(&program).unwrap();
    }

    #[test]
    fn consuming_one_of_two_aliases_cannot_prove_either_owner_empty() {
        let (program, declarations, facts) = prepare_staged(
            "(#struct Resource ((value #u64))) (#linear Resource)
             (#fn consume ((value (#ref-mut Resource))) ()
               (#forget (#deref value)) (#return ()))
             (#fn work ((choice #bool)) ()
               (#let-mut left Resource (#struct-literal Resource (: value 1u64)))
               (#let-mut right Resource (#struct-literal Resource (: value 2u64)))
               (#let selected (#ref-mut Resource)
                 (#if choice (#borrow-mut left) (#borrow-mut right)))
               (#call consume (: value selected)) (#drop selected)
               (#call checkpoint (:)) (#return (#unreachable)))",
        );
        let body = &declarations.bodies["work"];
        let types = LinearTypes::from_program(&program);
        let analysis = Analysis::new(body, &facts, &types, &declarations);
        let snapshot = analysis.before(checkpoint(body, &facts.flow, 0)).unwrap();
        assert!(!snapshot.unresolved_effects);
        for name in ["left", "right"] {
            assert_eq!(
                slot(body, &snapshot, name).obligations[0].availability,
                Availability::Conditional
            );
        }
        // The ordinary body traps rather than silently losing either owner.
        // A suspended/cancelled version still needs both conditional slots.
        crate::CheckedProgram::validate(&program).unwrap();
    }

    #[test]
    fn nonreturning_callee_has_no_following_suspension_snapshot() {
        let (program, declarations, facts) = prepare_staged(
            "(#struct Resource ((value #u64))) (#linear Resource)
             (#fn stop () () (#loop ()) (#return ()))
             (#fn work ((owner Resource)) ()
               (#call stop (:)) (#call checkpoint (:)) (#return ()))",
        );
        let body = &declarations.bodies["work"];
        let types = LinearTypes::from_program(&program);
        let analysis = Analysis::new(body, &facts, &types, &declarations);
        assert!(analysis.before(checkpoint(body, &facts.flow, 0)).is_none());
    }

    #[test]
    fn unresolved_effects_reach_later_events_and_cannot_prove_full_storage() {
        let (program, declarations) = prepare(
            "(#struct Resource ((value #u64))) (#linear Resource)
             (#fn work ((owner Resource)) ()
               (#call checkpoint (:)) (#call checkpoint (:)) (#return ()))",
        );
        let body = &declarations.bodies["work"];
        let flow = &declarations.flows["work"];
        let types = LinearTypes::from_program(&program);
        let mut facts = StorageFacts::local_for_test(body, flow, &types);
        let unknown = checkpoint(body, flow, 0);
        facts.moves =
            flow.referent_consumptions_with_calls(body, &types, &[(unknown, Vec::new(), true)]);
        let analysis = Analysis::new(body, &facts, &types, &declarations);
        assert!(!analysis.before(flow.entry).unwrap().unresolved_effects);
        let snapshot = analysis.before(checkpoint(body, flow, 1)).unwrap();
        assert!(snapshot.unresolved_effects);
        assert_eq!(
            slot(body, &snapshot, "owner").obligations[0].availability,
            Availability::Conditional
        );
    }

    #[test]
    fn opaque_reference_contract_does_not_produce_storage_proofs() {
        let (program, mut declarations) = prepare(
            "(#struct Resource ((value #u64))) (#linear Resource)
             (#extern-fn #abi-c opaque ((owner (#ref-mut Resource))) ())
             (#fn work ((owner (#ref-mut Resource))) ()
               (#unsafe (#call opaque (: owner owner)))
               (#call checkpoint (:)) (#return ()))",
        );
        let types = LinearTypes::from_program(&program);
        let error = declarations
            .suspension_storage_facts(&types, &HashSet::from(["work".into()]))
            .err()
            .expect("opaque checked reference effects must not become proofs");
        let crate::typed_ir::StagedReferentError::Use { function, conflict } = error else {
            panic!("unexpected error: {error:?}");
        };
        assert_eq!(function, "work");
        assert!(
            conflict.message.contains("unresolved call inputs"),
            "{conflict:?}"
        );
        assert!(conflict.span.is_some());
    }

    #[test]
    fn selected_initializer_outcome_refines_full_and_empty_slots() {
        let (program, declarations, facts) = prepare_staged(
            "(#struct Resource ((value #u64))) (#linear Resource)
             (#enum Outcome ((Ready) (Pending)))
             (#fn initialize ((value (#ref-mut Resource)) (complete #bool)) Outcome
               (#return (#if complete
                 (#block (#deref-set value (#struct-literal Resource (: value 42u64))) (Ready))
                 (Pending))))
             (#fn work ((complete #bool)) ()
               (#let-mut owner Resource (#struct-literal Resource (: value 1u64)))
               (#let view (#ref-mut Resource) (#borrow-mut owner))
               (#forget (#deref view))
               (#let outcome Outcome (#call initialize (: value view : complete complete)))
               (#let before-match #bool false)
               (#match outcome
                 (#case (Ready) (#block (#call checkpoint (:)) (#forget (#deref view))))
                 (#case (Pending) (#call checkpoint (:))))
               (#drop view) (#return (#unreachable)))",
        );
        let body = &declarations.bodies["work"];
        let types = LinearTypes::from_program(&program);
        let analysis = Analysis::new(body, &facts, &types, &declarations);
        for (index, expected) in [
            (0, Availability::Conditional),
            (1, Availability::Full),
            (2, Availability::Empty),
        ] {
            let event = if index == 0 {
                facts
                    .flow
                    .nodes
                    .iter()
                    .enumerate()
                    .find_map(|(index, node)| {
                        matches!(node.action, FlowAction::Bind { binding, .. }
                        if body.bindings[binding.0].name == "before-match")
                        .then_some(FlowNodeId(index))
                    })
                    .unwrap()
            } else {
                checkpoint(body, &facts.flow, index - 1)
            };
            let snapshot = analysis.before(event).unwrap();
            assert!(!snapshot.unresolved_effects);
            assert_eq!(
                slot(body, &snapshot, "owner").obligations[0].availability,
                expected
            );
        }
    }

    #[test]
    fn clearing_borrowed_contents_retires_their_address_dependency() {
        let (program, declarations, facts) = prepare_staged(
            "(#enum Choice ((Empty) (Full (#ref #u64))))
             (#fn clear ((target (#ref-mut Choice))) ()
               (#deref-set target (Empty)) (#return ()))
             (#fn work () ()
               (#let owner #u64 42u64)
               (#let-mut holder Choice (Full (#borrow owner)))
               (#let target (#ref-mut Choice) (#borrow-mut holder))
               (#call checkpoint (:)) (#call clear (: target target)) (#drop target)
               (#call checkpoint (:)) (#forget holder) (#return ()))",
        );
        let body = &declarations.bodies["work"];
        let types = LinearTypes::from_program(&program);
        let analysis = Analysis::new(body, &facts, &types, &declarations);
        let before = analysis.before(checkpoint(body, &facts.flow, 0)).unwrap();
        assert!(slot(body, &before, "owner").address_needed);
        let after = analysis.before(checkpoint(body, &facts.flow, 1)).unwrap();
        assert!(!slot(body, &after, "owner").retain());
        assert!(slot(body, &after, "holder").loans.is_empty());
        crate::CheckedProgram::validate(&program).unwrap();
    }

    #[test]
    fn unread_owners_need_cleanup_and_consumed_owners_do_not() {
        let (program, declarations) = prepare(
            "(#struct Resource ((value #u64))) (#linear Resource)
             (#fn work ((unread Resource) (consumed Resource)) ()
               (#forget consumed) (#call checkpoint (:)) (#return ()))",
        );
        let body = &declarations.bodies["work"];
        let flow = &declarations.flows["work"];
        let types = LinearTypes::from_program(&program);
        let facts = StorageFacts::local_for_test(body, flow, &types);
        let analysis = Analysis::new(body, &facts, &types, &declarations);
        let snapshot = analysis.before(checkpoint(body, flow, 0)).unwrap();
        let unread = slot(body, &snapshot, "unread");
        assert!(!unread.data_needed);
        assert!(unread.cleanup_needed());
        assert_eq!(unread.obligations[0].availability, Availability::Full);
        let consumed = slot(body, &snapshot, "consumed");
        assert!(!consumed.retain());
        assert_eq!(consumed.obligations[0].availability, Availability::Empty);
        assert!(crate::CheckedProgram::validate(&program)
            .err()
            .expect("unread linear owner must not disappear")
            .contains("unread"));
    }

    #[test]
    fn branch_consumption_is_conditional_and_restoration_is_full() {
        let (program, declarations) = prepare(
            "(#struct Resource ((value #u64))) (#linear Resource)
             (#fn work ((#mut owner Resource) (flag #bool)) ()
               (#if flag (#forget owner) ())
               (#call checkpoint (:))
               (#set owner (#struct-literal Resource (: value 1u64)))
               (#call checkpoint (:)) (#forget owner) (#return ()))",
        );
        let body = &declarations.bodies["work"];
        let flow = &declarations.flows["work"];
        let types = LinearTypes::from_program(&program);
        let facts = StorageFacts::local_for_test(body, flow, &types);
        let analysis = Analysis::new(body, &facts, &types, &declarations);
        for (index, expected) in [(0, Availability::Conditional), (1, Availability::Full)] {
            let snapshot = analysis.before(checkpoint(body, flow, index)).unwrap();
            assert_eq!(
                slot(body, &snapshot, "owner").obligations[0].availability,
                expected
            );
        }
        // The Full post-write snapshot is not permission to overwrite the
        // previous live value on the branch which did not consume it.
        let error = crate::CheckedProgram::validate_with_span(&program)
            .err()
            .expect("conditional consumption cannot justify replacement");
        assert_eq!(error.1, crate::DiagnosticCode::Linear);
        assert!(error.0.contains("owner"), "{error:?}");
    }

    #[test]
    fn fresh_unread_reference_retains_owner_address_until_release() {
        let (program, declarations) = prepare(
            "(#fn work () () (#let owner #u64 42u64)
               (#let view (#ref #u64) (#borrow owner))
               (#call checkpoint (:)) (#drop view)
               (#call checkpoint (:)) (#return ()))",
        );
        let body = &declarations.bodies["work"];
        let flow = &declarations.flows["work"];
        let types = LinearTypes::from_program(&program);
        let facts = StorageFacts::local_for_test(body, flow, &types);
        let analysis = Analysis::new(body, &facts, &types, &declarations);
        let first = analysis.before(checkpoint(body, flow, 0)).unwrap();
        assert_eq!(slot(body, &first, "view").loans.len(), 1);
        assert!(slot(body, &first, "owner").address_needed);
        let after = analysis.before(checkpoint(body, flow, 1)).unwrap();
        assert!(!slot(body, &after, "view").retain());
        assert!(!slot(body, &after, "owner").retain());
        crate::CheckedProgram::validate(&program).unwrap();
    }

    #[test]
    fn scopes_and_unreachable_events_have_no_initialized_slots() {
        let (program, declarations) = prepare(
            "(#struct Resource ((value #u64))) (#linear Resource)
             (#fn work () ()
               (#block (#let local Resource (#struct-literal Resource (: value 1u64)))
                 (#forget local))
               (#call checkpoint (:)) (#return ()) (#call checkpoint (:)) (#return ()))",
        );
        let body = &declarations.bodies["work"];
        let flow = &declarations.flows["work"];
        let types = LinearTypes::from_program(&program);
        let facts = StorageFacts::local_for_test(body, flow, &types);
        let analysis = Analysis::new(body, &facts, &types, &declarations);
        assert!(analysis
            .before(checkpoint(body, flow, 0))
            .unwrap()
            .slots
            .is_empty());
        assert!(analysis.before(checkpoint(body, flow, 1)).is_none());
    }

    #[test]
    fn partially_consumed_aggregate_is_never_a_full_loadable_value() {
        let (program, declarations) = prepare(
            "(#struct Resource ((value #u64))) (#linear Resource)
             (#struct Pair (: left.part Resource : right Resource))
             (#fn work ((owner.part Pair)) ()
               (#let extracted Resource (#get owner.part left.part))
               (#call checkpoint (:))
               (#forget extracted) (#forget owner.part) (#return ()))",
        );
        let body = &declarations.bodies["work"];
        let flow = &declarations.flows["work"];
        let types = LinearTypes::from_program(&program);
        let facts = StorageFacts::local_for_test(body, flow, &types);
        let analysis = Analysis::new(body, &facts, &types, &declarations);
        let snapshot = analysis.before(checkpoint(body, flow, 0)).unwrap();
        let owner = slot(body, &snapshot, "owner.part");
        assert!(owner.cleanup_needed());
        assert!(owner
            .obligations
            .iter()
            .any(|obligation| obligation.availability != Availability::Full));
        assert_eq!(
            slot(body, &snapshot, "extracted").obligations[0].availability,
            Availability::Full
        );
    }

    #[test]
    fn stale_pointer_anchor_retains_lifetime_without_claiming_address() {
        let (program, declarations) = prepare(
            "(#fn work ((raw (#ptr #u64))) ()
               (#let anchor #u64 0u64)
               (#let view (#ref #u64) (#unsafe (#ptr-borrow (#borrow anchor) raw)))
               (#call checkpoint (:)) (#drop view) (#return ()))",
        );
        let body = &declarations.bodies["work"];
        let flow = &declarations.flows["work"];
        let types = LinearTypes::from_program(&program);
        let facts = StorageFacts::local_for_test(body, flow, &types);
        let analysis = Analysis::new(body, &facts, &types, &declarations);
        let snapshot = analysis.before(checkpoint(body, flow, 0)).unwrap();
        let anchor = slot(body, &snapshot, "anchor");
        assert!(anchor.lifetime_needed);
        assert!(!anchor.address_needed);
    }

    #[test]
    fn entirely_unread_reference_is_not_ordinary_parameter_liveness() {
        let (program, declarations) = prepare(
            "(#fn work ((unused (#ref #u64))) ()
               (#let owner #u64 42u64)
               (#let fresh (#ref #u64) (#borrow owner))
               (#call checkpoint (:)) (#return ()))",
        );
        let body = &declarations.bodies["work"];
        let flow = &declarations.flows["work"];
        let types = LinearTypes::from_program(&program);
        let facts = StorageFacts::local_for_test(body, flow, &types);
        let analysis = Analysis::new(body, &facts, &types, &declarations);
        let snapshot = analysis.before(checkpoint(body, flow, 0)).unwrap();
        let fresh = slot(body, &snapshot, "fresh");
        assert!(!fresh.data_needed);
        assert!(!fresh.cleanup_needed());
        assert_eq!(fresh.loans.len(), 1);
        assert!(slot(body, &snapshot, "owner").address_needed);
        assert!(!slot(body, &snapshot, "unused").retain());
        crate::CheckedProgram::validate(&program).unwrap();
    }

    #[test]
    fn releasing_one_reference_field_preserves_only_the_other_loan() {
        let (program, declarations) = prepare(
            "(#struct Holder (: first (#ref #u64) : second (#ref #u64)))
             (#fn work () ()
               (#let first-owner #u64 1u64) (#let second-owner #u64 2u64)
               (#let holder Holder (#struct-literal Holder
                 (: first (#borrow first-owner) : second (#borrow second-owner))))
               (#drop (#get holder first))
               (#call checkpoint (:)) (#return ()))",
        );
        let body = &declarations.bodies["work"];
        let flow = &declarations.flows["work"];
        let types = LinearTypes::from_program(&program);
        let facts = StorageFacts::local_for_test(body, flow, &types);
        let analysis = Analysis::new(body, &facts, &types, &declarations);
        let snapshot = analysis.before(checkpoint(body, flow, 0)).unwrap();
        assert_eq!(slot(body, &snapshot, "holder").loans.len(), 1);
        assert!(!slot(body, &snapshot, "first-owner").retain());
        assert!(slot(body, &snapshot, "second-owner").address_needed);
    }
}
