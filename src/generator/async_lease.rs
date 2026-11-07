//! Storage proofs for nonmoving reference reads in the ordinary dispatcher.
//! Implementation detail of built-in code generation, not runtime semantics.
//!
//! An in-place window keeps the owning handle Full. Its only consumer is a
//! Copy leaf load or resolved call without reference-bearing results, after
//! pure address formation in the same executable block.
//! Other whole-binding exclusive reads materialize an ordinary checked
//! reborrow in a value cell at the original evaluation point. Checked pure
//! field/tuple projections retain the same evaluated child handle without
//! moving its holder or delaying evaluation.
//! The parent is not moved or copied,
//! and its pointer is never reevaluated after an effect or suspension.
//! This is an emission proof, not borrow permission:
//! the original source and the generated ordinary program remain mandatory.
#![allow(dead_code)]

use std::collections::{HashMap, HashSet};

use crate::generator::async_exec::{
    Action, AddressProjection, AddressRoot, Argument, BlockId, Compute, Graph, LoadKind, PlaceId,
    ValueId,
};
use crate::generator::async_lend::{Access, Plan as Accesses};
use crate::linearcheck::LinearTypes;
use crate::typed_body::{BindingId, PlaceRoot};
use crate::typed_place::Place;
use crate::Type;

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum Consumer {
    Leaf,
    Call,
    SliceIndex,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Lease {
    pub binding: BindingId,
    pub place: PlaceId,
    pub block: BlockId,
    pub load: usize,
    pub read: usize,
    pub consumer: Consumer,
}

pub(crate) struct Plan {
    leases: HashMap<ValueId, Lease>,
    snapshots: HashMap<ValueId, BindingId>,
    projected_snapshots: HashMap<ValueId, PlaceId>,
    snapshot_bindings: HashSet<BindingId>,
    /// Nonmoving field-handle loads used by one immediate scalar read. The
    /// emitted reader projects through the parent instead of storing a copy.
    handle_leaves: HashMap<ValueId, PlaceId>,
}

fn pure_path(descriptor: &crate::generator::async_exec::PlaceDescriptor, value: ValueId) -> bool {
    descriptor.root == AddressRoot::Value(value)
        && matches!(
            descriptor.projections.first(),
            Some(AddressProjection::Dereference)
        )
        && descriptor.projections[1..].iter().all(|step| {
            matches!(
                step,
                AddressProjection::Field(_) | AddressProjection::Tuple(_)
            )
        })
        && descriptor.checks().is_empty()
}

impl Plan {
    pub(crate) fn new(
        graph: &Graph,
        accesses: Option<&Accesses>,
        types: &LinearTypes,
        aliases: &HashMap<String, Type>,
    ) -> Result<Self, crate::generator::async_exec::Error> {
        graph.validate()?;
        let mut leases = HashMap::new();
        let mut snapshots = HashMap::new();
        let mut projected_snapshots = HashMap::new();
        let mut handle_leaves = HashMap::new();
        let Some(accesses) = accesses else {
            return Ok(Self {
                leases,
                snapshots,
                projected_snapshots,
                snapshot_bindings: HashSet::new(),
                handle_leaves,
            });
        };
        let reachable = graph.reachable();
        // Index physical uses once, including recomputed address roots. A
        // graph with many reads must not rescan every action for each handle.
        let mut users = vec![Vec::new(); graph.values.len()];
        let mut escapes = vec![false; graph.values.len()];
        let physical_uses = crate::generator::async_retire::PhysicalUses::new(graph);
        for &block in &reachable {
            let body = &graph.blocks[block.0];
            for (index, located) in body.actions.iter().enumerate() {
                let mut inputs = physical_uses.uses(&located.action);
                inputs.sort_unstable_by_key(|value| value.0);
                inputs.dedup();
                for value in inputs {
                    users[value.0].push((block, index));
                }
            }
            for value in crate::generator::async_retire::control(&body.terminator) {
                escapes[value.0] = true;
            }
            for edge in crate::generator::async_retire::edges(&body.terminator) {
                for argument in &edge.arguments {
                    if let Argument::Value(value) = argument {
                        escapes[value.0] = true;
                    }
                }
            }
        }
        for &block in &reachable {
            for (load, located) in graph.blocks[block.0].actions.iter().enumerate() {
                let Action::Load {
                    dst,
                    place,
                    kind: LoadKind::Read,
                } = located.action
                else {
                    continue;
                };
                let descriptor = &graph.places[place.0];
                if let AddressRoot::Value(parent) = descriptor.root {
                    let nonmoving = located
                        .source
                        .and_then(|source| accesses.access(source))
                        .is_some_and(|access| matches!(access, Access::Lend(_)));
                    if !nonmoving || !pure_path(descriptor, parent) || escapes[dst.0] {
                        continue;
                    }
                    let ty = crate::typed_ir::resolve_type(&graph.values[dst.0].ty, aliases)
                        .map_err(|message| crate::generator::async_exec::Error {
                            source: located.source,
                            message,
                        })?;
                    if matches!(
                        ty,
                        Type::Reference { mutable: true, .. }
                            | Type::PinnedReference { mutable: true, .. }
                    ) {
                        let mut consumer = None;
                        let mut valid = true;
                        for &(user_block, index) in &users[dst.0] {
                            if user_block != block || index <= load {
                                valid = false;
                                break;
                            }
                            match &graph.blocks[block.0].actions[index].action {
                                Action::Place { descriptor, .. } if pure_path(descriptor, dst) => {}
                                Action::Load {
                                    place,
                                    kind: LoadKind::Read,
                                    ..
                                } if pure_path(&graph.places[place.0], dst)
                                    && types.can_repeat(&graph.places[place.0].ty)
                                    && !types.contains_reference(&graph.places[place.0].ty) =>
                                {
                                    if consumer.replace(index).is_some() {
                                        valid = false;
                                    }
                                }
                                _ => valid = false,
                            }
                        }
                        if let Some(read) = consumer {
                            if valid && graph.blocks[block.0].actions[load + 1..read].iter()
                                .all(|action| matches!(&action.action, Action::Place { descriptor, .. } if pure_path(descriptor, dst))) {
                                handle_leaves.insert(dst, place);
                            }
                        }
                    }
                    continue;
                }
                let AddressRoot::Local(binding) = descriptor.root else {
                    continue;
                };
                let mut projected = Place::root(PlaceRoot::Local(binding));
                let mut pure = descriptor.checks().is_empty();
                for projection in &descriptor.projections {
                    projected.segments.push(match projection {
                        AddressProjection::Field(field) => {
                            crate::typed_place::Segment::Field(*field)
                        }
                        AddressProjection::Tuple(index) => {
                            crate::typed_place::Segment::Tuple(*index)
                        }
                        _ => {
                            pure = false;
                            break;
                        }
                    });
                }
                if !pure
                    || !located
                        .source
                        .and_then(|source| accesses.access(source))
                        .is_some_and(
                            |access| matches!(access, Access::Lend(place) if place == &projected),
                        )
                {
                    continue;
                }
                let ty = crate::typed_ir::resolve_type(&graph.values[dst.0].ty, aliases).map_err(
                    |message| crate::generator::async_exec::Error {
                        source: located.source,
                        message,
                    },
                )?;
                if !matches!(
                    ty,
                    Type::Reference { mutable: true, .. }
                        | Type::PinnedReference { mutable: true, .. }
                        | Type::MutableSlice(_)
                ) {
                    continue;
                }
                let projected_path = !descriptor.projections.is_empty()
                    && descriptor.checks().is_empty()
                    && descriptor.projections.iter().all(|projection| {
                        matches!(
                            projection,
                            AddressProjection::Field(_) | AddressProjection::Tuple(_)
                        )
                    });
                // Whole-binding reads have a checked reborrow adapter.
                // Projected holders use a child-handle adapter; do not mistake
                // a field read for a whole-binding snapshot.
                if descriptor.projections.is_empty() {
                    snapshots.insert(dst, binding);
                } else if projected_path {
                    projected_snapshots.insert(dst, place);
                }
                let mut consumer = None;
                let mut selected_slice = None;
                let mut valid = !escapes[dst.0];
                for &(user_block, index) in &users[dst.0] {
                    let user = &graph.blocks[user_block.0].actions[index];
                    if user_block != block || index <= load {
                        valid = false;
                        continue;
                    }
                    match &user.action {
                        Action::Place {
                            dst: selected,
                            descriptor,
                        } if matches!(ty, Type::MutableSlice(_))
                            && graph.places[place.0].projections.is_empty()
                            && descriptor.root == AddressRoot::Value(dst)
                            && matches!(
                                descriptor.projections.as_slice(),
                                [AddressProjection::SliceIndex(_)]
                            ) =>
                        {
                            selected_slice = Some(*selected);
                            if consumer.replace((index, Consumer::SliceIndex)).is_some() {
                                valid = false;
                            }
                        }
                        // These reads use the selected address snapshot, not
                        // a reevaluated slice handle. Selection itself remains
                        // the only consumer of the holder's lending window.
                        Action::Borrow {
                            place: selected, ..
                        } if selected_slice == Some(*selected) => {}
                        Action::Place { descriptor, .. } if pure_path(descriptor, dst) => {}
                        Action::Load { place, .. }
                            if pure_path(&graph.places[place.0], dst)
                                && types.can_repeat(&graph.places[place.0].ty)
                                && !types.contains_reference(&graph.places[place.0].ty) =>
                        {
                            if consumer.replace((index, Consumer::Leaf)).is_some() {
                                valid = false
                            }
                        }
                        Action::Compute {
                            dst: result,
                            operation: Compute::Checked(operation),
                        } if operation.callee.is_some()
                            && !types.contains_reference(&graph.values[result.0].ty)
                            && operation
                                .operands
                                .iter()
                                .filter(|operand| operand.value == dst)
                                .count()
                                == 1 =>
                        {
                            // The ordinary callee contract still authorizes
                            // pointee access. This proof only avoids moving
                            // the parent handle, and cannot store a returned
                            // child reference without a retained lease.
                            if consumer.replace((index, Consumer::Call)).is_some() {
                                valid = false;
                            }
                        }
                        _ => valid = false,
                    }
                }
                let Some((read, consumer)) = consumer else {
                    continue;
                };
                // Not merely "no writes to this binding": calls, pointer
                // writes, checks, and unrelated operations can change the
                // evaluated pointer or permissions. Nothing effectful may
                // occur between the original handle read and its consumer.
                let pure_window = |user: &crate::generator::async_exec::LocatedAction| {
                    if matches!(&user.action, Action::Place { descriptor, .. } if pure_path(descriptor, dst))
                    {
                        return true;
                    }
                    if consumer != Consumer::SliceIndex {
                        return false;
                    }
                    match &user.action {
                        Action::Place { descriptor, .. } => {
                            descriptor.projections.is_empty()
                                && matches!(descriptor.root, AddressRoot::Local(_))
                                && types.can_repeat(&descriptor.ty)
                                && !types.contains_reference(&descriptor.ty)
                        }
                        Action::Compute {
                            operation:
                                Compute::Atom {
                                    kind: crate::typed_body::NodeKind::Literal(_),
                                    ..
                                },
                            ..
                        } => true,
                        Action::Compute {
                            operation: Compute::Checked(operation),
                            ..
                        } => {
                            operation.head == "literal"
                                && operation.callee.is_none()
                                && operation.operands.is_empty()
                        }
                        Action::Load {
                            place,
                            kind: LoadKind::Read,
                            ..
                        } => {
                            let descriptor = &graph.places[place.0];
                            descriptor.projections.is_empty()
                                && matches!(descriptor.root, AddressRoot::Local(_))
                                && types.can_repeat(&descriptor.ty)
                                && !types.contains_reference(&descriptor.ty)
                        }
                        _ => false,
                    }
                };
                if !valid
                    || !graph.blocks[block.0].actions[load + 1..read]
                        .iter()
                        .all(pure_window)
                {
                    continue;
                }
                leases.insert(
                    dst,
                    Lease {
                        binding,
                        place,
                        block,
                        load,
                        read,
                        consumer,
                    },
                );
                snapshots.remove(&dst);
                projected_snapshots.remove(&dst);
            }
        }
        let snapshot_bindings = snapshots.values().copied().collect();
        Ok(Self {
            leases,
            snapshots,
            projected_snapshots,
            snapshot_bindings,
            handle_leaves,
        })
    }

    pub(crate) fn get(&self, value: ValueId) -> Option<&Lease> {
        self.leases.get(&value)
    }

    pub(crate) fn handle_leaf(&self, value: ValueId) -> Option<PlaceId> {
        self.handle_leaves.get(&value).copied()
    }

    /// A deferred scalar reader uses the evaluated parent capability, not the
    /// elided child handle. Keep that parent alive through the actual read.
    pub(crate) fn extend_physical_uses(&self, graph: &Graph, values: &mut Vec<ValueId>) {
        let mut index = 0;
        let mut seen = HashSet::new();
        while index < values.len() {
            let value = values[index];
            index += 1;
            if !seen.insert(value) {
                continue;
            }
            if let Some(place) = self.handle_leaf(value) {
                if let AddressRoot::Value(parent) = graph.places[place.0].root {
                    values.push(parent);
                }
            }
        }
    }

    pub(crate) fn snapshot(&self, value: ValueId) -> Option<BindingId> {
        self.snapshots.get(&value).copied()
    }

    pub(crate) fn projected_snapshot(&self, value: ValueId) -> Option<PlaceId> {
        self.projected_snapshots.get(&value).copied()
    }

    pub(crate) fn snapshots_binding(&self, binding: BindingId) -> bool {
        self.snapshot_bindings.contains(&binding)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct Checked {
        graph: Graph,
        types: LinearTypes,
        accesses: Option<Accesses>,
        aliases: HashMap<String, Type>,
    }

    impl Checked {
        fn new(source: &str) -> Self {
            let program = crate::parse_program(source).unwrap();
            let declarations =
                crate::typecheck::resolve_program_for_analysis(&program, true).unwrap();
            let body = &declarations.bodies["work"];
            let types = LinearTypes::from_program(&program);
            let accesses = Accesses::new(body, &declarations.flows["work"], &types).unwrap();
            let graph = crate::generator::async_exec::build(body, &[]).unwrap();
            graph.validate().unwrap();
            Self {
                graph,
                types,
                accesses,
                aliases: declarations.aliases.clone(),
            }
        }

        fn plan(&self) -> Plan {
            Plan::new(
                &self.graph,
                self.accesses.as_ref(),
                &self.types,
                &self.aliases,
            )
            .unwrap()
        }
    }

    fn borrowed_field() -> Checked {
        Checked::new(
            "(#struct View (#linear) (: field (#ref-mut #u64)))
          (#fn work (: view (#ref View)) #u64 (#return (#deref (#get view field))))",
        )
    }

    #[test]
    fn borrowed_exclusive_field_leaves_require_one_immediate_nonmoving_read() {
        let mut checked = borrowed_field();
        let plan = checked.plan();
        assert_eq!(plan.handle_leaves.len(), 1);
        let value = *plan.handle_leaves.keys().next().unwrap();
        let (block, load) = checked.graph.blocks.iter().enumerate().find_map(|(block, body)|
            body.actions.iter().position(|located| matches!(located.action, Action::Load { dst, .. } if dst == value))
                .map(|load| (block, load))).unwrap();
        let AddressRoot::Value(parent) = checked.graph.places[plan.handle_leaves[&value].0].root
        else {
            unreachable!()
        };
        let retirement = super::super::async_retire::Plan::with_lending_snapshots(
            &checked.graph,
            &checked.types,
            &HashSet::new(),
            &checked.aliases,
            Some(&plan),
        )
        .unwrap();
        assert!(
            !retirement.after_action[block][load].contains(&parent),
            "parent capability must survive the elided load"
        );
        assert!(
            retirement.after_action[block]
                .iter()
                .skip(load + 1)
                .any(|retired| retired.contains(&parent)),
            "the actual scalar consumer retires the parent"
        );
        let unit = ValueId(checked.graph.values.len());
        checked
            .graph
            .values
            .push(crate::generator::async_exec::Value {
                source: None,
                ty: Type::Unit,
                span: None,
            });
        checked.graph.blocks[block].actions.insert(
            load + 1,
            crate::generator::async_exec::LocatedAction {
                action: Action::Compute {
                    dst: unit,
                    operation: Compute::Unit,
                },
                source: None,
                span: None,
                unsafe_context: false,
            },
        );
        checked.graph.validate().unwrap();
        assert!(
            checked.plan().handle_leaf(value).is_none(),
            "no deferred read across another operation"
        );

        let mut checked = borrowed_field();
        let value = *checked.plan().handle_leaves.keys().next().unwrap();
        checked.graph.blocks[checked.graph.entry.0].terminator =
            crate::generator::async_exec::Terminator::Return(Some(value));
        checked.graph.validate().unwrap();
        assert!(
            checked.plan().handle_leaf(value).is_none(),
            "a borrowed field window cannot escape as an owned handle"
        );
    }

    #[test]
    fn borrowed_field_windows_reject_missing_permission_and_multiple_consumers() {
        let mut checked = borrowed_field();
        let value = *checked.plan().handle_leaves.keys().next().unwrap();
        checked.accesses = None;
        assert!(checked.plan().handle_leaf(value).is_none());

        let mut checked = borrowed_field();
        let value = *checked.plan().handle_leaves.keys().next().unwrap();
        let physical = super::super::async_retire::PhysicalUses::new(&checked.graph);
        let (block, index) = checked
            .graph
            .blocks
            .iter()
            .enumerate()
            .find_map(|(block, body)| {
                body.actions
                    .iter()
                    .enumerate()
                    .find_map(|(index, located)| {
                        (matches!(located.action, Action::Load { .. })
                            && physical.uses(&located.action).contains(&value))
                        .then_some((block, index))
                    })
            })
            .unwrap();
        let mut duplicate = checked.graph.blocks[block].actions[index].clone();
        let Action::Load { dst, .. } = &mut duplicate.action else {
            unreachable!()
        };
        let ty = checked.graph.values[dst.0].clone();
        *dst = ValueId(checked.graph.values.len());
        checked.graph.values.push(ty);
        checked.graph.blocks[block]
            .actions
            .insert(index + 1, duplicate);
        checked.graph.validate().unwrap();
        assert!(
            checked.plan().handle_leaf(value).is_none(),
            "the certificate covers one scalar read, not repeated consumers"
        );
    }

    #[test]
    fn borrowed_field_windows_do_not_cross_block_boundaries() {
        let mut checked = borrowed_field();
        let value = *checked.plan().handle_leaves.keys().next().unwrap();
        let (block, load) = checked.graph.blocks.iter().enumerate().find_map(|(block, body)|
            body.actions.iter().position(|located| matches!(located.action, Action::Load { dst, .. } if dst == value))
                .map(|load| (block, load))).unwrap();
        let target = BlockId(checked.graph.blocks.len());
        let terminal = std::mem::replace(
            &mut checked.graph.blocks[block].terminator,
            crate::generator::async_exec::Terminator::Goto(crate::generator::async_exec::Edge {
                target,
                arguments: vec![],
            }),
        );
        let actions = checked.graph.blocks[block].actions.split_off(load + 1);
        checked
            .graph
            .blocks
            .push(crate::generator::async_exec::Block {
                parameters: vec![],
                actions,
                terminator: terminal,
            });
        checked.graph.validate().unwrap();
        assert!(checked.plan().handle_leaf(value).is_none());
    }

    #[test]
    fn slice_selection_lends_only_through_effect_free_index_windows() {
        for index in ["0usize", "index"] {
            let checked = Checked::new(&format!(
                "(#fn work (: items (#slice-mut #u64) : index #usize) #u64
                  (#let answer #u64 (#deref (#slice-mut-idx items {index})))
                  (#forget items) (#return answer))"
            ));
            let plan = checked.plan();
            assert_eq!(plan.leases.len(), 1);
            let lease = plan.leases.values().next().unwrap();
            assert_eq!(lease.consumer, Consumer::SliceIndex);
            assert!(plan.snapshot(*plan.leases.keys().next().unwrap()).is_none());
        }
        let checked = Checked::new(
            "(#fn choose () #usize (#return 0usize))
             (#fn work (: items (#slice-mut #u64)) #u64
               (#let answer #u64 (#deref (#slice-mut-idx items (#call choose ()))))
               (#forget items) (#return answer))",
        );
        let plan = checked.plan();
        assert!(
            plan.leases.is_empty(),
            "a call cannot be moved across the slice read"
        );
        assert_eq!(plan.snapshots.len(), 1);
    }

    #[test]
    fn owned_slice_transfers_cannot_be_retired_as_lending_snapshots() {
        let checked = Checked::new(
            "(#fn work (: items (#slice-mut #u64)) (#slice-mut #u64) (#return items))",
        );
        let plan = checked.plan();
        let requested = (0..checked.graph.values.len()).map(ValueId).collect();
        assert!(super::super::async_retire::Plan::with_lending_snapshots(
            &checked.graph,
            &checked.types,
            &requested,
            &checked.aliases,
            Some(&plan)
        )
        .is_none());
    }

    #[test]
    fn immediate_exclusive_reads_have_exact_nonmoving_windows() {
        for ty in ["#ref-mut", "#pin-ref-mut"] {
            let checked = Checked::new(&format!(
                "(#fn work (: view ({ty} #u64)) #u64
                  (#let first #u64 (#deref view)) (#return (#u64::add-wrap first (#deref view))))"
            ));
            let plan = checked.plan();
            assert_eq!(plan.leases.len(), 2);
            assert!(plan.snapshots.is_empty());
            assert!(plan.snapshot_bindings.is_empty());
            assert_eq!(plan.leases, checked.plan().leases);
            for (value, lease) in &plan.leases {
                assert_eq!(lease.binding, BindingId(0));
                assert_eq!(lease.consumer, Consumer::Leaf);
                assert!(lease.load < lease.read);
                let actions = &checked.graph.blocks[lease.block.0].actions;
                assert!(
                    matches!(actions[lease.load].action, Action::Load { dst, .. } if dst == *value)
                );
                assert!(matches!(actions[lease.read].action, Action::Load { .. }));
            }
        }
    }

    #[test]
    fn owned_transfers_and_shared_handles_are_not_read_leases() {
        for source in [
            "(#fn work (: view (#ref-mut #u64)) (#ref-mut #u64) (#return view))",
            "(#fn work (: view (#ref #u64)) #u64 (#return (#deref view)))",
        ] {
            let plan = Checked::new(source).plan();
            assert!(plan.leases.is_empty(), "{source}");
            assert!(
                plan.snapshots.is_empty(),
                "owned/shared read must not reborrow: {source}"
            );
        }
    }

    #[test]
    fn immediate_resolved_calls_lend_without_retaining_results() {
        for ty in ["#ref-mut", "#pin-ref-mut"] {
            for result in ["#u64", "()", "Owned"] {
                let value = match result {
                    "#u64" => "(#deref view)",
                    "()" => "()",
                    _ => "(#struct-literal Owned (: value (#deref view)))",
                };
                let checked = Checked::new(&format!(
                    "(#struct Owned (#linear) (: value #u64))
                     (#fn read (: view ({ty} #u64)) {result} (#return {value}))
                     (#fn work (: view ({ty} #u64)) {result} (#return (#call read (: view view))))"
                ));
                let plan = checked.plan();
                assert_eq!(plan.leases.len(), 1, "{ty} {result}");
                assert!(plan.snapshots.is_empty());
                let lease = plan.leases.values().next().unwrap();
                assert_eq!(lease.consumer, Consumer::Call);
                assert!(matches!(
                    checked.graph.blocks[lease.block.0].actions[lease.read].action,
                    Action::Compute {
                        operation: Compute::Checked(_),
                        ..
                    }
                ));
            }
        }
    }

    #[test]
    fn projected_exclusive_handles_only_elide_certified_immediate_windows() {
        for projection in ["(#get owner view)", "(#get (#get owner pair) 0)"] {
            let context =
                "(#struct Holder (#linear) (: view (#ref-mut #u64) : pair (#tuple (#ref-mut #u64))))

              (#fn read (: view (#ref-mut #u64) : amount #u64) #u64
                (#return (#u64::add-wrap (#deref view) amount)))
              (#fn later () #u64 (#return 1u64))";
            let immediate = Checked::new(&format!(
                "{context} (#fn work (: owner Holder) #u64
                  (#let answer #u64 (#deref {projection}))
                  (#forget owner) (#return answer))"
            ));
            let plan = immediate.plan();
            assert_eq!(plan.leases.len(), 1);
            assert!(plan.snapshots.is_empty());
            let (_, lease) = plan.leases.iter().next().unwrap();
            assert!(!immediate.graph.places[lease.place.0].projections.is_empty());
            let effectful = Checked::new(&format!(
                "{context} (#fn work (: owner Holder) #u64
                  (#let answer #u64 (#call read (: view {projection} : amount (#call later ()))))
                  (#forget owner) (#return answer))"
            ));
            let plan = effectful.plan();
            assert!(plan.leases.is_empty());
            let (value, place) = plan.projected_snapshots.iter().next().unwrap();
            assert_eq!(plan.projected_snapshots.len(), 1);
            assert_eq!(plan.projected_snapshot(*value), Some(*place));
            assert!(!effectful.graph.places[place.0].projections.is_empty());
            assert!(plan.snapshots.is_empty());
        }
    }

    #[test]
    fn projected_snapshots_require_checked_pure_paths_and_retain_escapes() {
        let mut retained = Checked::new(
            "(#struct Holder (#linear) (: view (#ref-mut #u64)))
             (#fn read (: view (#ref-mut #u64) : amount #u64) #u64 (#return amount))
             (#fn later () #u64 (#return 1u64))
             (#fn work (: owner Holder) #u64
               (#let answer #u64 (#call read (: view (#get owner view) : amount (#call later ()))))
               (#forget owner) (#return answer))",
        );
        let original = retained.plan();
        let (value, place) = original.projected_snapshots.iter().next().unwrap();
        let value = *value;
        let place = *place;
        retained.graph.blocks[retained.graph.entry.0].terminator =
            crate::generator::async_exec::Terminator::Return(Some(value));
        retained.graph.validate().unwrap();
        let plan = retained.plan();
        assert!(plan.leases.is_empty());
        assert_eq!(plan.projected_snapshot(value), Some(place));

        for source in [
            "(#fn work (: view (#ref-mut (#array #u64 1))) #u64
               (#return (#index (#deref view) 0usize)))",
            "(#struct Holder () (: view (#ref #u64)))
             (#fn work (: owner Holder) #u64 (#return (#deref (#get owner view))))",
        ] {
            let plan = Checked::new(source).plan();
            assert!(plan.projected_snapshots.is_empty(), "{source}");
        }
    }

    #[test]
    fn returned_references_and_later_operands_require_retained_storage() {
        for source in [
            "(#fn read (: view (#ref-mut #u64)) (#ref-mut #u64) (#return view))
             (#fn work (: view (#ref-mut #u64)) (#ref-mut #u64) (#return (#call read (: view view))))",
            "(#struct Source () (: leaf (#ref #u64))) (#struct Holder () (: view (#ref #u64)))
             (#fn read (: view (#ref-mut Source)) Holder (#return (#struct-literal Holder (: view (#get view leaf)))))
             (#fn work (: view (#ref-mut Source)) Holder (#return (#call read (: view view))))",
            "(#fn read (: view (#ref-mut #u64) : amount #u64) #u64 (#return amount))
             (#fn later () #u64 (#return 42u64))
             (#fn work (: view (#ref-mut #u64)) #u64 (#return (#call read (: view view : amount (#call later ())))))",
        ] {
            let checked = Checked::new(source);
            let plan = checked.plan();
            assert!(plan.leases.is_empty(), "{source}");
            assert_eq!(plan.snapshots.len(), 1, "{source}");
            assert!(plan.snapshots.values().all(|binding| *binding == BindingId(0)));
            assert_eq!(plan.snapshots, checked.plan().snapshots);
            assert!(plan.snapshots_binding(BindingId(0)));
        }
    }

    #[test]
    fn aliases_preserve_the_exclusive_handle_kind() {
        let checked = Checked::new(
            "(#type View (#ref-mut #u64))
          (#fn work (: view View) #u64 (#return (#deref view)))",
        );
        assert_eq!(checked.plan().leases.len(), 1);
    }

    #[test]
    fn a_block_boundary_requires_retained_lending_storage() {
        let mut checked =
            Checked::new("(#fn work (: view (#ref-mut #u64)) #u64 (#return (#deref view)))");
        let plan = checked.plan();
        let (value, lease) = plan.leases.iter().next().unwrap();
        let value = *value;
        let lease = lease.clone();
        let target = BlockId(checked.graph.blocks.len());
        let terminal = std::mem::replace(
            &mut checked.graph.blocks[lease.block.0].terminator,
            crate::generator::async_exec::Terminator::Goto(crate::generator::async_exec::Edge {
                target,
                arguments: vec![],
            }),
        );
        let actions = checked.graph.blocks[lease.block.0]
            .actions
            .split_off(lease.load + 1);
        checked
            .graph
            .blocks
            .push(crate::generator::async_exec::Block {
                parameters: vec![],
                actions,
                terminator: terminal,
            });
        checked.graph.validate().unwrap();
        let plan = checked.plan();
        assert!(plan.get(value).is_none());
        assert_eq!(plan.snapshot(value), Some(lease.binding));
    }

    #[test]
    fn immediate_field_paths_are_proved_but_checks_and_reference_leaves_are_not() {
        for (source, expected) in [
            ("(#struct Value () (: amount #u64)) (#fn work (: view (#ref-mut Value)) #u64 (#return (#get view amount)))", 1),
            ("(#fn work (: view (#ref-mut (#tuple #u64 #u64))) #u64 (#return (#get view 1)))", 1),
            ("(#struct Value () (: nested (#ref #u64))) (#fn work (: view (#ref-mut Value)) (#ref #u64) (#return (#get view nested)))", 0),
            ("(#fn work (: view (#ref-mut (#array #u64 1))) #u64 (#return (#index (#deref view) 0usize)))", 0),
        ] {
            assert_eq!(Checked::new(source).plan().leases.len(), expected, "{source}");
        }
    }

    #[test]
    fn an_intervening_operation_invalidates_pointer_reevaluation() {
        let mut checked =
            Checked::new("(#fn work (: view (#ref-mut #u64)) #u64 (#return (#deref view)))");
        let plan = checked.plan();
        let (value, lease) = plan.leases.iter().next().unwrap();
        let value = *value;
        let lease = lease.clone();
        // This operation is deliberately unrelated to the address recipe.
        // The verifier must not guess its effects or permit reevaluation
        // merely because it contains no syntactic write to the owner.
        let unit = ValueId(checked.graph.values.len());
        checked
            .graph
            .values
            .push(crate::generator::async_exec::Value {
                source: None,
                ty: Type::Unit,
                span: None,
            });
        checked.graph.blocks[lease.block.0].actions.insert(
            lease.load + 1,
            crate::generator::async_exec::LocatedAction {
                action: Action::Compute {
                    dst: unit,
                    operation: crate::generator::async_exec::Compute::Unit,
                },
                source: None,
                span: None,
                unsafe_context: false,
            },
        );
        checked.graph.validate().unwrap();
        let plan = checked.plan();
        assert!(plan.get(value).is_none());
        assert_eq!(plan.snapshot(value), Some(lease.binding));
    }

    #[test]
    fn another_consumer_or_an_escaping_edge_invalidates_the_lease() {
        let mut checked =
            Checked::new("(#fn work (: view (#ref-mut #u64)) #u64 (#return (#deref view)))");
        let plan = checked.plan();
        let (value, lease) = plan.leases.iter().next().unwrap();
        let value = *value;
        let lease = lease.clone();
        let mut duplicate = checked.graph.blocks[lease.block.0].actions[lease.read].clone();
        let dst = ValueId(checked.graph.values.len());
        checked.graph.values.push(checked.graph.values[0].clone());
        checked.graph.values[dst.0].ty = Type::U64;
        if let Action::Load { dst: output, .. } = &mut duplicate.action {
            *output = dst
        }
        checked.graph.blocks[lease.block.0].actions.push(duplicate);
        checked.graph.validate().unwrap();
        assert!(
            checked.plan().get(value).is_none(),
            "a handle snapshot cannot acquire multiple deferred readers"
        );

        let mut checked =
            Checked::new("(#fn work (: view (#ref-mut #u64)) #u64 (#return (#deref view)))");
        let plan = checked.plan();
        let value = *plan.leases.keys().next().unwrap();
        checked.graph.blocks[checked.graph.entry.0].terminator =
            crate::generator::async_exec::Terminator::Return(Some(value));
        checked.graph.validate().unwrap();
        assert!(
            checked.plan().get(value).is_none(),
            "a nonmoving read is not a returnable owned value"
        );
    }
}
