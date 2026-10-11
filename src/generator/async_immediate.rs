//! Operation-local owner borrows that need no future storage.
//!
//! This certifies emission order, not access permission. Source and generated
//! ordinary checking remain authoritative. Only a single resolved synchronous
//! call in the same block may consume a borrow, with no intervening effects or
//! control edges. Thus its owning frame is stationary for that operation even
//! when the frame may move between polls.
use std::collections::HashMap;

use super::async_exec::{
    Action, AddressProjection, AddressRoot, BlockId, Compute, Graph, PlaceId, ValueId,
};

pub(crate) struct Borrow {
    pub place: PlaceId,
    pub mutable: bool,
}

pub(crate) struct Plan {
    borrows: HashMap<ValueId, Borrow>,
}

impl Plan {
    pub(crate) fn new(graph: &Graph) -> Result<Self, super::async_exec::Error> {
        graph.validate()?;
        let mut users = vec![Vec::new(); graph.values.len()];
        let mut escapes = vec![false; graph.values.len()];
        for block in graph.reachable() {
            for (index, action) in graph.blocks[block.0].actions.iter().enumerate() {
                let mut inputs = super::async_retire::uses(graph, &action.action);
                inputs.sort_unstable_by_key(|value| value.0);
                inputs.dedup();
                for value in inputs {
                    users[value.0].push((block, index));
                }
            }
            for value in super::async_retire::control(&graph.blocks[block.0].terminator) {
                escapes[value.0] = true;
            }
            for edge in super::async_retire::edges(&graph.blocks[block.0].terminator) {
                for argument in &edge.arguments {
                    if let super::async_exec::Argument::Value(value) = argument {
                        escapes[value.0] = true;
                    }
                }
            }
        }
        let pure_place = |place: PlaceId| {
            let descriptor = &graph.places[place.0];
            matches!(descriptor.root, AddressRoot::Local(_))
                && descriptor.checks().is_empty()
                && descriptor.projections.iter().all(|step| {
                    matches!(
                        step,
                        AddressProjection::Field(_) | AddressProjection::Tuple(_)
                    )
                })
        };
        let mut candidates = HashMap::<ValueId, (BlockId, usize, usize, Borrow)>::new();
        for block in graph.reachable() {
            for (index, located) in graph.blocks[block.0].actions.iter().enumerate() {
                let Action::Borrow {
                    dst: Some(dst),
                    place,
                    mutable,
                    pinned: false,
                    scope: None,
                } = located.action
                else {
                    continue;
                };
                if !pure_place(place) || escapes[dst.0] {
                    continue;
                }
                let [(consumer_block, consumer)] = users[dst.0].as_slice() else {
                    continue;
                };
                if *consumer_block != block || *consumer <= index {
                    continue;
                }
                let Action::Compute {
                    operation: Compute::Checked(operation),
                    ..
                } = &graph.blocks[block.0].actions[*consumer].action
                else {
                    continue;
                };
                if operation.callee.is_none()
                    || operation
                        .operands
                        .iter()
                        .filter(|operand| operand.value == dst)
                        .count()
                        != 1
                {
                    continue;
                }
                candidates.insert(dst, (block, index, *consumer, Borrow { place, mutable }));
            }
        }
        // Other borrows may be delayed together only if they feed the same
        // call. The ordinary checker, not this proof, checks disjointness.
        let mut borrows = HashMap::new();
        for (&value, &(block, index, consumer, _)) in &candidates {
            let valid = graph.blocks[block.0].actions[index + 1..consumer]
                .iter()
                .all(|located| match &located.action {
                    Action::Place { dst, .. } => pure_place(*dst),
                    Action::Borrow {
                        dst: Some(other), ..
                    } => candidates
                        .get(other)
                        .is_some_and(|(b, _, c, _)| *b == block && *c == consumer),
                    Action::Compute {
                        operation:
                            Compute::Atom {
                                kind: crate::typed_body::NodeKind::Literal(_),
                                ..
                            }
                            | Compute::Unit
                            | Compute::Bool(_),
                        ..
                    } => true,
                    _ => false,
                });
            if valid {
                let candidate = &candidates[&value].3;
                borrows.insert(
                    value,
                    Borrow {
                        place: candidate.place,
                        mutable: candidate.mutable,
                    },
                );
            }
        }
        // An intervening candidate rejected by its own window is an effectful
        // stored borrow, not another jointly emitted call argument.
        loop {
            let invalid = borrows
                .keys()
                .copied()
                .filter(|value| {
                    let (block, index, consumer, _) = &candidates[value];
                    graph.blocks[block.0].actions[index + 1..*consumer]
                        .iter()
                        .any(|located| {
                            matches!(located.action,
                    Action::Borrow { dst: Some(other), .. } if !borrows.contains_key(&other))
                        })
                })
                .collect::<Vec<_>>();
            if invalid.is_empty() {
                break;
            }
            for value in invalid {
                borrows.remove(&value);
            }
        }
        Ok(Self { borrows })
    }

    pub(crate) fn get(&self, value: ValueId) -> Option<&Borrow> {
        self.borrows.get(&value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn graph(body: &str) -> Graph {
        let source = format!(
            "(#enum Child ((Waiting #u64)))
          (#enum ChildPoll ((Pending Child) (Ready #u64)))
          (#fn child-poll (: task Child : waker (#ref #u64)) ChildPoll
            (#return (#match task (#case (Waiting value) (Ready value)))))
          (#fn touch (: value #u64 : target (#ref-mut #u64)) ()
            (#deref-set target value) (#return ()))
          (#fn touch-before (: target (#ref-mut #u64) : value #u64) ()
            (#deref-set target value) (#return ()))
          (#fn effect () #u64 (#return 1u64))
          (#struct Pair (: left #u64 : right #u64))
          (#fn touch-two (: left (#ref-mut #u64) : right (#ref-mut #u64)) ()
            (#deref-set left 20u64) (#deref-set right 22u64) (#return ()))
          (@#async-fn (: protocol WorkAwait : waker #u64
            : function (#fn work () #u64 {body})))"
        );
        let prepared = crate::prepare_program_syntax(
            &source,
            std::path::Path::new("."),
            None,
            &crate::CompileConfig::default(),
            None,
        )
        .unwrap();
        super::super::async_prepare::prepare(&prepared)
            .unwrap()
            .functions
            .remove(0)
            .graph
    }

    #[test]
    fn borrow_after_await_has_one_operation_local_consumer() {
        let graph = graph("(#let-mut owner #u64 0u64)
          (#call touch (: value (#await Child Pending Ready child-poll (Waiting 42u64)) : target (#borrow-mut owner)))
          (#return owner)");
        assert_eq!(Plan::new(&graph).unwrap().borrows.len(), 1);
        let graph = super::tests::graph(
            "(#let-mut owner #u64 0u64)
          (#call touch (: target (#borrow-mut owner) : value 42u64)) (#return owner)",
        );
        assert_eq!(Plan::new(&graph).unwrap().borrows.len(), 1);
    }

    #[test]
    fn borrows_before_await_or_effects_and_stored_handles_are_not_delayed() {
        for body in [
            "(#call touch-before (: target (#borrow-mut owner) : value (#await Child Pending Ready child-poll (Waiting 42u64))))",
            "(#call touch-before (: target (#borrow-mut owner) : value (#call effect ())))",
            "(#let view (#ref-mut #u64) (#borrow-mut owner)) (#call touch (: target view : value 42u64))",
        ] {
            let graph = graph(&format!("(#let-mut owner #u64 0u64) {body} (#return owner)"));
            assert!(Plan::new(&graph).unwrap().borrows.is_empty(), "{body}");
        }
    }

    #[test]
    fn disjoint_projection_arguments_share_a_single_synchronous_call() {
        let graph = graph("(#let-mut pair Pair (#struct-literal Pair (: left 0u64 : right 0u64)))
          (#call touch-two (: left (#borrow-mut (#get pair left)) : right (#borrow-mut (#get pair right))))
          (#return (#u64.+.wrap (#get pair left) (#get pair right)))");
        assert_eq!(Plan::new(&graph).unwrap().borrows.len(), 2);
    }
}
