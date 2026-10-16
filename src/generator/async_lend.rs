//! Owned transfers versus lending reads of move-only reference holders.
//! Implementation detail of built-in code generation, not runtime semantics.
//!
//! Use the ordinary flow's consumption classification, not the fact that a
//! type is non-Copy. This is storage classification, never borrow permission.
//! The emitter still needs an actual lending lease for every nonmoving read.
#![allow(dead_code)]

use std::collections::HashMap;

use crate::linearcheck::LinearTypes;
use crate::typed_body::{Body, NodeId, PlaceRoot};
use crate::typed_flow::{FlowAction, FlowGraph, FlowNodeId};
use crate::typed_place::Place;

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum Access {
    Move(Place),
    Lend(Place),
}

pub(crate) struct Plan {
    accesses: HashMap<NodeId, Access>,
}

impl Plan {
    pub(crate) fn new(
        body: &Body,
        flow: &FlowGraph,
        types: &LinearTypes,
    ) -> Result<Option<Self>, crate::generator::async_exec::Error> {
        let candidates = flow
            .nodes
            .iter()
            .enumerate()
            .filter_map(|(index, event)| {
                let FlowAction::Read { value, place, .. } = &event.action else {
                    return None;
                };
                let ty = body.nodes[value.0].ty.as_ref()?;
                (matches!(place.root, PlaceRoot::Local(_))
                    && types.requires_move(ty)
                    && types.contains_reference(ty))
                .then_some((FlowNodeId(index), *value, place))
            })
            .collect::<Vec<_>>();
        if candidates.is_empty() {
            return Ok(None);
        }
        // These local transfer markers are the same ones used by production
        // ownership. Referent/callee effects are not permission to move the
        // handle's own cell and do not belong in this classification.
        let moves = flow.consumptions(body, types);
        let reachable = flow.reachable();
        let mut accesses = HashMap::new();
        for (event, value, place) in candidates {
            if !reachable.contains(&event) {
                continue;
            }
            let access = if moves.consumes_at(event, place) {
                Access::Move(place.clone())
            } else {
                Access::Lend(place.clone())
            };
            if let Some(previous) = accesses.insert(value, access.clone()) {
                if previous != access {
                    return Err(crate::generator::async_exec::Error {
                        source: Some(value),
                        message: "reference load has inconsistent checked transfer events".into(),
                    });
                }
            }
        }
        Ok(Some(Self { accesses }))
    }

    pub(crate) fn access(&self, source: NodeId) -> Option<&Access> {
        self.accesses.get(&source)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn classify(source: &str) -> (Body, Option<Plan>) {
        let program = crate::parse_program(source).unwrap();
        let mut declarations =
            crate::typecheck::resolve_program_for_analysis(&program, true).unwrap();
        let body = declarations.bodies.remove("work").unwrap();
        let flow = &declarations.flows["work"];
        let plan = Plan::new(&body, flow, &LinearTypes::from_program(&program)).unwrap();
        (body, plan)
    }

    fn named<'a>(body: &'a Body, plan: &'a Plan, name: &str) -> Vec<&'a Access> {
        body.nodes
            .iter()
            .enumerate()
            .filter_map(|(index, node)| {
                matches!(&node.kind, crate::typed_body::NodeKind::Symbol { name: found, .. } if found == name)
                    .then(|| plan.access(NodeId(index)))
                    .flatten()
            })
            .collect()
    }

    #[test]
    fn exclusive_reads_and_direct_calls_lend_without_moving_the_handle() {
        for ty in ["#ref-mut", "#pin-ref-mut"] {
            let (body, plan) = classify(&format!(
                "(#fn read (: view ({ty} #u64)) #u64 (#return (#deref view)))
                 (#fn work (: view ({ty} #u64)) #u64
                   (#let first #u64 (#deref view))
                   (#return (#call read (: view view))))"
            ));
            let accesses = named(&body, plan.as_ref().unwrap(), "view");
            assert_eq!(accesses.len(), 2);
            assert!(accesses
                .iter()
                .all(|access| matches!(access, Access::Lend(_))));
        }
    }

    #[test]
    fn owned_reference_bindings_returns_and_constructors_transfer() {
        for tail in [
            "(#return view)",
            "(#let moved (#ref-mut #u64) view) (#return moved)",
            "(#return (#if choose view other))",
            "(#return (#block (#let moved (#ref-mut #u64) view) moved))",
            "(#return (#unsafe view))",
        ] {
            let (body, plan) = classify(&format!(
                "(#fn work (: choose #bool : view (#ref-mut #u64) : other (#ref-mut #u64))
                   (#ref-mut #u64) {tail})"
            ));
            let accesses = named(&body, plan.as_ref().unwrap(), "view");
            assert_eq!(accesses.len(), 1);
            assert!(matches!(accesses[0], Access::Move(_)), "{tail}");
        }
        let (body, plan) = classify(
            "(#struct Holder () (: view (#ref-mut #u64)))
             (#fn work (: view (#ref-mut #u64)) Holder
               (#return (#struct-literal Holder (: view view))))",
        );
        assert!(matches!(
            named(&body, plan.as_ref().unwrap(), "view")[0],
            Access::Move(_)
        ));
    }

    #[test]
    fn copied_handles_do_not_need_exclusive_storage_classification() {
        let (_, plan) = classify("(#fn work (: view (#ref #u64)) (#ref #u64) (#return view))");
        assert!(plan.is_none());
    }
}
