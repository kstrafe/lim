//! Representation planning for references into a stationary async frame.
//!
//! Ordinary source loan analysis remains the authority for access and escape
//! checks. This module only identifies thin internal handles that can be
//! stored as raw pointers and materialized for an individual poll operation.
use std::collections::HashMap;

use crate::generator::async_exec::{Action, AddressRoot, Graph, ValueId};
use crate::typed_body::{BindingId, Body, PlaceRoot};
use crate::typed_flow::{FlowGraph, FlowNodeId, LoanOrigin};
use crate::typed_ir::Declarations;
use crate::Type;

#[derive(Default)]
pub(crate) struct Plan {
    pub bindings: HashMap<BindingId, crate::typed_place::Place>,
    pub values: HashMap<ValueId, crate::typed_place::Place>,
}

#[derive(Debug)]
pub(crate) struct Error {
    pub message: String,
    pub span: Option<crate::Span>,
}

fn at<T>(result: Result<T, String>, span: Option<crate::Span>) -> Result<T, Error> {
    result.map_err(|message| Error { message, span })
}

fn internal(origin: &LoanOrigin) -> bool {
    matches!(origin.place.root, PlaceRoot::Local(_))
        && !origin.owned_allocation
        && !origin.lifetime_only
        && !origin
            .place
            .segments
            .iter()
            .any(|segment| matches!(segment, crate::typed_place::Segment::Dereference))
}

fn classify(origins: &[LoanOrigin]) -> Result<bool, String> {
    let local = origins.iter().any(internal);
    if local && origins.iter().any(|origin| !internal(origin)) {
        return Err(
            "async handles mixing frame-local and external referents require separate storage"
                .into(),
        );
    }
    Ok(local)
}

fn anchor(origins: &[LoanOrigin]) -> Result<Option<crate::typed_place::Place>, String> {
    if !classify(origins)? {
        return Ok(None);
    }
    let mut places = origins
        .iter()
        .filter(|origin| internal(origin))
        .map(|origin| &origin.place);
    let first = places.next().unwrap();
    if places.any(|place| place != first) {
        return Err("async handles selecting different frame-local referents require a checked selected-anchor representation".into());
    }
    if first.segments.iter().any(|segment| {
        !matches!(
            segment,
            crate::typed_place::Segment::Field(_) | crate::typed_place::Segment::Tuple(_)
        )
    }) {
        return Err(
            "internal reference anchors require checked static struct/tuple projections".into(),
        );
    }
    Ok(Some(first.clone()))
}

pub(crate) fn direct_place(
    graph: &Graph,
    place: crate::generator::async_exec::PlaceId,
) -> Result<crate::typed_place::Place, String> {
    use crate::generator::async_exec::AddressProjection;
    use crate::typed_place::Segment;
    let descriptor = &graph.places[place.0];
    let AddressRoot::Local(binding) = descriptor.root else {
        return Err("internal reference anchor must name a frame owner".into());
    };
    let segments = descriptor
        .projections
        .iter()
        .map(|projection| match projection {
            AddressProjection::Field(field) => Ok(Segment::Field(*field)),
            AddressProjection::Tuple(index) => Ok(Segment::Tuple(*index)),
            _ => Err(
                "internal reference anchors require checked static struct/tuple projections".into(),
            ),
        })
        .collect::<Result<Vec<_>, String>>()?;
    Ok(crate::typed_place::Place {
        root: PlaceRoot::Local(binding),
        segments,
    })
}

impl Plan {
    pub(crate) fn new(
        graph: &Graph,
        body: &Body,
        flow: &FlowGraph,
        declarations: &Declarations,
        stationary: bool,
    ) -> Result<Self, Error> {
        if !stationary
            || !graph
                .blocks
                .iter()
                .flat_map(|block| &block.actions)
                .any(|action| {
                    matches!(action.action, Action::Borrow { place, pinned: false, .. }
                if matches!(graph.places[place.0].root, AddressRoot::Local(_)))
                })
        {
            return Ok(Self::default());
        }
        let origins = flow.loan_origins(body);
        let thin = |ty: &Type| {
            matches!(
                crate::typed_ir::resolve_type(ty, &declarations.aliases),
                Ok(Type::Reference { .. })
            )
        };
        let mut plan = Self::default();
        for (index, binding) in graph.bindings.iter().enumerate() {
            let mut all = Vec::new();
            for event in 0..flow.nodes.len() {
                for origin in origins
                    .before(FlowNodeId(event), BindingId(index))
                    .iter()
                    .chain(origins.after(FlowNodeId(event), BindingId(index)))
                {
                    if !all.contains(origin) {
                        all.push(origin.clone());
                    }
                }
            }
            if !thin(&binding.ty) {
                at(reject_retained_internal(&all), binding.span)?;
                continue;
            }
            if let Some(place) = at(anchor(&all), binding.span)? {
                plan.bindings.insert(BindingId(index), place);
            }
        }
        for (index, value) in graph.values.iter().enumerate() {
            if let Some(source) = value.source {
                let loans = origins.value_before(body, flow, FlowNodeId(0), source);
                if !thin(&value.ty) {
                    at(reject_retained_internal(&loans), value.span)?;
                    continue;
                }
                if let Some(place) = at(anchor(&loans), value.span)? {
                    plan.values.insert(ValueId(index), place);
                }
            }
        }
        // A directly formed address is known even if its expression has no
        // completion snapshot in the ordinary analysis graph.
        for action in graph.blocks.iter().flat_map(|block| &block.actions) {
            if let Action::Borrow {
                dst: Some(value),
                place,
                pinned: false,
                ..
            } = action.action
            {
                if matches!(graph.places[place.0].root, AddressRoot::Local(_)) {
                    plan.values
                        .entry(value)
                        .or_insert(at(direct_place(graph, place), action.span)?);
                }
            }
        }
        Ok(plan)
    }
}

// Cleanup currently exports owning cells by value. A child or aggregate with
// a pointer into its parent cannot accompany a moved referent. Until cleanup
// can destroy dependents in place, reject this representation rather than
// losing that lifetime when the thin reference is erased.
fn reject_retained_internal(origins: &[LoanOrigin]) -> Result<(), String> {
    if origins
        .iter()
        .any(|origin| internal(origin) && !origin.pinned)
    {
        Err("async aggregates or child futures retaining frame-local borrows require in-place cancellation before owner extraction".into())
    } else {
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn plan(source: &str) -> Result<Plan, String> {
        let program = crate::parse_program(source).unwrap();
        let declarations = crate::typecheck::resolve_program_for_analysis(&program, true).unwrap();
        let body = &declarations.bodies["work"];
        let graph = crate::generator::async_exec::build(body, &[]).unwrap();
        Plan::new(
            &graph,
            body,
            &declarations.flows["work"],
            &declarations,
            true,
        )
        .map_err(|error| error.message)
    }

    #[test]
    fn only_internal_thin_references_lose_their_physical_lifetime() {
        let plan = plan(
            "(#fn work (: external (#ref #u64)) #u64
          (#let owner #u64 40u64)
          (#let view (#ref #u64) (#borrow owner))
          (#let outside (#ref #u64) external)
          (#drop outside) (#drop view) (#forget owner) (#return 0u64))",
        )
        .unwrap();
        assert_eq!(plan.bindings.len(), 1);
        assert!(!plan.values.is_empty());
    }

    #[test]
    fn mixed_internal_external_handles_cannot_erase_caller_lifetimes() {
        let error = plan(
            "(#fn work (: external (#ref #u64) : choose #bool) #u64
          (#let owner #u64 40u64)
          (#let view (#ref #u64) (#if choose (#borrow owner) external))
          (#drop view) (#forget owner) (#return 0u64))",
        )
        .err()
        .unwrap();
        assert!(error.contains("mixing frame-local and external"), "{error}");
    }

    #[test]
    fn aggregates_cannot_export_a_pointer_into_an_extracted_owner() {
        let error = plan(
            "(#struct Held (: view (#ref #u64)))
          (#fn work () #u64
            (#let owner #u64 40u64)
            (#let held Held (#struct-literal Held (: view (#borrow owner))))
            (#forget held) (#forget owner) (#return 0u64))",
        )
        .err()
        .unwrap();
        assert!(error.contains("in-place cancellation"), "{error}");
    }
}
