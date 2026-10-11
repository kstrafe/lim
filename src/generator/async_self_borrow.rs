//! Representation planning for references into a stationary async frame.
//!
//! Ordinary source loan analysis remains the authority for access and escape
//! checks. This module identifies thin selected handles that can be stored as
//! raw pointers and materialized for an individual poll operation. Boundary
//! references retain separate lifetime-bearing captures.
use std::collections::{HashMap, HashSet};

use crate::generator::async_exec::{Action, AddressRoot, Graph, ValueId};
use crate::typed_body::{BindingId, Body, PlaceRoot};
use crate::typed_flow::{FlowGraph, FlowNodeId, LoanOrigin};
use crate::typed_ir::Declarations;
use crate::Type;

#[derive(Default)]
pub(crate) struct Plan {
    pub bindings: HashMap<BindingId, Vec<crate::typed_place::Place>>,
    pub values: HashMap<ValueId, Vec<crate::typed_place::Place>>,
    /// Real boundary references retained separately from erased selected handles.
    pub external_parameters: HashSet<BindingId>,
    /// Owning cells whose references depend on local stationary storage.
    pub dependent_bindings: HashMap<BindingId, Vec<BindingId>>,
    pub dependent_values: HashMap<ValueId, Vec<BindingId>>,
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
    if local
        && origins.iter().any(|origin| {
            !internal(origin)
                && (!matches!(origin.place.root, PlaceRoot::Parameter(_))
                    || origin.owned_allocation
                    || origin.lifetime_only)
        })
    {
        return Err("selected external async anchors require a checked reference parameter".into());
    }
    Ok(local)
}

fn anchor(origins: &[LoanOrigin]) -> Result<Option<Vec<crate::typed_place::Place>>, String> {
    if !classify(origins)? {
        return Ok(None);
    }
    let mut places = Vec::new();
    for origin in origins {
        if !places.contains(&origin.place) {
            places.push(origin.place.clone());
        }
    }
    if places.iter().any(|place| {
        place.segments.iter().any(|segment| {
            !matches!(
                segment,
                crate::typed_place::Segment::Field(_)
                    | crate::typed_place::Segment::Tuple(_)
                    | crate::typed_place::Segment::Index(_)
            )
        })
    }) {
        return Err(
            "internal reference anchors require checked static struct/tuple/array projections"
                .into(),
        );
    }
    Ok(Some(places))
}

pub(crate) fn direct_place(
    graph: &Graph,
    body: &Body,
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
            AddressProjection::Index(index) => graph.values[index.0]
                .source
                .and_then(|source| crate::typed_place::literal_index(body, source))
                .map(Segment::Index)
                .ok_or_else(|| "internal array anchors require a checked constant index".into()),
            _ => Err(
                "internal reference anchors require checked static struct/tuple/array projections"
                    .into(),
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
                let owners = internal_owners(&all);
                if !owners.is_empty() {
                    plan.dependent_bindings.insert(BindingId(index), owners);
                }
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
                    let owners = internal_owners(&loans);
                    if !owners.is_empty() {
                        plan.dependent_values.insert(ValueId(index), owners);
                    }
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
                        .or_insert(vec![at(direct_place(graph, body, place), action.span)?]);
                }
            }
        }
        for place in plan.bindings.values().chain(plan.values.values()).flatten() {
            if let PlaceRoot::Parameter(binding) = place.root {
                if !thin(&graph.bindings[binding.0].ty) {
                    return Err(Error {
                        message:
                            "selected external async anchors require a thin reference parameter"
                                .into(),
                        span: graph.bindings[binding.0].span,
                    });
                }
                plan.external_parameters.insert(binding);
            }
        }
        // The parameter's real reference moves into a hidden capture, not into
        // an erased source cell. The source binding uses a pointer to the same
        // referent and is reconstructed from that lifetime-bearing capture.
        for &binding in &plan.external_parameters {
            plan.bindings.insert(
                binding,
                vec![crate::typed_place::Place::root(PlaceRoot::Parameter(
                    binding,
                ))],
            );
        }
        Ok(plan)
    }

    /// Declaration-only child factories have no ordinary return-loan summary
    /// during planning. Their implementation retains every argument in its
    /// initial frame; account for those captures without fabricating a layout
    /// or granting access permissions. Final ordinary checking remains required.
    pub(crate) fn retain_async_captures(
        &mut self,
        graph: &Graph,
        declarations: &Declarations,
        interfaces: &crate::generator::async_interfaces::Registry,
    ) {
        use crate::generator::async_exec::Compute;
        fn merge(
            map: &mut HashMap<ValueId, Vec<BindingId>>,
            dst: ValueId,
            owners: Vec<BindingId>,
        ) -> bool {
            let entry = map.entry(dst).or_default();
            let old = entry.len();
            for owner in owners {
                if !entry.contains(&owner) {
                    entry.push(owner);
                }
            }
            entry.sort_by_key(|owner| owner.0);
            entry.len() != old
        }
        loop {
            let mut changed = false;
            for action in graph.blocks.iter().flat_map(|block| &block.actions) {
                match &action.action {
                    Action::Compute {
                        dst,
                        operation: Compute::Checked(operation),
                    } if operation.callee.is_some_and(|callee| {
                        interfaces
                            .functions
                            .get(&declarations.function(callee).name)
                            .is_some_and(|interface| {
                                interface.provenance
                                    == crate::generator::async_interfaces::Provenance::AsyncStart
                            })
                    }) =>
                    {
                        let mut owners = Vec::new();
                        for operand in &operation.operands {
                            if let Some(places) = self.values.get(&operand.value) {
                                for place in places {
                                    if let PlaceRoot::Local(owner) = place.root {
                                        owners.push(owner);
                                    }
                                }
                            }
                            owners.extend(
                                self.dependent_values
                                    .get(&operand.value)
                                    .into_iter()
                                    .flatten()
                                    .copied(),
                            );
                        }
                        changed |= merge(&mut self.dependent_values, *dst, owners);
                    }
                    Action::Bind { binding, value, .. } => {
                        let owners = self
                            .dependent_values
                            .get(value)
                            .cloned()
                            .unwrap_or_default();
                        let entry = self.dependent_bindings.entry(*binding).or_default();
                        for owner in owners {
                            if !entry.contains(&owner) {
                                entry.push(owner);
                                changed = true;
                            }
                        }
                        entry.sort_by_key(|owner| owner.0);
                    }
                    Action::Store { place, value } => {
                        if let AddressRoot::Local(binding) = graph.places[place.0].root {
                            let owners = self
                                .dependent_values
                                .get(value)
                                .cloned()
                                .unwrap_or_default();
                            let entry = self.dependent_bindings.entry(binding).or_default();
                            for owner in owners {
                                if !entry.contains(&owner) {
                                    entry.push(owner);
                                    changed = true;
                                }
                            }
                            entry.sort_by_key(|owner| owner.0);
                        }
                    }
                    Action::Load { dst, place, .. } => {
                        if let AddressRoot::Local(binding) = graph.places[place.0].root {
                            changed |= merge(
                                &mut self.dependent_values,
                                *dst,
                                self.dependent_bindings
                                    .get(&binding)
                                    .cloned()
                                    .unwrap_or_default(),
                            );
                        }
                    }
                    Action::Compute {
                        dst,
                        operation: Compute::Identity(value),
                    } => {
                        let owners = self
                            .dependent_values
                            .get(value)
                            .cloned()
                            .unwrap_or_default();
                        changed |= merge(&mut self.dependent_values, *dst, owners);
                    }
                    _ => {}
                }
            }
            for block in &graph.blocks {
                use crate::generator::async_exec::{Argument, Terminator};
                let edges = match &block.terminator {
                    Terminator::Goto(edge) => vec![edge],
                    Terminator::Branch { yes, no, .. }
                    | Terminator::PatternTest { yes, no, .. } => vec![yes, no],
                    Terminator::Await { ready, .. } => vec![ready],
                    _ => Vec::new(),
                };
                for edge in edges {
                    for (argument, parameter) in edge
                        .arguments
                        .iter()
                        .zip(&graph.blocks[edge.target.0].parameters)
                    {
                        if let Argument::Value(value) = argument {
                            let owners = self
                                .dependent_values
                                .get(value)
                                .cloned()
                                .unwrap_or_default();
                            changed |= merge(&mut self.dependent_values, *parameter, owners);
                        }
                    }
                }
            }
            if !changed {
                break;
            }
        }
        self.dependent_bindings
            .retain(|_, owners| !owners.is_empty());
        self.dependent_values.retain(|_, owners| !owners.is_empty());
    }
}

fn internal_owners(origins: &[LoanOrigin]) -> Vec<BindingId> {
    let mut owners = Vec::new();
    for origin in origins.iter().filter(|origin| internal(origin)) {
        if let PlaceRoot::Local(binding) = origin.place.root {
            if !owners.contains(&binding) {
                owners.push(binding);
            }
        }
    }
    owners.sort_by_key(|binding| binding.0);
    owners
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
    fn selected_internal_handles_retain_all_checked_static_anchors() {
        let plan = plan(
            "(#fn work (: choose #bool) #u64
          (#let left #u64 40u64) (#let right #u64 50u64)
          (#let view (#ref #u64) (#if choose (#borrow left) (#borrow right)))
          (#let result #u64 (#deref view))
          (#drop view) (#forget left) (#forget right) (#return result))",
        )
        .unwrap();
        assert!(plan.bindings.values().any(|places| places.len() == 2));
        assert!(plan.values.values().any(|places| places.len() == 2));
    }

    #[test]
    fn mixed_internal_external_handles_retain_reference_parameters() {
        let plan = plan(
            "(#fn work (: external (#ref #u64) : choose #bool) #u64
          (#let owner #u64 40u64)
          (#let view (#ref #u64) (#if choose (#borrow owner) external))
          (#drop view) (#forget owner) (#return 0u64))",
        )
        .unwrap();
        assert_eq!(plan.external_parameters.len(), 1);
        assert!(plan.bindings.values().any(|places| places
            .iter()
            .any(|place| matches!(place.root, PlaceRoot::Parameter(_)))
            && places
                .iter()
                .any(|place| matches!(place.root, PlaceRoot::Local(_)))));
    }

    #[test]
    fn aggregates_record_dependencies_for_in_place_cleanup() {
        let plan = plan(
            "(#struct Held (: view (#ref #u64)))
          (#fn work () #u64
            (#let owner #u64 40u64)
            (#let held Held (#struct-literal Held (: view (#borrow owner))))
            (#forget held) (#forget owner) (#return 0u64))",
        )
        .unwrap();
        assert_eq!(plan.dependent_bindings.len(), 1);
        assert!(!plan.dependent_values.is_empty());
    }
}
