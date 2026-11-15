//! Retirement of evaluated reference handles in the ordinary async dispatcher.
//! Implementation detail of built-in code generation, not runtime semantics.
//!
//! This verifies value-cell availability, not ownership or borrow permission.
//! Source and generated ordinary bodies still require their original proofs.
//! Places remain recipes in the current emitter, so each use retains their
//! evaluated roots/indices, not only the graph's formed address token.
#![allow(dead_code)]

use std::cell::OnceCell;
use std::collections::{HashMap, HashSet};

use crate::generator::async_exec::{
    Action, AddressProjection, AddressRoot, Argument, BlockId, Compute, Edge, Graph, PlaceId,
    Terminator, ValueId,
};
use crate::linearcheck::LinearTypes;
use crate::typed_body::BindingId;

#[derive(Debug)]
pub(crate) struct Plan {
    pub entry: Vec<Vec<ValueId>>,
    pub after_action: Vec<Vec<Vec<ValueId>>>,
    /// Goto: 0; branch/pattern: yes 0, no 1; await: Ready 0, Pending 1.
    /// Normal edges clear AFTER staging arguments but BEFORE destination puts.
    pub edge: Vec<Vec<Vec<ValueId>>>,
    /// Dead non-owning exclusive input/local holders, not their referents. A
    /// child may retain a reborrow after the source holder's last use.
    pub pending_bindings: Vec<Vec<BindingId>>,
    candidates: HashSet<ValueId>,
    binding_candidates: HashSet<BindingId>,
}

pub(crate) fn edges(terminal: &Terminator) -> Vec<&Edge> {
    match terminal {
        Terminator::Goto(edge) => vec![edge],
        Terminator::Branch { yes, no, .. } | Terminator::PatternTest { yes, no, .. } => {
            vec![yes, no]
        }
        Terminator::Await { ready, .. } => vec![ready],
        _ => vec![],
    }
}

fn recipe(place: &crate::generator::async_exec::PlaceDescriptor) -> Vec<ValueId> {
    let mut values = Vec::new();
    if let AddressRoot::Value(value) = place.root {
        values.push(value);
    }
    for step in &place.projections {
        if let AddressProjection::Index(value) | AddressProjection::SliceIndex(value) = step {
            values.push(*value);
        }
    }
    // Checked descriptors include the complete parent prefix, not a suffix.
    values
}

/// Physical dependencies from one immutable graph snapshot. In particular,
/// closing each lending scope must not scan every borrow in the graph again.
/// This is a use index, not a cache of ownership or loan-solving results.
pub(crate) struct PhysicalUses<'a> {
    graph: &'a Graph,
    scopes: HashMap<crate::typed_body::NodeId, Vec<ValueId>>,
    clone_uses: OnceCell<CloneUses>,
}

struct CloneUses {
    total: Vec<usize>,
    places: HashMap<(PlaceId, ValueId), usize>,
    loads: HashMap<(ValueId, ValueId), usize>,
}

impl<'a> PhysicalUses<'a> {
    pub(crate) fn new(graph: &'a Graph) -> Self {
        let mut scopes = HashMap::<_, Vec<_>>::new();
        for located in graph.blocks.iter().flat_map(|block| &block.actions) {
            if let Action::Borrow {
                scope: Some(scope),
                place,
                ..
            } = located.action
            {
                scopes
                    .entry(scope)
                    .or_default()
                    .extend(recipe(&graph.places[place.0]));
            }
        }
        Self {
            graph,
            scopes,
            clone_uses: OnceCell::new(),
        }
    }

    pub(crate) fn uses(&self, action: &Action) -> Vec<ValueId> {
        match action {
            Action::EndBorrow { scope } => self.scopes.get(scope).cloned().unwrap_or_default(),
            _ => uses(self.graph, action),
        }
    }

    /// Match the emitter's whole-graph retention query, including unreachable
    /// actions. Exclude only this clone's place formation and result load.
    /// Build lazily: ordinary retirement/lending queries need no clone index.
    pub(crate) fn retained_after_clone(
        &self,
        value: ValueId,
        place: PlaceId,
        result: ValueId,
    ) -> bool {
        let index = self.clone_use_index();
        index.total[value.0]
            > index.places.get(&(place, value)).copied().unwrap_or(0)
                + index.loads.get(&(result, value)).copied().unwrap_or(0)
    }

    /// Projected clones also form parent address recipes. Those formations
    /// are part of this clone, not retained owning uses; actual later loads,
    /// borrows, stores, releases and edge arguments still retain the source.
    pub(crate) fn retained_after_projected_clone(
        &self,
        value: ValueId,
        place: PlaceId,
        result: ValueId,
    ) -> bool {
        let index = self.clone_use_index();
        let mut excluded = index.loads.get(&(result, value)).copied().unwrap_or(0);
        let mut current = Some(place);
        while let Some(place) = current {
            excluded += index.places.get(&(place, value)).copied().unwrap_or(0);
            current = self.graph.places[place.0].parent;
        }
        index.total[value.0] > excluded
    }

    fn clone_use_index(&self) -> &CloneUses {
        self.clone_uses.get_or_init(|| {
            let mut index = CloneUses {
                total: vec![0; self.graph.values.len()],
                places: HashMap::new(),
                loads: HashMap::new(),
            };
            for block in &self.graph.blocks {
                for located in &block.actions {
                    let mut values = self.uses(&located.action);
                    values.sort_unstable_by_key(|value| value.0);
                    values.dedup();
                    for value in values {
                        index.total[value.0] += 1;
                        match located.action {
                            Action::Place { dst, .. } => {
                                *index.places.entry((dst, value)).or_default() += 1;
                            }
                            Action::Load { dst, .. } => {
                                *index.loads.entry((dst, value)).or_default() += 1;
                            }
                            _ => {}
                        }
                    }
                }
                let mut values = control(&block.terminator);
                values.extend(edges(&block.terminator).iter().flat_map(|edge| {
                    edge.arguments.iter().filter_map(|argument| match argument {
                        Argument::Value(value) => Some(*value),
                        _ => None,
                    })
                }));
                values.sort_unstable_by_key(|value| value.0);
                values.dedup();
                for value in values {
                    index.total[value.0] += 1;
                }
            }
            index
        })
    }
}

// Physical emitter dependencies, including roots of address recipes. The
// lending-window verifier must use these too: graph address tokens alone do
// not describe a root that the current emitter will evaluate at a later load.
pub(crate) fn uses(graph: &Graph, action: &Action) -> Vec<ValueId> {
    match action {
        Action::Compute {
            operation: Compute::Checked(operation),
            ..
        } => operation
            .operands
            .iter()
            .map(|operand| operand.value)
            .collect(),
        Action::Compute {
            operation: Compute::Identity(value),
            ..
        }
        | Action::Bind { value, .. } => vec![*value],
        Action::Place { descriptor, .. } => recipe(descriptor),
        Action::Load { place, .. }
        | Action::Borrow { place, .. }
        | Action::Release { place, .. } => recipe(&graph.places[place.0]),
        Action::Store { place, value } => {
            let mut values = recipe(&graph.places[place.0]);
            values.push(*value);
            values
        }
        Action::Preview(pattern) | Action::Commit(pattern) | Action::EndPreview(pattern) => {
            vec![pattern.scrutinee]
        }
        Action::EndBorrow { scope } => graph
            .blocks
            .iter()
            .flat_map(|block| &block.actions)
            .filter_map(|located| match &located.action {
                Action::Borrow {
                    scope: Some(found),
                    place,
                    ..
                } if found == scope => Some(*place),
                _ => None,
            })
            .flat_map(|place| recipe(&graph.places[place.0]))
            .collect(),
        _ => vec![],
    }
}

fn definition(action: &Action) -> Option<ValueId> {
    match action {
        Action::Compute { dst, .. }
        | Action::Load { dst, .. }
        | Action::Borrow { dst: Some(dst), .. } => Some(*dst),
        _ => None,
    }
}

pub(crate) fn control(terminal: &Terminator) -> Vec<ValueId> {
    match terminal {
        Terminator::Branch { condition, .. } => vec![*condition],
        Terminator::PatternTest { pattern, .. } => vec![pattern.scrutinee],
        Terminator::Await { child, .. } => vec![*child],
        Terminator::Return(Some(value)) => vec![*value],
        _ => vec![],
    }
}

fn sorted(values: impl IntoIterator<Item = ValueId>) -> Vec<ValueId> {
    let mut values = values.into_iter().collect::<Vec<_>>();
    values.sort_by_key(|value| value.0);
    values.dedup();
    values
}

fn pending_binding_retirement(
    graph: &Graph,
    candidates: &HashSet<BindingId>,
) -> Vec<Vec<BindingId>> {
    if candidates.is_empty() {
        return vec![vec![]; graph.blocks.len()];
    }
    let mut entry = vec![HashSet::new(); graph.blocks.len()];
    let reachable = graph.reachable();
    loop {
        let mut changed = false;
        for block in &reachable {
            let body = &graph.blocks[block.0];
            let mut held = HashSet::new();
            for successor in graph.successors(*block) {
                held.extend(entry[successor.0].iter().copied());
            }
            for located in body.actions.iter().rev() {
                match &located.action {
                    Action::Bind { binding, .. } => {
                        held.remove(binding);
                    }
                    Action::ScopeEnter(bindings) | Action::ScopeExit(bindings) => {
                        for binding in bindings {
                            held.remove(binding);
                        }
                    }
                    Action::Commit(pattern)
                    | Action::Preview(pattern)
                    | Action::EndPreview(pattern) => {
                        for binding in &pattern.bindings {
                            held.remove(binding);
                        }
                    }
                    Action::Place { descriptor, .. } => {
                        if let AddressRoot::Local(binding) = descriptor.root {
                            if candidates.contains(&binding) {
                                held.insert(binding);
                            }
                        }
                    }
                    Action::Load { place, .. }
                    | Action::Borrow { place, .. }
                    | Action::Store { place, .. }
                    | Action::Release { place, .. } => {
                        if let AddressRoot::Local(binding) = graph.places[place.0].root {
                            if candidates.contains(&binding) {
                                held.insert(binding);
                            }
                        }
                    }
                    _ => {}
                }
            }
            if held != entry[block.0] {
                entry[block.0] = held;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    graph
        .blocks
        .iter()
        .map(|block| {
            let Terminator::Await { pending, ready, .. } = &block.terminator else {
                return vec![];
            };
            let mut retired = candidates
                .iter()
                .filter(|binding| {
                    !entry[pending.0].contains(binding) && !entry[ready.target.0].contains(binding)
                })
                .copied()
                .collect::<Vec<_>>();
            retired.sort_by_key(|binding| binding.0);
            retired
        })
        .collect()
}

impl Plan {
    /// A selected internal address can keep its source holder alive even
    /// without another lexical read. Such frame storage is not dead merely
    /// because later graph operations use the derived value instead.
    pub(crate) fn protect_binding_anchors(&mut self, graph: &Graph, anchors: &HashSet<BindingId>) {
        if !self
            .binding_candidates
            .iter()
            .any(|binding| anchors.contains(binding))
        {
            return;
        }
        self.binding_candidates
            .retain(|binding| !anchors.contains(binding));
        self.pending_bindings = pending_binding_retirement(graph, &self.binding_candidates);
    }

    pub fn new(graph: &Graph, types: &LinearTypes) -> Option<Self> {
        Self::with_exclusive_handles(graph, types, &HashSet::new(), &HashMap::new())
    }

    /// Additional candidates are materialized direct exclusive references,
    /// not owning aggregates. References have no linear destruction obligation;
    /// retiring their holder does not destroy the pointee or returned children.
    pub fn with_exclusive_handles(
        graph: &Graph,
        types: &LinearTypes,
        handles: &HashSet<ValueId>,
        aliases: &HashMap<String, crate::Type>,
    ) -> Option<Self> {
        Self::with_lending_snapshots(graph, types, handles, aliases, None)
    }

    /// Synthetic slice reborrows may end after their last physical use. Their
    /// source holders remain linear and require explicit source consumption.
    /// Only a checked lending certificate authorizes these extra candidates.
    pub fn with_lending_snapshots(
        graph: &Graph,
        types: &LinearTypes,
        handles: &HashSet<ValueId>,
        aliases: &HashMap<String, crate::Type>,
        lending: Option<&super::async_lease::Plan>,
    ) -> Option<Self> {
        let candidates = graph
            .values
            .iter()
            .enumerate()
            .filter_map(|(index, value)| {
                ((types.can_repeat(&value.ty) && types.contains_reference(&value.ty))
                    || (handles.contains(&ValueId(index))
                        && crate::typed_ir::resolve_type(&value.ty, aliases).is_ok_and(|ty| {
                            matches!(
                                ty,
                                crate::Type::Reference { mutable: true, .. }
                                    | crate::Type::PinnedReference { mutable: true, .. }
                            )
                        }))
                    || (lending.is_some_and(|plan| {
                        plan.snapshot(ValueId(index)).is_some()
                            || plan.projected_snapshot(ValueId(index)).is_some()
                    }) && matches!(
                        crate::typed_ir::resolve_type(&value.ty, aliases),
                        Ok(crate::Type::MutableSlice(_))
                    )))
                .then_some(ValueId(index))
            })
            .collect::<HashSet<_>>();
        let binding_candidates = graph
            .bindings
            .iter()
            .enumerate()
            .filter_map(|(index, binding)| {
                (types.contains_reference(&binding.ty)
                    && !types.is_linear(&binding.ty)
                    && !types.can_repeat(&binding.ty))
                .then_some(BindingId(index))
            })
            .collect::<HashSet<_>>();
        let pending_bindings = pending_binding_retirement(graph, &binding_candidates);
        if candidates.is_empty() && pending_bindings.iter().all(Vec::is_empty) {
            return None;
        }
        let mut live = graph.reachable().into_iter().collect::<Vec<_>>();
        live.sort_by_key(|block| block.0);
        let selected = |values: Vec<ValueId>| {
            values
                .into_iter()
                .filter(|value| candidates.contains(value))
                .collect::<HashSet<_>>()
        };
        let physical_uses = PhysicalUses::new(graph);
        let action_uses = graph
            .blocks
            .iter()
            .map(|block| {
                block
                    .actions
                    .iter()
                    .map(|located| {
                        let mut uses = physical_uses.uses(&located.action);
                        if let Some(lending) = lending {
                            lending.extend_physical_uses(graph, &mut uses);
                        }
                        selected(uses)
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let mut entry = vec![HashSet::new(); graph.blocks.len()];
        let mut external = entry.clone();
        // May-live sets grow from bottom, including cyclic and Pending edges.
        loop {
            let mut changed = false;
            for &block in &live {
                let body = &graph.blocks[block.0];
                let mut held = selected(control(&body.terminator));
                for edge in edges(&body.terminator) {
                    held.extend(external[edge.target.0].iter().copied());
                    held.extend(edge.arguments.iter().filter_map(|argument| match argument {
                        Argument::Value(value) if candidates.contains(value) => Some(*value),
                        _ => None,
                    }));
                }
                if let Terminator::Await { pending, .. } = body.terminator {
                    held.extend(entry[pending.0].iter().copied());
                }
                for (index, located) in body.actions.iter().enumerate().rev() {
                    if let Some(dst) = definition(&located.action) {
                        held.remove(&dst);
                    }
                    held.extend(action_uses[block.0][index].iter().copied());
                }
                let mut outside = held.clone();
                for parameter in &body.parameters {
                    outside.remove(parameter);
                }
                changed |= held != entry[block.0] || outside != external[block.0];
                entry[block.0] = held;
                external[block.0] = outside;
            }
            if !changed {
                break;
            }
        }
        let mut plan = Self {
            pending_bindings,
            binding_candidates,
            entry: vec![vec![]; graph.blocks.len()],
            after_action: graph
                .blocks
                .iter()
                .map(|block| vec![vec![]; block.actions.len()])
                .collect(),
            edge: graph
                .blocks
                .iter()
                .enumerate()
                .map(|(index, _)| vec![vec![]; graph.successors(BlockId(index)).len()])
                .collect(),
            candidates: candidates.clone(),
        };
        for &block in &live {
            let body = &graph.blocks[block.0];
            plan.entry[block.0] = sorted(body.parameters.iter().copied().filter(|value| {
                plan.candidates.contains(value) && !entry[block.0].contains(value)
            }));
            let mut held = selected(control(&body.terminator));
            for edge in edges(&body.terminator) {
                held.extend(external[edge.target.0].iter().copied());
                held.extend(edge.arguments.iter().filter_map(|argument| match argument {
                    Argument::Value(value) if plan.candidates.contains(value) => Some(*value),
                    _ => None,
                }));
            }
            if let Terminator::Await { pending, .. } = body.terminator {
                held.extend(entry[pending.0].iter().copied());
            }
            for (index, edge) in edges(&body.terminator).into_iter().enumerate() {
                plan.edge[block.0][index] =
                    sorted(held.difference(&external[edge.target.0]).copied());
            }
            if let Terminator::Await { pending, .. } = body.terminator {
                // A poll entry receives a physical frame, not the graph's
                // definite-value set. Dead optional cells can still contain
                // old handles from a prior state. Before returning Pending,
                // make ALL non-retry value cells visibly Empty, including
                // cells not defined on this selected path. Clearing Empty is
                // valid; reference-handle retirement never destroys a referent.
                plan.edge[block.0][1] = sorted(candidates.difference(&entry[pending.0]).copied());
            }
            for (index, located) in body.actions.iter().enumerate().rev() {
                let mut touched = action_uses[block.0][index].clone();
                if let Some(dst) =
                    definition(&located.action).filter(|dst| plan.candidates.contains(dst))
                {
                    touched.insert(dst);
                }
                plan.after_action[block.0][index] = sorted(touched.difference(&held).copied());
                if let Some(dst) = definition(&located.action) {
                    held.remove(&dst);
                }
                held.extend(action_uses[block.0][index].iter().copied());
            }
        }
        Some(plan)
    }

    /// Check all actual value-cell reads after inserting retirement. Normal
    /// edge parameter stores define their destination; Pending only restores
    /// its child. Entering a block must not invent newly initialized cells.
    pub fn validate(&self, graph: &Graph) -> Result<(), crate::generator::async_exec::Error> {
        let failure = |source, message: &str| crate::generator::async_exec::Error {
            source,
            message: message.into(),
        };
        if self.entry.len() != graph.blocks.len()
            || self.after_action.len() != graph.blocks.len()
            || self.edge.len() != graph.blocks.len()
            || self.pending_bindings.len() != graph.blocks.len()
        {
            return Err(failure(None, "retirement plan has the wrong block count"));
        }
        if self.pending_bindings != pending_binding_retirement(graph, &self.binding_candidates) {
            return Err(failure(
                None,
                "ChildPoll.Pending binding retirement disagrees with source liveness",
            ));
        }
        for (index, block) in graph.blocks.iter().enumerate() {
            if self.after_action[index].len() != block.actions.len()
                || self.edge[index].len() != graph.successors(BlockId(index)).len()
            {
                return Err(failure(
                    None,
                    "retirement plan has the wrong action/edge count",
                ));
            }
            for value in self.entry[index]
                .iter()
                .chain(self.after_action[index].iter().flatten())
                .chain(self.edge[index].iter().flatten())
            {
                if !self.candidates.contains(value) {
                    return Err(failure(
                        None,
                        "retirement attempts to clear a value outside its reference-handle candidates",
                    ));
                }
            }
        }
        let mut live = graph.reachable().into_iter().collect::<Vec<_>>();
        live.sort_by_key(|block| block.0);
        let mut predecessors = vec![Vec::new(); graph.blocks.len()];
        for &source in &live {
            for (index, target) in graph.successors(source).into_iter().enumerate() {
                predecessors[target.0].push((source, index));
            }
        }
        let clear = |held: &mut HashSet<ValueId>, values: &[ValueId]| {
            for value in values {
                held.remove(value);
            }
        };
        let action = |held: &mut HashSet<ValueId>,
                      located: &crate::generator::async_exec::LocatedAction| {
            if let Some(dst) =
                definition(&located.action).filter(|dst| self.candidates.contains(dst))
            {
                held.insert(dst);
            }
        };
        let outgoing = |block: BlockId, mut held: HashSet<ValueId>| {
            clear(&mut held, &self.entry[block.0]);
            for (index, located) in graph.blocks[block.0].actions.iter().enumerate() {
                action(&mut held, located);
                clear(&mut held, &self.after_action[block.0][index]);
            }
            let mut outputs = Vec::new();
            for (index, edge) in edges(&graph.blocks[block.0].terminator)
                .into_iter()
                .enumerate()
            {
                let mut output = held.clone();
                clear(&mut output, &self.edge[block.0][index]);
                output.extend(
                    graph.blocks[edge.target.0]
                        .parameters
                        .iter()
                        .copied()
                        .filter(|value| self.candidates.contains(value)),
                );
                outputs.push(output);
            }
            if let Terminator::Await { child, .. } = graph.blocks[block.0].terminator {
                clear(&mut held, &self.edge[block.0][1]);
                if self.candidates.contains(&child) {
                    held.insert(child);
                }
                outputs.push(held);
            }
            outputs
        };
        let mut before = vec![self.candidates.clone(); graph.blocks.len()];
        let mut after = self
            .edge
            .iter()
            .map(|edges| vec![self.candidates.clone(); edges.len()])
            .collect::<Vec<_>>();
        loop {
            let mut changed = false;
            for &block in &live {
                let mut incoming = if block == graph.entry {
                    HashSet::new()
                } else {
                    self.candidates.clone()
                };
                for &(previous, edge) in &predecessors[block.0] {
                    incoming.retain(|value| after[previous.0][edge].contains(value));
                }
                let output = outgoing(block, incoming.clone());
                changed |= before[block.0] != incoming || after[block.0] != output;
                before[block.0] = incoming;
                after[block.0] = output;
            }
            if !changed {
                break;
            }
        }
        let physical_uses = PhysicalUses::new(graph);
        for block in live {
            let mut held = before[block.0].clone();
            clear(&mut held, &self.entry[block.0]);
            for (index, located) in graph.blocks[block.0].actions.iter().enumerate() {
                if physical_uses
                    .uses(&located.action)
                    .iter()
                    .any(|value| self.candidates.contains(value) && !held.contains(value))
                {
                    return Err(failure(
                        located.source,
                        "emitted operation reads an uninitialized or retired handle cell",
                    ));
                }
                action(&mut held, located);
                clear(&mut held, &self.after_action[block.0][index]);
            }
            let terminal = &graph.blocks[block.0].terminator;
            let mut inputs = control(terminal);
            inputs.extend(
                edges(terminal)
                    .into_iter()
                    .flat_map(|edge| &edge.arguments)
                    .filter_map(|argument| match argument {
                        Argument::Value(value) => Some(*value),
                        _ => None,
                    }),
            );
            if inputs
                .iter()
                .any(|value| self.candidates.contains(value) && !held.contains(value))
            {
                return Err(failure(
                    None,
                    "emitted terminator reads an uninitialized or retired handle cell",
                ));
            }
            // Pending must keep the actual restored child, including when it
            // is also a block parameter. Never clear it after its put.
            if let Terminator::Await { child, .. } = terminal {
                if self.edge[block.0][1].contains(child) {
                    return Err(failure(
                        None,
                        "ChildPoll.Pending retirement clears its restored child",
                    ));
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn prepare(source: &str) -> (Graph, LinearTypes) {
        let program = crate::parse_program(source).unwrap();
        let declarations = crate::typecheck::resolve_program_for_analysis(&program, true).unwrap();
        let graph = crate::generator::async_exec::build(&declarations.bodies["work"], &[]).unwrap();
        graph.validate().unwrap();
        (graph, LinearTypes::from_program(&program))
    }

    fn scoped_graph(count: usize) -> Graph {
        let statements = "(#borrow (#deref view) ())\n".repeat(count);
        prepare(&format!(
            "#fn work ((view (#ref-mut #u64))) () {statements} (#return ())\n"
        ))
        .0
    }

    fn clone_graph(count: usize) -> Graph {
        let statements = (0..count)
            .map(|index| {
                format!(
                    "(#let duplicate{index} Resource (#clone (#call make ((value {index}u64)))))
                 (#forget duplicate{index})"
                )
            })
            .collect::<Vec<_>>()
            .join("\n");
        prepare(&format!(
            "#struct Resource (#linear) ((value #u64))
#fn make ((value #u64)) Resource
                 (#return (#struct-literal Resource ((value value))))
#fn work () () {statements} (#return ())\n"
        ))
        .0
    }

    fn retained_after_clone_scan(
        uses: &PhysicalUses<'_>,
        value: ValueId,
        place: PlaceId,
        result: ValueId,
    ) -> bool {
        uses.graph.blocks.iter().any(|block| {
            block.actions.iter().any(|located| match &located.action {
                Action::Place { dst, .. } if *dst == place => false,
                Action::Load { dst, .. } if *dst == result => false,
                other => uses.uses(other).contains(&value),
            }) || control(&block.terminator).contains(&value)
                || edges(&block.terminator)
                    .iter()
                    .flat_map(|edge| &edge.arguments)
                    .any(|argument| matches!(argument, Argument::Value(actual) if *actual == value))
        })
    }

    #[test]
    fn projected_clone_retention_excludes_only_its_parent_formations() {
        let (mut graph, _) = prepare(
            "#struct Resource (#linear) ((value #u64))
#struct Envelope () ((item (#tuple Resource #u64)))
#fn make () Envelope
                 (#return (#struct-literal Envelope ((item
                   (#tuple (#tuple Resource #u64)
                     (#struct-literal Resource ((value 42u64))) 0u64)))))
#fn work () ()
                 (#let duplicate Resource (#clone (#get (#get (#call make ()) item) 0)))
                 (#forget duplicate) (#return ())\n",
        );
        let (value, place, result) = graph
            .blocks
            .iter()
            .flat_map(|block| &block.actions)
            .find_map(|located| match located.action {
                Action::Load {
                    dst,
                    place,
                    kind: super::super::async_exec::LoadKind::Clone,
                } => match graph.places[place.0].root {
                    AddressRoot::Value(value) => Some((value, place, dst)),
                    _ => None,
                },
                _ => None,
            })
            .unwrap();
        let uses = PhysicalUses::new(&graph);
        assert!(uses.retained_after_clone(value, place, result));
        assert!(!uses.retained_after_projected_clone(value, place, result));
        drop(uses);
        // A real later dependency, including a control input, is not one of
        // those inert formation sites. This synthetic exit tests counting,
        // not permission to return an owner from a unit-returning function.
        graph.blocks.last_mut().unwrap().terminator = Terminator::Return(Some(value));
        assert!(PhysicalUses::new(&graph).retained_after_projected_clone(value, place, result));
    }

    #[test]
    fn clone_retention_index_matches_scan_for_all_exclusion_pairs() {
        let branch = prepare(
            "#fn work ((choose #bool) (value #u64)) #u64
                 (#return (#if choose (#clone value) (#clone (#u64::add-wrap value value))))\n",
        )
        .0;
        for mut graph in [clone_graph(3), scoped_graph(3), branch] {
            let indexed = PhysicalUses::new(&graph);
            assert!(indexed.clone_uses.get().is_none());
            for action in graph.blocks.iter().flat_map(|block| &block.actions) {
                indexed.uses(&action.action);
            }
            assert!(indexed.clone_uses.get().is_none());
            drop(indexed);
            // Preserve baseline behavior even for duplicate formation/load
            // sites in synthetic graphs, rather than subtracting just one use.
            let duplicates = graph.blocks[0].actions.clone();
            graph.blocks[0].actions.extend(duplicates);
            let indexed = PhysicalUses::new(&graph);
            for value in (0..graph.values.len()).map(ValueId) {
                for place in (0..=graph.places.len()).map(PlaceId) {
                    for result in (0..=graph.values.len()).map(ValueId) {
                        assert_eq!(
                            indexed.retained_after_clone(value, place, result),
                            retained_after_clone_scan(&indexed, value, place, result),
                            "value {value:?}, place {place:?}, result {result:?}"
                        );
                    }
                }
            }
        }
    }

    #[test]
    #[ignore = "manual computed clone retention benchmark"]
    fn benchmark_computed_clone_retention() {
        use std::{hint::black_box, time::Instant};
        let graph = clone_graph(1024);
        let queries = graph
            .blocks
            .iter()
            .flat_map(|block| &block.actions)
            .filter_map(|located| match located.action {
                Action::Load {
                    dst,
                    place,
                    kind: super::super::async_exec::LoadKind::Clone,
                } => match graph.places[place.0].root {
                    AddressRoot::Value(value) => Some((value, place, dst)),
                    _ => None,
                },
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(queries.len(), 1024);
        let mut baseline = Vec::new();
        let mut indexed = Vec::new();
        for sample in 0..8 {
            let run = |cached: bool| {
                let start = Instant::now();
                let uses = PhysicalUses::new(black_box(&graph));
                let mut kept = 0;
                for &(value, place, result) in &queries {
                    kept += usize::from(if cached {
                        uses.retained_after_clone(black_box(value), place, result)
                    } else {
                        retained_after_clone_scan(&uses, black_box(value), place, result)
                    });
                }
                (start.elapsed().as_micros(), black_box(kept))
            };
            let (old, new) = if sample % 2 == 0 {
                (run(false), run(true))
            } else {
                let new = run(true);
                (run(false), new)
            };
            assert_eq!(old.1, new.1);
            if sample > 0 {
                baseline.push(old.0);
                indexed.push(new.0);
            }
        }
        baseline.sort_unstable();
        indexed.sort_unstable();
        eprintln!("computed clone retention, 1024 clones, seven samples: baseline {}us, indexed {}us (includes construction)", baseline[3], indexed[3]);
    }

    #[test]
    fn physical_use_index_matches_scoped_and_ordinary_dependencies() {
        let mut graph = scoped_graph(12);
        // A scope may have multiple formation sites, including unreachable
        // ones. Keep the baseline's exact order and duplicates, not just a set.
        let borrowed = graph
            .blocks
            .iter()
            .flat_map(|block| &block.actions)
            .find(|located| matches!(located.action, Action::Borrow { scope: Some(_), .. }))
            .unwrap()
            .clone();
        graph.blocks[0].actions.push(borrowed);
        let indexed = PhysicalUses::new(&graph);
        for located in graph.blocks.iter().flat_map(|block| &block.actions) {
            assert_eq!(indexed.uses(&located.action), uses(&graph, &located.action));
        }
        let missing = Action::EndBorrow {
            scope: crate::typed_body::NodeId(usize::MAX),
        };
        assert_eq!(indexed.uses(&missing), uses(&graph, &missing));
        assert!(indexed.uses(&missing).is_empty());
    }

    #[test]
    #[ignore = "manual scoped lending dependency benchmark"]
    fn benchmark_scoped_physical_uses() {
        use std::{hint::black_box, time::Instant};
        let graph = scoped_graph(1024);
        let mut baseline = Vec::new();
        let mut indexed = Vec::new();
        for sample in 0..8 {
            let run = |cached: bool| {
                let start = Instant::now();
                let index = cached.then(|| PhysicalUses::new(black_box(&graph)));
                let mut sum = 0usize;
                for action in graph.blocks.iter().flat_map(|block| &block.actions) {
                    let values = match &index {
                        Some(index) => index.uses(black_box(&action.action)),
                        None => uses(black_box(&graph), black_box(&action.action)),
                    };
                    for value in values {
                        sum = sum.wrapping_add(value.0 + 1);
                    }
                }
                (start.elapsed().as_micros(), black_box(sum))
            };
            // Alternate ordering; the indexed measurement includes building
            // the snapshot, not just queries on a prewarmed cache.
            let (old, new) = if sample % 2 == 0 {
                (run(false), run(true))
            } else {
                let new = run(true);
                (run(false), new)
            };
            assert_eq!(old.1, new.1);
            if sample > 0 {
                baseline.push(old.0);
                indexed.push(new.0);
            }
        }
        baseline.sort_unstable();
        indexed.sort_unstable();
        eprintln!("scoped physical uses, 1024 scopes, seven samples: baseline {}us, indexed {}us (includes construction)", baseline[3], indexed[3]);
    }

    #[test]
    fn no_handle_values_need_no_plan() {
        let (graph, types) = prepare("#fn work ((value #u64)) #u64 (#return value)\n");
        assert!(Plan::new(&graph, &types).is_none());
        for source in [
            "#fn work ((view (#ref-mut #u64))) #u64 (#return (#deref view))\n",
            "#struct Holder (#linear) ((view (#ref #u64)))
#fn work ((owner Holder)) () (#forget owner) (#return ())\n",
        ] {
            let (graph, types) = prepare(source);
            assert!(
                Plan::new(&graph, &types).is_none(),
                "neither exclusive handles nor linear owners may be retired as Copy values"
            );
        }
    }

    #[test]
    fn handle_roots_live_until_the_place_recipe_is_used() {
        let (graph, types) =
            prepare("#fn work ((view (#ref #u64))) #u64 (#return (#deref view))\n");
        let mut plan = Plan::new(&graph, &types).unwrap();
        plan.validate(&graph).unwrap();
        let (block, index, root) = graph
            .blocks
            .iter()
            .enumerate()
            .find_map(|(block, body)| {
                body.actions
                    .iter()
                    .enumerate()
                    .find_map(|(index, action)| match &action.action {
                        Action::Place { descriptor, .. } => match descriptor.root {
                            AddressRoot::Value(root) if plan.candidates.contains(&root) => {
                                Some((block, index, root))
                            }
                            _ => None,
                        },
                        _ => None,
                    })
            })
            .unwrap();
        assert!(!plan.after_action[block][index].contains(&root));
        assert!(plan.after_action[block]
            .iter()
            .skip(index + 1)
            .any(|retired| retired.contains(&root)));
        plan.after_action[block][index].push(root);
        let error = plan.validate(&graph).unwrap_err();
        assert!(error.message.contains("retired handle cell"), "{error:?}");
    }

    #[test]
    fn materialized_exclusive_handles_retire_only_after_their_actual_reader() {
        for ty in ["#ref-mut", "#pin-ref-mut"] {
            let (graph, types) = prepare(&format!(
                "#type View ({ty} #u64)
#fn echo ((view View)) View (#return view)
#fn work ((view View)) #u64 (#return (#deref (#call echo ((view view)))))\n"
            ));
            let target = Box::new(crate::Type::U64);
            let alias = if ty == "#ref-mut" {
                crate::Type::Reference {
                    mutable: true,
                    target,
                }
            } else {
                crate::Type::PinnedReference {
                    mutable: true,
                    target,
                }
            };
            let aliases = HashMap::from([("View".into(), alias)]);
            let requested = (0..graph.values.len()).map(ValueId).collect::<HashSet<_>>();
            let mut plan =
                Plan::with_exclusive_handles(&graph, &types, &requested, &aliases).unwrap();
            plan.validate(&graph).unwrap();
            assert!(plan.candidates.iter().all(|value| matches!(
                crate::typed_ir::resolve_type(&graph.values[value.0].ty, &aliases).unwrap(),
                crate::Type::Reference { mutable: true, .. }
                    | crate::Type::PinnedReference { mutable: true, .. }
            )));
            let (block, index, root) = graph
                .blocks
                .iter()
                .enumerate()
                .find_map(|(block, body)| {
                    body.actions.iter().enumerate().find_map(|(index, action)| {
                        match &action.action {
                            Action::Place { descriptor, .. } => match descriptor.root {
                                AddressRoot::Value(root) if plan.candidates.contains(&root) => {
                                    Some((block, index, root))
                                }
                                _ => None,
                            },
                            _ => None,
                        }
                    })
                })
                .unwrap();
            assert!(!plan.after_action[block][index].contains(&root));
            assert!(plan.after_action[block]
                .iter()
                .skip(index + 1)
                .any(|values| values.contains(&root)));
            plan.after_action[block][index].push(root);
            assert!(plan
                .validate(&graph)
                .unwrap_err()
                .message
                .contains("retired handle cell"));
        }
    }

    #[test]
    fn exclusive_candidate_requests_cannot_retire_arbitrary_owners() {
        for source in [
            "#fn work ((value #u64)) #u64 (#return value)\n",
            "#struct Holder (#linear) ((view (#ref-mut #u64)))
#fn work ((value Holder)) Holder (#return value)\n",
        ] {
            let (graph, types) = prepare(source);
            let requested = (0..graph.values.len()).map(ValueId).collect();
            assert!(
                Plan::with_exclusive_handles(&graph, &types, &requested, &HashMap::new()).is_none()
            );
        }
    }

    #[test]
    fn aliases_branches_and_loop_backedges_keep_required_handles_available() {
        for source in [
            "#fn work ((view (#ref #u64))) #u64
                  (#let alias (#ref #u64) view) (#drop view) (#return (#deref alias))\n",
            "#fn work ((choose #bool) (left (#ref #u64)) (right (#ref #u64))) #u64
                  (#let selected (#ref #u64) (#if choose left right)) (#return (#deref selected))\n",
            "#fn work ((view (#ref #u64))) #u64
                  (#let-mut count #u64 0u64)
                  (#while (#u64::lt count 2u64)
                      (#let observed #u64 (#deref view))
                      (#set count (#u64::add-wrap count 1u64)))
                  (#return (#deref view))\n",
        ] {
            let (graph, types) = prepare(source);
            let plan = Plan::new(&graph, &types).unwrap();
            plan.validate(&graph).unwrap();
            assert!(
                plan.after_action
                    .iter()
                    .flatten()
                    .any(|retired| !retired.is_empty())
                    || plan
                        .edge
                        .iter()
                        .flatten()
                        .any(|retired| !retired.is_empty())
            );
            let again = Plan::new(&graph, &types).unwrap();
            assert_eq!(plan.entry, again.entry);
            assert_eq!(plan.after_action, again.after_action);
            assert_eq!(plan.edge, again.edge);
        }
    }

    #[test]
    fn block_entry_cannot_fabricate_a_retired_parameter() {
        let (graph, types) = prepare(
            "#fn work ((choose #bool) (left (#ref #u64)) (right (#ref #u64))) #u64
              (#let selected (#ref #u64) (#if choose left right)) (#return (#deref selected))\n",
        );
        let mut plan = Plan::new(&graph, &types).unwrap();
        plan.validate(&graph).unwrap();
        let (block, parameter) = graph
            .blocks
            .iter()
            .enumerate()
            .find_map(|(index, block)| {
                block
                    .parameters
                    .iter()
                    .find(|value| plan.candidates.contains(value))
                    .map(|value| (index, *value))
            })
            .unwrap();
        plan.entry[block].push(parameter);
        assert!(plan
            .validate(&graph)
            .unwrap_err()
            .message
            .contains("retired handle cell"));
    }

    #[test]
    fn pending_retains_evaluated_operands_and_restores_only_its_child() {
        let context = crate::parse_program(
            "#enum Child (#linear) ((Child.Waiting #u64))
#enum ChildPoll () ((ChildPoll.Pending Child) (ChildPoll.Ready #u64))
#fn step-poll ((task Child) (waker (#ref #u64))) ChildPoll
              (#return (#match task (#case (Child.Waiting count)
                (#if (#u64::eq count 0u64) (ChildPoll.Ready 42u64) (ChildPoll.Pending (Child.Waiting 0u64))))))
#fn combine ((view (#ref #u64)) (result #u64)) #u64
              (#return (#u64::add-wrap (#deref view) result))\n",
        )
        .unwrap();
        let source = crate::parse(
            "(#fn work ((view (#ref #u64))) #u64
          (#return (#call combine ((view view)
            (result (#await #u64 Child ChildPoll.Pending ChildPoll.Ready step-poll (Child.Waiting 1u64)))))))",
        )
        .unwrap()
        .remove(0);
        let lowered =
            crate::generator::async_source::lower(&source, crate::Type::U64, &context).unwrap();
        let program = lowered.program(&context).unwrap();
        let declarations = crate::typecheck::resolve_program_for_analysis(&program, true).unwrap();
        let body = &declarations.bodies[&lowered.body_name];
        let sites = lowered
            .map(body, &declarations.flows[&lowered.body_name], &declarations)
            .unwrap();
        let graph = crate::generator::async_exec::build(body, &sites).unwrap();
        let types = LinearTypes::from_program(&program);
        let mut plan = Plan::new(&graph, &types).unwrap();
        plan.validate(&graph).unwrap();
        let (block, child) = graph
            .blocks
            .iter()
            .enumerate()
            .find_map(|(index, block)| match block.terminator {
                Terminator::Await { child, .. } => Some((index, child)),
                _ => None,
            })
            .unwrap();
        assert!(
            plan.edge[block][1].is_empty(),
            "the pending retry still needs its earlier reference operand"
        );
        // Independently corrupt an earlier definition. Pending is not a
        // normal parameter transfer that can make the lost handle Full.
        let (definition_block, action, value) = graph
            .blocks
            .iter()
            .enumerate()
            .find_map(|(block, body)| {
                body.actions.iter().enumerate().find_map(|(index, action)| {
                    definition(&action.action)
                        .filter(|value| plan.candidates.contains(value))
                        .map(|value| (block, index, value))
                })
            })
            .unwrap();
        assert!(!plan.after_action[definition_block][action].contains(&value));
        plan.after_action[definition_block][action].push(value);
        assert!(plan.validate(&graph).is_err());
        assert!(!plan.edge[block][1].contains(&child));
    }
}
