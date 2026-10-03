//! Definite physical reference-cell state along the executable async graph.
//!
//! A poll's scalar program counter is not an ownership contract for ordinary
//! callees. At Pending, make graph-proved Empty cells visibly Empty even for
//! dispatch cases that the ordinary loop analysis cannot correlate with an
//! earlier state. Never clear a live or conditionally owned cell. This is a
//! representation check, not a replacement for source or generated borrowing.
#![allow(dead_code)]

use std::collections::{HashMap, VecDeque};

use crate::async_exec::{
    Action, AddressRoot, Argument, BlockId, Compute, Graph, LoadKind, Terminator, ValueId,
};
use crate::linearcheck::LinearTypes;
use crate::typed_body::{BindingId, NodeId};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Cell {
    Binding(BindingId),
    Value(ValueId),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum State {
    Empty,
    Full,
    Conditional,
}

pub(crate) struct Plan {
    pub pending_empty: HashMap<BlockId, Vec<Cell>>,
    pub exit_empty: HashMap<BlockId, Vec<Cell>>,
}

struct Solver<'a> {
    graph: &'a Graph,
    cells: Vec<Cell>,
    bindings: Vec<Option<usize>>,
    values: Vec<Option<usize>>,
    copy: Vec<bool>,
    retirement: Option<&'a crate::async_retire::Plan>,
    lending: Option<&'a crate::async_lend::Plan>,
    types: &'a LinearTypes,
}

impl Solver<'_> {
    fn value(&self, states: &mut [State], value: ValueId, take: bool) {
        if let Some(index) = self.values[value.0] {
            if take && !self.copy[index] {
                states[index] = State::Empty;
            }
        }
    }

    fn define(&self, states: &mut [State], value: ValueId) {
        if let Some(index) = self.values[value.0] {
            states[index] = State::Full;
        }
    }

    fn clear(&self, states: &mut [State], values: &[ValueId]) {
        for value in values {
            if let Some(index) = self.values[value.0] {
                states[index] = State::Empty;
            }
        }
    }

    fn action(&self, states: &mut [State], action: &Action, source: Option<NodeId>) {
        match action {
            Action::Compute { dst, operation } => {
                match operation {
                    Compute::Identity(value) => self.value(states, *value, true),
                    Compute::Checked(operation) => {
                        for operand in &operation.operands {
                            self.value(states, operand.value, true);
                        }
                    }
                    _ => {}
                }
                self.define(states, *dst);
            }
            Action::Load { dst, place, kind } => {
                let descriptor = &self.graph.places[place.0];
                if descriptor.projections.is_empty() {
                    if let AddressRoot::Local(binding) = descriptor.root {
                        if let Some(index) = self.bindings[binding.0] {
                            if !self.copy[index]
                                && *kind == LoadKind::Read
                                && source
                                    .and_then(|source| self.lending?.access(source))
                                    .is_some_and(|access| {
                                        matches!(access, crate::async_lend::Access::Move(_))
                                    })
                            {
                                states[index] = State::Empty;
                            }
                        }
                    }
                }
                self.define(states, *dst);
            }
            Action::Bind { binding, value, .. } => {
                self.value(states, *value, true);
                if let Some(index) = self.bindings[binding.0] {
                    states[index] = State::Full;
                }
            }
            Action::Store { place, value } => {
                self.value(states, *value, true);
                let descriptor = &self.graph.places[place.0];
                if let AddressRoot::Local(binding) = descriptor.root {
                    if let Some(index) = self.bindings[binding.0] {
                        if descriptor.projections.is_empty() {
                            states[index] = State::Full;
                        } else if self.types.contains_reference(&descriptor.ty) {
                            states[index] = State::Conditional;
                        }
                    }
                }
            }
            Action::Release { place, .. } => {
                let descriptor = &self.graph.places[place.0];
                if let AddressRoot::Local(binding) = descriptor.root {
                    if let Some(index) = self.bindings[binding.0] {
                        states[index] = if descriptor.projections.is_empty() {
                            State::Empty
                        } else {
                            State::Conditional
                        };
                    }
                }
            }
            Action::Borrow { dst: Some(dst), .. } => self.define(states, *dst),
            Action::Commit(pattern) => {
                self.value(states, pattern.scrutinee, true);
                for binding in &pattern.bindings {
                    if let Some(index) = self.bindings[binding.0] {
                        states[index] = State::Full;
                    }
                }
            }
            Action::Preview(pattern) => {
                for binding in &pattern.bindings {
                    if let Some(index) = self.bindings[binding.0] {
                        states[index] = State::Full;
                    }
                }
            }
            Action::EndPreview(pattern) => {
                for binding in &pattern.bindings {
                    if let Some(index) = self.bindings[binding.0] {
                        states[index] = State::Empty;
                    }
                }
            }
            Action::ScopeExit(bindings) => {
                for binding in bindings {
                    if let Some(index) = self.bindings[binding.0] {
                        states[index] = State::Empty;
                    }
                }
            }
            _ => {}
        }
    }

    fn terminal(&self, block: BlockId, mut states: Vec<State>) -> Vec<(BlockId, Vec<State>)> {
        let terminal = &self.graph.blocks[block.0].terminator;
        let edges = match terminal {
            Terminator::Goto(edge) => vec![edge],
            Terminator::Branch { yes, no, .. } | Terminator::PatternTest { yes, no, .. } => {
                vec![yes, no]
            }
            Terminator::Await { child, ready, .. } => {
                self.value(&mut states, *child, true);
                vec![ready]
            }
            _ => vec![],
        };
        let mut outputs = Vec::new();
        for (index, edge) in edges.into_iter().enumerate() {
            let mut next = states.clone();
            for argument in &edge.arguments {
                if let Argument::Value(value) = argument {
                    self.value(&mut next, *value, true);
                }
            }
            if let Some(plan) = self.retirement {
                self.clear(&mut next, &plan.edge[block.0][index]);
            }
            for parameter in &self.graph.blocks[edge.target.0].parameters {
                self.define(&mut next, *parameter);
            }
            outputs.push((edge.target, next));
        }
        if let Terminator::Await { child, pending, .. } = terminal {
            self.define(&mut states, *child);
            if let Some(plan) = self.retirement {
                self.clear(&mut states, &plan.edge[block.0][1]);
            }
            outputs.push((*pending, states));
        }
        outputs
    }

    fn block(&self, block: BlockId, mut states: Vec<State>) -> Vec<State> {
        if let Some(plan) = self.retirement {
            self.clear(&mut states, &plan.entry[block.0]);
        }
        for (index, located) in self.graph.blocks[block.0].actions.iter().enumerate() {
            self.action(&mut states, &located.action, located.source);
            if let Some(plan) = self.retirement {
                self.clear(&mut states, &plan.after_action[block.0][index]);
            }
        }
        states
    }
}

impl Plan {
    pub(crate) fn new(
        graph: &Graph,
        types: &LinearTypes,
        retirement: Option<&crate::async_retire::Plan>,
        lending: Option<&crate::async_lend::Plan>,
    ) -> Option<Self> {
        let mut solver = Solver {
            graph,
            cells: Vec::new(),
            bindings: vec![None; graph.bindings.len()],
            values: vec![None; graph.values.len()],
            copy: Vec::new(),
            retirement,
            lending,
            types,
        };
        for (index, binding) in graph.bindings.iter().enumerate() {
            if types.contains_reference(&binding.ty) {
                solver.bindings[index] = Some(solver.cells.len());
                solver.cells.push(Cell::Binding(BindingId(index)));
                solver.copy.push(types.can_repeat(&binding.ty));
            }
        }
        for (index, value) in graph.values.iter().enumerate() {
            if types.contains_reference(&value.ty) {
                solver.values[index] = Some(solver.cells.len());
                solver.cells.push(Cell::Value(ValueId(index)));
                solver.copy.push(types.can_repeat(&value.ty));
            }
        }
        if solver.cells.is_empty() {
            return None;
        }
        let mut initial = vec![State::Empty; solver.cells.len()];
        for (index, cell) in solver.cells.iter().enumerate() {
            if matches!(cell, Cell::Binding(binding) if binding.0 < graph.parameter_count) {
                initial[index] = State::Full;
            }
        }
        let mut before = vec![None; graph.blocks.len()];
        before[graph.entry.0] = Some(initial);
        let mut pending = VecDeque::from([graph.entry]);
        while let Some(block) = pending.pop_front() {
            let states = solver.block(block, before[block.0].clone().unwrap());
            for (target, states) in solver.terminal(block, states) {
                let changed = match &mut before[target.0] {
                    None => {
                        before[target.0] = Some(states);
                        true
                    }
                    Some(existing) => {
                        let mut changed = false;
                        for (old, new) in existing.iter_mut().zip(states) {
                            if *old != new && *old != State::Conditional {
                                *old = State::Conditional;
                                changed = true;
                            }
                        }
                        changed
                    }
                };
                if changed {
                    pending.push_back(target);
                }
            }
        }
        let mut pending_empty = HashMap::new();
        let mut exit_empty = HashMap::new();
        for (index, block) in graph.blocks.iter().enumerate() {
            if let Terminator::Return(value) = block.terminator {
                if let Some(incoming) = before[index].clone() {
                    let mut states = solver.block(BlockId(index), incoming);
                    if let Some(value) = value {
                        solver.value(&mut states, value, true);
                    }
                    exit_empty.insert(
                        BlockId(index),
                        solver
                            .cells
                            .iter()
                            .copied()
                            .zip(states)
                            .filter_map(|(cell, state)| (state == State::Empty).then_some(cell))
                            .collect(),
                    );
                }
            }
            let Terminator::Await { child, .. } = block.terminator else {
                continue;
            };
            let Some(incoming) = before[index].clone() else {
                continue;
            };
            let mut states = solver.block(BlockId(index), incoming);
            solver.value(&mut states, child, true);
            solver.define(&mut states, child);
            if let Some(plan) = retirement {
                solver.clear(&mut states, &plan.edge[index][1]);
            }
            pending_empty.insert(
                BlockId(index),
                solver
                    .cells
                    .iter()
                    .copied()
                    .zip(states)
                    .filter_map(|(cell, state)| (state == State::Empty).then_some(cell))
                    .collect(),
            );
        }
        Some(Self {
            pending_empty,
            exit_empty,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn prepare(source: &str) -> (Graph, LinearTypes, Option<crate::async_lend::Plan>) {
        let program = crate::parse_program(source).unwrap();
        let declarations = crate::typecheck::resolve_program_for_analysis(&program, true).unwrap();
        let body = &declarations.bodies["work"];
        let types = LinearTypes::from_program(&program);
        let lending =
            crate::async_lend::Plan::new(body, &declarations.flows["work"], &types).unwrap();
        let graph = crate::async_exec::build(body, &[]).unwrap();
        graph.validate().unwrap();
        (graph, types, lending)
    }

    #[test]
    fn no_reference_cells_need_no_plan() {
        let (graph, types, lending) = prepare("(#fn work (: value u64) u64 (#return value))");
        assert!(Plan::new(&graph, &types, None, lending.as_ref()).is_none());
    }

    #[test]
    fn owned_moves_empty_bindings_but_lending_and_copying_do_not() {
        for (source, empty) in [
            (
                "(#fn work (: view (#ref-mut u64)) (#ref-mut u64) (#return view))",
                true,
            ),
            (
                "(#fn work (: view (#ref-mut u64)) u64 (#return (#deref view)))",
                false,
            ),
            (
                "(#fn work (: view (#ref u64)) (#ref u64) (#return (#clone view)))",
                false,
            ),
        ] {
            let (graph, types, lending) = prepare(source);
            let plan = Plan::new(&graph, &types, None, lending.as_ref()).unwrap();
            assert!(!plan.exit_empty.is_empty());
            for cells in plan.exit_empty.values() {
                assert_eq!(
                    cells.contains(&Cell::Binding(BindingId(0))),
                    empty,
                    "{source}"
                );
            }
        }
    }

    #[test]
    fn conditional_release_is_not_proof_of_empty_storage() {
        let (graph, types, lending) = prepare(
            "(#fn work (: view (#ref-mut u64) : release bool) ()
              (#if release (#drop view) ()) (#return ()))",
        );
        let plan = Plan::new(&graph, &types, None, lending.as_ref()).unwrap();
        for cells in plan.exit_empty.values() {
            assert!(!cells.contains(&Cell::Binding(BindingId(0))));
        }
    }

    #[test]
    fn primitive_field_writes_preserve_a_live_reference_holder() {
        let (graph, types, lending) = prepare(
            "(#struct Holder (: view (#ref u64) : count u64))
              (#fn work (: owner Holder) ()
                (#let-mut holder Holder owner) (#set-field holder count 1u64) (#return ()))",
        );
        let solver = Solver {
            graph: &graph,
            cells: vec![Cell::Binding(BindingId(1))],
            bindings: vec![None, Some(0)],
            values: vec![None; graph.values.len()],
            copy: vec![true],
            retirement: None,
            lending: lending.as_ref(),
            types: &types,
        };
        let store = graph
            .blocks
            .iter()
            .flat_map(|block| &block.actions)
            .find(|located| matches!(located.action, Action::Store { .. }))
            .unwrap();
        let mut states = vec![State::Full];
        solver.action(&mut states, &store.action, store.source);
        assert_eq!(states, vec![State::Full]);
    }

    #[test]
    fn pending_preserves_only_the_restored_owned_child() {
        let context = crate::parse_program(
            "(#enum Child ((Waiting (#ref-mut u64)))) (#linear Child)
              (#enum ChildPoll ((Pending Child) (Ready u64)))
              (#fn step-poll (: task Child : waker (#ref u64)) ChildPoll
                (#return (#match task (#case (Waiting view) (Pending (Waiting view))))))",
        )
        .unwrap();
        let source = crate::parse(
            "(#fn work (: view (#ref-mut u64)) u64
              (#let child Child (Waiting view))
              (#return (#await u64 Child Pending Ready step-poll child)))",
        )
        .unwrap()
        .remove(0);
        let lowered = crate::async_source::lower(&source, crate::Type::U64, &context).unwrap();
        let program = lowered.program(&context).unwrap();
        let declarations = crate::typecheck::resolve_program_for_analysis(&program, true).unwrap();
        let body = &declarations.bodies[&lowered.body_name];
        let flow = &declarations.flows[&lowered.body_name];
        let sites = lowered.map(body, flow, &declarations).unwrap();
        let graph = crate::async_exec::build(body, &sites).unwrap();
        graph.validate().unwrap();
        let types = LinearTypes::from_program(&program);
        let lending = crate::async_lend::Plan::new(body, flow, &types).unwrap();
        let plan = Plan::new(&graph, &types, None, lending.as_ref()).unwrap();
        let again = Plan::new(&graph, &types, None, lending.as_ref()).unwrap();
        assert_eq!(plan.pending_empty, again.pending_empty);
        assert_eq!(plan.exit_empty, again.exit_empty);
        let (block, child) = graph
            .blocks
            .iter()
            .enumerate()
            .find_map(|(index, block)| {
                if let Terminator::Await { child, .. } = block.terminator {
                    Some((BlockId(index), child))
                } else {
                    None
                }
            })
            .unwrap();
        let cells = &plan.pending_empty[&block];
        assert!(
            !cells.contains(&Cell::Value(child)),
            "Pending restores, not clears, its actual child"
        );
        assert!(
            cells.contains(&Cell::Binding(BindingId(0))),
            "the input handle moved into the child"
        );
        for cells in plan.exit_empty.values() {
            assert!(
                cells.contains(&Cell::Value(child)),
                "Ready consumes the child"
            );
        }
    }
}
