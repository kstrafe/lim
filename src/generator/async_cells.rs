//! Definite physical reference-cell state along the executable async graph.
//! Implementation detail of built-in code generation, not runtime semantics.
//!
//! A poll's scalar program counter is not an ownership contract for ordinary
//! callees. At Pending, make graph-proved Empty cells visibly Empty even for
//! dispatch cases that the ordinary loop analysis cannot correlate with an
//! earlier state. The emitter asserts the tag of a proved Empty cell before
//! extracting/restoring it, including after its referent has been destroyed.
//! Never clear a live or conditionally owned cell. This is a
//! representation check, not a replacement for source or generated borrowing.
#![allow(dead_code)]

use std::collections::{HashMap, VecDeque};

use crate::generator::async_exec::{
    Action, AddressRoot, Argument, BlockId, Compute, Graph, LoadKind, Terminator, ValueId,
};
use crate::linearcheck::LinearTypes;
use crate::typed_body::{BindingId, NodeId};

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum Cell {
    Binding(BindingId),
    Value(ValueId),
    Scope(NodeId),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum State {
    Empty,
    Full,
    Conditional,
}

pub(crate) struct Plan {
    /// Possibly occupied at task construction or a reachable Pending return.
    /// Used only for public cleanup layout; ordinary checking remains required.
    pub cancel_live: Vec<Cell>,
    pub action_empty: HashMap<(BlockId, usize), Vec<Cell>>,
    pub pending_empty: HashMap<BlockId, Vec<Cell>>,
    pub exit_empty: HashMap<BlockId, Vec<Cell>>,
}

struct Solver<'a> {
    graph: &'a Graph,
    cells: Vec<Cell>,
    bindings: Vec<Option<usize>>,
    values: Vec<Option<usize>>,
    scopes: HashMap<NodeId, usize>,
    copy: Vec<bool>,
    retirement: Option<&'a crate::generator::async_retire::Plan>,
    lending: Option<&'a crate::generator::async_lend::Plan>,
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

    fn clear_bindings(&self, states: &mut [State], bindings: &[BindingId]) {
        for binding in bindings {
            if let Some(index) = self.bindings[binding.0] {
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
                                        matches!(
                                            access,
                                            crate::generator::async_lend::Access::Move(_)
                                        )
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
            Action::Borrow { dst, scope, .. } => {
                if let Some(dst) = dst {
                    self.define(states, *dst);
                }
                if let Some(index) = scope.and_then(|scope| self.scopes.get(&scope)) {
                    states[*index] = State::Full;
                }
            }
            Action::EndBorrow { scope } => {
                if let Some(index) = self.scopes.get(scope) {
                    states[*index] = State::Empty;
                }
            }
            Action::Commit(pattern) => {
                if !pattern.borrowed {
                    self.value(states, pattern.scrutinee, true);
                }
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
                self.clear_bindings(&mut states, &plan.pending_bindings[block.0]);
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
        retirement: Option<&crate::generator::async_retire::Plan>,
        lending: Option<&crate::generator::async_lend::Plan>,
    ) -> Option<Self> {
        Self::solve(graph, types, retirement, lending, false)
    }

    #[cfg(test)]
    pub(crate) fn cancellation(
        graph: &Graph,
        types: &LinearTypes,
        retirement: Option<&crate::generator::async_retire::Plan>,
        lending: Option<&crate::generator::async_lend::Plan>,
    ) -> Option<Self> {
        #[cfg(test)]
        CANCELLATION_SOLVES.with(|count| count.set(count.get() + 1));
        Self::solve(graph, types, retirement, lending, true)
    }

    fn solve(
        graph: &Graph,
        types: &LinearTypes,
        retirement: Option<&crate::generator::async_retire::Plan>,
        lending: Option<&crate::generator::async_lend::Plan>,
        owners: bool,
    ) -> Option<Self> {
        let mut solver = Solver {
            graph,
            cells: Vec::new(),
            bindings: vec![None; graph.bindings.len()],
            values: vec![None; graph.values.len()],
            scopes: HashMap::new(),
            copy: Vec::new(),
            retirement,
            lending,
            types,
        };
        for (index, binding) in graph.bindings.iter().enumerate() {
            if types.contains_reference(&binding.ty) || (owners && types.is_linear(&binding.ty)) {
                solver.bindings[index] = Some(solver.cells.len());
                solver.cells.push(Cell::Binding(BindingId(index)));
                solver.copy.push(types.can_repeat(&binding.ty));
            }
        }
        for (index, value) in graph.values.iter().enumerate() {
            if types.contains_reference(&value.ty) || (owners && types.is_linear(&value.ty)) {
                solver.values[index] = Some(solver.cells.len());
                solver.cells.push(Cell::Value(ValueId(index)));
                solver.copy.push(types.can_repeat(&value.ty));
            }
        }
        for located in graph.blocks.iter().flat_map(|block| &block.actions) {
            if let Action::Borrow {
                scope: Some(scope),
                mutable,
                ..
            } = located.action
            {
                if !solver.scopes.contains_key(&scope) {
                    solver.scopes.insert(scope, solver.cells.len());
                    solver.cells.push(Cell::Scope(scope));
                    solver.copy.push(!mutable);
                }
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
        let mut cancel_live = solver
            .cells
            .iter()
            .copied()
            .zip(initial.iter())
            .filter_map(|(cell, state)| (*state != State::Empty).then_some(cell))
            .collect::<std::collections::HashSet<_>>();
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
        let mut action_empty = HashMap::new();
        for (index, incoming) in before.iter().enumerate() {
            if let Some(mut states) = incoming.clone() {
                if let Some(plan) = retirement {
                    solver.clear(&mut states, &plan.entry[index]);
                }
                for (action_index, action) in graph.blocks[index].actions.iter().enumerate() {
                    action_empty.insert(
                        (BlockId(index), action_index),
                        solver
                            .cells
                            .iter()
                            .copied()
                            .zip(states.iter().copied())
                            .filter_map(|(cell, state)| (state == State::Empty).then_some(cell))
                            .collect(),
                    );
                    solver.action(&mut states, &action.action, action.source);
                    if let Some(plan) = retirement {
                        solver.clear(&mut states, &plan.after_action[index][action_index]);
                    }
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
                solver.clear_bindings(&mut states, &plan.pending_bindings[index]);
            }
            cancel_live.extend(
                solver
                    .cells
                    .iter()
                    .copied()
                    .zip(states.iter())
                    .filter_map(|(cell, state)| (*state != State::Empty).then_some(cell)),
            );
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
            cancel_live: solver
                .cells
                .iter()
                .copied()
                .filter(|cell| cancel_live.contains(cell))
                .collect(),
            action_empty,
            pending_empty,
            exit_empty,
        })
    }
}

#[cfg(test)]
thread_local! {
    pub(crate) static CANCELLATION_SOLVES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
mod tests {
    use super::*;

    fn prepare(
        source: &str,
    ) -> (
        Graph,
        LinearTypes,
        Option<crate::generator::async_lend::Plan>,
    ) {
        let program = crate::parse_program(source).unwrap();
        let declarations = crate::typecheck::resolve_program_for_analysis(&program, true).unwrap();
        let body = &declarations.bodies["work"];
        let types = LinearTypes::from_program(&program);
        let lending =
            crate::generator::async_lend::Plan::new(body, &declarations.flows["work"], &types)
                .unwrap();
        let graph = crate::generator::async_exec::build(body, &[]).unwrap();
        graph.validate().unwrap();
        (graph, types, lending)
    }

    #[test]
    fn no_reference_cells_need_no_plan() {
        let (graph, types, lending) = prepare("#fn work ((value #u64)) #u64 (#return value)\n");
        assert!(Plan::new(&graph, &types, None, lending.as_ref()).is_none());
    }

    #[test]
    fn owned_moves_empty_bindings_but_lending_and_copying_do_not() {
        for (source, empty) in [
            (
                "#fn work ((view (#ref-mut #u64))) (#ref-mut #u64) (#return view)\n",
                true,
            ),
            (
                "#fn work ((view (#ref-mut #u64))) #u64 (#return (#deref view))\n",
                false,
            ),
            (
                "#fn work ((view (#ref #u64))) (#ref #u64) (#return (#clone view))\n",
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
            "#fn work ((view (#ref-mut #u64)) (release #bool)) ()
                (#if release (#drop view) ()) (#return ())\n",
        );
        let plan = Plan::new(&graph, &types, None, lending.as_ref()).unwrap();
        for cells in plan.exit_empty.values() {
            assert!(!cells.contains(&Cell::Binding(BindingId(0))));
        }
    }

    #[test]
    fn primitive_field_writes_preserve_a_live_reference_holder() {
        let (graph, types, lending) = prepare(
            "#struct Holder () ((view (#ref #u64)) (count #u64))
#fn work ((owner Holder)) ()
                  (#let-mut holder Holder owner) (#set-field holder count 1u64) (#return ())\n",
        );
        let solver = Solver {
            graph: &graph,
            cells: vec![Cell::Binding(BindingId(1))],
            bindings: vec![None, Some(0)],
            values: vec![None; graph.values.len()],
            scopes: HashMap::new(),
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
    fn pending_retires_only_dead_exclusive_bindings() {
        let context = crate::parse_program(
            "#type View (#ref-mut #u64)
#enum ChildPoll () ((ChildPoll.Pending View) (ChildPoll.Ready #u64))
#fn step-poll ((task View) (waker (#ref #u64))) ChildPoll
                  (#return (ChildPoll.Pending task))\n",
        )
        .unwrap();
        for (body, dead) in [
            (
                "(#let answer #u64 (#await #u64 View ChildPoll.Pending ChildPoll.Ready step-poll view))
                (#return answer)",
                true,
            ),
            (
                "(#let answer #u64 (#await #u64 View ChildPoll.Pending ChildPoll.Ready step-poll view))
                (#forget answer) (#return (#deref view))",
                false,
            ),
            (
                "(#let answer #u64 (#await #u64 View ChildPoll.Pending ChildPoll.Ready step-poll view))
                (#return (#if selected (#deref view) answer))",
                false,
            ),
            (
                "(#while (#u64::lt (#deref view) 2u64)
                (#let answer #u64 (#await #u64 View ChildPoll.Pending ChildPoll.Ready step-poll view))
                (#forget answer)) (#return 2u64)",
                false,
            ),
        ] {
            let source = crate::parse_source_unit(&format!(
                "#fn work ((view View) (selected #bool)) #u64 {body}\n"
            ))
            .unwrap()
            .remove(0);
            let lowered =
                crate::generator::async_source::lower(&source, crate::Type::U64, &context).unwrap();
            let program = lowered.program(&context).unwrap();
            let declarations =
                crate::typecheck::resolve_program_for_analysis(&program, true).unwrap();
            let lowered_body = &declarations.bodies[&lowered.body_name];
            let flow = &declarations.flows[&lowered.body_name];
            let sites = lowered.map(lowered_body, flow, &declarations).unwrap();
            let graph = crate::generator::async_exec::build(lowered_body, &sites).unwrap();
            graph.validate().unwrap();
            let types = LinearTypes::from_program(&program);
            let lending =
                crate::generator::async_lend::Plan::new(lowered_body, flow, &types).unwrap();
            let mut retirement = crate::generator::async_retire::Plan::with_exclusive_handles(
                &graph,
                &types,
                &std::collections::HashSet::new(),
                &declarations.aliases,
            );
            let plan = Plan::new(&graph, &types, retirement.as_ref(), lending.as_ref()).unwrap();
            for (block, cells) in &plan.pending_empty {
                assert_eq!(cells.contains(&Cell::Binding(BindingId(0))), dead, "{body}");
                if let Some(retirement) = retirement.as_mut() {
                    retirement.validate(&graph).unwrap();
                    assert_eq!(
                        retirement.pending_bindings[block.0].contains(&BindingId(0)),
                        dead
                    );
                    // The validator must reject clearing a live handle, or
                    // omitting the agreed physical retirement for a dead one.
                    retirement.pending_bindings[block.0] =
                        if dead { vec![] } else { vec![BindingId(0)] };
                    assert!(retirement
                        .validate(&graph)
                        .unwrap_err()
                        .message
                        .contains("liveness"));
                    if dead {
                        retirement.protect_binding_anchors(
                            &graph,
                            &std::collections::HashSet::from([BindingId(0)]),
                        );
                        retirement.validate(&graph).unwrap();
                        assert!(
                            !retirement.pending_bindings[block.0].contains(&BindingId(0)),
                            "derived internal addresses keep their source storage alive"
                        );
                    }
                } else {
                    assert!(!dead);
                }
            }
        }
    }

    #[test]
    fn pending_preserves_only_the_restored_owned_child() {
        let context = crate::parse_program(
            "#enum Child (#linear) ((Child.Waiting (#ref-mut #u64)))
#enum ChildPoll () ((ChildPoll.Pending Child) (ChildPoll.Ready #u64))
#fn step-poll ((task Child) (waker (#ref #u64))) ChildPoll
                  (#return (#match task (#case (Child.Waiting view) (ChildPoll.Pending (Child.Waiting view)))))\n",
        )
        .unwrap();
        let source = crate::parse(
            "(#fn work ((view (#ref-mut #u64))) #u64
              (#let child Child (Child.Waiting view))
              (#return (#await #u64 Child ChildPoll.Pending ChildPoll.Ready step-poll child)))",
        )
        .unwrap()
        .remove(0);
        let lowered =
            crate::generator::async_source::lower(&source, crate::Type::U64, &context).unwrap();
        let program = lowered.program(&context).unwrap();
        let declarations = crate::typecheck::resolve_program_for_analysis(&program, true).unwrap();
        let body = &declarations.bodies[&lowered.body_name];
        let flow = &declarations.flows[&lowered.body_name];
        let sites = lowered.map(body, flow, &declarations).unwrap();
        let graph = crate::generator::async_exec::build(body, &sites).unwrap();
        graph.validate().unwrap();
        let types = LinearTypes::from_program(&program);
        let lending = crate::generator::async_lend::Plan::new(body, flow, &types).unwrap();
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
            "ChildPoll.Pending restores, not clears, its actual child"
        );
        assert!(
            cells.contains(&Cell::Binding(BindingId(0))),
            "the input handle moved into the child"
        );
        for cells in plan.exit_empty.values() {
            assert!(
                cells.contains(&Cell::Value(child)),
                "ChildPoll.Ready consumes the child"
            );
        }
    }
}
