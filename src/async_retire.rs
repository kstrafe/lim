//! Retirement of evaluated Copy handles in the ordinary async dispatcher.
//!
//! This verifies value-cell availability, not ownership or borrow permission.
//! Source and generated ordinary bodies still require their original proofs.
//! Places remain recipes in the current emitter, so each use retains their
//! evaluated roots/indices, not only the graph's formed address token.
#![allow(dead_code)]

use std::collections::HashSet;

use crate::async_exec::{
    Action, AddressProjection, AddressRoot, Argument, BlockId, Compute, Edge, Graph, Terminator,
    ValueId,
};
use crate::linearcheck::LinearTypes;

#[derive(Debug)]
pub(crate) struct Plan {
    pub entry: Vec<Vec<ValueId>>,
    pub after_action: Vec<Vec<Vec<ValueId>>>,
    /// Goto: 0; branch/pattern: yes 0, no 1; await: Ready 0, Pending 1.
    /// Normal edges clear AFTER staging arguments but BEFORE destination puts.
    pub edge: Vec<Vec<Vec<ValueId>>>,
    candidates: HashSet<ValueId>,
}

fn edges(terminal: &Terminator) -> Vec<&Edge> {
    match terminal {
        Terminator::Goto(edge) => vec![edge],
        Terminator::Branch { yes, no, .. } | Terminator::PatternTest { yes, no, .. } => {
            vec![yes, no]
        }
        Terminator::Await { ready, .. } => vec![ready],
        _ => vec![],
    }
}

fn recipe(place: &crate::async_exec::PlaceDescriptor) -> Vec<ValueId> {
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

fn uses(graph: &Graph, action: &Action) -> Vec<ValueId> {
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

fn control(terminal: &Terminator) -> Vec<ValueId> {
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

impl Plan {
    pub fn new(graph: &Graph, types: &LinearTypes) -> Option<Self> {
        let candidates = graph
            .values
            .iter()
            .enumerate()
            .filter_map(|(index, value)| {
                (types.can_repeat(&value.ty) && types.contains_reference(&value.ty))
                    .then_some(ValueId(index))
            })
            .collect::<HashSet<_>>();
        if candidates.is_empty() {
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
        let action_uses = graph
            .blocks
            .iter()
            .map(|block| {
                block
                    .actions
                    .iter()
                    .map(|located| selected(uses(graph, &located.action)))
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
                // valid; Copy-handle retirement never destroys a referent.
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
    pub fn validate(&self, graph: &Graph) -> Result<(), crate::async_exec::Error> {
        let failure = |source, message: &str| crate::async_exec::Error {
            source,
            message: message.into(),
        };
        if self.entry.len() != graph.blocks.len()
            || self.after_action.len() != graph.blocks.len()
            || self.edge.len() != graph.blocks.len()
        {
            return Err(failure(None, "retirement plan has the wrong block count"));
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
                        "retirement attempts to clear a non-Copy handle value",
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
        let action = |held: &mut HashSet<ValueId>, located: &crate::async_exec::LocatedAction| {
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
        for block in live {
            let mut held = before[block.0].clone();
            clear(&mut held, &self.entry[block.0]);
            for (index, located) in graph.blocks[block.0].actions.iter().enumerate() {
                if uses(graph, &located.action)
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
                        "Pending retirement clears its restored child",
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
        let graph = crate::async_exec::build(&declarations.bodies["work"], &[]).unwrap();
        graph.validate().unwrap();
        (graph, LinearTypes::from_program(&program))
    }

    #[test]
    fn no_handle_values_need_no_plan() {
        let (graph, types) = prepare("(#fn work (: value u64) u64 (#return value))");
        assert!(Plan::new(&graph, &types).is_none());
        for source in [
            "(#fn work (: view (#ref-mut u64)) u64 (#return (#deref view)))",
            "(#struct Holder (: view (#ref u64))) (#linear Holder)
                (#fn work (: owner Holder) () (#forget owner) (#return ()))",
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
        let (graph, types) = prepare("(#fn work (: view (#ref u64)) u64 (#return (#deref view)))");
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
    fn aliases_branches_and_loop_backedges_keep_required_handles_available() {
        for source in [
            "(#fn work (: view (#ref u64)) u64
                (#let alias (#ref u64) view) (#drop view) (#return (#deref alias)))",
            "(#fn work (: choose bool : left (#ref u64) : right (#ref u64)) u64
                (#let selected (#ref u64) (#if choose left right)) (#return (#deref selected)))",
            "(#fn work (: view (#ref u64)) u64
                (#let-mut count u64 0u64)
                (#while (#u64.< count 2u64)
                    (#let observed u64 (#deref view))
                    (#set count (#u64.+.wrap count 1u64)))
                (#return (#deref view)))",
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
            "(#fn work (: choose bool : left (#ref u64) : right (#ref u64)) u64
            (#let selected (#ref u64) (#if choose left right)) (#return (#deref selected)))",
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
            "(#enum Child ((Waiting u64))) (#linear Child)
          (#enum ChildPoll ((Pending Child) (Ready u64)))
          (#fn step-poll (: task Child : waker (#ref u64)) ChildPoll
            (#return (#match task (#case (Waiting count)
              (#if (#u64.== count 0u64) (Ready 42u64) (Pending (Waiting 0u64)))))))
          (#fn combine (: view (#ref u64) : result u64) u64
            (#return (#u64.+.wrap (#deref view) result)))",
        )
        .unwrap();
        let source = crate::parse(
            "(#fn work (: view (#ref u64)) u64
          (#return (#call combine (: view view
            : result (#await u64 Child Pending Ready step-poll (Waiting 1u64))))))",
        )
        .unwrap()
        .remove(0);
        let lowered = crate::async_source::lower(&source, crate::Type::U64, &context).unwrap();
        let program = lowered.program(&context).unwrap();
        let declarations = crate::typecheck::resolve_program_for_analysis(&program, true).unwrap();
        let body = &declarations.bodies[&lowered.body_name];
        let sites = lowered
            .map(body, &declarations.flows[&lowered.body_name], &declarations)
            .unwrap();
        let graph = crate::async_exec::build(body, &sites).unwrap();
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
