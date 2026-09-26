//! Stable, address-free control flow over the checked body arena.
//! Ownership passes can share these edges instead of reconstructing branch
//! and loop behavior independently from syntax.

use std::collections::{HashSet, VecDeque};

use crate::typed_body::{
    BindingId, Body, Control, Instruction, NodeId, NodeKind, NumericOpcode, PlaceRoot, Projection,
};
use crate::Span;

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) struct FlowNodeId(pub usize);

#[derive(Clone, Debug)]
pub(crate) enum FlowAction {
    Entry,
    Exit,
    Evaluate(NodeId),
    Bind(BindingId),
    Assign(PlaceRoot),
    Pattern(NodeId),
    Branch(NodeId),
    LoopHead,
    Return,
    Break,
    Continue,
    Diverge,
}

#[derive(Clone, Debug)]
pub(crate) struct FlowNode {
    pub action: FlowAction,
    /// Branch edges are in source order. For `if` and loop conditions the
    /// first edge is true/success and the second is false/fallthrough.
    pub successors: Vec<FlowNodeId>,
    pub span: Option<Span>,
}

#[derive(Clone, Debug)]
pub(crate) struct FlowGraph {
    pub nodes: Vec<FlowNode>,
    pub entry: FlowNodeId,
    pub exit: FlowNodeId,
}

#[derive(Clone)]
struct Target {
    name: Option<String>,
    break_to: FlowNodeId,
    continue_to: Option<FlowNodeId>,
}

struct Builder<'a> {
    body: &'a Body,
    nodes: Vec<FlowNode>,
    exit: FlowNodeId,
}

impl FlowGraph {
    pub fn lower(body: &Body) -> Result<Self, String> {
        let mut builder = Builder {
            body,
            nodes: Vec::new(),
            exit: FlowNodeId(0),
        };
        builder.exit = builder.push(FlowAction::Exit, None, vec![]);
        let first = builder.instructions(&body.instructions, builder.exit, &[])?;
        let entry = builder.push(FlowAction::Entry, None, vec![first]);
        let graph = Self {
            nodes: builder.nodes,
            entry,
            exit: builder.exit,
        };
        graph.verify(body)?;
        Ok(graph)
    }

    pub fn reachable(&self) -> HashSet<FlowNodeId> {
        let mut seen = HashSet::new();
        let mut pending = vec![self.entry];
        while let Some(id) = pending.pop() {
            if seen.insert(id) {
                pending.extend(self.nodes[id.0].successors.iter().copied());
            }
        }
        seen
    }

    fn verify(&self, body: &Body) -> Result<(), String> {
        for (index, node) in self.nodes.iter().enumerate() {
            if node
                .successors
                .iter()
                .any(|next| next.0 >= self.nodes.len())
            {
                return Err(format!("typed flow node {index} has an invalid successor"));
            }
            match &node.action {
                FlowAction::Evaluate(id) => {
                    if body.nodes.get(id.0).is_none_or(|node| node.ty.is_none()) {
                        return Err(format!("typed flow evaluates invalid node {id:?}"));
                    }
                }
                FlowAction::Bind(id) => {
                    if id.0 >= body.bindings.len() {
                        return Err(format!("typed flow binds invalid local {id:?}"));
                    }
                }
                FlowAction::Assign(PlaceRoot::Local(id)) => {
                    if id.0 >= body.bindings.len() {
                        return Err(format!("typed flow assigns invalid local {id:?}"));
                    }
                }
                FlowAction::Assign(PlaceRoot::Global(_)) => {}
                FlowAction::Pattern(id) | FlowAction::Branch(id) => {
                    if id.0 >= body.nodes.len() {
                        return Err(format!("typed flow references invalid node {id:?}"));
                    }
                }
                FlowAction::Entry
                | FlowAction::Exit
                | FlowAction::LoopHead
                | FlowAction::Return
                | FlowAction::Break
                | FlowAction::Continue
                | FlowAction::Diverge => {}
            }
            if matches!(node.action, FlowAction::Return)
                && node.successors.as_slice() != [self.exit]
            {
                return Err(format!("typed flow return {index} does not reach exit"));
            }
        }
        Ok(())
    }

    pub fn dump(&self) -> String {
        use std::fmt::Write;
        let reachable = self.reachable();
        let mut output = format!("  flow entry {} exit {}\n", self.entry.0, self.exit.0);
        for (index, node) in self.nodes.iter().enumerate() {
            let edges = node.successors.iter().map(|id| id.0).collect::<Vec<_>>();
            writeln!(
                output,
                "  flow {index}: {:?} {:?} -> {edges:?}{}",
                node.action,
                node.span,
                if reachable.contains(&FlowNodeId(index)) {
                    ""
                } else {
                    " unreachable"
                }
            )
            .unwrap();
        }
        output
    }

    /// First ownership consumer of the shared graph: a local must be bound on
    /// every reachable path before it can be read or assigned. This operates
    /// on stable binding IDs, not reconstructed names or syntax addresses.
    pub fn check_definite_bindings(
        &self,
        body: &Body,
        parameter_count: usize,
    ) -> Result<(), String> {
        let mut reachable = vec![false; self.nodes.len()];
        for id in self.reachable() {
            reachable[id.0] = true;
        }
        let words = body.bindings.len().div_ceil(64);
        let all = vec![u64::MAX; words];
        let mut parameters = vec![0u64; words];
        for index in 0..parameter_count {
            parameters[index / 64] |= 1u64 << (index % 64);
        }
        let mut predecessors = vec![Vec::<FlowNodeId>::new(); self.nodes.len()];
        let mut generated = vec![vec![0u64; words]; self.nodes.len()];
        for (index, node) in self.nodes.iter().enumerate() {
            if reachable[index] {
                for successor in &node.successors {
                    predecessors[successor.0].push(FlowNodeId(index));
                }
                match node.action {
                    FlowAction::Bind(binding) => {
                        generated[index][binding.0 / 64] |= 1u64 << (binding.0 % 64);
                    }
                    FlowAction::Pattern(pattern) => {
                        let mut bindings = HashSet::new();
                        collect_pattern_bindings(body, pattern, &mut bindings);
                        for binding in bindings {
                            generated[index][binding.0 / 64] |= 1u64 << (binding.0 % 64);
                        }
                    }
                    _ => {}
                }
            }
        }
        let mut incoming = vec![all.clone(); self.nodes.len()];
        let mut outgoing = vec![all.clone(); self.nodes.len()];
        let mut pending = VecDeque::from([self.entry]);
        let mut queued = vec![false; self.nodes.len()];
        let mut visited = vec![false; self.nodes.len()];
        queued[self.entry.0] = true;
        while let Some(id) = pending.pop_front() {
            queued[id.0] = false;
            let next_in = if id == self.entry {
                parameters.clone()
            } else {
                let mut paths = predecessors[id.0].iter();
                let Some(first) = paths.next() else {
                    continue;
                };
                let mut intersection = outgoing[first.0].clone();
                for predecessor in paths {
                    for (word, predecessor_word) in
                        intersection.iter_mut().zip(&outgoing[predecessor.0])
                    {
                        *word &= predecessor_word;
                    }
                }
                intersection
            };
            let mut next_out = next_in.clone();
            for (word, generated_word) in next_out.iter_mut().zip(&generated[id.0]) {
                *word |= generated_word;
            }
            let changed_out = outgoing[id.0] != next_out;
            incoming[id.0] = next_in;
            if !visited[id.0] || changed_out {
                outgoing[id.0] = next_out;
                visited[id.0] = true;
                for successor in &self.nodes[id.0].successors {
                    if !queued[successor.0] {
                        pending.push_back(*successor);
                        queued[successor.0] = true;
                    }
                }
            }
        }
        for (index, node) in self.nodes.iter().enumerate() {
            if !reachable[index] {
                continue;
            }
            let binding = match node.action {
                FlowAction::Evaluate(id) => match body.nodes[id.0].kind {
                    NodeKind::Symbol {
                        binding: Some(binding),
                        ..
                    } => Some(binding),
                    _ => None,
                },
                FlowAction::Assign(PlaceRoot::Local(binding)) => Some(binding),
                _ => None,
            };
            if let Some(binding) = binding {
                if incoming[index][binding.0 / 64] & (1u64 << (binding.0 % 64)) == 0 {
                    return Err(format!(
                        "typed flow uses binding {binding:?} before it is bound on every path"
                    ));
                }
            }
        }
        Ok(())
    }
}

fn collect_pattern_bindings(body: &Body, id: NodeId, bindings: &mut HashSet<BindingId>) {
    match &body.nodes[id.0].kind {
        NodeKind::Symbol {
            binding: Some(binding),
            ..
        } => {
            bindings.insert(*binding);
        }
        NodeKind::Form { children, .. } | NodeKind::Syntax(children) => {
            for child in children {
                collect_pattern_bindings(body, *child, bindings);
            }
        }
        NodeKind::Labeled(_, inner) => collect_pattern_bindings(body, *inner, bindings),
        _ => {}
    }
}

impl Builder<'_> {
    fn push(
        &mut self,
        action: FlowAction,
        span: Option<Span>,
        successors: Vec<FlowNodeId>,
    ) -> FlowNodeId {
        let id = FlowNodeId(self.nodes.len());
        self.nodes.push(FlowNode {
            action,
            successors,
            span,
        });
        id
    }

    fn instructions(
        &mut self,
        instructions: &[Instruction],
        mut next: FlowNodeId,
        targets: &[Target],
    ) -> Result<FlowNodeId, String> {
        for instruction in instructions.iter().rev() {
            next = self.instruction(instruction, next, targets, None)?;
        }
        Ok(next)
    }

    fn instruction(
        &mut self,
        instruction: &Instruction,
        next: FlowNodeId,
        targets: &[Target],
        label: Option<&str>,
    ) -> Result<FlowNodeId, String> {
        let span = instruction.span;
        match &instruction.control {
            Control::Bind(binding, value, _) => {
                let bind = self.push(FlowAction::Bind(*binding), span, vec![next]);
                self.expression(*value, bind, targets, None)
            }
            Control::Destructure {
                pattern,
                value,
                otherwise,
                ..
            } => {
                let bind = self.push(FlowAction::Pattern(*pattern), span, vec![next]);
                let decision = if let Some(otherwise) = otherwise {
                    let failure = self.instructions(otherwise, next, targets)?;
                    self.push(FlowAction::Branch(*pattern), span, vec![bind, failure])
                } else {
                    bind
                };
                self.expression(*value, decision, targets, None)
            }
            Control::Assign(root, projection, value) => {
                let assign = self.push(FlowAction::Assign(root.clone()), span, vec![next]);
                let value_entry = self.expression(*value, assign, targets, None)?;
                if let Projection::Array(index) = projection {
                    self.expression(*index, value_entry, targets, None)
                } else {
                    Ok(value_entry)
                }
            }
            Control::While(condition, body) => {
                self.while_loop(*condition, body, next, targets, label, span)
            }
            Control::Loop(body) => self.loop_body(body, next, targets, label, span),
            Control::For(init, condition, step, body) => {
                let decision = self.push(FlowAction::Branch(*condition), span, vec![]);
                let condition_entry = self.expression(*condition, decision, targets, None)?;
                let mut loop_targets = targets.to_vec();
                let step_entry = self.instruction(step, condition_entry, targets, None)?;
                loop_targets.push(Target {
                    name: label.map(str::to_owned),
                    break_to: next,
                    continue_to: Some(step_entry),
                });
                let body_entry = self.instructions(body, step_entry, &loop_targets)?;
                self.nodes[decision.0].successors = vec![body_entry, next];
                self.instruction(init, condition_entry, targets, None)
            }
            Control::Labeled(name, inner) => {
                if matches!(
                    inner.control,
                    Control::While(..) | Control::Loop(..) | Control::For(..)
                ) {
                    self.instruction(inner, next, targets, Some(name))
                } else {
                    let mut labeled = targets.to_vec();
                    labeled.push(Target {
                        name: Some(name.clone()),
                        break_to: next,
                        continue_to: None,
                    });
                    self.instruction(inner, next, &labeled, None)
                }
            }
            Control::Return(value) => {
                let end = self.push(FlowAction::Return, span, vec![self.exit]);
                match value {
                    Some(value) => self.expression(*value, end, targets, None),
                    None => Ok(end),
                }
            }
            Control::Break(label, value) => {
                let target = targets
                    .iter()
                    .rev()
                    .find(|target| match label {
                        Some(name) => target.name.as_deref() == Some(name),
                        None => target.continue_to.is_some(),
                    })
                    .ok_or_else(|| format!("typed flow has no break target for {label:?}"))?;
                let end = self.push(FlowAction::Break, span, vec![target.break_to]);
                match value {
                    Some(value) => self.expression(*value, end, targets, None),
                    None => Ok(end),
                }
            }
            Control::Continue(label) => {
                let target = targets
                    .iter()
                    .rev()
                    .find(|target| match label {
                        Some(name) => target.name.as_deref() == Some(name),
                        None => target.continue_to.is_some(),
                    })
                    .and_then(|target| target.continue_to)
                    .ok_or_else(|| format!("typed flow has no continue target for {label:?}"))?;
                Ok(self.push(FlowAction::Continue, span, vec![target]))
            }
            Control::Evaluate(value) => self.expression(*value, next, targets, None),
        }
    }

    fn while_loop(
        &mut self,
        condition: NodeId,
        body: &[Instruction],
        next: FlowNodeId,
        targets: &[Target],
        label: Option<&str>,
        span: Option<Span>,
    ) -> Result<FlowNodeId, String> {
        let decision = self.push(FlowAction::Branch(condition), span, vec![]);
        let condition_entry = self.expression(condition, decision, targets, None)?;
        let mut loop_targets = targets.to_vec();
        loop_targets.push(Target {
            name: label.map(str::to_owned),
            break_to: next,
            continue_to: Some(condition_entry),
        });
        let body_entry = self.instructions(body, condition_entry, &loop_targets)?;
        self.nodes[decision.0].successors = vec![body_entry, next];
        Ok(condition_entry)
    }

    fn loop_body(
        &mut self,
        body: &[Instruction],
        next: FlowNodeId,
        targets: &[Target],
        label: Option<&str>,
        span: Option<Span>,
    ) -> Result<FlowNodeId, String> {
        let header = self.push(FlowAction::LoopHead, span, vec![]);
        let mut loop_targets = targets.to_vec();
        loop_targets.push(Target {
            name: label.map(str::to_owned),
            break_to: next,
            continue_to: Some(header),
        });
        let body_entry = self.instructions(body, header, &loop_targets)?;
        self.nodes[header.0].successors = vec![body_entry];
        Ok(header)
    }

    fn expression(
        &mut self,
        id: NodeId,
        next: FlowNodeId,
        targets: &[Target],
        label: Option<&str>,
    ) -> Result<FlowNodeId, String> {
        let node = &self.body.nodes[id.0];
        let span = node.span;
        match &node.kind {
            NodeKind::If {
                condition,
                then_value,
                else_value,
                ..
            } => {
                let true_entry = self.expression(*then_value, next, targets, None)?;
                let false_entry = match else_value {
                    Some(value) => self.expression(*value, next, targets, None)?,
                    None => next,
                };
                let decision =
                    self.push(FlowAction::Branch(id), span, vec![true_entry, false_entry]);
                self.expression(*condition, decision, targets, None)
            }
            NodeKind::Match { value, arms, .. } => {
                // Try arms in source order. A failed pattern or guard resumes
                // at the next arm; only the successful edge binds its pattern.
                let mut entry = self.push(FlowAction::Diverge, span, vec![]);
                for arm in arms.iter().rev() {
                    entry = self.match_arm(*arm, next, entry, targets)?;
                }
                let decision = self.push(FlowAction::Branch(id), span, vec![entry]);
                self.expression(*value, decision, targets, None)
            }
            NodeKind::MatchArm { .. } => Err("typed match arm has no dispatch".into()),
            NodeKind::Block(body) => self.instructions(body, next, targets),
            NodeKind::Loop(body) => self.loop_body(body, next, targets, label, span),
            NodeKind::Labeled(name, value) => self.expression(*value, next, targets, Some(name)),
            NodeKind::Form {
                children, numeric, ..
            } if numeric.as_ref().is_some_and(|numeric| {
                matches!(
                    numeric.operation,
                    NumericOpcode::LogicalAnd | NumericOpcode::LogicalOr
                )
            }) && children.len() == 3 =>
            {
                let done = self.push(FlowAction::Evaluate(id), span, vec![next]);
                let right = self.expression(children[2], done, targets, None)?;
                let (yes, no) = if numeric
                    .as_ref()
                    .is_some_and(|numeric| numeric.operation == NumericOpcode::LogicalAnd)
                {
                    (right, done)
                } else {
                    (done, right)
                };
                let decision = self.push(FlowAction::Branch(id), span, vec![yes, no]);
                self.expression(children[1], decision, targets, None)
            }
            NodeKind::Form { head, .. } if matches!(head.as_str(), "panic" | "unreachable") => {
                Ok(self.push(FlowAction::Diverge, span, vec![]))
            }
            NodeKind::Form { children, .. } => {
                let mut entry = if node.ty.is_some() {
                    self.push(FlowAction::Evaluate(id), span, vec![next])
                } else {
                    next
                };
                for child in children.iter().skip(1).rev() {
                    entry = self.expression(*child, entry, targets, None)?;
                }
                Ok(entry)
            }
            NodeKind::Syntax(children) => {
                let mut entry = next;
                for child in children.iter().rev() {
                    entry = self.expression(*child, entry, targets, None)?;
                }
                Ok(entry)
            }
            NodeKind::Quoted(..) => Ok(next),
            NodeKind::Declaration(..) | NodeKind::Symbol { .. } | NodeKind::Literal(..) => {
                if node.ty.is_some() {
                    Ok(self.push(FlowAction::Evaluate(id), span, vec![next]))
                } else {
                    Ok(next)
                }
            }
        }
    }

    fn match_arm(
        &mut self,
        id: NodeId,
        next: FlowNodeId,
        failure: FlowNodeId,
        targets: &[Target],
    ) -> Result<FlowNodeId, String> {
        let node = &self.body.nodes[id.0];
        let NodeKind::MatchArm { pattern, values } = &node.kind else {
            return Err("typed match dispatch has a non-arm target".into());
        };
        let pattern = *pattern;
        let span = node.span;
        let (guard, body) = match values.as_slice() {
            [body] => (None, *body),
            [guard, body] => {
                let NodeKind::Form { head, children, .. } = &self.body.nodes[guard.0].kind else {
                    return Err("typed match guard is not a form".into());
                };
                if head != "when" || children.len() != 2 {
                    return Err("typed match guard has an invalid shape".into());
                }
                (Some(children[1]), *body)
            }
            _ => return Err("typed match arm has an invalid shape".into()),
        };
        let body_entry = self.expression(body, next, targets, None)?;
        let success = if let Some(guard) = guard {
            let decision = self.push(
                FlowAction::Branch(guard),
                self.body.nodes[guard.0].span,
                vec![body_entry, failure],
            );
            self.expression(guard, decision, targets, None)?
        } else {
            body_entry
        };
        let bound = self.push(FlowAction::Pattern(pattern), span, vec![success]);
        Ok(self.push(FlowAction::Branch(pattern), span, vec![bound, failure]))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn definite_binding_requires_every_live_predecessor() {
        let mut body = Body::default();
        body.bindings.push(crate::typed_body::Binding {
            name: "value".into(),
            ty: crate::Type::U64,
        });
        body.nodes.push(crate::typed_body::Node {
            ty: Some(crate::Type::U64),
            span: None,
            kind: NodeKind::Symbol {
                name: "value".into(),
                binding: Some(BindingId(0)),
            },
        });
        let mut graph = FlowGraph {
            nodes: vec![
                FlowNode {
                    action: FlowAction::Exit,
                    successors: vec![],
                    span: None,
                },
                FlowNode {
                    action: FlowAction::Evaluate(NodeId(0)),
                    successors: vec![FlowNodeId(0)],
                    span: None,
                },
                FlowNode {
                    action: FlowAction::Bind(BindingId(0)),
                    successors: vec![FlowNodeId(1)],
                    span: None,
                },
                FlowNode {
                    action: FlowAction::Diverge,
                    successors: vec![],
                    span: None,
                },
                FlowNode {
                    action: FlowAction::Branch(NodeId(0)),
                    successors: vec![FlowNodeId(2), FlowNodeId(1)],
                    span: None,
                },
                FlowNode {
                    action: FlowAction::Entry,
                    successors: vec![FlowNodeId(4)],
                    span: None,
                },
            ],
            entry: FlowNodeId(5),
            exit: FlowNodeId(0),
        };
        assert!(graph.check_definite_bindings(&body, 0).is_err());
        graph.nodes[4].successors[1] = FlowNodeId(3);
        graph.check_definite_bindings(&body, 0).unwrap();
    }

    #[test]
    fn return_cuts_off_later_statements() {
        let mut body = Body::default();
        for value in [1, 2] {
            body.nodes.push(crate::typed_body::Node {
                ty: Some(crate::Type::U64),
                span: None,
                kind: NodeKind::Literal(crate::Expr::Integer(value)),
            });
            body.instructions.push(Instruction {
                span: None,
                control: Control::Return(Some(NodeId(body.nodes.len() - 1))),
            });
        }
        let graph = FlowGraph::lower(&body).unwrap();
        let reachable = graph.reachable();
        let returns = graph
            .nodes
            .iter()
            .enumerate()
            .filter(|(_, node)| matches!(node.action, FlowAction::Return))
            .collect::<Vec<_>>();
        assert_eq!(returns.len(), 2);
        assert_eq!(
            returns
                .iter()
                .filter(|(index, _)| reachable.contains(&FlowNodeId(*index)))
                .count(),
            1
        );
    }

    #[test]
    fn checked_flow_has_explicit_if_match_and_short_circuit_edges() {
        let source = "(#enum Choice ((Some u64) None))
          (#fn main () u64
            (#let flag bool (#bool.&& true false))
            (#return (#if flag
              (#match (Some 42u64)
                (#case (Some value) value)
                (#case None 0u64))
              0u64)))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let graph = &checked.declarations().flows["main"];
        let branches = graph
            .nodes
            .iter()
            .filter_map(|node| match node.action {
                FlowAction::Branch(id) => Some((id, node)),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert!(branches.iter().any(|(id, node)| {
            matches!(body.nodes[id.0].kind, NodeKind::If { .. }) && node.successors.len() == 2
        }));
        assert!(branches.iter().any(|(id, node)| {
            matches!(body.nodes[id.0].kind, NodeKind::Match { .. }) && node.successors.len() == 1
        }));
        assert!(branches.iter().any(|(id, node)| {
            matches!(body.nodes[id.0].kind, NodeKind::Form { .. }) && node.successors.len() == 2
        }));
        assert!(graph.reachable().contains(&graph.exit));
    }

    #[test]
    fn guarded_match_failure_reaches_next_arm_without_its_bindings() {
        let program =
            crate::parse_program(include_str!("../examples/match_guard_fallback.lim")).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let graph = &checked.declarations().flows["main"];
        let dispatch = graph
            .nodes
            .iter()
            .find(|node| {
                matches!(node.action, FlowAction::Branch(id) if matches!(body.nodes[id.0].kind, NodeKind::Match { .. }))
            })
            .unwrap();
        let first = dispatch.successors[0];
        let first_node = &graph.nodes[first.0];
        assert!(matches!(first_node.action, FlowAction::Branch(_)));
        let fallback = first_node.successors[1];
        assert!(matches!(
            graph.nodes[fallback.0].action,
            FlowAction::Branch(_)
        ));
        let bound = first_node.successors[0];
        assert!(matches!(
            graph.nodes[bound.0].action,
            FlowAction::Pattern(_)
        ));

        let mut pending = vec![bound];
        let mut seen = HashSet::new();
        let mut guard = None;
        while let Some(id) = pending.pop() {
            if !seen.insert(id) {
                continue;
            }
            if matches!(graph.nodes[id.0].action, FlowAction::Branch(_)) {
                guard = Some(id);
                break;
            }
            pending.extend(graph.nodes[id.0].successors.iter().copied());
        }
        let guard = guard.expect("guard branch after pattern binding");
        assert_eq!(graph.nodes[guard.0].successors[1], fallback);
        graph
            .check_definite_bindings(body, 0)
            .expect("guarded fallback has valid local scopes");
    }

    #[test]
    fn labeled_loop_breaks_and_continues_have_real_targets() {
        let program = crate::parse_program(include_str!("../examples/labeled_loop.lim")).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let graph = &checked.declarations().flows["main"];
        let reachable = graph.reachable();
        let breaks = graph
            .nodes
            .iter()
            .filter(|node| matches!(node.action, FlowAction::Break))
            .collect::<Vec<_>>();
        let continues = graph
            .nodes
            .iter()
            .filter(|node| matches!(node.action, FlowAction::Continue))
            .collect::<Vec<_>>();
        assert!(!breaks.is_empty());
        assert!(!continues.is_empty());
        for node in breaks.into_iter().chain(continues) {
            assert_eq!(node.successors.len(), 1);
            assert!(reachable.contains(&node.successors[0]));
        }
        assert!(graph.nodes.iter().any(|node| {
            matches!(node.action, FlowAction::Return) && node.successors == vec![graph.exit]
        }));
    }
}
