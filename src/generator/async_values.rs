//! Evaluated values outstanding at original awaits modeled as ordinary calls.
//! Implementation detail of built-in code generation, not runtime semantics.
//!
//! This is a value capture plan, not frame emission or an ownership proof. The
//! frontier is immediately BEFORE the mapped call: it includes the enclosing
//! operation's unfinished operands and this call's evaluated arguments. Await
//! lowering must account for arguments transferred into the child rather than
//! duplicating them in Pending storage. Named locals, place addresses, explicit
//! cleanup, slot initialization, and stable-frame lifetimes need separate planning.
//! Pass the storage facts' own flow and feed each vector to
//! `async_storage::Analysis::before_with_values` at the corresponding call.
//!
//! Structured checked bodies determine evaluation order and selected joins.
//! Flow edges determine reachability and identify call events; neither arena
//! numbering nor source spans determine execution order. In particular, a
//! completed branch/block/loop is one value, not all of its producer operands.
#![allow(dead_code)] // Deliberately separate until the source/graph planner is wired.

use std::collections::{HashMap, HashSet};

use crate::linearcheck::LinearTypes;
use crate::typed_body::{Body, Control, Instruction, NodeId, NodeKind, NumericOpcode, Projection};
use crate::typed_flow::{FlowAction, FlowGraph, FlowNodeId};
use crate::typed_place::Place;
use crate::Type;

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Error {
    pub value: Option<NodeId>,
    pub message: String,
}

fn error(value: Option<NodeId>, message: impl Into<String>) -> Error {
    Error {
        value,
        message: message.into(),
    }
}

pub(crate) type Plan = HashMap<NodeId, Vec<NodeId>>;

fn is_handle(ty: Option<&Type>) -> bool {
    matches!(
        ty,
        Some(
            Type::Reference { .. }
                | Type::PinnedReference { .. }
                | Type::RawPointer { .. }
                | Type::Slice(_)
                | Type::MutableSlice(_)
        )
    )
}

fn reachable(flow: &FlowGraph) -> Result<HashSet<FlowNodeId>, Error> {
    let mut seen = HashSet::new();
    let mut work = vec![flow.entry];
    while let Some(event) = work.pop() {
        let node = flow
            .nodes
            .get(event.0)
            .ok_or_else(|| error(None, "value planning received an invalid flow edge"))?;
        if seen.insert(event) {
            work.extend(node.successors.iter().copied());
        }
    }
    Ok(seen)
}

fn call_events(flow: &FlowGraph) -> HashMap<NodeId, Vec<FlowNodeId>> {
    let mut events: HashMap<NodeId, Vec<FlowNodeId>> = HashMap::new();
    for (index, node) in flow.nodes.iter().enumerate() {
        if let FlowAction::Evaluate(value) = node.action {
            events.entry(value).or_default().push(FlowNodeId(index));
        }
    }
    events
}

/// Completion frontiers for values without their own Evaluate event (selected
/// branch results, block tails, and value-loop breaks). These are alternatives,
/// not a request to store every producer. A loop head is never a completion.
fn completions(
    body: &Body,
    flow: &FlowGraph,
    value: NodeId,
    active: &mut HashSet<NodeId>,
) -> Result<HashSet<FlowNodeId>, Error> {
    if !active.insert(value) {
        return Err(error(Some(value), "cyclic value completion structure"));
    }
    let mut found = HashSet::new();
    let scoped_borrow = matches!(&body.nodes[value.0].kind,
        NodeKind::Form { head, children, .. }
            if matches!(head.as_str(), "borrow" | "borrow-mut") && children.len() == 3);
    for (index, node) in flow.nodes.iter().enumerate() {
        let complete = match node.action {
            FlowAction::Evaluate(id)
            | FlowAction::Read { value: id, .. }
            | FlowAction::Clone { value: id, .. }
            | FlowAction::Write { value: id, .. }
            | FlowAction::Release { value: id, .. } => id == value,
            FlowAction::Borrow { value: id, .. } => id == value && !scoped_borrow,
            FlowAction::BorrowScopeEnd { scope } => scoped_borrow && scope == value,
            FlowAction::Break {
                result: Some(id), ..
            } => id == value,
            _ => false,
        };
        if complete {
            found.insert(FlowNodeId(index));
        }
    }
    if found.is_empty() {
        let producers: Vec<NodeId> = match &body.nodes[value.0].kind {
            NodeKind::If {
                then_value,
                else_value,
                ..
            } => std::iter::once(*then_value).chain(*else_value).collect(),
            NodeKind::Match { arms, .. } => arms
                .iter()
                .filter_map(|arm| {
                    if let NodeKind::MatchArm { values, .. } = &body.nodes[arm.0].kind {
                        values.last().copied()
                    } else {
                        None
                    }
                })
                .collect(),
            NodeKind::Block(instructions) => match instructions.last().map(|tail| &tail.control) {
                Some(Control::Evaluate(tail)) => vec![*tail],
                _ => Vec::new(),
            },
            NodeKind::Labeled(_, child) => vec![*child],
            _ => Vec::new(),
        };
        for producer in producers {
            if body.nodes[producer.0].ty == Some(Type::Never) {
                continue;
            }
            found.extend(completions(body, flow, producer, active)?);
        }
    }
    active.remove(&value);
    Ok(found)
}

/// A path to the pre-call event bypassing every completion frontier proves
/// that a snapshot is not definitely evaluated. This uses edges, never event
/// indices as timestamps, and works with selected producers and loop cycles.
fn initialized(flow: &FlowGraph, event: FlowNodeId, completed: &HashSet<FlowNodeId>) -> bool {
    let mut seen = HashSet::new();
    let mut pending = vec![flow.entry];
    while let Some(next) = pending.pop() {
        if next == event {
            return false;
        }
        if completed.contains(&next) || !seen.insert(next) {
            continue;
        }
        pending.extend(flow.nodes[next.0].successors.iter().copied());
    }
    true
}

/// Plan evaluated operands at mapped await result identities (ordinary call
/// nodes). Unreachable sites are omitted. Output vectors follow structured
/// evaluation order, with enclosing operands first and duplicate IDs removed.
/// No child protocol or consumption contract is assumed by this API.
/// Reachable guard awaits with move-only preview bindings require alias-aware
/// emission and are rejected using the checked program's LinearTypes.
pub(crate) fn plan_with_types(
    body: &Body,
    flow: &FlowGraph,
    await_results: &[NodeId],
    types: &LinearTypes,
) -> Result<Plan, Error> {
    plan_impl(body, flow, await_results, Some(types))
}

// Legacy planner fixtures do not model linear preview aliases. Production
// must always use plan_with_types and the checked program's type declarations.
#[cfg(test)]
fn plan(body: &Body, flow: &FlowGraph, await_results: &[NodeId]) -> Result<Plan, Error> {
    plan_impl(body, flow, await_results, None)
}

fn plan_impl(
    body: &Body,
    flow: &FlowGraph,
    await_results: &[NodeId],
    types: Option<&LinearTypes>,
) -> Result<Plan, Error> {
    let awaits: HashSet<_> = await_results.iter().copied().collect();
    let live = reachable(flow)?;
    let events = call_events(flow);
    for &value in &awaits {
        let node = body
            .nodes
            .get(value.0)
            .ok_or_else(|| error(Some(value), "await result is outside the checked body"))?;
        if node.ty.is_none()
            || !matches!(
                &node.kind,
                NodeKind::Form {
                    callee: Some(_),
                    ..
                }
            )
        {
            return Err(error(
                Some(value),
                "await result must identify a checked ordinary call",
            ));
        }
        let Some(found) = events.get(&value) else {
            return Err(error(
                Some(value),
                "mapped await has no ordinary call event",
            ));
        };
        if found.iter().filter(|event| live.contains(event)).count() > 1 {
            return Err(error(
                Some(value),
                "mapped await has multiple reachable call events",
            ));
        }
    }
    let mut walker = Walker {
        body,
        flow,
        awaits,
        live,
        events,
        active: HashSet::new(),
        visited: HashSet::new(),
        output: HashMap::new(),
        types,
        exclusive_preview: false,
    };
    walker.instructions(&body.instructions, &[])?;
    for &value in &walker.awaits {
        if !walker.visited.contains(&value) {
            return Err(error(
                Some(value),
                "mapped await occurs in unsupported syntax or metadata",
            ));
        }
    }
    Ok(walker.output)
}

struct Walker<'a> {
    body: &'a Body,
    flow: &'a FlowGraph,
    types: Option<&'a LinearTypes>,
    exclusive_preview: bool,
    awaits: HashSet<NodeId>,
    live: HashSet<FlowNodeId>,
    events: HashMap<NodeId, Vec<FlowNodeId>>,
    active: HashSet<NodeId>,
    visited: HashSet<NodeId>,
    output: Plan,
}

impl Walker<'_> {
    fn push_value(&self, held: &mut Vec<NodeId>, value: NodeId) -> Result<(), Error> {
        let ty = self
            .body
            .nodes
            .get(value.0)
            .and_then(|node| node.ty.as_ref())
            .ok_or_else(|| error(Some(value), "runtime operand has no checked type"))?;
        // Unit has effects but needs no value storage; Never never completes.
        if !matches!(ty, Type::Unit | Type::Never) && !held.contains(&value) {
            held.push(value);
        }
        Ok(())
    }

    fn record(&mut self, site: NodeId, held: &[NodeId]) -> Result<(), Error> {
        if !self.awaits.contains(&site) {
            return Ok(());
        }
        if !self.visited.insert(site) {
            return Err(error(
                Some(site),
                "await identity is shared by multiple structured occurrences",
            ));
        }
        if let Some(event) = self.events[&site]
            .iter()
            .copied()
            .find(|event| self.live.contains(event))
        {
            if self.exclusive_preview {
                return Err(error(Some(site),
                    "exclusive/linear preview alias emission is not implemented for awaits inside match guards"));
            }
            for &value in held {
                let completed = completions(self.body, self.flow, value, &mut HashSet::new())?;
                if completed.is_empty() || !initialized(self.flow, event, &completed) {
                    return Err(error(
                        Some(value),
                        "outstanding operand is not definitely evaluated before the await call",
                    ));
                }
            }
            self.output.insert(site, held.to_vec());
        }
        Ok(())
    }

    fn pattern_requires_move(&self, pattern: NodeId) -> Result<bool, Error> {
        let Some(types) = self.types else {
            return Ok(false);
        };
        let mut pending = vec![pattern];
        let mut seen = HashSet::new();
        let mut bindings = HashSet::new();
        while let Some(value) = pending.pop() {
            if !seen.insert(value) {
                continue;
            }
            let node = self
                .body
                .nodes
                .get(value.0)
                .ok_or_else(|| error(Some(value), "pattern is outside the checked body"))?;
            match &node.kind {
                NodeKind::Symbol {
                    binding: Some(binding),
                    ..
                } => {
                    bindings.insert(*binding);
                }
                NodeKind::Form { children, .. } | NodeKind::Syntax(children) => {
                    pending.extend(children.iter().copied())
                }
                NodeKind::Labeled(_, child) => pending.push(*child),
                NodeKind::Symbol { binding: None, .. }
                | NodeKind::Declaration(_)
                | NodeKind::Literal(_) => {}
                _ => return Err(error(Some(value), "unsupported checked guard pattern")),
            }
        }
        for binding in bindings {
            let binding = self
                .body
                .bindings
                .get(binding.0)
                .ok_or_else(|| error(Some(pattern), "guard pattern has no checked binding"))?;
            if types.requires_move(&binding.ty) {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn instructions(&mut self, instructions: &[Instruction], held: &[NodeId]) -> Result<(), Error> {
        for instruction in instructions {
            self.instruction(instruction, held)?;
        }
        Ok(())
    }

    fn instruction(&mut self, instruction: &Instruction, held: &[NodeId]) -> Result<(), Error> {
        match &instruction.control {
            Control::Bind(_, value, _) | Control::Evaluate(value) => self.expression(*value, held),
            Control::Destructure {
                value, otherwise, ..
            } => {
                self.expression(*value, held)?;
                if let Some(otherwise) = otherwise {
                    self.instructions(otherwise, held)?;
                }
                Ok(())
            }
            Control::Assign(_, projection, value) => {
                let mut operands = held.to_vec();
                if let Projection::Array(index) = projection {
                    self.expression(*index, held)?;
                    self.push_value(&mut operands, *index)?;
                }
                self.expression(*value, &operands)
            }
            Control::While(condition, body) => {
                self.expression(*condition, held)?;
                self.instructions(body, held)
            }
            Control::Loop(body) => self.instructions(body, held),
            Control::For(init, condition, step, body) => {
                self.instruction(init, held)?;
                self.expression(*condition, held)?;
                self.instructions(body, held)?;
                self.instruction(step, held)
            }
            Control::Labeled(_, instruction) => self.instruction(instruction, held),
            Control::Return(value) | Control::Break(_, value) => {
                if let Some(value) = value {
                    self.expression(*value, held)?;
                }
                Ok(())
            }
            Control::Continue(_) => Ok(()),
        }
    }

    fn expression(&mut self, value: NodeId, held: &[NodeId]) -> Result<(), Error> {
        let node = self
            .body
            .nodes
            .get(value.0)
            .ok_or_else(|| error(Some(value), "operand is outside the checked body"))?;
        let kind = node.kind.clone();
        if !self.active.insert(value) {
            return Err(error(Some(value), "cyclic checked expression structure"));
        }
        let result = match kind {
            NodeKind::If {
                condition,
                then_value,
                else_value,
                ..
            } => {
                self.expression(condition, held)?;
                // The condition selects an arm; it is not an outstanding operand.
                self.expression(then_value, held)?;
                if let Some(other) = else_value {
                    self.expression(other, held)?;
                }
                Ok(())
            }
            NodeKind::Match {
                value: source,
                arms,
                ..
            } => {
                self.expression(source, held)?;
                for arm in arms {
                    let NodeKind::MatchArm { pattern, values } =
                        self.body.nodes[arm.0].kind.clone()
                    else {
                        return Err(error(Some(arm), "checked match has no structured arm"));
                    };
                    match values.as_slice() {
                        [body] => self.expression(*body, held)?,
                        [guard, body] => {
                            let NodeKind::Form { head, children, .. } =
                                self.body.nodes[guard.0].kind.clone()
                            else {
                                return Err(error(Some(*guard), "unsupported match guard"));
                            };
                            if head != "when" || children.len() != 2 {
                                return Err(error(Some(*guard), "unsupported match guard"));
                            }
                            let mut preview = held.to_vec();
                            self.push_value(&mut preview, source)?;
                            // Rejecting a guard resumes matching the evaluated
                            // scrutinee. Committing a pattern consumes/transfers
                            // it; the arm body needs bindings, not another copy.
                            // Preview bindings alias the uncommitted scrutinee.
                            // Until alias-aware emission exists, move-only
                            // payloads cannot be independently stored at await.
                            // Preserve outer guard context through nested matches.
                            let outer_preview = self.exclusive_preview;
                            let requires_alias = self.pattern_requires_move(pattern)?;
                            self.exclusive_preview = outer_preview || requires_alias;
                            let result = self.expression(children[1], &preview);
                            self.exclusive_preview = outer_preview;
                            result?;
                            self.expression(*body, held)?;
                        }
                        _ => return Err(error(Some(arm), "unsupported match arm sequence")),
                    }
                }
                Ok(())
            }
            NodeKind::Block(instructions) | NodeKind::Loop(instructions) => {
                self.instructions(&instructions, held)
            }
            NodeKind::Labeled(_, child) => self.expression(child, held),
            NodeKind::Form {
                head,
                children,
                numeric,
                callee,
                argument_source_order,
            } => {
                if numeric.as_ref().is_some_and(|operation| {
                    matches!(
                        operation.operation,
                        NumericOpcode::LogicalAnd | NumericOpcode::LogicalOr
                    )
                }) && children.len() == 3
                {
                    self.expression(children[1], held)?;
                    self.expression(children[2], held)?;
                    Ok(())
                } else if callee.is_some() || argument_source_order.is_some() {
                    let operands = (0..children.len().saturating_sub(1))
                        .map(|index| {
                            children[argument_source_order
                                .as_ref()
                                .map_or(index, |order| order[index])
                                + 1]
                        })
                        .collect::<Vec<_>>();
                    self.operands(value, &operands, held)
                } else {
                    self.form(value, &head, &children, held)
                }
            }
            NodeKind::Declaration(_) | NodeKind::Symbol { .. } | NodeKind::Literal(_) => Ok(()),
            NodeKind::Quoted(..) | NodeKind::Syntax(_) => Ok(()),
            NodeKind::MatchArm { .. } => {
                Err(error(Some(value), "match arm outside structured dispatch"))
            }
        };
        self.active.remove(&value);
        result
    }

    fn operands(
        &mut self,
        result: NodeId,
        operands: &[NodeId],
        held: &[NodeId],
    ) -> Result<(), Error> {
        let mut pending = held.to_vec();
        for &operand in operands {
            // Types, field/constructor names, and literal syntax are not values.
            if self.body.nodes[operand.0].ty.is_none() {
                continue;
            }
            self.expression(operand, &pending)?;
            self.push_value(&mut pending, operand)?;
        }
        self.record(result, &pending)
    }

    fn form(
        &mut self,
        value: NodeId,
        head: &str,
        children: &[NodeId],
        held: &[NodeId],
    ) -> Result<(), Error> {
        match head {
            "literal" | "size-of" | "align-of" | "offset-of" | "panic" | "unreachable" => Ok(()),
            "get"
            | "get-payload"
            | "pin-get-payload"
            | "pin-get-payload-mut"
            | "pin-get-payload-unchecked"
            | "pin-get-payload-unchecked-mut"
            | "index"
            | "index-proven"
                if Place::from_expression(self.body, value).is_some() =>
            {
                self.place(value, &mut held.to_vec(), true)
            }
            "get"
            | "get-payload"
            | "pin-get-payload"
            | "pin-get-payload-mut"
            | "pin-get-payload-unchecked"
            | "pin-get-payload-unchecked-mut"
            | "as"
                if children.len() >= 2 =>
            {
                self.expression(children[1], held)
            }
            "borrow" | "borrow-mut" | "pin-borrow" | "pin-borrow-mut" | "clone" | "drop"
            | "forget"
                if children.len() >= 2 =>
            {
                let mut pending = held.to_vec();
                self.place(children[1], &mut pending, false)?;
                if children.len() == 3 && matches!(head, "borrow" | "borrow-mut") {
                    self.expression(children[2], &pending)?;
                } else if children.len() != 2 {
                    return Err(error(Some(value), "unsupported place operation arity"));
                }
                Ok(())
            }
            "pin-set-field" if children.len() == 4 => {
                self.operands(value, &[children[1], children[3]], held)
            }
            "array-repeat" => {
                // Some ordinary aggregate paths evaluate the element once per
                // destination. One NodeId cannot identify those dynamic sites.
                if self.contains_await(value, &mut HashSet::new())
                    && !matches!(self.body.nodes[value.0].ty, Some(Type::Array(_, 1)))
                {
                    return Err(error(
                        Some(value),
                        "suspending repeated array element has ambiguous evaluation multiplicity",
                    ));
                }
                self.operands(value, &children[1..], held)
            }
            "asm" => {
                if self.contains_await(value, &mut HashSet::new()) {
                    return Err(error(
                        Some(value),
                        "suspending assembly input needs an explicit operand-order model",
                    ));
                }
                Ok(())
            }
            _ => self.operands(value, &children[1..], held),
        }
    }

    /// Evaluate address components without moving the addressed owner. Dynamic
    /// indices and reference/descriptor snapshots ARE values; lexical roots
    /// and projection metadata are delegated to the place/storage planner.
    fn place(
        &mut self,
        value: NodeId,
        pending: &mut Vec<NodeId>,
        load_handle: bool,
    ) -> Result<(), Error> {
        if Place::from_expression(self.body, value).is_none() {
            self.expression(value, pending)?;
            return self.push_value(pending, value);
        }
        match self.body.nodes[value.0].kind.clone() {
            NodeKind::Symbol { .. } | NodeKind::Declaration(_) => {
                if load_handle && is_handle(self.body.nodes[value.0].ty.as_ref()) {
                    self.expression(value, pending)?;
                    self.push_value(pending, value)?;
                }
                Ok(())
            }
            NodeKind::Form { head, children, .. } => {
                if !matches!(
                    head.as_str(),
                    "get"
                        | "get-payload"
                        | "pin-get-payload"
                        | "pin-get-payload-mut"
                        | "pin-get-payload-unchecked"
                        | "pin-get-payload-unchecked-mut"
                        | "index"
                        | "index-proven"
                        | "slice-idx"
                        | "slice-mut-idx"
                        | "deref"
                        | "borrow"
                        | "borrow-mut"
                        | "pin-borrow"
                        | "pin-borrow-mut"
                ) {
                    return Err(error(
                        Some(value),
                        "unsupported outstanding place evaluation",
                    ));
                }
                let enclosing = pending.len();
                // Borrowing a reference cell uses its address, not its loaded
                // contents. Projection/index/dereference bases instead use
                // the evaluated handle when the base is reference-bearing.
                let base_is_value = !matches!(
                    head.as_str(),
                    "borrow" | "borrow-mut" | "pin-borrow" | "pin-borrow-mut"
                );
                self.place(children[1], pending, base_is_value)?;
                if matches!(
                    head.as_str(),
                    "index" | "index-proven" | "slice-idx" | "slice-mut-idx"
                ) {
                    self.expression(children[2], pending)?;
                    self.push_value(pending, children[2])?;
                }
                if load_handle && is_handle(self.body.nodes[value.0].ty.as_ref()) {
                    // This projection has finished loading a handle. Further
                    // address evaluation uses that snapshot, not a later load
                    // through its holder. Its own base/indices are now consumed;
                    // keep enclosing unfinished operands, then the loaded value.
                    pending.truncate(enclosing);
                    self.push_value(pending, value)?;
                }
                Ok(())
            }
            _ => Err(error(Some(value), "unsupported outstanding place root")),
        }
    }

    fn contains_await(&self, value: NodeId, seen: &mut HashSet<NodeId>) -> bool {
        if !seen.insert(value) {
            return false;
        }
        if self.awaits.contains(&value) {
            return true;
        }
        // Runtime traversal reports any other hidden site as unsupported. This
        // scan only detects special forms with nonstandard operand evaluation.
        match &self.body.nodes[value.0].kind {
            NodeKind::Form { children, .. } | NodeKind::Syntax(children) => children
                .iter()
                .any(|&child| self.contains_await(child, seen)),
            NodeKind::If {
                condition,
                then_value,
                else_value,
                ..
            } => {
                self.contains_await(*condition, seen)
                    || self.contains_await(*then_value, seen)
                    || else_value.is_some_and(|child| self.contains_await(child, seen))
            }
            NodeKind::Match { value, arms, .. } => {
                self.contains_await(*value, seen)
                    || arms.iter().any(|&arm| self.contains_await(arm, seen))
            }
            NodeKind::MatchArm { values, .. } => {
                values.iter().any(|&child| self.contains_await(child, seen))
            }
            NodeKind::Block(instructions) | NodeKind::Loop(instructions) => instructions
                .iter()
                .any(|instruction| self.instruction_contains_await(instruction, seen)),
            NodeKind::Labeled(_, child) => self.contains_await(*child, seen),
            _ => false,
        }
    }

    fn instruction_contains_await(
        &self,
        instruction: &Instruction,
        seen: &mut HashSet<NodeId>,
    ) -> bool {
        match &instruction.control {
            Control::Bind(_, value, _) | Control::Evaluate(value) => {
                self.contains_await(*value, seen)
            }
            Control::Assign(_, projection, value) => {
                self.contains_await(*value, seen)
                    || matches!(projection, Projection::Array(index) if self.contains_await(*index, seen))
            }
            Control::Destructure {
                value, otherwise, ..
            } => {
                self.contains_await(*value, seen)
                    || otherwise.as_ref().is_some_and(|body| {
                        body.iter()
                            .any(|i| self.instruction_contains_await(i, seen))
                    })
            }
            Control::While(condition, body) => {
                self.contains_await(*condition, seen)
                    || body
                        .iter()
                        .any(|i| self.instruction_contains_await(i, seen))
            }
            Control::Loop(body) => body
                .iter()
                .any(|i| self.instruction_contains_await(i, seen)),
            Control::For(init, condition, step, body) => {
                self.instruction_contains_await(init, seen)
                    || self.contains_await(*condition, seen)
                    || self.instruction_contains_await(step, seen)
                    || body
                        .iter()
                        .any(|i| self.instruction_contains_await(i, seen))
            }
            Control::Labeled(_, instruction) => self.instruction_contains_await(instruction, seen),
            Control::Return(value) | Control::Break(_, value) => {
                value.is_some_and(|value| self.contains_await(value, seen))
            }
            Control::Continue(_) => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::typed_ir::Declarations;

    const CONTEXT: &str = "
#fn first () #u64 (#return 11u64)
#fn second () #u64 (#return 22u64)
#fn await-a () #u64 (#return 1u64)
#fn await-b () #u64 (#return 2u64)
#fn await-value ((value #u64)) #u64 (#return value)
#fn combine ((first #u64) (second #u64)) #u64
          (#return (#u64::add-wrap first second))\n";

    fn prepare(source: &str) -> (crate::Program, Declarations) {
        let program = crate::parse_program(&format!("{CONTEXT}\n{source}")).unwrap();
        let declarations = crate::typecheck::resolve_program_for_analysis(&program, true).unwrap();
        (program, declarations)
    }

    fn calls(body: &Body, name: &str) -> Vec<NodeId> {
        body.nodes
            .iter()
            .enumerate()
            .filter_map(|(index, node)| {
                let NodeKind::Form {
                    callee: Some(callee),
                    ..
                } = &node.kind
                else {
                    return None;
                };
                (body.declaration_name(crate::typed_ir::DeclarationId::Function(*callee))
                    == Some(name))
                .then_some(NodeId(index))
            })
            .collect()
    }

    fn call(body: &Body, name: &str) -> NodeId {
        let found = calls(body, name);
        assert_eq!(found.len(), 1, "expected unique call to {name}");
        found[0]
    }

    fn named_values(body: &Body, values: &[NodeId]) -> Vec<String> {
        values
            .iter()
            .map(|&value| crate::expression_source(&body.syntax(value, false)).unwrap())
            .collect()
    }

    #[test]
    fn named_calls_hold_only_completed_written_operands() {
        let (_, declarations) = prepare(
            "#fn work () #u64
            (#return (#call combine ((second (#call await-a ())) (first (#call first ())))))\n",
        );
        let body = &declarations.bodies["work"];
        let site = call(body, "await-a");
        let captures = plan(body, &declarations.flows["work"], &[site]).unwrap();
        assert!(captures[&site].is_empty());
    }

    #[test]
    fn constructors_and_builtins_keep_only_completed_earlier_operands() {
        let (_, declarations) = prepare(
            "#struct Pair () ((left #u64) (right #u64))
#fn work () Pair (#return (#struct-literal Pair
              ((right (#u64::add-wrap (#call second ()) (#call await-a ())))
               (left (#call first ())))))\n",
        );
        let body = &declarations.bodies["work"];
        let site = call(body, "await-a");
        let captures = plan(body, &declarations.flows["work"], &[site]).unwrap();
        assert_eq!(captures[&site], [call(body, "second")]);
        assert!(captures[&site]
            .iter()
            .all(|id| body.nodes[id.0].ty.is_some()));
    }

    #[test]
    fn linear_and_reference_bearing_call_results_are_value_snapshots() {
        let (_, declarations) = prepare(
            "#struct Token (#linear) ((value #u64))
#struct Holder () ((view (#ref #u64)))
#fn token () Token (#return (#struct-literal Token ((value 7u64))))
#fn holder ((view (#ref #u64))) Holder (#return (#struct-literal Holder ((view view))))
#fn use-values ((owned Token) (borrowed Holder) (number #u64)) #u64
              (#forget owned) (#forget borrowed) (#return number)
#fn work ((view (#ref #u64))) #u64
              (#return (#call use-values ((owned (#call token ()))
                (borrowed (#call holder ((view view)))) (number (#call await-a ())))))\n",
        );
        let body = &declarations.bodies["work"];
        let site = call(body, "await-a");
        let values = plan(body, &declarations.flows["work"], &[site]).unwrap();
        assert_eq!(values[&site], [call(body, "token"), call(body, "holder")]);
        assert_eq!(
            body.nodes[values[&site][0].0].ty,
            Some(Type::Named("Token".into()))
        );
        assert_eq!(
            body.nodes[values[&site][1].0].ty,
            Some(Type::Named("Holder".into()))
        );
    }

    #[test]
    fn nested_await_results_reach_outer_and_later_sibling_calls() {
        let (_, declarations) = prepare(
            "#fn work () #u64 (#return (#call combine
            ((first (#call await-value ((value (#call await-a ())))))
             (second (#call await-b ())))))\n",
        );
        let body = &declarations.bodies["work"];
        let inner = call(body, "await-a");
        let outer = call(body, "await-value");
        let sibling = call(body, "await-b");
        let captures = plan(body, &declarations.flows["work"], &[inner, outer, sibling]).unwrap();
        assert!(captures[&inner].is_empty());
        assert_eq!(captures[&outer], [inner]);
        assert_eq!(captures[&sibling], [outer]);
    }

    #[test]
    fn joined_branch_and_loop_results_replace_their_producer_operands() {
        let (_, declarations) = prepare(
            "#fn work ((choose #bool)) #u64
            (#return (#call combine
              ((first (#if choose (#call first ()) (#loop (#break (#call second ())))))
               (second (#call await-a ())))))\n",
        );
        let body = &declarations.bodies["work"];
        let site = call(body, "await-a");
        let captures = plan(body, &declarations.flows["work"], &[site]).unwrap();
        assert_eq!(captures[&site].len(), 1);
        assert!(matches!(
            body.nodes[captures[&site][0].0].kind,
            NodeKind::If { .. }
        ));
        assert!(!captures[&site].contains(&call(body, "first")));
        assert!(!captures[&site].contains(&call(body, "second")));
    }

    #[test]
    fn guards_retain_the_scrutinee_but_committed_arm_bodies_do_not() {
        let (_, declarations) = prepare(
            "#enum Choice () ((Choice.Some #u64) Choice.None)
#fn make-choice () Choice (#return (Choice.Some 4u64))
#fn await-guard () #bool (#return true)
#fn work () #u64 (#return (#call combine
              ((first (#call first ())) (second (#match (#call make-choice ())
                (#case (Choice.Some value) (#when (#call await-guard ())) (#call await-a ()))
                (#case _ (#call await-b ())))))))\n",
        );
        let body = &declarations.bodies["work"];
        let guard = call(body, "await-guard");
        let arm = call(body, "await-a");
        let fallback = call(body, "await-b");
        let captures = plan(body, &declarations.flows["work"], &[guard, arm, fallback]).unwrap();
        assert_eq!(
            captures[&guard],
            [call(body, "first"), call(body, "make-choice")]
        );
        assert_eq!(captures[&arm], [call(body, "first")]);
        // The staged flow can prove that a constant true guard skips fallback.
        if let Some(values) = captures.get(&fallback) {
            assert_eq!(values, &[call(body, "first")]);
        }
    }

    fn preview_program(
        payload: &str,
        properties: &str,
        guard: &str,
        prefix: &str,
    ) -> (crate::Program, Declarations) {
        prepare(&format!(
            "#struct Token {properties} ((value #u64))
#enum Choice () ((Choice.Owned {payload}) Choice.Empty)
#fn await-guard () #bool (#return true)
#fn work ((choice Choice) (selected #bool)) #u64
              {prefix}
              (#return (#match choice
                (#case (Choice.Owned preview) (#when {guard})
                  (#block (#forget preview) (#call await-a ())))
                (#case (Choice.Owned committed) (#block (#forget committed) 0u64))
                (#case Choice.Empty 0u64)))\n"
        ))
    }

    #[test]
    fn production_guard_planning_distinguishes_custom_copy_and_linear_payloads() {
        // Custom aggregates are Copy unless #linear or exclusive fields make
        // them move-only; the language has no separate #copy annotation.
        for (properties, move_only) in [("()", false), ("(#linear)", true)] {
            let (program, declarations) =
                preview_program("Token", properties, "(#call await-guard ())", "");
            let types = LinearTypes::from_program(&program);
            let body = &declarations.bodies["work"];
            let flow = &declarations.flows["work"];
            let site = call(body, "await-guard");
            let preview = body
                .bindings
                .iter()
                .find(|binding| binding.name == "preview")
                .unwrap();
            assert_eq!(types.requires_move(&preview.ty), move_only);
            let result = plan_with_types(body, flow, &[site], &types);
            if move_only {
                let error = result.unwrap_err();
                assert_eq!(error.value, Some(site));
                assert!(error
                    .message
                    .contains("exclusive/linear preview alias emission"));
            } else {
                assert!(result.unwrap().contains_key(&site));
            }
            // The same move-only payload is committed before this body call.
            let committed = call(body, "await-a");
            assert!(plan_with_types(body, flow, &[committed], &types)
                .unwrap()
                .contains_key(&committed));
        }
    }

    #[test]
    fn production_guards_reject_exclusive_preview_bindings_including_nested_fields() {
        for payload in ["(#ref-mut #u64)", "Token"] {
            let source = if payload == "Token" {
                // An exclusive field is move-only without an explicit linear
                // annotation. Match the nested field, not the aggregate itself.
                "#struct Token (#linear) ((value (#ref-mut #u64)))
#enum Choice () ((Choice.Owned Token) Choice.Empty)
#fn await-guard () #bool (#return true)
#fn work ((choice Choice)) #u64
                      (#return (#match choice
                        (#case (Choice.Owned (Token preview)) (#when (#call await-guard ()))
                          (#block (#forget preview) 1u64))
                        (#case (Choice.Owned committed) (#block (#forget committed) 0u64))
                        (#case Choice.Empty 0u64)))\n"
            } else {
                ""
            };
            let (program, declarations) = if source.is_empty() {
                preview_program(payload, "()", "(#call await-guard ())", "")
            } else {
                prepare(source)
            };
            let types = LinearTypes::from_program(&program);
            let body = &declarations.bodies["work"];
            let site = call(body, "await-guard");
            let preview = body
                .bindings
                .iter()
                .find(|binding| binding.name == "preview")
                .unwrap();
            assert!(types.requires_move(&preview.ty));
            let error =
                plan_with_types(body, &declarations.flows["work"], &[site], &types).unwrap_err();
            assert_eq!(error.value, Some(site));
            assert!(error
                .message
                .contains("exclusive/linear preview alias emission"));
        }
    }

    #[test]
    fn production_guard_restriction_ignores_unreachable_awaits() {
        let (program, declarations) = preview_program(
            "Token",
            "()",
            "(#call await-guard ())",
            "(#forget choice) (#return 42u64)",
        );
        let types = LinearTypes::from_program(&program);
        let body = &declarations.bodies["work"];
        let site = call(body, "await-guard");
        assert!(
            plan_with_types(body, &declarations.flows["work"], &[site], &types)
                .unwrap()
                .is_empty()
        );
    }

    #[test]
    fn production_guard_restriction_preserves_outer_linear_preview_context() {
        let (program, declarations) = preview_program(
            "Token",
            "(#linear)",
            "(#match selected
              (#case true (#when (#call await-guard ())) true)
              (#case _ false))",
            "",
        );
        let types = LinearTypes::from_program(&program);
        let body = &declarations.bodies["work"];
        let site = call(body, "await-guard");
        let error =
            plan_with_types(body, &declarations.flows["work"], &[site], &types).unwrap_err();
        assert_eq!(error.value, Some(site));
        assert!(error
            .message
            .contains("exclusive/linear preview alias emission"));
    }

    #[test]
    fn production_scalar_previews_can_suspend() {
        let (program, declarations) = prepare(
            "#enum Choice () ((Choice.Some #u64) Choice.None)
#fn await-guard () #bool (#return true)
#fn work ((choice Choice)) #u64 (#return (#match choice
              (#case (Choice.Some preview) (#when (#call await-guard ())) preview)
              (#case _ 0u64)))\n",
        );
        let types = LinearTypes::from_program(&program);
        let body = &declarations.bodies["work"];
        let site = call(body, "await-guard");
        assert!(
            plan_with_types(body, &declarations.flows["work"], &[site], &types)
                .unwrap()
                .contains_key(&site)
        );
    }

    #[test]
    fn place_bases_and_projection_metadata_are_not_moved_operands() {
        let (_, declarations) = prepare(
            "#struct Pair () ((left #u64) (right #u64))
#fn work ((pair Pair) (array (#array #u64 2))) #u64
              (#let pair-view (#ref Pair) (#borrow pair))
              (#let view (#ref #u64) (#borrow (#get pair-view left)))
              (#let result #u64 (#index array (#call await-a ())))
              (#drop view) (#drop pair-view) (#forget pair) (#forget array) (#return result)\n",
        );
        let body = &declarations.bodies["work"];
        let site = call(body, "await-a");
        assert!(plan(body, &declarations.flows["work"], &[site]).unwrap()[&site].is_empty());
    }

    #[test]
    fn reference_field_load_survives_the_later_index_await() {
        let (_, declarations) = prepare(
            "#struct Holder () ((values (#ref (#array #u64 2))))
#fn work ((holder (#ref Holder))) #u64
              (#return (#index (#get holder values) (#call await-a ())))\n",
        );
        let body = &declarations.bodies["work"];
        let site = call(body, "await-a");
        let loaded = body
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| {
                matches!(&node.kind, NodeKind::Form { head, .. } if head == "get")
                    .then_some(NodeId(index))
            })
            .unwrap();
        let captures = plan(body, &declarations.flows["work"], &[site]).unwrap();
        assert_eq!(captures[&site], [loaded]);
        assert_eq!(
            body.nodes[loaded.0].ty,
            Some(Type::Reference {
                mutable: false,
                target: Box::new(Type::Array(Box::new(Type::U64), 2)),
            })
        );
    }

    #[test]
    fn nested_reference_index_load_replaces_its_completed_address_components() {
        let (_, declarations) = prepare(
            "#struct Holder ()
            ((links (#ref (#array (#ref (#array #u64 2)) 2))))
#fn work ((holder (#ref Holder))) #u64
              (#return (#u64::add-wrap (#call first ())
                (#index (#index (#get holder links) 0usize) (#call await-a ()))))\n",
        );
        let body = &declarations.bodies["work"];
        let site = call(body, "await-a");
        let loaded = body
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| {
                (matches!(&node.kind, NodeKind::Form { head, .. } if crate::is_array_index_head(head))
                    && matches!(node.ty, Some(Type::Reference { .. })))
                .then_some(NodeId(index))
            })
            .unwrap();
        let captures = plan(body, &declarations.flows["work"], &[site]).unwrap();
        assert_eq!(captures[&site], [call(body, "first"), loaded]);
    }

    #[test]
    fn replacing_holder_contents_keeps_the_previously_loaded_reference() {
        let (_, declarations) = prepare(
            "#struct Holder () ((values (#ref (#array #u64 2))))
#fn work ((holder (#ref-mut Holder)) (replacement (#ref (#array #u64 2)))) #u64
              (#return (#index (#get holder values) (#block
                (#deref-set holder (#struct-literal Holder ((values replacement))))
                (#call await-a ()))))\n",
        );
        let body = &declarations.bodies["work"];
        let site = call(body, "await-a");
        let loaded = body
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| {
                matches!(&node.kind, NodeKind::Form { head, .. } if head == "get")
                    .then_some(NodeId(index))
            })
            .unwrap();
        let captures = plan(body, &declarations.flows["work"], &[site]).unwrap();
        assert_eq!(captures[&site], [loaded]);
        assert!(matches!(&body.nodes[loaded.0].kind,
            NodeKind::Form { children, .. }
                if matches!(&body.nodes[children[1].0].kind,
                    NodeKind::Symbol { binding: Some(binding), .. }
                        if body.bindings[binding.0].name == "holder")));
    }

    #[test]
    fn array_assignment_keeps_its_evaluated_index_across_rhs_suspension() {
        let (_, declarations) = prepare(
            "#fn work () #u64
            (#let-mut values (#array #u64 2) (#array-of (#array #u64 2) 3u64 4u64))
            (#set-index values (#call first ()) (#call await-a ()))
            (#forget values) (#return 0u64)\n",
        );
        let body = &declarations.bodies["work"];
        let site = call(body, "await-a");
        assert_eq!(
            plan(body, &declarations.flows["work"], &[site]).unwrap()[&site],
            [call(body, "first")]
        );
    }

    #[test]
    fn short_circuit_conditions_and_finished_statements_are_not_outstanding() {
        let (_, declarations) = prepare(
            "#fn await-bool () #bool (#return true)
#fn work ((choose #bool)) #bool
              (#call first ())
              (#return (#bool::and choose (#call await-bool ())))\n",
        );
        let body = &declarations.bodies["work"];
        let site = call(body, "await-bool");
        assert!(plan(body, &declarations.flows["work"], &[site]).unwrap()[&site].is_empty());
    }

    #[test]
    fn flow_arena_permutation_and_collapsed_spans_do_not_change_the_plan() {
        let (_, mut declarations) = prepare(
            "#fn work () #u64
            (#return (#call combine ((first (#call first ())) (second (#call await-a ())))))\n",
        );
        let body = declarations.bodies.get_mut("work").unwrap();
        let span = body.nodes.iter().find_map(|node| node.span);
        for node in &mut body.nodes {
            node.span = span;
        }
        let site = call(body, "await-a");
        let flow = &declarations.flows["work"];
        let expected = plan(body, flow, &[site]).unwrap();
        let mut permuted = flow.clone();
        let remap = |id: FlowNodeId| FlowNodeId(flow.nodes.len() - 1 - id.0);
        permuted.nodes.reverse();
        for node in &mut permuted.nodes {
            for target in &mut node.successors {
                *target = remap(*target);
            }
        }
        permuted.entry = remap(flow.entry);
        permuted.exit = remap(flow.exit);
        permuted.variant_pruned_edges = flow
            .variant_pruned_edges
            .iter()
            .map(|(&from, targets)| (remap(from), targets.iter().copied().map(remap).collect()))
            .collect();
        assert_eq!(plan(body, &permuted, &[site]).unwrap(), expected);
        assert!(!named_values(body, &expected[&site]).is_empty());
    }

    #[test]
    fn unreachable_calls_are_omitted_and_duplicate_events_are_rejected() {
        let (_, declarations) = prepare(
            "#fn work () #u64
            (#return 42u64) (#call await-a ()) (#return 0u64)\n",
        );
        let body = &declarations.bodies["work"];
        let site = call(body, "await-a");
        let flow = &declarations.flows["work"];
        assert!(plan(body, flow, &[site]).unwrap().is_empty());

        let (_, declarations) = prepare("#fn work () #u64 (#return (#call await-a ()))\n");
        let body = &declarations.bodies["work"];
        let site = call(body, "await-a");
        let mut flow = declarations.flows["work"].clone();
        let duplicate = FlowNodeId(flow.nodes.len());
        flow.nodes.push(crate::typed_flow::FlowNode {
            action: FlowAction::Evaluate(site),
            successors: vec![flow.exit],
            span: None,
        });
        flow.nodes[flow.entry.0].successors.push(duplicate);
        assert!(plan(body, &flow, &[site])
            .unwrap_err()
            .message
            .contains("multiple reachable"));
    }

    #[test]
    fn repeated_suspending_elements_need_a_multiplicity_model() {
        let (_, declarations) = prepare(
            "#fn work () (#array #u64 2)
            (#return (#array-repeat (#call await-a ())))\n",
        );
        let body = &declarations.bodies["work"];
        let site = call(body, "await-a");
        let flow = &declarations.flows["work"];
        assert!(plan(body, flow, &[site])
            .unwrap_err()
            .message
            .contains("multiplicity"));
    }
}
