//! Stable, address-free control flow over the checked body arena.
//! Ownership passes can share these edges instead of reconstructing branch
//! and loop behavior independently from syntax.

use std::collections::{HashSet, VecDeque};

use crate::typed_body::{
    BindingId, Body, Control, Instruction, NodeId, NodeKind, NumericOpcode, PlaceRoot, Projection,
};
use crate::typed_ir::{DeclarationId, FieldId};
use crate::typed_place::{Place, Segment};
use crate::Span;

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) struct FlowNodeId(pub usize);

#[derive(Clone, Debug)]
pub(crate) enum FlowAction {
    Entry,
    Exit,
    Evaluate(NodeId),
    Borrow {
        value: NodeId,
        place: Place,
        mutable: bool,
    },
    Bind {
        binding: BindingId,
        value: NodeId,
    },
    Assign {
        place: Place,
        value: NodeId,
    },
    Pattern {
        pattern: NodeId,
        value: NodeId,
    },
    ScopeExit(Vec<BindingId>),
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

/// Future reads of each local at each control-flow point. This is not an
/// ownership or loan analysis: a value may still need cleanup when no later
/// expression reads it.
pub(crate) struct FlowLiveness {
    before: Vec<Vec<u64>>,
    after: Vec<Vec<u64>>,
    binding_count: usize,
}

#[derive(Clone, Debug)]
pub(crate) struct LoanOrigin {
    pub place: Place,
    pub mutable: bool,
    pub span: Option<Span>,
    /// Position inside the value held by a binding, not the referent place.
    pub storage: Vec<Segment>,
}

impl PartialEq for LoanOrigin {
    fn eq(&self, other: &Self) -> bool {
        self.place == other.place && self.mutable == other.mutable && self.storage == other.storage
    }
}

impl Eq for LoanOrigin {}

type LoanState = Vec<Vec<LoanOrigin>>;

/// Direct reference origins at each typed flow point. This is a may-analysis,
/// not yet an enforcing borrow check; indirect provenance and destructured
/// payloads still need the full IR-04 transfer.
pub(crate) struct FlowLoanOrigins {
    before: Vec<Option<LoanState>>,
    after: Vec<Option<LoanState>>,
}

impl FlowLoanOrigins {
    pub fn before(&self, node: FlowNodeId, binding: BindingId) -> &[LoanOrigin] {
        self.before[node.0]
            .as_ref()
            .map_or(&[], |state| state[binding.0].as_slice())
    }

    pub fn after(&self, node: FlowNodeId, binding: BindingId) -> &[LoanOrigin] {
        self.after[node.0]
            .as_ref()
            .map_or(&[], |state| state[binding.0].as_slice())
    }

    pub fn dump(&self) -> String {
        use std::fmt::Write;
        let mut output = String::new();
        let binding_count = self.before.iter().flatten().next().map_or(0, Vec::len);
        for index in 0..self.before.len() {
            for binding in 0..binding_count {
                let id = FlowNodeId(index);
                let binding = BindingId(binding);
                let before = self.before(id, binding);
                let after = self.after(id, binding);
                if before.is_empty() && after.is_empty() {
                    continue;
                }
                let describe = |origins: &[LoanOrigin]| {
                    origins
                        .iter()
                        .map(|origin| {
                            format!(
                                "{:?} {:?} {} {:?}",
                                origin.place,
                                origin.storage,
                                if origin.mutable { "mutable" } else { "shared" },
                                origin.span
                            )
                        })
                        .collect::<Vec<_>>()
                };
                writeln!(
                    output,
                    "  loan {index} binding {}: {:?}->{:?}",
                    binding.0,
                    describe(before),
                    describe(after)
                )
                .unwrap();
            }
        }
        output
    }
}

impl FlowLiveness {
    pub fn before(&self, id: FlowNodeId) -> Vec<BindingId> {
        self.bindings(&self.before[id.0])
    }

    pub fn after(&self, id: FlowNodeId) -> Vec<BindingId> {
        self.bindings(&self.after[id.0])
    }

    fn bindings(&self, bits: &[u64]) -> Vec<BindingId> {
        (0..self.binding_count)
            .filter(|index| bits[index / 64] & (1u64 << (index % 64)) != 0)
            .map(BindingId)
            .collect()
    }
}

#[derive(Clone)]
struct Target {
    name: Option<String>,
    break_to: FlowNodeId,
    continue_to: Option<FlowNodeId>,
    scope_depth: usize,
}

struct Builder<'a> {
    body: &'a Body,
    nodes: Vec<FlowNode>,
    exit: FlowNodeId,
    active_scopes: Vec<Vec<BindingId>>,
}

impl FlowGraph {
    pub fn lower(body: &Body) -> Result<Self, String> {
        let mut builder = Builder {
            body,
            nodes: Vec::new(),
            exit: FlowNodeId(0),
            active_scopes: Vec::new(),
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

    /// Forward may-analysis of direct reference origins held by local
    /// bindings. The transfer uses checked value IDs rather than syntax names.
    pub fn loan_origins(&self, body: &Body) -> FlowLoanOrigins {
        let empty = vec![Vec::new(); body.bindings.len()];
        let mut before = vec![None; self.nodes.len()];
        let mut after = vec![None; self.nodes.len()];
        let mut queued = vec![false; self.nodes.len()];
        let mut pending = VecDeque::from([self.entry]);
        before[self.entry.0] = Some(empty);
        queued[self.entry.0] = true;
        while let Some(id) = pending.pop_front() {
            queued[id.0] = false;
            let mut state = before[id.0].as_ref().unwrap().clone();
            match &self.nodes[id.0].action {
                FlowAction::Bind { binding, value } => {
                    state[binding.0] = value_loan_origins(body, *value, &state);
                }
                FlowAction::Pattern { pattern, value } => {
                    let origins = value_loan_origins(body, *value, &state);
                    distribute_pattern_origins(body, *pattern, &origins, &mut state);
                }
                FlowAction::ScopeExit(bindings) => {
                    for binding in bindings {
                        state[binding.0].clear();
                    }
                }
                FlowAction::Assign {
                    place:
                        Place {
                            root: PlaceRoot::Local(binding),
                            segments,
                        },
                    value,
                } if segments.is_empty() => {
                    state[binding.0] = value_loan_origins(body, *value, &state);
                }
                FlowAction::Evaluate(value) => {
                    if let NodeKind::Form { head, children, .. } = &body.nodes[value.0].kind {
                        if matches!(head.as_str(), "drop" | "forget") && children.len() == 2 {
                            if let NodeKind::Symbol {
                                binding: Some(binding),
                                ..
                            } = body.nodes[children[1].0].kind
                            {
                                state[binding.0].clear();
                            }
                        }
                    }
                }
                _ => {}
            }
            after[id.0] = Some(state.clone());
            for successor in &self.nodes[id.0].successors {
                let changed = match &mut before[successor.0] {
                    Some(existing) => merge_loan_states(existing, &state),
                    slot @ None => {
                        *slot = Some(state.clone());
                        true
                    }
                };
                if changed && !queued[successor.0] {
                    pending.push_back(*successor);
                    queued[successor.0] = true;
                }
            }
        }
        FlowLoanOrigins { before, after }
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
                FlowAction::Borrow {
                    value,
                    place,
                    mutable,
                } => {
                    if body.nodes.get(value.0).is_none_or(|node| node.ty.is_none()) {
                        return Err(format!("typed flow borrows invalid node {value:?}"));
                    }
                    let NodeKind::Form { head, children, .. } = &body.nodes[value.0].kind else {
                        return Err(format!("typed flow borrow {value:?} is not a form"));
                    };
                    if !matches!(head.as_str(), "borrow" | "borrow-mut")
                        || (head == "borrow-mut") != *mutable
                        || children.len() != 2
                        || Place::from_expression(body, children[1]).as_ref() != Some(place)
                    {
                        return Err(format!("typed flow borrow {value:?} has invalid metadata"));
                    }
                    if let PlaceRoot::Local(binding) = place.root {
                        if binding.0 >= body.bindings.len() {
                            return Err(format!("typed flow borrows invalid local {binding:?}"));
                        }
                    }
                }
                FlowAction::Bind { binding, value } => {
                    if binding.0 >= body.bindings.len() || value.0 >= body.nodes.len() {
                        return Err(format!("typed flow binds invalid local {binding:?}"));
                    }
                }
                FlowAction::Assign {
                    place:
                        Place {
                            root: PlaceRoot::Local(binding),
                            ..
                        },
                    value,
                } => {
                    if binding.0 >= body.bindings.len() || value.0 >= body.nodes.len() {
                        return Err(format!("typed flow assigns invalid local {binding:?}"));
                    }
                }
                FlowAction::Assign {
                    place:
                        Place {
                            root: PlaceRoot::Global(_),
                            ..
                        },
                    value,
                } => {
                    if value.0 >= body.nodes.len() {
                        return Err(format!("typed flow assigns invalid value {value:?}"));
                    }
                }
                FlowAction::Pattern { pattern, value } => {
                    if pattern.0 >= body.nodes.len() || value.0 >= body.nodes.len() {
                        return Err(format!("typed flow references invalid pattern {pattern:?}"));
                    }
                }
                FlowAction::ScopeExit(bindings) => {
                    if bindings
                        .iter()
                        .any(|binding| binding.0 >= body.bindings.len())
                    {
                        return Err(format!("typed flow node {index} exits an invalid binding"));
                    }
                }
                FlowAction::Branch(id) => {
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

    pub fn dump(&self, liveness: &FlowLiveness) -> String {
        use std::fmt::Write;
        let reachable = self.reachable();
        let mut output = format!("  flow entry {} exit {}\n", self.entry.0, self.exit.0);
        for (index, node) in self.nodes.iter().enumerate() {
            let edges = node.successors.iter().map(|id| id.0).collect::<Vec<_>>();
            writeln!(
                output,
                "  flow {index}: {:?} {:?} -> {edges:?} live={:?}->{:?}{}",
                node.action,
                node.span,
                liveness.before(FlowNodeId(index)),
                liveness.after(FlowNodeId(index)),
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

    /// Backward may-liveness over the same edges used by ownership analyses.
    /// Definitions kill older values only on the edge where the binding is
    /// introduced or wholly replaced. Projected writes read the aggregate.
    pub fn liveness(&self, body: &Body) -> FlowLiveness {
        let count = body.bindings.len();
        let words = count.div_ceil(64);
        let mut before = vec![vec![0u64; words]; self.nodes.len()];
        let mut after = before.clone();
        let mut uses = before.clone();
        let mut defs = before.clone();
        let mut predecessors = vec![Vec::<FlowNodeId>::new(); self.nodes.len()];
        let reachable = self.reachable();
        for id in &reachable {
            let node = &self.nodes[id.0];
            for successor in &node.successors {
                predecessors[successor.0].push(*id);
            }
            let set = |bits: &mut [Vec<u64>], binding: BindingId| {
                bits[id.0][binding.0 / 64] |= 1u64 << (binding.0 % 64);
            };
            match &node.action {
                FlowAction::Evaluate(value) => {
                    if let Some(Place {
                        root: PlaceRoot::Local(binding),
                        ..
                    }) = Place::from_expression(body, *value)
                    {
                        set(&mut uses, binding);
                    }
                }
                FlowAction::Borrow {
                    place:
                        Place {
                            root: PlaceRoot::Local(binding),
                            ..
                        },
                    ..
                } => set(&mut uses, *binding),
                FlowAction::Bind { binding, .. } => set(&mut defs, *binding),
                FlowAction::Pattern { pattern, .. } => {
                    let mut bindings = HashSet::new();
                    collect_pattern_bindings(body, *pattern, &mut bindings);
                    for binding in bindings {
                        set(&mut defs, binding);
                    }
                }
                FlowAction::Assign {
                    place:
                        Place {
                            root: PlaceRoot::Local(binding),
                            segments,
                        },
                    ..
                } => {
                    if segments.is_empty() {
                        set(&mut defs, *binding);
                    } else {
                        set(&mut uses, *binding);
                    }
                }
                _ => {}
            }
        }
        let mut pending = VecDeque::from_iter(reachable.iter().copied());
        let mut queued = vec![false; self.nodes.len()];
        for id in &reachable {
            queued[id.0] = true;
        }
        while let Some(id) = pending.pop_front() {
            queued[id.0] = false;
            let mut next_after = vec![0u64; words];
            for successor in &self.nodes[id.0].successors {
                for (word, successor_word) in next_after.iter_mut().zip(&before[successor.0]) {
                    *word |= successor_word;
                }
            }
            let mut next_before = next_after.clone();
            for ((word, used), defined) in next_before.iter_mut().zip(&uses[id.0]).zip(&defs[id.0])
            {
                *word = (*word & !*defined) | *used;
            }
            let changed = before[id.0] != next_before || after[id.0] != next_after;
            if changed {
                before[id.0] = next_before;
                after[id.0] = next_after;
                for predecessor in &predecessors[id.0] {
                    if !queued[predecessor.0] {
                        pending.push_back(*predecessor);
                        queued[predecessor.0] = true;
                    }
                }
            }
        }
        FlowLiveness {
            before,
            after,
            binding_count: count,
        }
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
                match &node.action {
                    FlowAction::Bind { binding, .. } => {
                        generated[index][binding.0 / 64] |= 1u64 << (binding.0 % 64);
                    }
                    FlowAction::Pattern { pattern, .. } => {
                        let mut bindings = HashSet::new();
                        collect_pattern_bindings(body, *pattern, &mut bindings);
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
            let binding = match &node.action {
                FlowAction::Evaluate(id) => match Place::from_expression(body, *id) {
                    Some(Place {
                        root: PlaceRoot::Local(binding),
                        ..
                    }) => Some(binding),
                    _ => None,
                },
                FlowAction::Assign {
                    place:
                        Place {
                            root: PlaceRoot::Local(binding),
                            ..
                        },
                    ..
                } => Some(*binding),
                FlowAction::Borrow {
                    place:
                        Place {
                            root: PlaceRoot::Local(binding),
                            ..
                        },
                    ..
                } => Some(*binding),
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

fn merge_loan_states(existing: &mut LoanState, incoming: &LoanState) -> bool {
    let mut changed = false;
    for (held, other) in existing.iter_mut().zip(incoming) {
        changed |= merge_loan_origins(held, other);
    }
    changed
}

fn merge_loan_origins(existing: &mut Vec<LoanOrigin>, incoming: &[LoanOrigin]) -> bool {
    let mut changed = false;
    for origin in incoming {
        if !existing.contains(origin) {
            existing.push(origin.clone());
            changed = true;
        }
    }
    changed
}

fn value_loan_origins(body: &Body, id: NodeId, state: &LoanState) -> Vec<LoanOrigin> {
    let node = &body.nodes[id.0];
    match &node.kind {
        NodeKind::Symbol {
            binding: Some(binding),
            ..
        } => state[binding.0].clone(),
        NodeKind::Form { head, children, .. }
            if matches!(head.as_str(), "borrow" | "borrow-mut") && children.len() == 2 =>
        {
            Place::from_expression(body, children[1]).map_or_else(Vec::new, |place| {
                vec![LoanOrigin {
                    place,
                    mutable: head == "borrow-mut",
                    span: node.span,
                    storage: Vec::new(),
                }]
            })
        }
        NodeKind::If {
            then_value,
            else_value,
            ..
        } => {
            let mut origins = value_loan_origins(body, *then_value, state);
            if let Some(value) = else_value {
                merge_loan_origins(&mut origins, &value_loan_origins(body, *value, state));
            }
            origins
        }
        NodeKind::Match { arms, .. } => {
            let mut origins = Vec::new();
            for arm in arms {
                if let NodeKind::MatchArm { values, .. } = &body.nodes[arm.0].kind {
                    if let Some(value) = values.last() {
                        merge_loan_origins(&mut origins, &value_loan_origins(body, *value, state));
                    }
                }
            }
            origins
        }
        NodeKind::Form { head, children, .. }
            if matches!(head.as_str(), "unsafe" | "clone") && children.len() == 2 =>
        {
            value_loan_origins(body, children[1], state)
        }
        NodeKind::Form { head, children, .. }
            if matches!(head.as_str(), "tuple" | "array" | "struct-literal")
                || matches!(
                    children.first().map(|child| &body.nodes[child.0].kind),
                    Some(NodeKind::Declaration(
                        DeclarationId::Aggregate(_) | DeclarationId::Variant(_)
                    ))
                ) =>
        {
            let mut origins = Vec::new();
            // Tuple/array value forms carry an explicit type operand after
            // the head. Patterns do not, so their slots start at child one.
            let values_start = if matches!(head.as_str(), "tuple" | "array") {
                2
            } else {
                1
            };
            for (index, child) in children.iter().skip(values_start).enumerate() {
                let Some(slot) = aggregate_slot(body, head, children, index) else {
                    continue;
                };
                let mut nested = value_loan_origins(body, *child, state);
                for origin in &mut nested {
                    origin.storage.insert(0, slot.clone());
                }
                merge_loan_origins(&mut origins, &nested);
            }
            origins
        }
        NodeKind::Syntax(children) => {
            let mut origins = Vec::new();
            for child in children {
                merge_loan_origins(&mut origins, &value_loan_origins(body, *child, state));
            }
            origins
        }
        NodeKind::Block(instructions) => match instructions.last().map(|item| &item.control) {
            Some(Control::Evaluate(value)) => value_loan_origins(body, *value, state),
            _ => Vec::new(),
        },
        NodeKind::Labeled(_, inner) => value_loan_origins(body, *inner, state),
        _ => Vec::new(),
    }
}

fn aggregate_slot(body: &Body, head: &str, children: &[NodeId], index: usize) -> Option<Segment> {
    match children.first().map(|child| &body.nodes[child.0].kind) {
        Some(NodeKind::Declaration(DeclarationId::Aggregate(owner))) => {
            Some(Segment::Field(FieldId {
                owner: *owner,
                index,
            }))
        }
        Some(NodeKind::Declaration(DeclarationId::Variant(variant))) => {
            Some(Segment::Payload(*variant, index))
        }
        _ => match head {
            "tuple" => Some(Segment::Tuple(index)),
            "array" => Some(Segment::Index(index as u128)),
            _ => None,
        },
    }
}

fn distribute_pattern_origins(
    body: &Body,
    pattern: NodeId,
    origins: &[LoanOrigin],
    state: &mut LoanState,
) {
    match &body.nodes[pattern.0].kind {
        NodeKind::Symbol {
            binding: Some(binding),
            ..
        } => state[binding.0] = origins.to_vec(),
        NodeKind::Form { head, children, .. } => {
            for (index, child) in children.iter().skip(1).enumerate() {
                let Some(slot) = aggregate_slot(body, head, children, index) else {
                    continue;
                };
                let nested = origins
                    .iter()
                    .filter_map(|origin| {
                        if origin.storage.first() != Some(&slot) {
                            return None;
                        }
                        let mut origin = origin.clone();
                        origin.storage.remove(0);
                        Some(origin)
                    })
                    .collect::<Vec<_>>();
                distribute_pattern_origins(body, *child, &nested, state);
            }
        }
        _ => {}
    }
}

fn direct_scope_bindings(body: &Body, instructions: &[Instruction]) -> Vec<BindingId> {
    fn collect(body: &Body, instruction: &Instruction, bindings: &mut HashSet<BindingId>) {
        match &instruction.control {
            Control::Bind(binding, _, _) => {
                bindings.insert(*binding);
            }
            Control::Destructure { pattern, .. } => {
                collect_pattern_bindings(body, *pattern, bindings);
            }
            Control::Labeled(_, inner) => collect(body, inner, bindings),
            _ => {}
        }
    }
    let mut bindings = HashSet::new();
    for instruction in instructions {
        collect(body, instruction, &mut bindings);
    }
    let mut bindings = bindings.into_iter().collect::<Vec<_>>();
    bindings.sort_by_key(|binding| binding.0);
    bindings
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

    fn scoped_instructions(
        &mut self,
        instructions: &[Instruction],
        next: FlowNodeId,
        targets: &[Target],
    ) -> Result<FlowNodeId, String> {
        let bindings = direct_scope_bindings(self.body, instructions);
        let after = if bindings.is_empty() {
            next
        } else {
            self.push(FlowAction::ScopeExit(bindings.clone()), None, vec![next])
        };
        self.active_scopes.push(bindings);
        let result = self.instructions(instructions, after, targets);
        self.active_scopes.pop();
        result
    }

    fn cleanup_to(&mut self, depth: usize, mut next: FlowNodeId) -> FlowNodeId {
        for bindings in self.active_scopes[depth..].to_vec() {
            if !bindings.is_empty() {
                next = self.push(FlowAction::ScopeExit(bindings), None, vec![next]);
            }
        }
        next
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
                let bind = self.push(
                    FlowAction::Bind {
                        binding: *binding,
                        value: *value,
                    },
                    span,
                    vec![next],
                );
                self.expression(*value, bind, targets, None)
            }
            Control::Destructure {
                pattern,
                value,
                otherwise,
                ..
            } => {
                let bind = self.push(
                    FlowAction::Pattern {
                        pattern: *pattern,
                        value: *value,
                    },
                    span,
                    vec![next],
                );
                let decision = if let Some(otherwise) = otherwise {
                    let failure = self.scoped_instructions(otherwise, next, targets)?;
                    self.push(FlowAction::Branch(*pattern), span, vec![bind, failure])
                } else {
                    bind
                };
                self.expression(*value, decision, targets, None)
            }
            Control::Assign(root, projection, value) => {
                let assign = self.push(
                    FlowAction::Assign {
                        place: Place::from_assignment(self.body, root, projection),
                        value: *value,
                    },
                    span,
                    vec![next],
                );
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
                let init_bindings =
                    direct_scope_bindings(self.body, std::slice::from_ref(init.as_ref()));
                let after_loop = if init_bindings.is_empty() {
                    next
                } else {
                    self.push(
                        FlowAction::ScopeExit(init_bindings.clone()),
                        span,
                        vec![next],
                    )
                };
                self.active_scopes.push(init_bindings);
                let decision = self.push(FlowAction::Branch(*condition), span, vec![]);
                let condition_entry = self.expression(*condition, decision, targets, None)?;
                let mut loop_targets = targets.to_vec();
                let step_entry = self.instruction(step, condition_entry, targets, None)?;
                loop_targets.push(Target {
                    name: label.map(str::to_owned),
                    break_to: after_loop,
                    continue_to: Some(step_entry),
                    scope_depth: self.active_scopes.len(),
                });
                let body_entry = self.scoped_instructions(body, step_entry, &loop_targets)?;
                self.nodes[decision.0].successors = vec![body_entry, after_loop];
                let entry = self.instruction(init, condition_entry, targets, None);
                self.active_scopes.pop();
                entry
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
                        scope_depth: self.active_scopes.len(),
                    });
                    self.instruction(inner, next, &labeled, None)
                }
            }
            Control::Return(value) => {
                let end = self.push(FlowAction::Return, span, vec![self.exit]);
                let end = self.cleanup_to(0, end);
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
                let end = self.cleanup_to(target.scope_depth, end);
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
                    .and_then(|target| target.continue_to.map(|next| (next, target.scope_depth)))
                    .ok_or_else(|| format!("typed flow has no continue target for {label:?}"))?;
                let end = self.push(FlowAction::Continue, span, vec![target.0]);
                Ok(self.cleanup_to(target.1, end))
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
            scope_depth: self.active_scopes.len(),
        });
        let body_entry = self.scoped_instructions(body, condition_entry, &loop_targets)?;
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
            scope_depth: self.active_scopes.len(),
        });
        let body_entry = self.scoped_instructions(body, header, &loop_targets)?;
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
                    entry = self.match_arm(*arm, *value, next, entry, targets)?;
                }
                let decision = self.push(FlowAction::Branch(id), span, vec![entry]);
                self.expression(*value, decision, targets, None)
            }
            NodeKind::MatchArm { .. } => Err("typed match arm has no dispatch".into()),
            NodeKind::Block(body) => self.scoped_instructions(body, next, targets),
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
            NodeKind::Form { head, children, .. }
                if matches!(head.as_str(), "borrow" | "borrow-mut") && children.len() == 2 =>
            {
                let action = Place::from_expression(self.body, children[1]).map_or(
                    FlowAction::Evaluate(id),
                    |place| FlowAction::Borrow {
                        value: id,
                        place,
                        mutable: head == "borrow-mut",
                    },
                );
                let done = self.push(action, span, vec![next]);
                self.expression(children[1], done, targets, None)
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
        source: NodeId,
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
        let mut bindings = HashSet::new();
        collect_pattern_bindings(self.body, pattern, &mut bindings);
        let mut bindings = bindings.into_iter().collect::<Vec<_>>();
        bindings.sort_by_key(|binding| binding.0);
        let success_end = if bindings.is_empty() {
            next
        } else {
            self.push(FlowAction::ScopeExit(bindings.clone()), span, vec![next])
        };
        let failure_end = if bindings.is_empty() {
            failure
        } else {
            self.push(FlowAction::ScopeExit(bindings.clone()), span, vec![failure])
        };
        self.active_scopes.push(bindings);
        let body_entry = self.expression(body, success_end, targets, None)?;
        let success = if let Some(guard) = guard {
            let decision = self.push(
                FlowAction::Branch(guard),
                self.body.nodes[guard.0].span,
                vec![body_entry, failure_end],
            );
            self.expression(guard, decision, targets, None)?
        } else {
            body_entry
        };
        self.active_scopes.pop();
        let bound = self.push(
            FlowAction::Pattern {
                pattern,
                value: source,
            },
            span,
            vec![success],
        );
        Ok(self.push(FlowAction::Branch(pattern), span, vec![bound, failure]))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::typed_place::Segment;

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
                    action: FlowAction::Bind {
                        binding: BindingId(0),
                        value: NodeId(0),
                    },
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
            FlowAction::Pattern { .. }
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
        let cleanup = graph.nodes[guard.0].successors[1];
        assert!(matches!(
            graph.nodes[cleanup.0].action,
            FlowAction::ScopeExit(_)
        ));
        assert_eq!(graph.nodes[cleanup.0].successors, vec![fallback]);
        graph
            .check_definite_bindings(body, 0)
            .expect("guarded fallback has valid local scopes");

        let liveness = &checked.declarations().liveness["main"];
        let FlowAction::Pattern { pattern, .. } = graph.nodes[bound.0].action else {
            unreachable!()
        };
        let mut payloads = HashSet::new();
        collect_pattern_bindings(body, pattern, &mut payloads);
        for payload in payloads {
            assert!(!liveness.before(bound).contains(&payload));
            assert!(liveness.after(bound).contains(&payload));
        }
    }

    #[test]
    fn liveness_distinguishes_whole_and_projected_assignments() {
        let source = "(#struct Point ((x u64) (y u64)))
          (#fn main () u64
            (#let-mut point Point (#struct-literal Point ((x 1u64) (y 2u64))))
            (#let-mut replacement Point (#struct-literal Point ((x 3u64) (y 4u64))))
            (#set-field point x 5u64)
            (#let field-before u64 (#get point y))
            (#set point replacement)
            (#return (#u64.+.wrap field-before (#get point x))))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let graph = &checked.declarations().flows["main"];
        let liveness = &checked.declarations().liveness["main"];
        let point = BindingId(
            body.bindings
                .iter()
                .position(|b| b.name == "point")
                .unwrap(),
        );
        let projected = graph
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| match &node.action {
                FlowAction::Assign {
                    place:
                        Place {
                            root: PlaceRoot::Local(id),
                            segments,
                        },
                    ..
                } if *id == point && matches!(segments.as_slice(), [Segment::Field(_)]) => {
                    Some(FlowNodeId(index))
                }
                _ => None,
            })
            .unwrap();
        let whole = graph
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| match &node.action {
                FlowAction::Assign {
                    place:
                        Place {
                            root: PlaceRoot::Local(id),
                            segments,
                        },
                    ..
                } if *id == point && segments.is_empty() => Some(FlowNodeId(index)),
                _ => None,
            })
            .unwrap();
        assert!(liveness.before(projected).contains(&point));
        assert!(liveness.after(projected).contains(&point));
        assert!(!liveness.before(whole).contains(&point));
        assert!(liveness.after(whole).contains(&point));
    }

    #[test]
    fn transfer_actions_retain_checked_value_identities() {
        let source = "(#enum Choice ((Some u64) None))
          (#fn main () u64
            (#let-mut value u64 1u64)
            (#set value 2u64)
            (#let pair (#tuple u64 u64) (#tuple (#tuple u64 u64) value 3u64))
            (#let (#tuple first second) (#tuple u64 u64) pair)
            (#return (#match (Some first)
              (#case (Some selected) (#u64.+.wrap selected second))
              (#case None 0u64))))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let graph = &checked.declarations().flows["main"];
        let value_text = |value: NodeId| {
            let span = body.nodes[value.0].span.unwrap();
            &source[span.start..span.end]
        };
        assert!(graph.nodes.iter().any(|node| matches!(node.action,
            FlowAction::Bind { value, .. } if value_text(value) == "1u64")));
        assert!(graph.nodes.iter().any(|node| matches!(&node.action,
            FlowAction::Assign { value, .. } if value_text(*value) == "2u64")));
        assert!(graph.nodes.iter().any(|node| matches!(node.action,
            FlowAction::Pattern { value, .. } if value_text(value) == "pair")));
        assert!(graph.nodes.iter().any(|node| matches!(node.action,
            FlowAction::Pattern { value, .. } if value_text(value) == "(Some first)")));
    }

    #[test]
    fn direct_borrow_actions_retain_place_mode_and_exact_source() {
        let source = "(#fn main () u64
          (#let-mut value u64 1u64)
          (#let shared (#ref u64) (#borrow value))
          (#drop shared)
          (#let exclusive (#ref-mut u64) (#borrow-mut value))
          (#return (#deref exclusive)))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let graph = &checked.declarations().flows["main"];
        let owner = BindingId(
            body.bindings
                .iter()
                .position(|b| b.name == "value")
                .unwrap(),
        );
        let mut borrows = graph
            .nodes
            .iter()
            .filter_map(|node| match &node.action {
                FlowAction::Borrow {
                    value,
                    place,
                    mutable,
                } => Some((body.nodes[value.0].span.unwrap(), place, *mutable)),
                _ => None,
            })
            .collect::<Vec<_>>();
        borrows.sort_by_key(|(span, _, _)| span.start);
        assert_eq!(borrows.len(), 2);
        assert_eq!(
            &source[borrows[0].0.start..borrows[0].0.end],
            "(#borrow value)"
        );
        assert_eq!(
            &source[borrows[1].0.start..borrows[1].0.end],
            "(#borrow-mut value)"
        );
        assert!(borrows
            .iter()
            .all(|(_, place, _)| place.root == PlaceRoot::Local(owner)));
        assert!(!borrows[0].2);
        assert!(borrows[1].2);
    }

    #[test]
    fn direct_loan_origins_join_and_survive_alias_drop() {
        let source = "(#fn main ((choose bool)) u64
          (#let-mut left u64 1u64)
          (#let-mut right u64 2u64)
          (#let view (#ref u64) (#if choose (#borrow left) (#borrow right)))
          (#let alias (#ref u64) view)
          (#drop view)
          (#return (#deref alias)))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let graph = &checked.declarations().flows["main"];
        let origins = graph.loan_origins(body);
        let binding = |name: &str| {
            BindingId(
                body.bindings
                    .iter()
                    .position(|binding| binding.name == name)
                    .unwrap(),
            )
        };
        let view = binding("view");
        let alias = binding("alias");
        let alias_bind = graph
            .nodes
            .iter()
            .position(
                |node| matches!(node.action, FlowAction::Bind { binding, .. } if binding == alias),
            )
            .map(FlowNodeId)
            .unwrap();
        let held = origins.after(alias_bind, alias);
        assert_eq!(held.len(), 2);
        let mut sites = held
            .iter()
            .map(|loan| {
                let span = loan.span.unwrap();
                &source[span.start..span.end]
            })
            .collect::<Vec<_>>();
        sites.sort_unstable();
        assert_eq!(sites, ["(#borrow left)", "(#borrow right)"]);

        let drop = graph
            .nodes
            .iter()
            .position(|node| match node.action {
                FlowAction::Evaluate(value) => matches!(&body.nodes[value.0].kind,
                    NodeKind::Form { head, .. } if head == "drop"),
                _ => false,
            })
            .map(FlowNodeId)
            .unwrap();
        assert_eq!(origins.before(drop, view).len(), 2);
        assert!(origins.after(drop, view).is_empty());
        assert_eq!(origins.after(drop, alias).len(), 2);
    }

    #[test]
    fn aggregate_bindings_retain_nested_direct_loan_origins() {
        let source = "(#struct Pair ((first (#ref u64)) (second (#ref u64))))
          (#fn main () u64
            (#let left u64 1u64)
            (#let right u64 2u64)
            (#let pair Pair (#struct-literal Pair
              ((second (#borrow right)) (first (#borrow left)))))
            (#let (Pair first second) Pair pair)
            (#return (#u64.+.wrap (#deref first) (#deref second))))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let graph = &checked.declarations().flows["main"];
        let origins = graph.loan_origins(body);
        let pair = BindingId(body.bindings.iter().position(|b| b.name == "pair").unwrap());
        let bound = graph
            .nodes
            .iter()
            .position(
                |node| matches!(node.action, FlowAction::Bind { binding, .. } if binding == pair),
            )
            .map(FlowNodeId)
            .unwrap();
        let held = origins.after(bound, pair);
        assert_eq!(held.len(), 2);
        let mut sites = held
            .iter()
            .map(|loan| {
                let span = loan.span.unwrap();
                &source[span.start..span.end]
            })
            .collect::<Vec<_>>();
        sites.sort_unstable();
        assert_eq!(sites, ["(#borrow left)", "(#borrow right)"]);

        let pattern = graph
            .nodes
            .iter()
            .position(|node| matches!(node.action, FlowAction::Pattern { .. }))
            .map(FlowNodeId)
            .unwrap();
        for (name, expected) in [("first", "(#borrow left)"), ("second", "(#borrow right)")] {
            let binding = BindingId(body.bindings.iter().position(|b| b.name == name).unwrap());
            let loans = origins.after(pattern, binding);
            assert_eq!(loans.len(), 1, "{name}");
            assert!(loans[0].storage.is_empty());
            let span = loans[0].span.unwrap();
            assert_eq!(&source[span.start..span.end], expected);
        }
    }

    #[test]
    fn enum_binding_retains_payload_borrow_origin() {
        let source = "(#enum Choice ((Has (#ref u64)) Empty))
          (#fn main () u64
            (#let owner u64 4u64)
            (#let choice Choice (Has (#borrow owner)))
            (#return (#match choice
              (#case (Has view) (#deref view))
              (#case Empty 0u64))))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let graph = &checked.declarations().flows["main"];
        let choice = BindingId(
            body.bindings
                .iter()
                .position(|b| b.name == "choice")
                .unwrap(),
        );
        let bound = graph
            .nodes
            .iter()
            .position(
                |node| matches!(node.action, FlowAction::Bind { binding, .. } if binding == choice),
            )
            .map(FlowNodeId)
            .unwrap();
        let origins = graph.loan_origins(body);
        let held = origins.after(bound, choice);
        assert_eq!(held.len(), 1);
        let span = held[0].span.unwrap();
        assert_eq!(&source[span.start..span.end], "(#borrow owner)");

        let view = BindingId(body.bindings.iter().position(|b| b.name == "view").unwrap());
        let pattern = graph
            .nodes
            .iter()
            .position(|node| match node.action {
                FlowAction::Pattern { pattern, .. } => {
                    let mut bindings = HashSet::new();
                    collect_pattern_bindings(body, pattern, &mut bindings);
                    bindings.contains(&view)
                }
                _ => false,
            })
            .map(FlowNodeId)
            .unwrap();
        let payload = origins.after(pattern, view);
        assert_eq!(payload.len(), 1);
        assert!(payload[0].storage.is_empty());
        assert_eq!(payload[0].place, held[0].place);
    }

    #[test]
    fn variant_payload_origins_do_not_cross_match_arms() {
        let source = "(#enum Choice ((Left (#ref u64)) (Right (#ref u64))))
          (#fn main ((choose bool)) u64
            (#let left u64 1u64)
            (#let right u64 2u64)
            (#let choice Choice (#if choose
              (Left (#borrow left))
              (Right (#borrow right))))
            (#return (#match choice
              (#case (Left left-view) (#deref left-view))
              (#case (Right right-view) (#deref right-view)))))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let graph = &checked.declarations().flows["main"];
        let origins = graph.loan_origins(body);
        for (name, expected) in [
            ("left-view", "(#borrow left)"),
            ("right-view", "(#borrow right)"),
        ] {
            let binding = BindingId(body.bindings.iter().position(|b| b.name == name).unwrap());
            let node = graph
                .nodes
                .iter()
                .position(|node| match node.action {
                    FlowAction::Pattern { pattern, .. } => {
                        let mut bindings = HashSet::new();
                        collect_pattern_bindings(body, pattern, &mut bindings);
                        bindings.contains(&binding)
                    }
                    _ => false,
                })
                .map(FlowNodeId)
                .unwrap();
            let held = origins.after(node, binding);
            assert_eq!(held.len(), 1, "{name}");
            let span = held[0].span.unwrap();
            assert_eq!(&source[span.start..span.end], expected);
        }
    }

    #[test]
    fn positional_destructuring_keeps_tuple_and_array_origins_separate() {
        for (ty, constructor, pattern) in [
            (
                "(#tuple (#ref u64) (#ref u64))",
                "(#tuple (#tuple (#ref u64) (#ref u64)) (#borrow left) (#borrow right))",
                "(#tuple first second)",
            ),
            (
                "(#array (#ref u64) 2)",
                "(#array (#array (#ref u64) 2) (#borrow left) (#borrow right))",
                "(#array first second)",
            ),
        ] {
            let source = format!(
                "(#fn main () u64
                  (#let left u64 1u64)
                  (#let right u64 2u64)
                  (#let aggregate {ty} {constructor})
                  (#let {pattern} {ty} aggregate)
                  (#return (#u64.+.wrap (#deref first) (#deref second))))"
            );
            let program = crate::parse_program(&source).unwrap();
            let checked = crate::CheckedProgram::validate(&program).unwrap();
            let body = &checked.declarations().bodies["main"];
            let graph = &checked.declarations().flows["main"];
            let origins = graph.loan_origins(body);
            let node = graph
                .nodes
                .iter()
                .position(|node| matches!(node.action, FlowAction::Pattern { .. }))
                .map(FlowNodeId)
                .unwrap();
            for (name, expected) in [("first", "(#borrow left)"), ("second", "(#borrow right)")] {
                let binding = BindingId(body.bindings.iter().position(|b| b.name == name).unwrap());
                let held = origins.after(node, binding);
                assert_eq!(held.len(), 1, "{ty} {name}");
                let span = held[0].span.unwrap();
                assert_eq!(&source[span.start..span.end], expected);
            }
        }
    }

    #[test]
    fn direct_loan_join_distinguishes_one_sided_and_complete_release() {
        for (else_branch, expected) in [("(#block (#drop view) 0u64)", 0), ("0u64", 1)] {
            let source = format!(
                "(#fn main ((choose bool)) u64
                  (#let-mut owner u64 1u64)
                  (#let view (#ref u64) (#borrow owner))
                  (#if choose (#block (#drop view) 0u64) {else_branch})
                  (#return owner))"
            );
            let program = crate::parse_program(&source).unwrap();
            let checked = crate::CheckedProgram::validate(&program).unwrap();
            let body = &checked.declarations().bodies["main"];
            let graph = &checked.declarations().flows["main"];
            let view = BindingId(body.bindings.iter().position(|b| b.name == "view").unwrap());
            let return_node = graph
                .nodes
                .iter()
                .position(|node| matches!(node.action, FlowAction::Return))
                .map(FlowNodeId)
                .unwrap();
            assert_eq!(
                graph.loan_origins(body).before(return_node, view).len(),
                expected
            );
        }
    }

    #[test]
    fn lexical_scope_exit_clears_block_and_break_origins() {
        for scope in [
            "(#block (#let view (#ref u64) (#borrow owner)) (#deref view))",
            "(#loop (#let view (#ref u64) (#borrow owner)) (#break))",
        ] {
            let source = format!(
                "(#fn main () u64
                  (#let-mut owner u64 1u64)
                  {scope}
                  (#return owner))"
            );
            let program = crate::parse_program(&source).unwrap();
            let checked = crate::CheckedProgram::validate(&program).unwrap();
            let body = &checked.declarations().bodies["main"];
            let graph = &checked.declarations().flows["main"];
            let view = BindingId(body.bindings.iter().position(|b| b.name == "view").unwrap());
            let origins = graph.loan_origins(body);
            let exit = graph
                .nodes
                .iter()
                .enumerate()
                .find_map(|(index, node)| match &node.action {
                    FlowAction::ScopeExit(bindings)
                        if bindings.contains(&view)
                            && !origins.before(FlowNodeId(index), view).is_empty() =>
                    {
                        Some(FlowNodeId(index))
                    }
                    _ => None,
                })
                .unwrap();
            assert_eq!(origins.before(exit, view).len(), 1);
            assert!(origins.after(exit, view).is_empty());
            let return_node = graph
                .nodes
                .iter()
                .position(|node| matches!(node.action, FlowAction::Return))
                .map(FlowNodeId)
                .unwrap();
            assert!(origins.before(return_node, view).is_empty());
        }
    }

    #[test]
    fn range_loop_initializer_scope_exits_on_fallthrough() {
        let source = "(#fn main () u64
          (#let-mut total u64 0u64)
          (#for-range (i u64) 0u64 2u64
            (#set total (#u64.+.wrap total i)))
          (#return total))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let graph = &checked.declarations().flows["main"];
        let index = BindingId(body.bindings.iter().position(|b| b.name == "i").unwrap());
        assert!(graph.nodes.iter().any(|node| matches!(&node.action,
            FlowAction::ScopeExit(bindings) if bindings.contains(&index))));
    }

    #[test]
    fn continue_clears_body_local_loan_before_next_iteration() {
        let source = "(#fn main () u64
          (#let-mut owner u64 1u64)
          (#let-mut counter u64 0u64)
          (#label outer (#loop
            (#let view (#ref u64) (#borrow owner))
            (#if (#u64.== counter 0u64)
              (#block (#set counter 1u64) (#continue-to outer))
              (#block (#break-to outer)))))
          (#return owner))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let graph = &checked.declarations().flows["main"];
        let view = BindingId(body.bindings.iter().position(|b| b.name == "view").unwrap());
        let origins = graph.loan_origins(body);
        let cleanup = graph
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| match &node.action {
                FlowAction::ScopeExit(bindings)
                    if bindings.contains(&view)
                        && node.successors.iter().any(|next| {
                            matches!(graph.nodes[next.0].action, FlowAction::Continue)
                        }) =>
                {
                    Some(FlowNodeId(index))
                }
                _ => None,
            })
            .unwrap();
        assert_eq!(origins.before(cleanup, view).len(), 1);
        assert!(origins.after(cleanup, view).is_empty());
    }

    #[test]
    fn liveness_reaches_loop_condition_through_back_edge() {
        let source = "(#fn main () u64
          (#let-mut counter u64 0u64)
          (#while (#u64.< counter 3u64)
            (#set counter (#u64.+.wrap counter 1u64)))
          (#return counter))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let graph = &checked.declarations().flows["main"];
        let liveness = &checked.declarations().liveness["main"];
        let counter = BindingId(
            body.bindings
                .iter()
                .position(|b| b.name == "counter")
                .unwrap(),
        );
        let branch = graph
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| match node.action {
                FlowAction::Branch(id)
                    if matches!(body.nodes[id.0].kind, NodeKind::Form { .. })
                        && node.successors.len() == 2 =>
                {
                    Some(FlowNodeId(index))
                }
                _ => None,
            })
            .unwrap();
        assert!(liveness.before(branch).contains(&counter));
        assert!(liveness.after(branch).contains(&counter));
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
