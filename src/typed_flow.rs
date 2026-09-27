//! Stable, address-free control flow over the checked body arena.
//! Ownership passes can share these edges instead of reconstructing branch
//! and loop behavior independently from syntax.

use std::collections::{HashMap, HashSet, VecDeque};

use crate::linearcheck::LinearTypes;
use crate::typed_body::{
    BindingId, Body, Control, Instruction, NodeId, NodeKind, NumericOpcode, PlaceRoot, Projection,
};
use crate::typed_ir::{DeclarationId, FieldId};
use crate::typed_place::{Place, Segment};
use crate::{Span, Type};

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) struct FlowNodeId(pub usize);

#[derive(Clone, Debug)]
pub(crate) enum FlowAction {
    Entry,
    Exit,
    Evaluate(NodeId),
    /// A checked place read. `place_base` is an intermediate projection or
    /// dedicated borrow/clone/release operand, not a value read of the root.
    Read {
        value: NodeId,
        place: Place,
        place_base: bool,
    },
    /// A local place is consumed by `#drop` or `#forget`.
    Release {
        place: Place,
        value: NodeId,
    },
    Borrow {
        value: NodeId,
        place: Place,
        mutable: bool,
    },
    Clone {
        value: NodeId,
        place: Place,
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
    Return(Option<NodeId>),
    Break(Option<NodeId>),
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

/// May-consumed places after explicit `#drop`/`#forget`. This does not yet
/// account for value moves through expressions or calls.
pub(crate) struct FlowReleases {
    before: Vec<Option<HashMap<Place, Vec<Option<Span>>>>>,
    after: Vec<Option<HashMap<Place, Vec<Option<Span>>>>>,
    definite_before: Vec<HashSet<Place>>,
    definite_after: Vec<HashSet<Place>>,
}

/// Possible value consumptions from typed reads and explicit releases.
pub(crate) struct FlowConsumptions {
    before: Vec<Option<HashMap<Place, Vec<Option<Span>>>>>,
    after: Vec<Option<HashMap<Place, Vec<Option<Span>>>>>,
}

impl FlowConsumptions {
    pub fn before(&self, node: FlowNodeId, place: &Place) -> Option<&[Option<Span>]> {
        self.before[node.0].as_ref()?.get(place).map(Vec::as_slice)
    }

    pub fn after(&self, node: FlowNodeId, place: &Place) -> Option<&[Option<Span>]> {
        self.after[node.0].as_ref()?.get(place).map(Vec::as_slice)
    }

    pub fn dump(&self) -> String {
        use std::fmt::Write;
        let mut output = String::new();
        for (index, state) in self.after.iter().enumerate() {
            let Some(state) = state else { continue };
            let mut places = state.keys().collect::<Vec<_>>();
            places.sort_by_key(|place| format!("{place:?}"));
            for place in places {
                let node = FlowNodeId(index);
                writeln!(
                    output,
                    "  consumed {index} {place:?} {:?}->{:?}",
                    self.before(node, place),
                    self.after(node, place)
                )
                .unwrap();
            }
        }
        output
    }
}

#[derive(Debug)]
pub(crate) struct ReleaseConflict {
    pub message: String,
    pub span: Option<Span>,
    pub labels: Vec<(Span, String)>,
}

impl FlowReleases {
    pub fn before(&self, node: FlowNodeId, place: &Place) -> Option<&[Option<Span>]> {
        self.before[node.0].as_ref()?.get(place).map(Vec::as_slice)
    }

    pub fn after(&self, node: FlowNodeId, place: &Place) -> Option<&[Option<Span>]> {
        self.after[node.0].as_ref()?.get(place).map(Vec::as_slice)
    }

    pub fn definitely_before(&self, node: FlowNodeId, place: &Place) -> bool {
        self.definite_before[node.0].contains(place)
    }

    pub fn definitely_after(&self, node: FlowNodeId, place: &Place) -> bool {
        self.definite_after[node.0].contains(place)
    }

    pub fn dump(&self) -> String {
        use std::fmt::Write;
        let mut output = String::new();
        for (index, state) in self.after.iter().enumerate() {
            let Some(state) = state else { continue };
            let mut entries = state.iter().collect::<Vec<_>>();
            entries.sort_by_key(|(place, _)| format!("{place:?}"));
            for (place, _) in entries {
                let node = FlowNodeId(index);
                let prior = self.before(node, place);
                let current = self.after(node, place);
                writeln!(
                    output,
                    "  release {index} {place:?} {prior:?}->{current:?} definite={}->{}",
                    self.definitely_before(node, place),
                    self.definitely_after(node, place)
                )
                .unwrap();
            }
        }
        output
    }
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
        let first = builder.scoped_instructions(&body.instructions, builder.exit, &[])?;
        let entry = builder.push(FlowAction::Entry, None, vec![first]);
        let mut graph = Self {
            nodes: builder.nodes,
            entry,
            exit: builder.exit,
        };
        let mut place_bases = HashSet::new();
        for node in &body.nodes {
            let NodeKind::Form { head, children, .. } = &node.kind else {
                continue;
            };
            if matches!(
                head.as_str(),
                "get"
                    | "get-payload"
                    | "index"
                    | "borrow"
                    | "borrow-mut"
                    | "clone"
                    | "drop"
                    | "forget"
            ) {
                if let Some(base) = children.get(1) {
                    place_bases.insert(*base);
                }
            }
        }
        for node in &mut graph.nodes {
            let FlowAction::Evaluate(value) = node.action else {
                continue;
            };
            if let Some(place) = Place::from_expression(body, value) {
                node.action = FlowAction::Read {
                    value,
                    place,
                    place_base: place_bases.contains(&value),
                };
            }
        }
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
                } => {
                    let incoming = value_loan_origins(body, *value, &state);
                    if segments.is_empty() {
                        state[binding.0] = incoming;
                    } else {
                        replace_projected_origins(&mut state[binding.0], segments, incoming);
                    }
                }
                FlowAction::Release {
                    place:
                        Place {
                            root: PlaceRoot::Local(binding),
                            segments,
                        },
                    ..
                } => replace_projected_origins(&mut state[binding.0], segments, Vec::new()),
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

    /// Forward may-analysis of explicitly released places. Replacement and
    /// lexical scope exit kill prior release facts; joins union them.
    pub fn releases(&self, body: &Body) -> FlowReleases {
        let mut before = vec![None; self.nodes.len()];
        let mut after = vec![None; self.nodes.len()];
        let mut queued = vec![false; self.nodes.len()];
        let mut pending = VecDeque::from([self.entry]);
        before[self.entry.0] = Some(HashMap::<Place, Vec<Option<Span>>>::new());
        queued[self.entry.0] = true;
        while let Some(id) = pending.pop_front() {
            queued[id.0] = false;
            let mut state = before[id.0].as_ref().unwrap().clone();
            match &self.nodes[id.0].action {
                FlowAction::Release { place, .. } => {
                    let origins = state.entry(place.clone()).or_default();
                    if !origins.contains(&self.nodes[id.0].span) {
                        origins.push(self.nodes[id.0].span);
                    }
                }
                FlowAction::Bind { binding, .. } => {
                    state.retain(|place, _| place.root != PlaceRoot::Local(*binding));
                }
                FlowAction::Pattern { pattern, .. } => {
                    let mut bindings = HashSet::new();
                    collect_pattern_bindings(body, *pattern, &mut bindings);
                    state.retain(|place, _| {
                        !matches!(place.root, PlaceRoot::Local(binding) if bindings.contains(&binding))
                    });
                }
                FlowAction::Assign { place, .. } => {
                    // A dynamic index cannot replace a known element on every
                    // path. A static replacement revives that place and its
                    // descendants, not its previously consumed parent.
                    if !place.segments.contains(&Segment::DynamicIndex) {
                        state.retain(|released, _| {
                            released.root != place.root
                                || !released.segments.starts_with(&place.segments)
                        });
                    }
                }
                FlowAction::ScopeExit(bindings) => {
                    state.retain(|place, _| {
                        !matches!(place.root, PlaceRoot::Local(binding) if bindings.contains(&binding))
                    });
                }
                _ => {}
            }
            after[id.0] = Some(state.clone());
            for successor in &self.nodes[id.0].successors {
                let changed = match &mut before[successor.0] {
                    Some(existing) => {
                        let mut changed = false;
                        for (place, spans) in &state {
                            let held = existing.entry(place.clone()).or_default();
                            for span in spans {
                                if !held.contains(span) {
                                    held.push(*span);
                                    changed = true;
                                }
                            }
                        }
                        changed
                    }
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
        let (definite_before, definite_after) = self.definite_releases(body);
        FlowReleases {
            before,
            after,
            definite_before,
            definite_after,
        }
    }

    /// Forward may-analysis of direct value transfers and explicit releases.
    /// Other expression reads may be borrowing builtins (for example slice
    /// indexing), so only a checked direct bind/assignment/pattern/return/
    /// break value is classified as an implicit move for now.
    pub fn consumptions(&self, body: &Body, types: &LinearTypes) -> FlowConsumptions {
        let mut transfer_roots = self
            .nodes
            .iter()
            .filter_map(|node| match node.action {
                FlowAction::Bind { value, .. }
                | FlowAction::Assign { value, .. }
                | FlowAction::Pattern { value, .. } => Some(value),
                FlowAction::Return(value) | FlowAction::Break(value) => value,
                _ => None,
            })
            .collect::<Vec<_>>();
        for node in &body.nodes {
            let NodeKind::Form {
                head,
                children,
                callee,
                ..
            } = &node.kind
            else {
                continue;
            };
            if callee.is_some() {
                transfer_roots.extend(children.iter().skip(1).copied());
            } else if node.ty.is_some() && matches!(head.as_str(), "tuple" | "array" | "array-of") {
                let start = if head == "array-of" {
                    2
                } else {
                    constructor_values_start(node.ty.as_ref(), children.len())
                };
                transfer_roots.extend(children.iter().skip(start).copied());
            } else if node.ty.is_some() && head == "slice-mut-split" {
                if let Some(source) = children.get(1) {
                    transfer_roots.push(*source);
                }
            } else if node.ty.is_some() && head == "struct-literal" {
                if let Some(fields) = children.get(2) {
                    if let NodeKind::Syntax(fields) = &body.nodes[fields.0].kind {
                        for field in fields {
                            if let NodeKind::Syntax(pair) = &body.nodes[field.0].kind {
                                if let Some(value) = pair.get(1) {
                                    transfer_roots.push(*value);
                                }
                            }
                        }
                    }
                }
            } else if node.ty.is_some()
                && matches!(
                    children.first().map(|id| &body.nodes[id.0].kind),
                    Some(NodeKind::Declaration(
                        DeclarationId::Variant(_) | DeclarationId::Aggregate(_)
                    ))
                )
            {
                transfer_roots.extend(children.iter().skip(1).copied());
            } else if node.ty.is_some()
                && !matches!(
                    head.as_str(),
                    "get"
                        | "get-payload"
                        | "index"
                        | "borrow"
                        | "borrow-mut"
                        | "clone"
                        | "drop"
                        | "forget"
                        | "slice-mut-idx"
                        | "slice-mut-len"
                        | "addr-of"
                        | "addr-of-mut"
                        | "ptr-read"
                        | "ptr-is-null"
                        | "ptr-borrow"
                        | "ptr-borrow-mut"
                        | "ptr-write"
                        | "deref"
                )
            {
                transfer_roots.extend(children.iter().skip(1).copied());
            }
        }
        let mut direct_transfers = HashSet::new();
        let mut pending_values = transfer_roots;
        while let Some(value) = pending_values.pop() {
            if !direct_transfers.insert(value) {
                continue;
            }
            match &body.nodes[value.0].kind {
                NodeKind::If {
                    then_value,
                    else_value,
                    ..
                } => {
                    pending_values.push(*then_value);
                    if let Some(other) = else_value {
                        pending_values.push(*other);
                    }
                }
                NodeKind::Match { arms, .. } => {
                    for arm in arms {
                        if let NodeKind::MatchArm { values, .. } = &body.nodes[arm.0].kind {
                            if let Some(result) = values.last() {
                                pending_values.push(*result);
                            }
                        }
                    }
                }
                NodeKind::Block(instructions) => {
                    if let Some(Instruction {
                        control: Control::Evaluate(result),
                        ..
                    }) = instructions.last()
                    {
                        pending_values.push(*result);
                    }
                }
                NodeKind::Labeled(_, result) => pending_values.push(*result),
                NodeKind::Form { head, children, .. } if head == "unsafe" => {
                    if let Some(result) = children.get(1) {
                        pending_values.push(*result);
                    }
                }
                _ => {}
            }
        }
        let mut before = vec![None; self.nodes.len()];
        let mut after = vec![None; self.nodes.len()];
        let mut queued = vec![false; self.nodes.len()];
        let mut pending = VecDeque::from([self.entry]);
        before[self.entry.0] = Some(HashMap::<Place, Vec<Option<Span>>>::new());
        queued[self.entry.0] = true;
        while let Some(id) = pending.pop_front() {
            queued[id.0] = false;
            let mut state = before[id.0].as_ref().unwrap().clone();
            let node = &self.nodes[id.0];
            match &node.action {
                FlowAction::Read {
                    value,
                    place,
                    place_base: false,
                } if matches!(place.root, PlaceRoot::Local(_))
                    && direct_transfers.contains(value)
                    && body.nodes[value.0]
                        .ty
                        .as_ref()
                        .is_some_and(|ty| types.is_linear(ty)) =>
                {
                    let spans = state.entry(place.clone()).or_default();
                    if !spans.contains(&node.span) {
                        spans.push(node.span);
                    }
                }
                FlowAction::Release { place, value }
                    if matches!(place.root, PlaceRoot::Local(_))
                        && release_operand_is_linear(body, *value, types) =>
                {
                    let spans = state.entry(place.clone()).or_default();
                    if !spans.contains(&node.span) {
                        spans.push(node.span);
                    }
                }
                FlowAction::Bind { binding, .. } => {
                    state.retain(|place, _| place.root != PlaceRoot::Local(*binding));
                }
                FlowAction::Pattern { pattern, .. } => {
                    let mut bindings = HashSet::new();
                    collect_pattern_bindings(body, *pattern, &mut bindings);
                    state.retain(|place, _| {
                        !matches!(place.root, PlaceRoot::Local(binding) if bindings.contains(&binding))
                    });
                }
                FlowAction::Assign { place, .. } => {
                    if !place.segments.contains(&Segment::DynamicIndex) {
                        state.retain(|moved, _| {
                            moved.root != place.root || !moved.segments.starts_with(&place.segments)
                        });
                    }
                }
                FlowAction::ScopeExit(bindings) => {
                    state.retain(|place, _| {
                        !matches!(place.root, PlaceRoot::Local(binding) if bindings.contains(&binding))
                    });
                }
                _ => {}
            }
            after[id.0] = Some(state.clone());
            for successor in &node.successors {
                let changed = match &mut before[successor.0] {
                    Some(existing) => {
                        let mut changed = false;
                        for (place, spans) in &state {
                            let held = existing.entry(place.clone()).or_default();
                            for span in spans {
                                if !held.contains(span) {
                                    held.push(*span);
                                    changed = true;
                                }
                            }
                        }
                        changed
                    }
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
        FlowConsumptions { before, after }
    }

    /// Reject use or explicit destruction after a possible linear move on
    /// any reachable predecessor path. Exit obligations remain with the
    /// existing linear checker until the full ownership migration.
    pub fn check_linear_consumptions(
        &self,
        body: &Body,
        types: &LinearTypes,
    ) -> Result<(), ReleaseConflict> {
        if !self.nodes.iter().any(|node| match &node.action {
            FlowAction::Read {
                value,
                place_base: false,
                ..
            } => body.nodes[value.0]
                .ty
                .as_ref()
                .is_some_and(|ty| types.is_linear(ty)),
            FlowAction::Release { value, .. } => release_operand_is_linear(body, *value, types),
            _ => false,
        }) {
            return Ok(());
        }
        let moves = self.consumptions(body, types);
        for (index, node) in self.nodes.iter().enumerate() {
            let (place, message) = match &node.action {
                FlowAction::Read {
                    place,
                    place_base: false,
                    ..
                } => (place, "cannot read a value after it was consumed"),
                FlowAction::Release { place, .. } => {
                    (place, "cannot destroy a value after it was consumed")
                }
                _ => continue,
            };
            let Some(state) = moves.before[index].as_ref() else {
                continue;
            };
            let previous = state
                .iter()
                .filter(|(moved, _)| moved.overlaps(place))
                .flat_map(|(_, spans)| spans)
                .flatten()
                .min_by_key(|span| (span.source_id, span.start));
            let Some(previous) = previous else {
                continue;
            };
            return Err(ReleaseConflict {
                message: message.into(),
                span: node.span,
                labels: vec![(*previous, "value was consumed here".into())],
            });
        }
        Ok(())
    }

    /// Reject a second explicit consumption of an overlapping linear place.
    /// The syntax checker still handles implicit moves and exit obligations.
    pub fn check_linear_releases(
        &self,
        body: &Body,
        types: &LinearTypes,
    ) -> Result<(), ReleaseConflict> {
        let linear_places = self
            .nodes
            .iter()
            .filter_map(|node| {
                let FlowAction::Release { place, value } = &node.action else {
                    return None;
                };
                let NodeKind::Form { children, .. } = &body.nodes[value.0].kind else {
                    return None;
                };
                let operand = *children.get(1)?;
                types
                    .is_linear(body.nodes[operand.0].ty.as_ref()?)
                    .then_some(place.clone())
            })
            .collect::<HashSet<_>>();
        if linear_places.is_empty() {
            return Ok(());
        }
        let releases = self.releases(body);
        for (index, node) in self.nodes.iter().enumerate() {
            let FlowAction::Release { place, value } = &node.action else {
                continue;
            };
            if !linear_places.contains(place) || releases.before[index].is_none() {
                continue;
            }
            let previous = releases.before[index]
                .as_ref()
                .unwrap()
                .iter()
                .filter(|(prior, _)| linear_places.contains(*prior) && prior.overlaps(place))
                .flat_map(|(_, spans)| spans)
                .flatten()
                .min_by_key(|span| (span.source_id, span.start));
            let Some(previous) = previous else {
                continue;
            };
            let NodeKind::Form { children, .. } = &body.nodes[value.0].kind else {
                continue;
            };
            let operand_span = children
                .get(1)
                .and_then(|id| body.nodes[id.0].span)
                .or(node.span);
            let name = match place.root {
                PlaceRoot::Local(binding) => body.bindings[binding.0].name.as_str(),
                PlaceRoot::Global(_) => "global",
            };
            return Err(ReleaseConflict {
                message: format!("linear value '{name}' was already consumed in part or whole"),
                span: operand_span,
                labels: vec![(*previous, "value first consumed here".into())],
            });
        }
        Ok(())
    }

    fn definite_releases(&self, body: &Body) -> (Vec<HashSet<Place>>, Vec<HashSet<Place>>) {
        let reachable = self.reachable();
        let mut predecessors = vec![Vec::new(); self.nodes.len()];
        let universe = self
            .nodes
            .iter()
            .enumerate()
            .filter_map(|(index, node)| match &node.action {
                FlowAction::Release { place, .. } if reachable.contains(&FlowNodeId(index)) => {
                    Some(place.clone())
                }
                _ => None,
            })
            .collect::<HashSet<_>>();
        for (index, node) in self.nodes.iter().enumerate() {
            if reachable.contains(&FlowNodeId(index)) {
                for successor in &node.successors {
                    predecessors[successor.0].push(FlowNodeId(index));
                }
            }
        }
        // Must-analysis starts at top except at entry, then intersects all
        // reachable incoming paths until loop back edges reach a fixed point.
        let mut before = vec![universe.clone(); self.nodes.len()];
        let mut after = vec![universe; self.nodes.len()];
        before[self.entry.0].clear();
        let mut pending = VecDeque::from([self.entry]);
        let mut queued = vec![false; self.nodes.len()];
        let mut visited = vec![false; self.nodes.len()];
        queued[self.entry.0] = true;
        while let Some(id) = pending.pop_front() {
            queued[id.0] = false;
            let incoming = if id == self.entry {
                HashSet::new()
            } else {
                let mut paths = predecessors[id.0].iter();
                let Some(first) = paths.next() else { continue };
                let mut intersection = after[first.0].clone();
                for predecessor in paths {
                    intersection.retain(|place| after[predecessor.0].contains(place));
                }
                intersection
            };
            let mut outgoing = incoming.clone();
            match &self.nodes[id.0].action {
                FlowAction::Release { place, .. } => {
                    outgoing.insert(place.clone());
                }
                FlowAction::Bind { binding, .. } => {
                    outgoing.retain(|place| place.root != PlaceRoot::Local(*binding));
                }
                FlowAction::Pattern { pattern, .. } => {
                    let mut bindings = HashSet::new();
                    collect_pattern_bindings(body, *pattern, &mut bindings);
                    outgoing.retain(|place| {
                        !matches!(place.root, PlaceRoot::Local(binding) if bindings.contains(&binding))
                    });
                }
                FlowAction::Assign { place, .. } => {
                    if !place.segments.contains(&Segment::DynamicIndex) {
                        outgoing.retain(|released| {
                            released.root != place.root
                                || !released.segments.starts_with(&place.segments)
                        });
                    }
                }
                FlowAction::ScopeExit(bindings) => {
                    outgoing.retain(|place| {
                        !matches!(place.root, PlaceRoot::Local(binding) if bindings.contains(&binding))
                    });
                }
                _ => {}
            }
            let changed = !visited[id.0] || before[id.0] != incoming || after[id.0] != outgoing;
            visited[id.0] = true;
            before[id.0] = incoming;
            after[id.0] = outgoing;
            if changed {
                for successor in &self.nodes[id.0].successors {
                    if !queued[successor.0] {
                        queued[successor.0] = true;
                        pending.push_back(*successor);
                    }
                }
            }
        }
        for index in 0..self.nodes.len() {
            if !reachable.contains(&FlowNodeId(index)) {
                before[index].clear();
                after[index].clear();
            }
        }
        (before, after)
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
                FlowAction::Read { value, place, .. } => {
                    if body.nodes.get(value.0).is_none_or(|node| node.ty.is_none())
                        || Place::from_expression(body, *value).as_ref() != Some(place)
                    {
                        return Err(format!("typed flow reads invalid place {value:?}"));
                    }
                }
                FlowAction::Release { place, value } => {
                    let Some(crate::typed_body::Node {
                        kind: NodeKind::Form { head, children, .. },
                        ty: Some(_),
                        ..
                    }) = body.nodes.get(value.0)
                    else {
                        return Err(format!("typed flow releases invalid node {value:?}"));
                    };
                    if !matches!(head.as_str(), "drop" | "forget")
                        || children.len() != 2
                        || Place::from_expression(body, children[1]).as_ref() != Some(place)
                        || !matches!(place.root, PlaceRoot::Local(binding) if binding.0 < body.bindings.len())
                    {
                        return Err(format!("typed flow release {value:?} has invalid metadata"));
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
                FlowAction::Clone { value, place } => {
                    let Some(crate::typed_body::Node {
                        kind: NodeKind::Form { head, children, .. },
                        ty: Some(_),
                        ..
                    }) = body.nodes.get(value.0)
                    else {
                        return Err(format!("typed flow clones invalid node {value:?}"));
                    };
                    if head != "clone"
                        || children.len() != 2
                        || Place::from_expression(body, children[1]).as_ref() != Some(place)
                    {
                        return Err(format!("typed flow clone {value:?} has invalid metadata"));
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
                FlowAction::Return(value) => {
                    if value
                        .is_some_and(|id| body.nodes.get(id.0).is_none_or(|node| node.ty.is_none()))
                    {
                        return Err(format!(
                            "typed flow return {index} references an invalid value"
                        ));
                    }
                }
                FlowAction::Break(value) => {
                    if value
                        .is_some_and(|id| body.nodes.get(id.0).is_none_or(|node| node.ty.is_none()))
                    {
                        return Err(format!(
                            "typed flow break {index} references an invalid value"
                        ));
                    }
                }
                FlowAction::Entry
                | FlowAction::Exit
                | FlowAction::LoopHead
                | FlowAction::Continue
                | FlowAction::Diverge => {}
            }
            if matches!(node.action, FlowAction::Return(_)) {
                let mut next = node.successors.as_slice();
                for _ in 0..=self.nodes.len() {
                    let [successor] = next else {
                        return Err(format!("typed flow return {index} does not reach exit"));
                    };
                    if *successor == self.exit {
                        break;
                    }
                    if !matches!(self.nodes[successor.0].action, FlowAction::ScopeExit(_)) {
                        return Err(format!("typed flow return {index} has invalid cleanup"));
                    }
                    next = &self.nodes[successor.0].successors;
                }
                if next != [self.exit] {
                    return Err(format!("typed flow return {index} has cyclic cleanup"));
                }
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
                FlowAction::Read {
                    place:
                        Place {
                            root: PlaceRoot::Local(binding),
                            ..
                        },
                    ..
                } => set(&mut uses, *binding),
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
                FlowAction::Release {
                    place:
                        Place {
                            root: PlaceRoot::Local(binding),
                            ..
                        },
                    ..
                } => set(&mut uses, *binding),
                FlowAction::Clone {
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
                FlowAction::Read {
                    place:
                        Place {
                            root: PlaceRoot::Local(binding),
                            ..
                        },
                    ..
                } => Some(*binding),
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

fn release_operand_is_linear(body: &Body, value: NodeId, types: &LinearTypes) -> bool {
    let NodeKind::Form { children, .. } = &body.nodes[value.0].kind else {
        return false;
    };
    children
        .get(1)
        .and_then(|operand| body.nodes[operand.0].ty.as_ref())
        .is_some_and(|ty| types.is_linear(ty))
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

fn replace_projected_origins(
    held: &mut Vec<LoanOrigin>,
    path: &[Segment],
    incoming: Vec<LoanOrigin>,
) {
    // A dynamic index may designate any element, so it cannot strongly kill
    // the old origin of a particular element on every path.
    if !path
        .iter()
        .any(|segment| matches!(segment, Segment::DynamicIndex))
    {
        held.retain(|origin| !origin.storage.starts_with(path));
    }
    for mut origin in incoming {
        let mut storage = path.to_vec();
        storage.extend(origin.storage);
        origin.storage = storage;
        if !held.contains(&origin) {
            held.push(origin);
        }
    }
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
                let places = resolve_known_referents(body, &place, state, &mut HashSet::new());
                places
                    .into_iter()
                    .map(|place| LoanOrigin {
                        place,
                        mutable: head == "borrow-mut",
                        span: node.span,
                        storage: Vec::new(),
                    })
                    .collect()
            })
        }
        NodeKind::Form {
            children,
            callee: Some(_),
            ..
        } if matches!(
            node.ty,
            Some(Type::Reference { .. } | Type::Slice(_) | Type::MutableSlice(_))
        ) =>
        {
            let mut origins = Vec::new();
            for argument in children.iter().skip(1) {
                for mut origin in value_loan_origins(body, *argument, state) {
                    // The callee can return any reference reachable through
                    // an argument. Its direct result no longer has the
                    // argument aggregate's storage path.
                    origin.storage.clear();
                    merge_loan_origins(&mut origins, &[origin]);
                }
            }
            origins
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
            if matches!(
                head.as_str(),
                "slice-of" | "slice-mut-of" | "slice-range" | "slice-idx" | "slice-mut-idx"
            ) =>
        {
            children
                .get(1)
                .map(|source| value_loan_origins(body, *source, state))
                .unwrap_or_default()
        }
        NodeKind::Form { head, children, .. }
            if head == "slice-mut-split" && children.len() == 3 =>
        {
            let source = value_loan_origins(body, children[1], state);
            let mut origins = Vec::with_capacity(source.len() * 2);
            for half in 0..2 {
                for origin in &source {
                    let mut origin = origin.clone();
                    origin.storage.insert(0, Segment::Tuple(half));
                    merge_loan_origins(&mut origins, &[origin]);
                }
            }
            origins
        }
        NodeKind::Form { head, children, .. }
            if matches!(head.as_str(), "get" | "get-payload" | "index") =>
        {
            let Some(base) = children.get(1) else {
                return Vec::new();
            };
            let Some(slot) =
                Place::from_expression(body, id).and_then(|place| place.segments.last().cloned())
            else {
                return Vec::new();
            };
            value_loan_origins(body, *base, state)
                .into_iter()
                .filter_map(|mut origin| {
                    let held_slot = origin.storage.first()?;
                    if !storage_slot_matches(&slot, held_slot) {
                        return None;
                    }
                    origin.storage.remove(0);
                    Some(origin)
                })
                .collect()
        }
        NodeKind::Form { head, children, .. } if head == "array-repeat" => {
            let Some(Type::Array(_, length)) = node.ty.as_ref() else {
                return Vec::new();
            };
            if *length == 0 {
                return Vec::new();
            }
            let Some(value) = children.get(if children.len() == 3 { 2 } else { 1 }) else {
                return Vec::new();
            };
            let slot = if *length == 1 {
                Segment::Index(0)
            } else {
                Segment::DynamicIndex
            };
            let mut origins = value_loan_origins(body, *value, state);
            for origin in &mut origins {
                origin.storage.insert(0, slot.clone());
            }
            origins
        }
        NodeKind::Form { head, children, .. }
            if matches!(
                head.as_str(),
                "tuple" | "array" | "array-of" | "struct-literal"
            ) || matches!(
                children.first().map(|child| &body.nodes[child.0].kind),
                Some(NodeKind::Declaration(
                    DeclarationId::Aggregate(_) | DeclarationId::Variant(_)
                ))
            ) =>
        {
            let mut origins = Vec::new();
            // Checked arity distinguishes contextual value forms from forms
            // carrying an explicit type operand after the head.
            let values_start = if head == "array-of" {
                2
            } else if matches!(head.as_str(), "tuple" | "array") {
                constructor_values_start(node.ty.as_ref(), children.len())
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

/// Follow only known, direct reference origins. Unknown parameters, aggregate
/// slots, and cycles keep their original place for conservative analysis.
fn resolve_known_referents(
    body: &Body,
    place: &Place,
    state: &LoanState,
    seen: &mut HashSet<BindingId>,
) -> Vec<Place> {
    let PlaceRoot::Local(binding) = place.root else {
        return vec![place.clone()];
    };
    if place.segments.is_empty()
        || !matches!(body.bindings[binding.0].ty, Type::Reference { .. })
        || seen.len() >= 128
        || !seen.insert(binding)
    {
        return vec![place.clone()];
    }
    let direct = state[binding.0]
        .iter()
        .filter(|origin| origin.storage.is_empty())
        .collect::<Vec<_>>();
    if direct.is_empty() || direct.len() != state[binding.0].len() {
        seen.remove(&binding);
        return vec![place.clone()];
    }
    let mut resolved = Vec::new();
    for origin in direct {
        let mut referent = origin.place.clone();
        referent.segments.extend(place.segments.iter().cloned());
        for next in resolve_known_referents(body, &referent, state, seen) {
            if !resolved.contains(&next) {
                resolved.push(next);
            }
        }
    }
    seen.remove(&binding);
    resolved
}

fn constructor_values_start(ty: Option<&Type>, child_count: usize) -> usize {
    let arity = match ty {
        Some(Type::Array(_, length)) => *length,
        Some(Type::Tuple(fields)) => fields.len(),
        _ => return 2,
    };
    // The head is child zero. Contextual constructors omit the type operand.
    if child_count == arity + 1 {
        1
    } else {
        2
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
            "array" | "array-of" => Some(Segment::Index(index as u128)),
            _ => None,
        },
    }
}

fn storage_slot_matches(slot: &Segment, held: &Segment) -> bool {
    slot == held
        || matches!(
            (slot, held),
            (Segment::DynamicIndex, Segment::Index(_)) | (Segment::Index(_), Segment::DynamicIndex)
        )
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
                        if !origin
                            .storage
                            .first()
                            .is_some_and(|held| storage_slot_matches(&slot, held))
                        {
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
                let cleanup = self.cleanup_to(0, self.exit);
                let end = self.push(FlowAction::Return(*value), span, vec![cleanup]);
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
                let cleanup = self.cleanup_to(target.scope_depth, target.break_to);
                let end = self.push(FlowAction::Break(*value), span, vec![cleanup]);
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
            NodeKind::Form { head, children, .. } if head == "clone" && children.len() == 2 => {
                let action = Place::from_expression(self.body, children[1]).map_or(
                    FlowAction::Evaluate(id),
                    |place| FlowAction::Clone { value: id, place },
                );
                let done = self.push(action, span, vec![next]);
                self.expression(children[1], done, targets, None)
            }
            NodeKind::Form { head, children, .. }
                if matches!(head.as_str(), "drop" | "forget") && children.len() == 2 =>
            {
                let action = Place::from_expression(self.body, children[1])
                    .filter(|place| matches!(place.root, PlaceRoot::Local(_)))
                    .map_or(FlowAction::Evaluate(id), |place| FlowAction::Release {
                        place,
                        value: id,
                    });
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
            .filter(|(_, node)| matches!(node.action, FlowAction::Return(_)))
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
    fn return_action_retains_checked_value_identity() {
        let source = "(#fn main ((value u64)) u64 (#return value))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let graph = &checked.declarations().flows["main"];
        let returns = graph
            .nodes
            .iter()
            .filter_map(|node| match node.action {
                FlowAction::Return(Some(value)) => Some(value),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(returns.len(), 1);
        let value = returns[0];
        assert!(matches!(
            body.nodes[value.0].kind,
            NodeKind::Symbol {
                binding: Some(_),
                ..
            }
        ));
        let span = body.nodes[value.0].span.unwrap();
        assert_eq!(&source[span.start..span.end], "value");
    }

    #[test]
    fn value_break_retains_checked_loop_result_identity() {
        let source = include_str!("../examples/loop_value_conditional.lim");
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let graph = &checked.declarations().flows["main"];
        let values = graph
            .nodes
            .iter()
            .filter_map(|node| match node.action {
                FlowAction::Break(Some(value)) => Some(value),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(values.len(), 1);
        let value = values[0];
        let span = body.nodes[value.0].span.unwrap();
        assert_eq!(&source[span.start..span.end], "(#clone i)");
    }

    #[test]
    fn break_observes_loans_before_scope_cleanup() {
        let source = "(#fn main () u64
            (#let owner u64 9u64)
            (#return (#loop
                (#let view (#ref u64) (#borrow owner))
                (#break (#deref view)))))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let graph = &checked.declarations().flows["main"];
        let origins = graph.loan_origins(body);
        let view = BindingId(
            body.bindings
                .iter()
                .position(|binding| binding.name == "view")
                .unwrap(),
        );
        let transfer = graph
            .nodes
            .iter()
            .position(|node| matches!(node.action, FlowAction::Break(Some(_))))
            .map(FlowNodeId)
            .unwrap();
        assert_eq!(origins.before(transfer, view).len(), 1);
        let cleanup = graph.nodes[transfer.0].successors[0];
        assert!(matches!(&graph.nodes[cleanup.0].action,
            FlowAction::ScopeExit(bindings) if bindings.contains(&view)));
        assert!(origins.after(cleanup, view).is_empty());
    }

    #[test]
    fn return_transfer_precedes_nested_scope_cleanup() {
        let mut body = Body::default();
        body.bindings.push(crate::typed_body::Binding {
            name: "value".into(),
            ty: crate::Type::U64,
        });
        body.nodes.push(crate::typed_body::Node {
            ty: Some(crate::Type::U64),
            span: None,
            kind: NodeKind::Literal(crate::Expr::Integer(7)),
        });
        body.nodes.push(crate::typed_body::Node {
            ty: Some(crate::Type::Unit),
            span: None,
            kind: NodeKind::Block(vec![
                Instruction {
                    span: None,
                    control: Control::Bind(BindingId(0), NodeId(0), false),
                },
                Instruction {
                    span: None,
                    control: Control::Return(Some(NodeId(0))),
                },
            ]),
        });
        body.instructions.push(Instruction {
            span: None,
            control: Control::Evaluate(NodeId(1)),
        });
        let graph = FlowGraph::lower(&body).unwrap();
        let transfer = graph
            .nodes
            .iter()
            .position(|node| matches!(node.action, FlowAction::Return(Some(NodeId(0)))))
            .map(FlowNodeId)
            .unwrap();
        let cleanup = graph.nodes[transfer.0].successors[0];
        assert!(matches!(&graph.nodes[cleanup.0].action,
            FlowAction::ScopeExit(bindings) if bindings == &[BindingId(0)]));
        assert_eq!(graph.nodes[cleanup.0].successors, vec![graph.exit]);
    }

    #[test]
    fn root_function_locals_exit_after_return_transfer() {
        let source = "(#fn main () u64
            (#let owner u64 9u64)
            (#let view (#ref u64) (#borrow owner))
            (#return (#deref view)))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let graph = &checked.declarations().flows["main"];
        let origins = graph.loan_origins(body);
        let view = BindingId(
            body.bindings
                .iter()
                .position(|binding| binding.name == "view")
                .unwrap(),
        );
        let transfer = graph
            .nodes
            .iter()
            .position(|node| matches!(node.action, FlowAction::Return(Some(_))))
            .map(FlowNodeId)
            .unwrap();
        assert_eq!(origins.before(transfer, view).len(), 1);
        let cleanup = graph.nodes[transfer.0].successors[0];
        assert!(matches!(&graph.nodes[cleanup.0].action,
            FlowAction::ScopeExit(bindings) if bindings.contains(&view)));
        assert!(origins.after(cleanup, view).is_empty());
        assert_eq!(graph.nodes[cleanup.0].successors, vec![graph.exit]);
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
    fn checked_read_actions_distinguish_projection_bases_from_values() {
        let source = "(#struct Pair ((left u64) (right u64)))
          (#fn main () u64
            (#let-mut pair Pair (#struct-literal Pair ((left 1u64) (right 2u64))))
            (#let pair-ref (#ref-mut Pair) (#borrow-mut pair))
            (#let view (#ref-mut u64) (#borrow-mut (#get pair-ref left)))
            (#let right u64 (#get pair-ref right))
            (#return (#u64.+.wrap (#deref view) right)))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let graph = &checked.declarations().flows["main"];
        let mut fields = graph
            .nodes
            .iter()
            .filter_map(|node| {
                let FlowAction::Read {
                    value,
                    place,
                    place_base,
                } = &node.action
                else {
                    return None;
                };
                let span = body.nodes[value.0].span?;
                source[span.start..span.end]
                    .starts_with("(#get pair-ref")
                    .then_some((span.start, place, *place_base))
            })
            .collect::<Vec<_>>();
        fields.sort_by_key(|(start, _, _)| *start);
        assert_eq!(fields.len(), 2);
        assert!(fields[0].2);
        assert!(!fields[1].2);
        assert_ne!(fields[0].1.segments, fields[1].1.segments);
        assert!(graph.nodes.iter().any(|node| matches!(&node.action,
            FlowAction::Read { value, place_base: true, .. }
                if matches!(&body.nodes[value.0].kind, NodeKind::Symbol { name, .. } if name == "pair-ref"))));
    }

    #[test]
    fn direct_linear_transfer_records_origin_and_rejects_later_release() {
        let source = "(#struct Token ((value u64)))
          (#linear Token)
          (#fn main () ()
            (#let a Token (#struct-literal Token ((value 1u64))))
            (#let b Token (#struct-literal Token ((value 2u64))))
            (#let moved Token b)
            (#forget moved)
            (#forget a)
            (#return ()))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let mut graph = FlowGraph::lower(body).unwrap();
        let types = LinearTypes::from_program(&program);
        graph.check_linear_consumptions(body, &types).unwrap();
        let a = BindingId(body.bindings.iter().position(|b| b.name == "a").unwrap());
        let b = BindingId(body.bindings.iter().position(|b| b.name == "b").unwrap());
        let transfer = graph
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| {
                matches!(&node.action, FlowAction::Read { place, .. }
                if place.root == PlaceRoot::Local(b))
                .then_some(FlowNodeId(index))
            })
            .unwrap();
        let b_place = Place::root(PlaceRoot::Local(b));
        let moves = graph.consumptions(body, &types);
        assert!(moves.before(transfer, &b_place).is_none());
        let origin = moves.after(transfer, &b_place).unwrap()[0].unwrap();
        assert_eq!(&source[origin.start..origin.end], "b");
        let FlowAction::Read { place, .. } = &mut graph.nodes[transfer.0].action else {
            unreachable!()
        };
        place.root = PlaceRoot::Local(a);
        let error = graph.check_linear_consumptions(body, &types).unwrap_err();
        let span = error.span.unwrap();
        assert_eq!(&source[span.start..span.end], "(#forget a)");
        let first = error.labels[0].0;
        assert_eq!(&source[first.start..first.end], "b");
    }

    #[test]
    fn direct_linear_transfers_join_from_both_branches() {
        let source = "(#struct Token ((value u64)))
          (#linear Token)
          (#fn main ((flag bool)) ()
            (#let token Token (#struct-literal Token ((value 7u64))))
            (#if flag
              (#block (#let moved Token token) (#forget moved) ())
              (#block (#let moved Token token) (#forget moved) ()))
            (#return ()))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let graph = &checked.declarations().flows["main"];
        let types = LinearTypes::from_program(&program);
        graph.check_linear_consumptions(body, &types).unwrap();
        let token = BindingId(
            body.bindings
                .iter()
                .position(|b| b.name == "token")
                .unwrap(),
        );
        let exit = graph
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| {
                matches!(node.action, FlowAction::Return(_)).then_some(FlowNodeId(index))
            })
            .unwrap();
        let place = Place::root(PlaceRoot::Local(token));
        let moves = graph.consumptions(body, &types);
        let origins = moves.before(exit, &place).unwrap();
        assert_eq!(origins.len(), 2);
        assert!(origins.iter().all(|span| {
            let span = span.unwrap();
            &source[span.start..span.end] == "token"
        }));
    }

    #[test]
    fn value_branch_result_transfers_are_counted_as_moves() {
        let source = "(#struct Token ((value u64)))
          (#linear Token)
          (#fn main ((flag bool)) ()
            (#let token Token (#struct-literal Token ((value 7u64))))
            (#let result Token (#if flag token token))
            (#forget result)
            (#return ()))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let graph = &checked.declarations().flows["main"];
        let types = LinearTypes::from_program(&program);
        graph.check_linear_consumptions(body, &types).unwrap();
        let token = BindingId(
            body.bindings
                .iter()
                .position(|b| b.name == "token")
                .unwrap(),
        );
        let bind = graph
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| {
                matches!(node.action, FlowAction::Bind { binding, .. }
                if body.bindings[binding.0].name == "result")
                .then_some(FlowNodeId(index))
            })
            .unwrap();
        let moves = graph.consumptions(body, &types);
        let place = Place::root(PlaceRoot::Local(token));
        assert_eq!(moves.before(bind, &place).unwrap().len(), 2);
    }

    #[test]
    fn match_and_block_results_transfer_direct_places() {
        for (value, expected_origins) in [
            ("(#match flag (#case true token) (#case false token))", 2),
            ("(#block token)", 1),
        ] {
            let source = format!(
                "(#struct Token ((value u64)))
              (#linear Token)
              (#fn main ((flag bool)) ()
                (#let token Token (#struct-literal Token ((value 7u64))))
                (#let result Token {value})
                (#forget result)
                (#return ()))"
            );
            let program = crate::parse_program(&source).unwrap();
            let checked = crate::CheckedProgram::validate(&program).unwrap();
            let body = &checked.declarations().bodies["main"];
            let graph = &checked.declarations().flows["main"];
            let types = LinearTypes::from_program(&program);
            graph.check_linear_consumptions(body, &types).unwrap();
            let token = BindingId(
                body.bindings
                    .iter()
                    .position(|b| b.name == "token")
                    .unwrap(),
            );
            let bind = graph
                .nodes
                .iter()
                .enumerate()
                .find_map(|(index, node)| {
                    matches!(node.action, FlowAction::Bind { binding, .. }
                    if body.bindings[binding.0].name == "result")
                    .then_some(FlowNodeId(index))
                })
                .unwrap();
            let place = Place::root(PlaceRoot::Local(token));
            let moves = graph.consumptions(body, &types);
            assert_eq!(
                moves.before(bind, &place).unwrap().len(),
                expected_origins,
                "{value}"
            );
        }
    }

    #[test]
    fn direct_call_argument_consumes_linear_binding_only() {
        let source = "(#struct Token ((value u64)))
          (#linear Token)
          (#fn consume ((arg Token)) () (#forget arg) (#return ()))
          (#fn main () ()
            (#let token Token (#struct-literal Token ((value 7u64))))
            (#let copy u64 4u64)
            (#call consume (: arg token))
            (#let still-copy u64 copy)
            (#return ()))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let graph = &checked.declarations().flows["main"];
        let types = LinearTypes::from_program(&program);
        graph.check_linear_consumptions(body, &types).unwrap();
        let token = BindingId(
            body.bindings
                .iter()
                .position(|b| b.name == "token")
                .unwrap(),
        );
        let copy = BindingId(body.bindings.iter().position(|b| b.name == "copy").unwrap());
        let after_call = graph
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| {
                matches!(node.action, FlowAction::Evaluate(id)
                if matches!(&body.nodes[id.0].kind, NodeKind::Form { callee: Some(_), .. }))
                .then_some(FlowNodeId(index))
            })
            .unwrap();
        let moves = graph.consumptions(body, &types);
        let origin = moves
            .before(after_call, &Place::root(PlaceRoot::Local(token)))
            .unwrap()[0]
            .unwrap();
        assert_eq!(&source[origin.start..origin.end], "token");
        assert!(moves
            .before(after_call, &Place::root(PlaceRoot::Local(copy)))
            .is_none());
    }

    #[test]
    fn aggregate_constructor_fields_consume_linear_values() {
        for (kind, holder_type, value) in [
            (
                "struct",
                "Holder",
                "(#struct-literal Holder ((item token)))",
            ),
            ("tuple", "(#tuple Token)", "(#tuple (#tuple Token) token)"),
            (
                "array",
                "(#array Token 1)",
                "(#array-of (#array Token 1) token)",
            ),
            ("enum", "Choice", "(Some token)"),
        ] {
            let source = format!(
                "(#struct Token ((value u64)))
              (#linear Token)
              (#struct Holder ((item Token)))
              (#enum Choice ((Some Token) None))
              (#fn main () ()
                (#let token Token (#struct-literal Token ((value 7u64))))
                (#let holder {holder_type} {value})
                (#forget holder)
                (#return ()))"
            );
            let program = crate::parse_program(&source).unwrap();
            let checked = crate::CheckedProgram::validate(&program)
                .unwrap_or_else(|error| panic!("{kind}: {error}"));
            let body = &checked.declarations().bodies["main"];
            let graph = &checked.declarations().flows["main"];
            let types = LinearTypes::from_program(&program);
            graph.check_linear_consumptions(body, &types).unwrap();
            let token = BindingId(
                body.bindings
                    .iter()
                    .position(|b| b.name == "token")
                    .unwrap(),
            );
            let bind = graph
                .nodes
                .iter()
                .enumerate()
                .find_map(|(index, node)| {
                    matches!(node.action, FlowAction::Bind { binding, .. }
                    if body.bindings[binding.0].name == "holder")
                    .then_some(FlowNodeId(index))
                })
                .unwrap();
            let place = Place::root(PlaceRoot::Local(token));
            let moves = graph.consumptions(body, &types);
            let origins = moves
                .before(bind, &place)
                .unwrap_or_else(|| panic!("{kind}: no token move"));
            assert_eq!(origins.len(), 1, "{kind}");
        }
    }

    #[test]
    fn mutable_slice_split_consumes_source_but_indexing_does_not() {
        let source = "(#fn main () ()
          (#let-mut values (#array u64 2) (#array-of (#array u64 2) 1u64 2u64))
          (#let view (#slice-mut u64) (#slice-mut-of (#borrow-mut values)))
          (#let (#tuple left right) (#tuple (#slice-mut u64) (#slice-mut u64))
            (#slice-mut-split view 1usize))
          (#let observed u64 (#deref (#slice-mut-idx left 0usize)))
          (#forget left) (#forget right)
          (#return ()))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let graph = &checked.declarations().flows["main"];
        let types = LinearTypes::from_program(&program);
        graph.check_linear_consumptions(body, &types).unwrap();
        let view = BindingId(body.bindings.iter().position(|b| b.name == "view").unwrap());
        let left = BindingId(body.bindings.iter().position(|b| b.name == "left").unwrap());
        let split = graph.nodes.iter().enumerate().find_map(|(index, node)| {
            matches!(node.action, FlowAction::Evaluate(id)
                if matches!(&body.nodes[id.0].kind, NodeKind::Form { head, .. } if head == "slice-mut-split"))
                .then_some(FlowNodeId(index))
        }).unwrap();
        let index = graph.nodes.iter().enumerate().find_map(|(index, node)| {
            matches!(node.action, FlowAction::Evaluate(id)
                if matches!(&body.nodes[id.0].kind, NodeKind::Form { head, .. } if head == "slice-mut-idx"))
                .then_some(FlowNodeId(index))
        }).unwrap();
        let moves = graph.consumptions(body, &types);
        assert_eq!(
            moves
                .before(split, &Place::root(PlaceRoot::Local(view)))
                .unwrap()
                .len(),
            1
        );
        assert!(moves
            .after(index, &Place::root(PlaceRoot::Local(left)))
            .is_none());
    }

    #[test]
    fn mutable_slice_split_assigns_both_loan_origins_to_pattern_bindings() {
        let source = "(#fn main () ()
          (#let-mut values (#array u64 2) (#array-of (#array u64 2) 1u64 2u64))
          (#let view (#slice-mut u64) (#slice-mut-of (#borrow-mut values)))
          (#let (#tuple left right) (#tuple (#slice-mut u64) (#slice-mut u64))
            (#slice-mut-split view 1usize))
          (#forget left) (#forget right)
          (#return ()))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let graph = &checked.declarations().flows["main"];
        let origins = graph.loan_origins(body);
        let bind = graph
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| {
                matches!(node.action, FlowAction::Pattern { .. }).then_some(FlowNodeId(index))
            })
            .unwrap();
        for name in ["left", "right"] {
            let binding = BindingId(body.bindings.iter().position(|b| b.name == name).unwrap());
            let held = origins.after(bind, binding);
            assert_eq!(held.len(), 1, "{name}");
            assert!(held[0].storage.is_empty(), "{name}");
            let span = held[0].span.unwrap();
            assert_eq!(&source[span.start..span.end], "(#borrow-mut values)");
        }
    }

    #[test]
    fn one_slot_array_repeat_transfers_its_linear_value() {
        let source = "(#struct Token ((value u64)))
          (#linear Token)
          (#fn main () ()
            (#let token Token (#struct-literal Token ((value 7u64))))
            (#let values (#array Token 1) (#array-repeat token))
            (#forget values)
            (#return ()))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let graph = &checked.declarations().flows["main"];
        let types = LinearTypes::from_program(&program);
        graph.check_linear_consumptions(body, &types).unwrap();
        let token = BindingId(
            body.bindings
                .iter()
                .position(|b| b.name == "token")
                .unwrap(),
        );
        let bind = graph
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| {
                matches!(node.action, FlowAction::Bind { binding, .. }
                if body.bindings[binding.0].name == "values")
                .then_some(FlowNodeId(index))
            })
            .unwrap();
        let place = Place::root(PlaceRoot::Local(token));
        let moves = graph.consumptions(body, &types);
        let origin = moves.before(bind, &place).unwrap()[0].unwrap();
        assert_eq!(&source[origin.start..origin.end], "token");
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
                FlowAction::Release { ref place, value } => {
                    place == &Place::root(PlaceRoot::Local(view))
                        && matches!(&body.nodes[value.0].kind,
                        NodeKind::Form { head, .. } if head == "drop")
                }
                _ => false,
            })
            .map(FlowNodeId)
            .unwrap();
        assert_eq!(origins.before(drop, view).len(), 2);
        assert!(origins.after(drop, view).is_empty());
        assert_eq!(origins.after(drop, alias).len(), 2);
    }

    #[test]
    fn forget_releases_only_the_direct_binding_in_typed_flow() {
        let source = "(#fn main () u64
          (#let owner u64 7u64)
          (#let first (#ref u64) (#borrow owner))
          (#let second (#ref u64) first)
          (#forget first)
          (#return (#deref second)))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let graph = &checked.declarations().flows["main"];
        let origins = graph.loan_origins(body);
        let binding = |name: &str| {
            BindingId(
                body.bindings
                    .iter()
                    .position(|item| item.name == name)
                    .unwrap(),
            )
        };
        let first = binding("first");
        let second = binding("second");
        let release = graph
            .nodes
            .iter()
            .position(|node| {
                matches!(node.action, FlowAction::Release { ref place, value }
                if place == &Place::root(PlaceRoot::Local(first)) && matches!(&body.nodes[value.0].kind,
                    NodeKind::Form { head, .. } if head == "forget"))
            })
            .map(FlowNodeId)
            .unwrap();
        assert_eq!(origins.before(release, first).len(), 1);
        assert!(origins.after(release, first).is_empty());
        assert_eq!(origins.after(release, second).len(), 1);
    }

    #[test]
    fn projected_release_clears_only_selected_aggregate_origin() {
        let source = "(#struct Pair ((first (#ref u64)) (second (#ref u64))))
          (#fn main () u64
            (#let left u64 1u64)
            (#let right u64 2u64)
            (#let pair Pair (#struct-literal Pair
              ((first (#borrow left)) (second (#borrow right)))))
            (#forget (#get pair first))
            (#forget (#get pair second))
            (#return 0u64))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let graph = &checked.declarations().flows["main"];
        let origins = graph.loan_origins(body);
        let pair = BindingId(
            body.bindings
                .iter()
                .position(|binding| binding.name == "pair")
                .unwrap(),
        );
        let mut releases = graph
            .nodes
            .iter()
            .enumerate()
            .filter_map(|(index, node)| match &node.action {
                FlowAction::Release { place, .. }
                    if place.root == PlaceRoot::Local(pair) && !place.segments.is_empty() =>
                {
                    Some((FlowNodeId(index), place.segments.clone()))
                }
                _ => None,
            })
            .collect::<Vec<_>>();
        releases.sort_by_key(|(id, _)| id.0);
        assert_eq!(releases.len(), 2);
        for (release, path) in releases {
            let before = origins.before(release, pair);
            let after = origins.after(release, pair);
            assert_eq!(before.len(), after.len() + 1);
            assert!(after
                .iter()
                .all(|origin| !origin.storage.starts_with(&path)));
        }
    }

    #[test]
    fn projected_clone_retains_checked_place_and_source_span() {
        let source = "(#struct Pair ((first u64) (second u64)))
          (#fn main () u64
            (#let pair Pair (#struct-literal Pair ((first 3u64) (second 4u64))))
            (#let copy u64 (#clone (#get pair first)))
            (#return (#u64.+.wrap copy (#get pair second))))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let graph = &checked.declarations().flows["main"];
        let pair = BindingId(
            body.bindings
                .iter()
                .position(|binding| binding.name == "pair")
                .unwrap(),
        );
        let clones = graph
            .nodes
            .iter()
            .filter_map(|node| match &node.action {
                FlowAction::Clone { value, place } => Some((value, place)),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(clones.len(), 1);
        let (value, place) = clones[0];
        assert_eq!(place.root, PlaceRoot::Local(pair));
        assert!(matches!(place.segments.as_slice(), [Segment::Field(_)]));
        let span = body.nodes[value.0].span.unwrap();
        assert_eq!(&source[span.start..span.end], "(#clone (#get pair first))");
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
    fn projected_assignment_replaces_only_known_aggregate_loan_slot() {
        let origin = |owner, storage| LoanOrigin {
            place: Place::root(PlaceRoot::Local(BindingId(owner))),
            mutable: false,
            span: None,
            storage,
        };
        let old_first = origin(1, vec![Segment::Tuple(0)]);
        let old_second = origin(2, vec![Segment::Tuple(1)]);
        let nested_first = origin(4, vec![Segment::Tuple(0), Segment::Index(2)]);
        let mut held = vec![old_first.clone(), old_second.clone(), nested_first.clone()];
        replace_projected_origins(&mut held, &[Segment::Tuple(0)], vec![origin(3, vec![])]);
        assert!(!held.contains(&old_first));
        assert!(!held.contains(&nested_first));
        assert!(held.contains(&old_second));
        assert!(held.contains(&origin(3, vec![Segment::Tuple(0)])));

        let mut uncertain = vec![origin(1, vec![Segment::Index(0)])];
        replace_projected_origins(
            &mut uncertain,
            &[Segment::DynamicIndex],
            vec![origin(3, vec![])],
        );
        assert!(uncertain.contains(&origin(1, vec![Segment::Index(0)])));
        assert!(uncertain.contains(&origin(3, vec![Segment::DynamicIndex])));
    }

    #[test]
    fn reference_field_read_retains_its_direct_origin() {
        let source = "(#struct Pair ((first (#ref u64)) (second (#ref u64))))
          (#fn main () u64
            (#let left u64 1u64)
            (#let right u64 2u64)
            (#let pair Pair (#struct-literal Pair
              ((first (#borrow left)) (second (#borrow right)))))
            (#let view (#ref u64) (#get pair first))
            (#drop view)
            (#forget pair)
            (#return 0u64))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let graph = &checked.declarations().flows["main"];
        let view = BindingId(body.bindings.iter().position(|b| b.name == "view").unwrap());
        let bound = graph
            .nodes
            .iter()
            .position(
                |node| matches!(node.action, FlowAction::Bind { binding, .. } if binding == view),
            )
            .map(FlowNodeId)
            .unwrap();
        let origins = graph.loan_origins(body);
        let [origin] = origins.after(bound, view) else {
            panic!("reference field must retain one origin");
        };
        assert!(origin.storage.is_empty());
        let span = origin.span.unwrap();
        assert_eq!(&source[span.start..span.end], "(#borrow left)");
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
    fn reference_call_result_retains_each_possible_argument_origin() {
        let source = "(#fn choose ((first (#ref u64)) (second (#ref u64))) (#ref u64)
          (#return first))
          (#fn main () u64
            (#let left u64 1u64)
            (#let right u64 2u64)
            (#let selected (#ref u64)
              (#call choose (: first (#borrow left) : second (#borrow right))))
            (#return (#deref selected)))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let graph = &checked.declarations().flows["main"];
        let selected = BindingId(
            body.bindings
                .iter()
                .position(|binding| binding.name == "selected")
                .unwrap(),
        );
        let bind = graph
            .nodes
            .iter()
            .position(|node| matches!(node.action, FlowAction::Bind { binding, .. } if binding == selected))
            .map(FlowNodeId)
            .unwrap();
        let origins = graph.loan_origins(body);
        let held = origins.after(bind, selected);
        assert_eq!(held.len(), 2);
        let mut sources = held
            .iter()
            .map(|origin| {
                assert!(origin.storage.is_empty());
                let span = origin.span.unwrap();
                &source[span.start..span.end]
            })
            .collect::<Vec<_>>();
        sources.sort();
        assert_eq!(sources, ["(#borrow left)", "(#borrow right)"]);
    }

    #[test]
    fn reference_call_result_lifts_origins_out_of_aggregate_argument_slots() {
        let source = "(#fn select ((pair (#tuple (#ref u64) (#ref u64)))) (#ref u64)
          (#return (#get pair 0)))
          (#fn main () u64
            (#let left u64 1u64)
            (#let right u64 2u64)
            (#let selected (#ref u64)
              (#call select (: pair (#tuple (#borrow left) (#borrow right)))))
            (#return (#deref selected)))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let graph = &checked.declarations().flows["main"];
        let selected = BindingId(
            body.bindings
                .iter()
                .position(|binding| binding.name == "selected")
                .unwrap(),
        );
        let bind = graph
            .nodes
            .iter()
            .position(|node| matches!(node.action, FlowAction::Bind { binding, .. } if binding == selected))
            .map(FlowNodeId)
            .unwrap();
        let origins = graph.loan_origins(body);
        let held = origins.after(bind, selected);
        assert_eq!(held.len(), 2);
        assert!(held.iter().all(|origin| origin.storage.is_empty()));
    }

    #[test]
    fn slice_views_and_element_references_keep_the_array_borrow_origin() {
        let source = "(#fn main () u64
          (#let values (#array u64 3)
            (#array-of (#array u64 3) 1u64 2u64 3u64))
          (#let view (#slice u64) (#slice-of (#borrow values)))
          (#let tail (#slice u64) (#slice-range view 1usize 2usize))
          (#let item (#ref u64) (#slice-idx tail 0usize))
          (#return (#deref item)))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let graph = &checked.declarations().flows["main"];
        let origins = graph.loan_origins(body);
        let values = BindingId(
            body.bindings
                .iter()
                .position(|binding| binding.name == "values")
                .unwrap(),
        );
        for name in ["view", "tail", "item"] {
            let binding = BindingId(
                body.bindings
                    .iter()
                    .position(|candidate| candidate.name == name)
                    .unwrap(),
            );
            let bind = graph
                .nodes
                .iter()
                .position(|node| matches!(node.action, FlowAction::Bind { binding: id, .. } if id == binding))
                .map(FlowNodeId)
                .unwrap();
            let held = origins.after(bind, binding);
            assert_eq!(held.len(), 1, "{name}");
            assert_eq!(held[0].place.root, PlaceRoot::Local(values));
            let span = held[0].span.unwrap();
            assert_eq!(&source[span.start..span.end], "(#borrow values)");
        }
    }

    #[test]
    fn mutable_slice_element_keeps_exclusive_array_origin() {
        let source = "(#fn main () u64
          (#let-mut values (#array u64 2)
            (#array-of (#array u64 2) 1u64 2u64))
          (#let view (#slice-mut u64) (#slice-mut-of (#borrow-mut values)))
          (#deref-set (#slice-mut-idx view 0usize) 7u64)
          (#forget view)
          (#return 0u64))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let graph = &checked.declarations().flows["main"];
        let origins = graph.loan_origins(body);
        let index = body
            .nodes
            .iter()
            .position(
                |node| matches!(&node.kind, NodeKind::Form { head, .. } if head == "slice-mut-idx"),
            )
            .map(NodeId)
            .unwrap();
        let event = graph
            .nodes
            .iter()
            .position(|node| matches!(node.action, FlowAction::Evaluate(id) if id == index))
            .map(FlowNodeId)
            .unwrap();
        let held = value_loan_origins(body, index, origins.before[event.0].as_ref().unwrap());
        assert_eq!(held.len(), 1);
        assert!(held[0].mutable);
        let span = held[0].span.unwrap();
        assert_eq!(&source[span.start..span.end], "(#borrow-mut values)");
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
            (
                "(#tuple (#ref u64) (#ref u64))",
                "(#tuple (#borrow left) (#borrow right))",
                "(#tuple first second)",
            ),
            (
                "(#array (#ref u64) 2)",
                "(#array (#borrow left) (#borrow right))",
                "(#array first second)",
            ),
            (
                "(#array (#ref u64) 2)",
                "(#array-of (#array (#ref u64) 2) (#borrow left) (#borrow right))",
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
    fn repeated_shared_reference_has_an_origin_at_every_array_index() {
        let source = "(#fn main () u64
          (#let owner u64 7u64)
          (#let aggregate (#array (#ref u64) 2)
            (#array-repeat (#borrow owner)))
          (#let (#array first second) (#array (#ref u64) 2) aggregate)
          (#return (#u64.+.wrap (#deref first) (#deref second))))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let graph = &checked.declarations().flows["main"];
        let origins = graph.loan_origins(body);
        let pattern = graph
            .nodes
            .iter()
            .position(|node| matches!(node.action, FlowAction::Pattern { .. }))
            .map(FlowNodeId)
            .unwrap();
        for name in ["first", "second"] {
            let binding = BindingId(body.bindings.iter().position(|b| b.name == name).unwrap());
            let held = origins.after(pattern, binding);
            assert_eq!(held.len(), 1, "{name}");
            let span = held[0].span.unwrap();
            assert_eq!(&source[span.start..span.end], "(#borrow owner)");
        }
    }

    #[test]
    fn zero_length_repeat_does_not_retain_its_borrow() {
        let source = "(#fn main () ()
          (#let owner u64 7u64)
          (#let aggregate (#array (#ref u64) 0)
            (#array-repeat (#borrow owner)))
          (#forget aggregate)
          (#return ()))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let graph = &checked.declarations().flows["main"];
        let aggregate = BindingId(
            body.bindings
                .iter()
                .position(|binding| binding.name == "aggregate")
                .unwrap(),
        );
        let bind = graph
            .nodes
            .iter()
            .position(|node| matches!(node.action, FlowAction::Bind { binding, .. } if binding == aggregate))
            .map(FlowNodeId)
            .unwrap();
        assert!(graph.loan_origins(body).after(bind, aggregate).is_empty());
    }

    #[test]
    fn single_slot_repeat_origin_ends_with_projected_release() {
        let source = "(#fn main () u64
          (#let-mut owner u64 7u64)
          (#let aggregate (#array (#ref-mut u64) 1)
            (#array-repeat (#borrow-mut owner)))
          (#forget (#index aggregate 0u64))
          (#return 0u64))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let graph = &checked.declarations().flows["main"];
        let aggregate = BindingId(
            body.bindings
                .iter()
                .position(|binding| binding.name == "aggregate")
                .unwrap(),
        );
        let release = graph
            .nodes
            .iter()
            .position(|node| {
                matches!(&node.action, FlowAction::Release { place, .. }
                if place.root == PlaceRoot::Local(aggregate)
                    && place.segments == [Segment::Index(0)])
            })
            .map(FlowNodeId)
            .unwrap();
        let origins = graph.loan_origins(body);
        assert_eq!(origins.before(release, aggregate).len(), 1);
        assert!(origins.after(release, aggregate).is_empty());
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
                .position(|node| matches!(node.action, FlowAction::Return(_)))
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
                .position(|node| matches!(node.action, FlowAction::Return(_)))
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
    fn stored_projected_borrow_resolves_through_reference_chain() {
        let source = "(#struct Inner ((x u64)))
          (#struct Outer ((inner Inner)))
          (#fn main () u64
            (#let-mut owner Outer (#struct-literal Outer
              ((inner (#struct-literal Inner ((x 3u64)))))))
            (#let outer-ref (#ref-mut Outer) (#borrow-mut owner))
            (#let inner-ref (#ref-mut Inner) (#borrow-mut (#get outer-ref inner)))
            (#let value-ref (#ref u64) (#borrow (#get inner-ref x)))
            (#drop value-ref)
            (#drop inner-ref)
            (#drop outer-ref)
            (#forget owner)
            (#return 0u64))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let graph = &checked.declarations().flows["main"];
        let binding = |name: &str| {
            BindingId(
                body.bindings
                    .iter()
                    .position(|item| item.name == name)
                    .unwrap(),
            )
        };
        let owner = binding("owner");
        let value_ref = binding("value-ref");
        let bind = graph
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| {
                matches!(node.action, FlowAction::Bind { binding, .. } if binding == value_ref)
                    .then_some(FlowNodeId(index))
            })
            .unwrap();
        let origins = graph.loan_origins(body);
        let [origin] = origins.after(bind, value_ref) else {
            panic!("projected borrow should retain one origin")
        };
        assert_eq!(origin.place.root, PlaceRoot::Local(owner));
        assert_eq!(origin.place.segments.len(), 2);
        assert!(!origin.mutable);
        assert!(origin.span.is_some());
    }

    #[test]
    fn explicit_release_state_joins_and_clears_at_scope_exit() {
        let source = "(#fn main ((flag bool)) u64
          (#let-mut owner u64 1u64)
          (#let view (#ref u64) (#borrow owner))
          (#if flag (#block (#drop view)) (#block ()))
          (#return 0u64))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let graph = &checked.declarations().flows["main"];
        let view = BindingId(
            body.bindings
                .iter()
                .position(|item| item.name == "view")
                .unwrap(),
        );
        let place = Place::root(PlaceRoot::Local(view));
        let releases = graph.releases(body);
        let release = graph.nodes.iter().enumerate().find_map(|(index, node)| {
            matches!(&node.action, FlowAction::Release { place: candidate, .. } if *candidate == place)
                .then_some(FlowNodeId(index))
        }).unwrap();
        assert_eq!(
            releases.after(release, &place),
            Some([graph.nodes[release.0].span].as_slice())
        );
        let return_node = graph
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| {
                matches!(node.action, FlowAction::Return(_)).then_some(FlowNodeId(index))
            })
            .unwrap();
        assert!(releases.before(return_node, &place).is_some());
        assert!(!releases.definitely_before(return_node, &place));
        assert!(releases.after(graph.exit, &place).is_none());
    }

    #[test]
    fn release_join_retains_both_source_origins() {
        let source = "(#fn main ((flag bool)) u64
          (#let-mut owner u64 1u64)
          (#let view (#ref u64) (#borrow owner))
          (#if flag (#block (#drop view)) (#block (#drop view)))
          (#return 0u64))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let graph = &checked.declarations().flows["main"];
        let view = BindingId(
            body.bindings
                .iter()
                .position(|item| item.name == "view")
                .unwrap(),
        );
        let place = Place::root(PlaceRoot::Local(view));
        let return_node = graph
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| {
                matches!(node.action, FlowAction::Return(_)).then_some(FlowNodeId(index))
            })
            .unwrap();
        let releases = graph.releases(body);
        let origins = releases.before(return_node, &place).unwrap();
        assert_eq!(origins.len(), 2);
        assert!(origins.iter().all(Option::is_some));
        assert_ne!(origins[0], origins[1]);
        assert!(releases.definitely_before(return_node, &place));
    }

    #[test]
    fn definite_projected_replacement_revives_released_slot() {
        let old = Place {
            root: PlaceRoot::Local(BindingId(0)),
            segments: vec![Segment::Index(0)],
        };
        let graph_for = |replacement: Place| FlowGraph {
            nodes: vec![
                FlowNode {
                    action: FlowAction::Exit,
                    successors: vec![],
                    span: None,
                },
                FlowNode {
                    action: FlowAction::Assign {
                        place: replacement,
                        value: NodeId(0),
                    },
                    successors: vec![FlowNodeId(0)],
                    span: None,
                },
                FlowNode {
                    action: FlowAction::Release {
                        place: old.clone(),
                        value: NodeId(0),
                    },
                    successors: vec![FlowNodeId(1)],
                    span: None,
                },
                FlowNode {
                    action: FlowAction::Entry,
                    successors: vec![FlowNodeId(2)],
                    span: None,
                },
            ],
            entry: FlowNodeId(3),
            exit: FlowNodeId(0),
        };
        let body = Body::default();
        assert!(graph_for(old.clone())
            .releases(&body)
            .after(FlowNodeId(1), &old)
            .is_none());
        let dynamic = Place {
            root: old.root.clone(),
            segments: vec![Segment::DynamicIndex],
        };
        assert!(graph_for(dynamic)
            .releases(&body)
            .after(FlowNodeId(1), &old)
            .is_some());
        assert!(!graph_for(old.clone())
            .releases(&body)
            .definitely_after(FlowNodeId(1), &old));
    }

    #[test]
    fn definite_release_fixed_point_respects_zero_iteration_path() {
        let place = Place::root(PlaceRoot::Local(BindingId(0)));
        let graph = FlowGraph {
            nodes: vec![
                FlowNode {
                    action: FlowAction::Exit,
                    successors: vec![],
                    span: None,
                },
                FlowNode {
                    action: FlowAction::Branch(NodeId(0)),
                    successors: vec![FlowNodeId(2), FlowNodeId(0)],
                    span: None,
                },
                FlowNode {
                    action: FlowAction::Release {
                        place: place.clone(),
                        value: NodeId(0),
                    },
                    successors: vec![FlowNodeId(1)],
                    span: None,
                },
                FlowNode {
                    action: FlowAction::Entry,
                    successors: vec![FlowNodeId(1)],
                    span: None,
                },
            ],
            entry: FlowNodeId(3),
            exit: FlowNodeId(0),
        };
        let releases = graph.releases(&Body::default());
        assert!(releases.definitely_after(FlowNodeId(2), &place));
        assert!(releases.before(graph.exit, &place).is_some());
        assert!(!releases.definitely_before(graph.exit, &place));

        // Moving the release before the loop makes it unavoidable even when
        // the body executes zero or many times.
        let mut before_loop = graph.clone();
        before_loop.nodes.push(FlowNode {
            action: FlowAction::Release {
                place: place.clone(),
                value: NodeId(0),
            },
            successors: vec![FlowNodeId(1)],
            span: None,
        });
        before_loop.nodes[before_loop.entry.0].successors = vec![FlowNodeId(4)];
        let releases = before_loop.releases(&Body::default());
        assert!(releases.definitely_before(before_loop.exit, &place));
    }

    #[test]
    fn consuming_linear_field_then_parent_is_rejected() {
        let source = "(#struct Resource ((value u64)))
          (#linear Resource)
          (#struct Pair ((item Resource) (other u64)))
          (#fn main () u64
            (#let pair Pair (#struct-literal Pair
              ((item (#struct-literal Resource ((value 1u64)))) (other 0u64))))
            (#forget (#get pair item))
            (#forget pair)
            (#return 0u64))";
        let program = crate::parse_program(source).unwrap();
        let (message, _, span, labels) =
            crate::typecheck::check_types_with_span(&program).unwrap_err();
        assert!(
            message.contains("already consumed in part or whole"),
            "{message}"
        );
        let span = span.expect("second consumption has a source span");
        assert_eq!(&source[span.start..span.end], "pair");
        assert_eq!(labels.len(), 1);
        assert!(source[labels[0].0.start..labels[0].0.end].contains("#forget (#get pair item)"));
    }

    #[test]
    fn forgetting_copy_field_does_not_consume_linear_parent() {
        let source = "(#struct Resource ((value u64)))
          (#linear Resource)
          (#struct Pair ((item Resource) (other u64)))
          (#fn main () u64
            (#let pair Pair (#struct-literal Pair
              ((item (#struct-literal Resource ((value 1u64)))) (other 0u64))))
            (#forget (#get pair other))
            (#forget pair)
            (#return 0u64))";
        let program = crate::parse_program(source).unwrap();
        crate::check_types(&program).unwrap();
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
            .filter(|node| matches!(node.action, FlowAction::Break(_)))
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
        assert!(graph
            .nodes
            .iter()
            .any(|node| matches!(node.action, FlowAction::Return(_))));
    }

    #[test]
    fn loop_local_reference_release_does_not_leak_to_the_next_iteration() {
        let source = "(#fn main () u64
          (#let-mut value u64 7u64)
          (#let-mut count u64 0u64)
          (#while (#u64.< count 2u64)
            (#let view (#ref u64) (#borrow value))
            (#let observed u64 (#deref view))
            (#forget view)
            (#set count (#u64.+.wrap count 1u64)))
          (#return value))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let graph = &checked.declarations().flows["main"];
        let view = BindingId(
            body.bindings
                .iter()
                .position(|binding| binding.name == "view")
                .unwrap(),
        );
        let condition = NodeId(
            body.nodes
                .iter()
                .position(
                    |node| matches!(&node.kind, NodeKind::Form { head, .. } if head == "u64.<"),
                )
                .unwrap(),
        );
        let header = graph
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| {
                matches!(node.action, FlowAction::Branch(value) if value == condition)
                    .then_some(FlowNodeId(index))
            })
            .unwrap();
        let loans = graph.loan_origins(body);
        assert!(loans.before(header, view).is_empty());
        assert!(loans.after(header, view).is_empty());
    }

    #[test]
    fn outer_reference_origin_survives_typed_loop_back_edges() {
        let source = "(#fn main () u64
          (#let-mut value u64 7u64)
          (#let view (#ref-mut u64) (#borrow-mut value))
          (#let-mut count u64 0u64)
          (#while (#u64.< count 2u64)
            (#let observed u64 (#deref view))
            (#set count (#u64.+.wrap count 1u64)))
          (#forget view)
          (#return value))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let graph = &checked.declarations().flows["main"];
        let view = BindingId(
            body.bindings
                .iter()
                .position(|binding| binding.name == "view")
                .unwrap(),
        );
        let value = BindingId(
            body.bindings
                .iter()
                .position(|binding| binding.name == "value")
                .unwrap(),
        );
        let condition = NodeId(
            body.nodes
                .iter()
                .position(
                    |node| matches!(&node.kind, NodeKind::Form { head, .. } if head == "u64.<"),
                )
                .unwrap(),
        );
        let header = graph
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| {
                matches!(node.action, FlowAction::Branch(found) if found == condition)
                    .then_some(FlowNodeId(index))
            })
            .unwrap();
        let loans = graph.loan_origins(body);
        for loan in loans
            .before(header, view)
            .iter()
            .chain(loans.after(header, view))
        {
            assert_eq!(loan.place.root, PlaceRoot::Local(value));
            assert!(loan.mutable);
        }
        assert!(!loans.before(header, view).is_empty());
    }
}
