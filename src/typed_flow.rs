//! Stable, address-free control flow over the checked body arena.
//! Ownership passes can share these edges instead of reconstructing branch
//! and loop behavior independently from syntax.

use std::collections::{HashMap, HashSet, VecDeque};

use crate::linearcheck::LinearTypes;
use crate::typed_body::{
    BindingId, Body, Control, Instruction, NodeId, NodeKind, NumericOpcode, PlaceRoot, Projection,
};
use crate::typed_ir::{DeclarationId, FieldId};
use crate::typed_place::{reads_through_reference, Place, Segment};
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
    BorrowScopeEnd {
        scope: NodeId,
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
    /// A write through a reference, such as `#deref-set`. This mutates the
    /// referent, not the local slot that stores the reference.
    Write {
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
    Break {
        value: Option<NodeId>,
        result: Option<NodeId>,
    },
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
    pub pinned: bool,
    /// Raw-pointer provenance may identify only a lifetime anchor.
    pub lifetime_only: bool,
    pub span: Option<Span>,
    /// Immediate reference binding whose referent this loan reborrows.
    pub borrowed_from: Option<BindingId>,
    /// Position inside the value held by a binding, not the referent place.
    pub storage: Vec<Segment>,
    /// Original slot inside a function parameter, retained through projections.
    pub parameter_storage: Option<Vec<Segment>>,
}

impl PartialEq for LoanOrigin {
    fn eq(&self, other: &Self) -> bool {
        self.place == other.place
            && self.mutable == other.mutable
            && self.pinned == other.pinned
            && self.lifetime_only == other.lifetime_only
            && self.borrowed_from == other.borrowed_from
            && self.storage == other.storage
            && self.parameter_storage == other.parameter_storage
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
    at: Vec<HashSet<Place>>,
    definitely_before: Vec<Option<HashSet<Place>>>,
    /// Indirect accesses lacking provenance; never an ownership proof.
    unresolved: HashSet<FlowNodeId>,
}

#[cfg(test)]
#[derive(Debug)]
pub(crate) struct ReferentExitEffect {
    pub place: Place,
    pub input_storage: Option<Vec<Segment>>,
    pub referent_projection: Vec<Segment>,
    pub definitely_consumed: bool,
    pub consumption_spans: Vec<Option<Span>>,
}

#[cfg(test)]
#[derive(Debug)]
pub(crate) struct ReferentFunctionEffects {
    pub has_normal_return: bool,
    pub effects: Vec<ReferentExitEffect>,
    pub unresolved: Vec<FlowNodeId>,
    pub reads: Vec<ReferentRead>,
    pub unresolved_reads: Vec<FlowNodeId>,
    pub entry_reads: Vec<ReferentRead>,
    pub restored_from_consumed_entry: Vec<Place>,
}

/// Independent read facts, not outgoing consumption or complete entry
/// requirements. Prior initialization writes must be considered separately.
#[cfg(test)]
#[derive(Debug)]
pub(crate) struct ReferentRead {
    pub event: FlowNodeId,
    pub place: Place,
    pub input_storage: Option<Vec<Segment>>,
    pub referent_projection: Vec<Segment>,
    pub span: Option<Span>,
}

#[cfg(test)]
#[derive(Default)]
pub(crate) struct ReferentCallFacts {
    pub effects: Vec<(FlowNodeId, Vec<ReferentExitEffect>, bool)>,
    pub restorations: Vec<(FlowNodeId, Vec<Place>)>,
    pub consumed_inputs: Vec<(FlowNodeId, Vec<Place>, bool)>,
    pub read_inputs: Vec<ReferentRead>,
    pub unresolved_inputs: Vec<FlowNodeId>,
}

#[derive(Default)]
struct CallConsumptionFacts {
    possible: Vec<(Place, Vec<Option<Span>>)>,
    definite: Vec<Place>,
    unresolved: bool,
    restored: Vec<Place>,
}

impl FlowConsumptions {
    #[cfg(test)]
    pub fn unresolved_nodes(&self) -> &HashSet<FlowNodeId> {
        &self.unresolved
    }
    pub fn before(&self, node: FlowNodeId, place: &Place) -> Option<&[Option<Span>]> {
        self.before[node.0].as_ref()?.get(place).map(Vec::as_slice)
    }

    pub fn after(&self, node: FlowNodeId, place: &Place) -> Option<&[Option<Span>]> {
        self.after[node.0].as_ref()?.get(place).map(Vec::as_slice)
    }

    /// Whether this flow node newly consumes the supplied place. Spans make
    /// the check stable when the same place has already been consumed on a
    /// different predecessor path.
    pub fn consumes_at(&self, node: FlowNodeId, place: &Place) -> bool {
        self.at[node.0].contains(place)
    }

    pub fn definitely_consumed_before(&self, node: FlowNodeId, place: &Place) -> bool {
        self.definitely_before[node.0]
            .as_ref()
            .is_some_and(|state| state.contains(place))
    }

    pub fn dump(&self) -> String {
        use std::fmt::Write;
        let mut output = String::new();
        for (index, state) in self.after.iter().enumerate() {
            if self.unresolved.contains(&FlowNodeId(index)) {
                writeln!(output, "  unresolved-referent {index}").unwrap();
            }
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
    pub fn value_before(
        &self,
        body: &Body,
        flow: &FlowGraph,
        node: FlowNodeId,
        value: NodeId,
    ) -> Vec<LoanOrigin> {
        if matches!(body.nodes[value.0].kind, NodeKind::Loop(_)) {
            let mut loop_results = Vec::new();
            for (index, event) in flow.nodes.iter().enumerate() {
                let FlowAction::Break {
                    value: Some(break_value),
                    result: Some(result),
                } = &event.action
                else {
                    continue;
                };
                if *result != value {
                    continue;
                }
                let Some(state) = &self.before[index] else {
                    continue;
                };
                let mut alternatives = Vec::new();
                collect_result_alternatives(body, *break_value, &mut alternatives);
                let mut evaluated = false;
                for alternative in alternatives {
                    for (event_index, candidate) in flow.nodes.iter().enumerate() {
                        if flow_action_has_value(&candidate.action, alternative) {
                            if let Some(state) = &self.before[event_index] {
                                evaluated = true;
                                merge_loan_origins(
                                    &mut loop_results,
                                    &value_loan_origins_at_events(
                                        body,
                                        flow,
                                        &self.before,
                                        alternative,
                                        state,
                                    ),
                                );
                            }
                        }
                    }
                }
                if !evaluated {
                    merge_loan_origins(
                        &mut loop_results,
                        &value_loan_origins_at_events(
                            body,
                            flow,
                            &self.before,
                            *break_value,
                            state,
                        ),
                    );
                }
            }
            if !loop_results.is_empty() {
                return loop_results;
            }
        }
        let mut results = Vec::new();
        let mut alternatives = Vec::new();
        collect_result_alternatives(body, value, &mut alternatives);
        for alternative in alternatives {
            for (index, event) in flow.nodes.iter().enumerate() {
                if !flow_action_has_value(&event.action, alternative) {
                    continue;
                }
                if let Some(state) = &self.before[index] {
                    merge_loan_origins(
                        &mut results,
                        &value_loan_origins_at_events(body, flow, &self.before, alternative, state),
                    );
                }
            }
        }
        if results.is_empty() {
            self.before[node.0].as_ref().map_or_else(Vec::new, |state| {
                value_loan_origins_at_events(body, flow, &self.before, value, state)
            })
        } else {
            results
        }
    }

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

    /// Resolve a projected access through a reference stored in a local. The
    /// stored loan slot is a prefix of the checked place; remaining field or
    /// index segments project from its referent.
    pub fn projected_referents(
        &self,
        node: FlowNodeId,
        binding: BindingId,
        segments: &[Segment],
    ) -> Vec<Place> {
        self.projected_referents_with_slots(node, binding, segments, false)
    }

    fn projected_referents_with_slots(
        &self,
        node: FlowNodeId,
        binding: BindingId,
        segments: &[Segment],
        parameter_slots: bool,
    ) -> Vec<Place> {
        let origin_place = |origin: &LoanOrigin| {
            let mut place = origin.place.clone();
            if parameter_slots && matches!(place.root, PlaceRoot::Parameter(_)) {
                if let Some(slot) = &origin.parameter_storage {
                    let mut segments = slot.clone();
                    segments.append(&mut place.segments);
                    place.segments = segments;
                }
            }
            place
        };
        let through_deref = segments
            .iter()
            .any(|segment| matches!(segment, Segment::Dereference));
        if let Some(index) = segments.iter().position(|segment| {
            matches!(segment, Segment::SliceIndex(_) | Segment::SliceDynamicIndex)
        }) {
            let prefix = &segments[..index];
            let suffix = segments[index + 1..]
                .iter()
                .filter(|segment| !matches!(segment, Segment::Dereference))
                .map(|segment| match segment {
                    Segment::SliceIndex(index) => Segment::Index(*index),
                    Segment::SliceDynamicIndex => Segment::DynamicIndex,
                    segment => segment.clone(),
                })
                .collect::<Vec<_>>();
            let mut places = Vec::new();
            for origin in self.before(node, binding) {
                if prefix.len() > origin.storage.len()
                    || !prefix
                        .iter()
                        .zip(&origin.storage)
                        .all(|(prefix, stored)| storage_slot_matches(prefix, stored))
                {
                    continue;
                }
                let mut place = origin_place(origin);
                for segment in &origin.storage[prefix.len()..] {
                    if matches!(segment, Segment::SliceHalf(_)) {
                        place.segments.push(segment.clone());
                    }
                }
                place.segments.extend(suffix.iter().cloned());
                if !places.contains(&place) {
                    places.push(place);
                }
            }
            return places;
        }
        let segments = segments
            .iter()
            .filter(|segment| !matches!(segment, Segment::Dereference))
            .cloned()
            .collect::<Vec<_>>();
        let mut places = Vec::new();
        for origin in self.before(node, binding) {
            if segments.len() < origin.storage.len()
                || (!through_deref && segments.len() == origin.storage.len())
                || !segments.starts_with(&origin.storage)
            {
                continue;
            }
            let mut place = origin_place(origin);
            place
                .segments
                .extend_from_slice(&segments[origin.storage.len()..]);
            if !places.contains(&place) {
                places.push(place);
            }
        }
        places
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
    break_result: Option<NodeId>,
    scope_depth: usize,
    borrow_scope_depth: usize,
}

struct Builder<'a> {
    body: &'a Body,
    nodes: Vec<FlowNode>,
    exit: FlowNodeId,
    active_scopes: Vec<Vec<BindingId>>,
    active_borrow_scopes: Vec<NodeId>,
}

fn display_linear_place(body: &Body, place: &Place) -> String {
    let root = match place.root {
        PlaceRoot::Local(binding) | PlaceRoot::Parameter(binding) => body
            .bindings
            .get(binding.0)
            .map(|binding| binding.name.clone())
            .unwrap_or_else(|| format!("binding#{}", binding.0)),
        PlaceRoot::Global(global) => body
            .declaration_name(DeclarationId::Global(global))
            .unwrap_or("global")
            .to_owned(),
    };
    let mut output = root;
    for segment in &place.segments {
        match segment {
            Segment::Dereference => output.push_str(".*"),
            Segment::Field(field) => {
                output.push('.');
                output.push_str(
                    body.declaration_name(DeclarationId::Field(*field))
                        .unwrap_or("field"),
                );
            }
            Segment::Tuple(index) => output.push_str(&format!(".{index}")),
            Segment::Payload(variant, index) => {
                output.push('.');
                output.push_str(
                    body.declaration_name(DeclarationId::Variant(*variant))
                        .unwrap_or("variant"),
                );
                output.push_str(&format!("[{index}]"));
            }
            Segment::Index(index) => output.push_str(&format!("[{index}]")),
            Segment::DynamicIndex => output.push_str("[*]"),
            Segment::SliceHalf(half) => output.push_str(&format!(".half-{half}")),
            Segment::SliceIndex(index) => output.push_str(&format!("[{index}]")),
            Segment::SliceDynamicIndex => output.push_str("[*]"),
        }
    }
    output
}

impl FlowGraph {
    pub fn lower(body: &Body) -> Result<Self, String> {
        let mut builder = Builder {
            body,
            nodes: Vec::new(),
            exit: FlowNodeId(0),
            active_scopes: Vec::new(),
            active_borrow_scopes: Vec::new(),
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
                    | "pin-get-payload"
                    | "pin-get-payload-mut"
                    | "index"
                    | "borrow"
                    | "borrow-mut"
                    | "pin-borrow"
                    | "pin-borrow-mut"
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
        // Branch results are read at their evaluation events, before lexical
        // cleanup kills their local bindings. Those snapshots are additional
        // dataflow dependencies: a changed snapshot must wake its consumers
        // even when the scope-exit state flowing to them did not change.
        let mut snapshot_users = vec![Vec::new(); self.nodes.len()];
        let mut events_by_value = vec![Vec::new(); body.nodes.len()];
        let mut loop_values = vec![Vec::new(); body.nodes.len()];
        for (index, event) in self.nodes.iter().enumerate() {
            let value = match event.action {
                FlowAction::Evaluate(value)
                | FlowAction::Read { value, .. }
                | FlowAction::Borrow { value, .. }
                | FlowAction::Clone { value, .. }
                | FlowAction::Release { value, .. }
                | FlowAction::Break {
                    value: Some(value), ..
                } => value,
                _ => continue,
            };
            events_by_value[value.0].push(index);
            if let FlowAction::Break {
                value: Some(value),
                result: Some(result),
            } = event.action
            {
                loop_values[result.0].push(value);
            }
        }
        for (consumer_index, consumer) in self.nodes.iter().enumerate() {
            let value = match consumer.action {
                FlowAction::Bind { value, .. }
                | FlowAction::Assign { value, .. }
                | FlowAction::Pattern { value, .. }
                | FlowAction::Write { value, .. } => value,
                _ => continue,
            };
            let mut dependencies = HashSet::new();
            let mut pending_values = vec![value];
            while let Some(value) = pending_values.pop() {
                if !dependencies.insert(value) {
                    continue;
                }
                match &body.nodes[value.0].kind {
                    NodeKind::Form { children, .. } => {
                        pending_values.extend(children.iter().copied())
                    }
                    NodeKind::If {
                        then_value,
                        else_value,
                        ..
                    } => {
                        pending_values.push(*then_value);
                        pending_values.extend(*else_value);
                    }
                    NodeKind::Match { arms, .. } => pending_values.extend(arms.iter().copied()),
                    NodeKind::MatchArm { values, .. } => {
                        pending_values.extend(values.last().copied())
                    }
                    NodeKind::Block(instructions) => {
                        if let Some(Control::Evaluate(value)) =
                            instructions.last().map(|instruction| &instruction.control)
                        {
                            pending_values.push(*value);
                        }
                    }
                    NodeKind::Loop(_) => {
                        pending_values.extend(loop_values[value.0].iter().copied())
                    }
                    NodeKind::Labeled(_, value) => pending_values.push(*value),
                    _ => {}
                }
            }
            for value in dependencies {
                for event_index in &events_by_value[value.0] {
                    snapshot_users[*event_index].push(FlowNodeId(consumer_index));
                }
            }
        }
        let mut empty = vec![Vec::new(); body.bindings.len()];
        // A reference parameter is an externally supplied loan root. Its
        // referent is intentionally represented by the parameter's stable
        // binding identity: callers have already checked aliasing between
        // their arguments, while this seed lets local reborrows retain the
        // parameter origin instead of appearing origin-free.
        for (index, slots) in body.parameter_loan_slots.iter().enumerate() {
            for slot in slots {
                empty[index].push(LoanOrigin {
                    place: Place::root(PlaceRoot::Parameter(BindingId(index))),
                    mutable: slot.mutable,
                    pinned: slot.pinned,
                    span: None,
                    borrowed_from: None,
                    storage: slot.storage.clone(),
                    parameter_storage: Some(slot.storage.clone()),
                    lifetime_only: false,
                });
            }
        }
        let mut before: Vec<Option<LoanState>> = vec![None; self.nodes.len()];
        let mut after: Vec<Option<LoanState>> = vec![None; self.nodes.len()];
        let mut queued = vec![false; self.nodes.len()];
        let mut pending = VecDeque::from([self.entry]);
        before[self.entry.0] = Some(empty);
        queued[self.entry.0] = true;
        while let Some(id) = pending.pop_front() {
            queued[id.0] = false;
            let mut state = before[id.0].as_ref().unwrap().clone();
            match &self.nodes[id.0].action {
                FlowAction::Bind { binding, value } => {
                    state[binding.0] =
                        value_loan_origins_at_events(body, self, &before, *value, &state);
                }
                FlowAction::Pattern { pattern, value } => {
                    let origins = value_loan_origins_at_events(body, self, &before, *value, &state);
                    distribute_pattern_origins(body, *pattern, &origins, &mut state);
                    if let (Some(place), Some(selected)) = (
                        Place::from_expression(body, *value),
                        origins_selected_by_variant(body, *pattern, &origins),
                    ) {
                        if let PlaceRoot::Local(binding) = place.root {
                            state[binding.0] = selected;
                        }
                    }
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
                    let incoming =
                        value_loan_origins_at_events(body, self, &before, *value, &state);
                    if segments.is_empty() {
                        state[binding.0] = incoming;
                    } else {
                        replace_projected_origins(&mut state[binding.0], segments, incoming);
                    }
                }
                FlowAction::Write { value, .. } | FlowAction::Evaluate(value)
                    if matches!(self.nodes[id.0].action, FlowAction::Write { .. })
                        || matches!(&body.nodes[value.0].kind,
                            NodeKind::Form { head, children, .. } if head == "deref-set" && children.len() == 3) =>
                {
                    let source = match &body.nodes[value.0].kind {
                        NodeKind::Form { head, children, .. }
                            if matches!(head.as_str(), "deref-set" | "pin-write")
                                && children.len() == 3 =>
                        {
                            children[2]
                        }
                        NodeKind::Form { head, children, .. }
                            if head == "pin-set-field" && children.len() == 4 =>
                        {
                            children[3]
                        }
                        _ => *value,
                    };
                    let incoming =
                        value_loan_origins_at_events(body, self, &before, source, &state);
                    let destinations = match &body.nodes[value.0].kind {
                        NodeKind::Form { head, children, .. }
                            if matches!(head.as_str(), "deref-set" | "pin-write")
                                && children.len() == 3 =>
                        {
                            let target = children[1];
                            let mut origins = Vec::new();
                            for event in &events_by_value[target.0] {
                                if let Some(snapshot) = &before[*event] {
                                    merge_loan_origins(
                                        &mut origins,
                                        &value_loan_origins_at_events(
                                            body, self, &before, target, snapshot,
                                        ),
                                    );
                                }
                            }
                            origins
                        }
                        _ => match &self.nodes[id.0].action {
                            FlowAction::Write { place, .. } => {
                                reborrow_source_origins(place, &state, &mut HashSet::new())
                            }
                            _ => Vec::new(),
                        },
                    };
                    let mut known_places = Vec::new();
                    for origin in &destinations {
                        if !known_places.contains(&origin.place) {
                            known_places.push(origin.place.clone());
                        }
                    }
                    let strong = known_places.len() == 1
                        && destinations.iter().all(|origin| !origin.lifetime_only);
                    for origin in destinations {
                        // Parameter roots describe external pointees, not
                        // the local reference handles indexed by LoanState.
                        if origin.lifetime_only {
                            continue;
                        }
                        let destination = origin.place;
                        if let PlaceRoot::Local(binding) = destination.root {
                            if strong {
                                replace_projected_origins(
                                    &mut state[binding.0],
                                    &destination.segments,
                                    incoming.clone(),
                                );
                            } else {
                                extend_projected_origins(
                                    &mut state[binding.0],
                                    &destination.segments,
                                    incoming.clone(),
                                );
                            }
                        }
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
            for successor in &self.nodes[id.0].successors {
                let changed = match &mut before[successor.0] {
                    Some(existing) => merge_loan_states(existing, &state),
                    slot @ None => {
                        *slot = Some(state.clone());
                        true
                    }
                };
                if changed {
                    if !queued[successor.0] {
                        pending.push_back(*successor);
                        queued[successor.0] = true;
                    }
                    for consumer in &snapshot_users[successor.0] {
                        if before[consumer.0].is_some() && !queued[consumer.0] {
                            pending.push_back(*consumer);
                            queued[consumer.0] = true;
                        }
                    }
                }
            }
            after[id.0] = Some(state);
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
        self.consumptions_with_origins(body, types, None)
    }

    /// Staging analysis for borrowed-storage ownership. Resolve reference
    /// projections to loan roots and retain those facts across alias cleanup.
    /// Ambiguous writes cannot definitely restore any one possible referent.
    #[cfg(test)]
    pub fn referent_consumptions(&self, body: &Body, types: &LinearTypes) -> FlowConsumptions {
        let origins = self.loan_origins(body);
        self.consumptions_with_origins(body, types, Some(&origins))
    }

    #[cfg(test)]
    pub fn referent_reads(&self, body: &Body) -> (Vec<ReferentRead>, Vec<FlowNodeId>) {
        let origins = self.loan_origins(body);
        let reachable = self.reachable();
        let mut reads = Vec::new();
        let mut unresolved = Vec::new();
        for (index, node) in self.nodes.iter().enumerate() {
            let event = FlowNodeId(index);
            if !reachable.contains(&event) {
                continue;
            }
            let FlowAction::Read {
                value,
                place,
                place_base: false,
            } = &node.action
            else {
                continue;
            };
            if !reads_through_reference(body, *value) {
                continue;
            }
            let places = match &place.root {
                PlaceRoot::Local(binding)
                    if !origins
                        .before(event, *binding)
                        .iter()
                        .any(|origin| origin.lifetime_only) =>
                {
                    origins.projected_referents_with_slots(event, *binding, &place.segments, true)
                }
                _ => Vec::new(),
            };
            if places.is_empty() {
                unresolved.push(event);
            }
            for place in places {
                let (input_storage, referent_projection) =
                    split_referent_effect_place(body, &place);
                reads.push(ReferentRead {
                    event,
                    place,
                    input_storage,
                    referent_projection,
                    span: node.span,
                });
            }
        }
        (reads, unresolved)
    }

    /// Staged exit facts plus unresolved accesses that can reach each exit.
    /// Entry requirements and caller transfer are not complete contracts yet.
    #[cfg(test)]
    pub fn referent_exit_effects(
        &self,
        body: &Body,
        types: &LinearTypes,
    ) -> Vec<(FlowNodeId, Vec<ReferentExitEffect>, Vec<FlowNodeId>)> {
        let moves = self.referent_consumptions(body, types);
        self.referent_exit_effects_from_moves(body, &moves)
    }

    #[cfg(test)]
    fn referent_exit_effects_from_moves(
        &self,
        body: &Body,
        moves: &FlowConsumptions,
    ) -> Vec<(FlowNodeId, Vec<ReferentExitEffect>, Vec<FlowNodeId>)> {
        let mut predecessors = vec![Vec::new(); self.nodes.len()];
        for (index, node) in self.nodes.iter().enumerate() {
            for successor in &node.successors {
                predecessors[successor.0].push(FlowNodeId(index));
            }
        }
        self.nodes
            .iter()
            .enumerate()
            .filter_map(|(index, node)| {
                if !matches!(node.action, FlowAction::Return(_)) {
                    return None;
                }
                let state = moves.before[index].as_ref()?;
                let event = FlowNodeId(index);
                let effects = state
                    .iter()
                    .filter(|(place, _)| {
                        matches!(place.root, PlaceRoot::Parameter(_) | PlaceRoot::Global(_))
                    })
                    .map(|(place, spans)| {
                        let (input_storage, referent_projection) =
                            split_referent_effect_place(body, place);
                        ReferentExitEffect {
                            place: place.clone(),
                            input_storage,
                            referent_projection,
                            definitely_consumed: moves.definitely_consumed_before(event, place),
                            consumption_spans: spans.clone(),
                        }
                    })
                    .collect();
                let mut ancestors = HashSet::new();
                let mut pending = vec![event];
                while let Some(node) = pending.pop() {
                    if ancestors.insert(node) {
                        pending.extend(predecessors[node.0].iter().copied());
                    }
                }
                let mut unresolved = moves
                    .unresolved
                    .iter()
                    .filter(|node| ancestors.contains(node))
                    .copied()
                    .collect::<Vec<_>>();
                unresolved.sort_by_key(|node| node.0);
                Some((event, effects, unresolved))
            })
            .collect()
    }

    #[cfg(test)]
    pub fn referent_function_effects(
        &self,
        body: &Body,
        types: &LinearTypes,
    ) -> ReferentFunctionEffects {
        let exits = self.referent_exit_effects(body, types);
        self.referent_function_effects_from_exits(body, exits)
    }

    /// Include mapped callee effects when summarizing a forwarding helper.
    /// This remains staged until entry and restoration contracts are available.
    #[cfg(test)]
    pub fn referent_function_effects_with_calls(
        &self,
        body: &Body,
        types: &LinearTypes,
        calls: &[(FlowNodeId, Vec<ReferentExitEffect>, bool)],
    ) -> ReferentFunctionEffects {
        self.referent_function_effects_with_restorations(body, types, calls, &[])
    }

    #[cfg(test)]
    pub fn referent_function_effects_with_restorations(
        &self,
        body: &Body,
        types: &LinearTypes,
        calls: &[(FlowNodeId, Vec<ReferentExitEffect>, bool)],
        restorations: &[(FlowNodeId, Vec<Place>)],
    ) -> ReferentFunctionEffects {
        let moves =
            self.referent_consumptions_with_restorations(body, types, calls, restorations, &[]);
        let exits = self.referent_exit_effects_from_moves(body, &moves);
        self.referent_function_effects_from_exits(body, exits)
    }

    #[cfg(test)]
    fn referent_function_effects_from_exits(
        &self,
        body: &Body,
        exits: Vec<(FlowNodeId, Vec<ReferentExitEffect>, Vec<FlowNodeId>)>,
    ) -> ReferentFunctionEffects {
        let mut places = Vec::new();
        let mut unresolved = Vec::new();
        for (_, effects, unknown) in &exits {
            for effect in effects {
                if !places.contains(&effect.place) {
                    places.push(effect.place.clone());
                }
            }
            for event in unknown {
                if !unresolved.contains(event) {
                    unresolved.push(*event);
                }
            }
        }
        places.sort_by_key(|place| format!("{place:?}"));
        unresolved.sort_by_key(|event| event.0);
        let effects = places
            .into_iter()
            .map(|place| {
                let definitely_consumed = exits.iter().all(|(_, effects, _)| {
                    effects.iter().any(|effect| {
                        effect.definitely_consumed && place_covers(&effect.place, &place)
                    })
                });
                let mut consumption_spans = Vec::new();
                for (_, effects, _) in &exits {
                    for effect in effects
                        .iter()
                        .filter(|effect| effect.place.overlaps(&place))
                    {
                        for span in &effect.consumption_spans {
                            if !consumption_spans.contains(span) {
                                consumption_spans.push(*span);
                            }
                        }
                    }
                }
                let (input_storage, referent_projection) =
                    split_referent_effect_place(body, &place);
                ReferentExitEffect {
                    place,
                    input_storage,
                    referent_projection,
                    definitely_consumed,
                    consumption_spans,
                }
            })
            .collect();
        let (reads, unresolved_reads) = self.referent_reads(body);
        ReferentFunctionEffects {
            has_normal_return: !exits.is_empty(),
            effects,
            unresolved,
            reads,
            unresolved_reads,
            entry_reads: Vec::new(),
            restored_from_consumed_entry: Vec::new(),
        }
    }

    /// Map consumed-entry restoration postconditions without transferring
    /// state or proving the callee's write-entry preconditions.
    #[cfg(test)]
    pub fn map_referent_call_restorations(
        &self,
        body: &Body,
        event: FlowNodeId,
        call: NodeId,
        callee_body: &Body,
        restored: &[Place],
    ) -> (Vec<Place>, bool) {
        let summary = ReferentFunctionEffects {
            has_normal_return: true,
            effects: restored
                .iter()
                .map(|place| {
                    let (input_storage, referent_projection) =
                        split_referent_effect_place(callee_body, place);
                    ReferentExitEffect {
                        place: place.clone(),
                        input_storage,
                        referent_projection,
                        definitely_consumed: true,
                        consumption_spans: Vec::new(),
                    }
                })
                .collect(),
            unresolved: Vec::new(),
            reads: Vec::new(),
            unresolved_reads: Vec::new(),
            entry_reads: Vec::new(),
            restored_from_consumed_entry: Vec::new(),
        };
        // The definite flag here requests exact destination substitution,
        // not a consumption effect. Never pass this adapter to move flow.
        let (mapped, unknown) = self.map_referent_call_effects(body, event, call, &summary);
        (
            mapped
                .into_iter()
                .filter(|effect| effect.definitely_consumed)
                .map(|effect| effect.place)
                .collect(),
            unknown,
        )
    }

    /// Entry obligations apply to every possible destination, unlike a
    /// restoration guarantee which needs one exact definite destination.
    #[cfg(test)]
    pub fn map_referent_call_consumed_entry(
        &self,
        body: &Body,
        event: FlowNodeId,
        call: NodeId,
        callee_body: &Body,
        required: &[Place],
    ) -> (Vec<Place>, bool) {
        let reads = required
            .iter()
            .map(|place| {
                let (input_storage, referent_projection) =
                    split_referent_effect_place(callee_body, place);
                ReferentRead {
                    event: self.entry,
                    place: place.clone(),
                    input_storage,
                    referent_projection,
                    span: None,
                }
            })
            .collect::<Vec<_>>();
        let (mapped, unknown) = self.map_referent_call_reads(body, event, call, &reads);
        (mapped.into_iter().map(|read| read.place).collect(), unknown)
    }

    /// Staged call mapping only; does not yet mutate caller ownership state.
    /// Map read identities without transferring ownership or treating these
    /// facts as complete entry requirements.
    #[cfg(test)]
    pub fn map_referent_call_reads(
        &self,
        body: &Body,
        event: FlowNodeId,
        call: NodeId,
        reads: &[ReferentRead],
    ) -> (Vec<ReferentRead>, bool) {
        let origins = self.loan_origins(body);
        self.map_referent_call_reads_with_origins(body, event, call, reads, &origins)
    }

    #[cfg(test)]
    pub fn map_referent_call_reads_with_origins(
        &self,
        body: &Body,
        event: FlowNodeId,
        call: NodeId,
        reads: &[ReferentRead],
        origins: &FlowLoanOrigins,
    ) -> (Vec<ReferentRead>, bool) {
        // Reuse storage/slot substitution, not consumption transfer. The
        // adapter is private and its result is converted back to read facts.
        let summary = ReferentFunctionEffects {
            has_normal_return: true,
            effects: reads
                .iter()
                // Callee-local storage is not an input requirement and must
                // never be substituted with a caller binding of the same ID.
                .filter(|read| {
                    matches!(
                        read.place.root,
                        PlaceRoot::Parameter(_) | PlaceRoot::Global(_)
                    )
                })
                .map(|read| ReferentExitEffect {
                    place: read.place.clone(),
                    input_storage: read.input_storage.clone(),
                    referent_projection: read.referent_projection.clone(),
                    definitely_consumed: false,
                    consumption_spans: vec![read.span],
                })
                .collect(),
            unresolved: Vec::new(),
            reads: Vec::new(),
            unresolved_reads: Vec::new(),
            entry_reads: Vec::new(),
            restored_from_consumed_entry: Vec::new(),
        };
        let (mapped, unknown) =
            self.map_referent_call_effects_with_origins(body, event, call, &summary, origins);
        let reads = mapped
            .into_iter()
            .map(|mapped| ReferentRead {
                event,
                place: mapped.place,
                input_storage: mapped.input_storage,
                referent_projection: mapped.referent_projection,
                span: mapped.consumption_spans.into_iter().next().flatten(),
            })
            .collect();
        (reads, unknown)
    }

    /// Staged outgoing consumption mapping; no state transfer on its own.
    #[cfg(test)]
    pub fn map_referent_call_effects(
        &self,
        body: &Body,
        event: FlowNodeId,
        call: NodeId,
        summary: &ReferentFunctionEffects,
    ) -> (Vec<ReferentExitEffect>, bool) {
        let origins = self.loan_origins(body);
        self.map_referent_call_effects_with_origins(body, event, call, summary, &origins)
    }

    #[cfg(test)]
    pub fn map_referent_call_effects_with_origins(
        &self,
        body: &Body,
        event: FlowNodeId,
        call: NodeId,
        summary: &ReferentFunctionEffects,
        origins: &FlowLoanOrigins,
    ) -> (Vec<ReferentExitEffect>, bool) {
        let NodeKind::Form { children, .. } = &body.nodes[call.0].kind else {
            return (Vec::new(), true);
        };
        let mut unknown = !summary.unresolved.is_empty();
        let mut mapped = Vec::new();
        for effect in &summary.effects {
            let mut places = Vec::new();
            let mut incomplete = false;
            match effect.place.root {
                PlaceRoot::Global(_) => places.push(effect.place.clone()),
                PlaceRoot::Parameter(parameter) => {
                    if let (Some(argument), Some(slot)) =
                        (children.get(parameter.0 + 1), &effect.input_storage)
                    {
                        for origin in origins.value_before(body, self, event, *argument) {
                            if origin.storage.len() != slot.len()
                                || !origin
                                    .storage
                                    .iter()
                                    .zip(slot)
                                    .all(|(held, required)| storage_slot_matches(required, held))
                            {
                                continue;
                            }
                            if origin.lifetime_only {
                                incomplete = true;
                                continue;
                            }
                            let mut place = origin.place.clone();
                            if matches!(place.root, PlaceRoot::Parameter(_)) {
                                if let Some(storage) = origin.parameter_storage {
                                    let mut path = storage;
                                    path.append(&mut place.segments);
                                    place.segments = path;
                                }
                            }
                            place
                                .segments
                                .extend(effect.referent_projection.iter().cloned());
                            if !places.contains(&place) {
                                places.push(place);
                            }
                        }
                    } else {
                        incomplete = true;
                    }
                }
                _ => incomplete = true,
            }
            if places.is_empty() {
                incomplete = true;
            }
            let definite = effect.definitely_consumed && places.len() == 1 && !incomplete;
            unknown |= incomplete;
            for place in places {
                let (input_storage, referent_projection) =
                    split_referent_effect_place(body, &place);
                mapped.push(ReferentExitEffect {
                    place,
                    input_storage,
                    referent_projection,
                    definitely_consumed: definite,
                    consumption_spans: effect.consumption_spans.clone(),
                });
            }
        }
        (mapped, unknown)
    }

    #[cfg(test)]
    pub fn referent_consumptions_with_calls(
        &self,
        body: &Body,
        types: &LinearTypes,
        calls: &[(FlowNodeId, Vec<ReferentExitEffect>, bool)],
    ) -> FlowConsumptions {
        self.referent_consumptions_with_calls_from_entry(body, types, calls, &[])
    }

    #[cfg(test)]
    pub fn referent_consumptions_with_calls_from_entry(
        &self,
        body: &Body,
        types: &LinearTypes,
        calls: &[(FlowNodeId, Vec<ReferentExitEffect>, bool)],
        entry_consumed: &[Place],
    ) -> FlowConsumptions {
        self.referent_consumptions_with_restorations(body, types, calls, &[], entry_consumed)
    }

    /// Transfer exact restoration proofs supplied by staging. Call-entry
    /// preconditions must be validated independently before production use.
    #[cfg(test)]
    pub fn referent_consumptions_with_restorations(
        &self,
        body: &Body,
        types: &LinearTypes,
        calls: &[(FlowNodeId, Vec<ReferentExitEffect>, bool)],
        restorations: &[(FlowNodeId, Vec<Place>)],
        entry_consumed: &[Place],
    ) -> FlowConsumptions {
        let mut calls = calls
            .iter()
            .map(|(event, effects, unresolved)| {
                (
                    *event,
                    CallConsumptionFacts {
                        possible: effects
                            .iter()
                            .map(|effect| (effect.place.clone(), effect.consumption_spans.clone()))
                            .collect(),
                        definite: effects
                            .iter()
                            .filter(|effect| effect.definitely_consumed)
                            .map(|effect| effect.place.clone())
                            .collect(),
                        unresolved: *unresolved,
                        restored: Vec::new(),
                    },
                )
            })
            .collect::<HashMap<FlowNodeId, CallConsumptionFacts>>();
        for (event, restored) in restorations {
            calls
                .entry(*event)
                .or_default()
                .restored
                .extend(restored.iter().cloned());
        }
        let origins = self.loan_origins(body);
        self.consumptions_with_origins_and_calls(
            body,
            types,
            Some(&origins),
            Some(&calls),
            entry_consumed,
        )
    }

    fn consumptions_with_origins(
        &self,
        body: &Body,
        types: &LinearTypes,
        origins: Option<&FlowLoanOrigins>,
    ) -> FlowConsumptions {
        self.consumptions_with_origins_and_calls(body, types, origins, None, &[])
    }

    /// Symbolic entry state for deriving initialization contracts. Seeded
    /// storage has no source consumption span because it is an assumption.
    #[cfg(test)]
    pub fn referent_consumptions_from_entry(
        &self,
        body: &Body,
        types: &LinearTypes,
        consumed: &[Place],
    ) -> FlowConsumptions {
        let origins = self.loan_origins(body);
        self.consumptions_with_origins_and_calls(body, types, Some(&origins), None, consumed)
    }

    /// Direct-read entry requirements under symbolic input initialization.
    /// Whole parameter-referent initialization on every normal return when
    /// those referents start consumed. Write-entry permissions/preconditions
    /// remain separate and are not established by this postcondition.
    #[cfg(test)]
    pub fn referent_restoration_guarantees(
        &self,
        body: &Body,
        types: &LinearTypes,
        calls: &[(FlowNodeId, Vec<ReferentExitEffect>, bool)],
    ) -> Vec<Place> {
        self.referent_restoration_guarantees_with_calls(body, types, calls, &[])
    }

    #[cfg(test)]
    pub fn referent_restoration_guarantees_with_calls(
        &self,
        body: &Body,
        types: &LinearTypes,
        calls: &[(FlowNodeId, Vec<ReferentExitEffect>, bool)],
        restorations: &[(FlowNodeId, Vec<Place>)],
    ) -> Vec<Place> {
        let mut candidates = Vec::new();
        for (index, slots) in body
            .parameter_loan_slots
            .iter()
            .enumerate()
            .take(body.parameter_count)
        {
            for slot in slots {
                let mut place = Place::root(PlaceRoot::Parameter(BindingId(index)));
                place.segments = slot.storage.clone();
                if !candidates.contains(&place) {
                    candidates.push(place);
                }
            }
        }
        let moves = self.referent_consumptions_with_restorations(
            body,
            types,
            calls,
            restorations,
            &candidates,
        );
        let exits = self.referent_exit_effects_from_moves(body, &moves);
        if exits.is_empty() {
            return Vec::new();
        }
        candidates
            .into_iter()
            .filter(|candidate| {
                exits.iter().all(|(_, effects, unresolved)| {
                    unresolved.is_empty()
                        && !effects
                            .iter()
                            .any(|effect| effect.place.overlaps(candidate))
                })
            })
            .collect()
    }

    /// Direct-read entry requirements under symbolic input initialization.
    /// Callee reads/restoration, write preconditions, and validity of local
    /// consumption are separate obligations, not proven by this filter.
    #[cfg(test)]
    pub fn direct_referent_entry_reads(
        &self,
        body: &Body,
        types: &LinearTypes,
    ) -> (Vec<ReferentRead>, Vec<FlowNodeId>) {
        let (reads, unresolved) = self.referent_reads(body);
        (
            self.filter_referent_entry_reads(body, types, reads),
            unresolved,
        )
    }

    #[cfg(test)]
    pub fn filter_referent_entry_reads(
        &self,
        body: &Body,
        types: &LinearTypes,
        reads: Vec<ReferentRead>,
    ) -> Vec<ReferentRead> {
        self.filter_referent_entry_reads_with_calls(body, types, reads, &[])
    }

    #[cfg(test)]
    pub fn filter_referent_entry_reads_with_calls(
        &self,
        body: &Body,
        types: &LinearTypes,
        reads: Vec<ReferentRead>,
        calls: &[(FlowNodeId, Vec<ReferentExitEffect>, bool)],
    ) -> Vec<ReferentRead> {
        self.filter_referent_entry_reads_with_restorations(body, types, reads, calls, &[])
    }

    #[cfg(test)]
    pub fn filter_referent_entry_reads_with_restorations(
        &self,
        body: &Body,
        types: &LinearTypes,
        reads: Vec<ReferentRead>,
        calls: &[(FlowNodeId, Vec<ReferentExitEffect>, bool)],
        restorations: &[(FlowNodeId, Vec<Place>)],
    ) -> Vec<ReferentRead> {
        let mut candidates = Vec::new();
        for read in &reads {
            if matches!(
                read.place.root,
                PlaceRoot::Parameter(_) | PlaceRoot::Global(_)
            ) && !candidates.contains(&read.place)
            {
                candidates.push(read.place.clone());
            }
        }
        let moves = self.referent_consumptions_with_restorations(
            body,
            types,
            calls,
            restorations,
            &candidates,
        );
        let requirements = reads
            .into_iter()
            .filter(|read| {
                candidates.contains(&read.place)
                    && moves.before[read.event.0]
                        .as_ref()
                        .is_some_and(|state| state.keys().any(|place| place.overlaps(&read.place)))
            })
            .collect();
        requirements
    }

    fn consumptions_with_origins_and_calls(
        &self,
        body: &Body,
        types: &LinearTypes,
        origins: Option<&FlowLoanOrigins>,
        calls: Option<&HashMap<FlowNodeId, CallConsumptionFacts>>,
        entry_consumed: &[Place],
    ) -> FlowConsumptions {
        let resolve = |id: FlowNodeId, place: &Place, value: NodeId| {
            let value = match &body.nodes[value.0].kind {
                NodeKind::Form { head, children, .. }
                    if matches!(head.as_str(), "drop" | "forget") && children.len() == 2 =>
                {
                    children[1]
                }
                _ => value,
            };
            let (indirect, inline_borrow) = match &body.nodes[value.0].kind {
                NodeKind::Form { head, children, .. } => {
                    let base = children.get(1).map(|id| &body.nodes[id.0].kind);
                    let inline = matches!(base, Some(NodeKind::Form { head, .. })
                        if matches!(head.as_str(), "borrow" | "borrow-mut"));
                    (
                        head == "deref-set" || reads_through_reference(body, value),
                        inline,
                    )
                }
                _ => (false, false),
            };
            let Some(origins) = origins else {
                return (vec![place.clone()], false);
            };
            let PlaceRoot::Local(binding) = place.root else {
                return (
                    vec![place.clone()],
                    place.segments.contains(&Segment::Dereference) || (indirect && !inline_borrow),
                );
            };
            let referents =
                origins.projected_referents_with_slots(id, binding, &place.segments, true);
            if indirect
                && origins
                    .before(id, binding)
                    .iter()
                    .any(|origin| origin.lifetime_only)
            {
                return (vec![place.clone()], true);
            }
            if !referents.is_empty() {
                (referents, false)
            } else {
                let mut resolved = place.clone();
                // Inline borrows preserve the owned place, but an outer
                // dereference adds a marker. It is not a pointer stored in
                // this binding if its type has no reference indirection.
                let reference_binding = matches!(
                    body.bindings[binding.0].ty,
                    Type::Reference { .. } | Type::PinnedReference { .. }
                );
                if !reference_binding && place.segments == [Segment::Dereference] {
                    resolved.segments.clear();
                }
                let unresolved = (reference_binding && !place.segments.is_empty())
                    || resolved.segments.contains(&Segment::Dereference)
                    || (indirect && !inline_borrow);
                (vec![resolved], unresolved)
            }
        };
        let mut transfer_roots = self
            .nodes
            .iter()
            .filter_map(|node| match node.action {
                FlowAction::Bind { value, .. }
                | FlowAction::Assign { value, .. }
                | FlowAction::Pattern { value, .. } => Some(value),
                FlowAction::Return(value) => value,
                FlowAction::Break { value, .. } => value,
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
                        | "pin-get-payload"
                        | "pin-get-payload-mut"
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
                        | "pin-ptr-borrow"
                        | "pin-ptr-borrow-mut"
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
        let mut consumed_at = vec![HashSet::new(); self.nodes.len()];
        let mut definite_consumed_at = origins.map(|_| vec![HashSet::new(); self.nodes.len()]);
        let mut unresolved = HashSet::new();
        let write_targets = origins.map(|origins| {
            self.nodes
                .iter()
                .enumerate()
                .map(|(index, node)| match &node.action {
                    FlowAction::Assign { place, .. } => vec![place.clone()],
                    FlowAction::Write { value, .. } | FlowAction::Evaluate(value)
                        if matches!(&body.nodes[value.0].kind,
                        NodeKind::Form { head, .. } if head == "deref-set") =>
                    {
                        let NodeKind::Form { children, .. } = &body.nodes[value.0].kind else {
                            unreachable!()
                        };
                        let loans =
                            origins.value_before(body, self, FlowNodeId(index), children[1]);
                        if loans.is_empty()
                            || loans
                                .iter()
                                .any(|loan| !loan.storage.is_empty() || loan.lifetime_only)
                        {
                            unresolved.insert(FlowNodeId(index));
                            Vec::new()
                        } else {
                            let mut places = Vec::new();
                            for loan in loans {
                                let mut place = loan.place;
                                if matches!(place.root, PlaceRoot::Parameter(_)) {
                                    if let Some(mut prefix) = loan.parameter_storage {
                                        prefix.append(&mut place.segments);
                                        place.segments = prefix;
                                    }
                                }
                                if !places.contains(&place) {
                                    places.push(place);
                                }
                            }
                            places
                        }
                    }
                    _ => Vec::new(),
                })
                .collect::<Vec<_>>()
        });
        let targets_for = |id: FlowNodeId| -> &[Place] {
            if let Some(targets) = &write_targets {
                &targets[id.0]
            } else if let FlowAction::Assign { place, .. } = &self.nodes[id.0].action {
                std::slice::from_ref(place)
            } else {
                &[]
            }
        };
        let mut queued = vec![false; self.nodes.len()];
        let mut pending = VecDeque::from([self.entry]);
        before[self.entry.0] = Some(
            entry_consumed
                .iter()
                .map(|place| (place.clone(), vec![None]))
                .collect::<HashMap<Place, Vec<Option<Span>>>>(),
        );
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
                    consumed_at[id.0].insert(place.clone());
                    if let Some(definite) = &mut definite_consumed_at {
                        let (referents, unknown) = resolve(id, place, *value);
                        if unknown {
                            unresolved.insert(id);
                        }
                        if !unknown && referents.len() == 1 {
                            definite[id.0].insert(referents[0].clone());
                        }
                        for referent in referents {
                            let spans = state.entry(referent).or_default();
                            if !spans.contains(&node.span) {
                                spans.push(node.span);
                            }
                        }
                    } else {
                        let spans = state.entry(place.clone()).or_default();
                        if !spans.contains(&node.span) {
                            spans.push(node.span);
                        }
                    }
                }
                FlowAction::Release { place, value }
                    if matches!(place.root, PlaceRoot::Local(_))
                        && release_operand_is_linear(body, *value, types) =>
                {
                    consumed_at[id.0].insert(place.clone());
                    if let Some(definite) = &mut definite_consumed_at {
                        let (referents, unknown) = resolve(id, place, *value);
                        if unknown {
                            unresolved.insert(id);
                        }
                        if !unknown && referents.len() == 1 {
                            definite[id.0].insert(referents[0].clone());
                        }
                        for referent in referents {
                            let spans = state.entry(referent).or_default();
                            if !spans.contains(&node.span) {
                                spans.push(node.span);
                            }
                        }
                    } else {
                        let spans = state.entry(place.clone()).or_default();
                        if !spans.contains(&node.span) {
                            spans.push(node.span);
                        }
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
                FlowAction::ScopeExit(bindings) => {
                    state.retain(|place, _| {
                        !matches!(place.root, PlaceRoot::Local(binding) if bindings.contains(&binding))
                    });
                }
                _ => {}
            }
            if let Some(call) = calls.and_then(|calls| calls.get(&id)) {
                for (place, spans) in &call.possible {
                    let held = state.entry(place.clone()).or_default();
                    for span in spans {
                        if !held.contains(span) {
                            held.push(*span);
                        }
                    }
                }
                if let Some(definite) = &mut definite_consumed_at {
                    definite[id.0].extend(call.definite.iter().cloned());
                }
                if call.unresolved {
                    unresolved.insert(id);
                } else {
                    for restored in &call.restored {
                        if !restored.segments.contains(&Segment::DynamicIndex) {
                            state.retain(|moved, _| !place_covers(restored, moved));
                        }
                    }
                }
            }
            if let [place] = targets_for(id) {
                if !place.segments.contains(&Segment::DynamicIndex) {
                    state.retain(|moved, _| !place_covers(place, moved));
                }
            }
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
            after[id.0] = Some(state);
        }
        let mut definitely_before = vec![None; self.nodes.len()];
        let definite_consumed_at = definite_consumed_at.as_ref().unwrap_or(&consumed_at);
        let mut queued = vec![false; self.nodes.len()];
        let mut pending = VecDeque::from([self.entry]);
        definitely_before[self.entry.0] =
            Some(entry_consumed.iter().cloned().collect::<HashSet<Place>>());
        queued[self.entry.0] = true;
        while let Some(id) = pending.pop_front() {
            queued[id.0] = false;
            let mut state = definitely_before[id.0].as_ref().unwrap().clone();
            state.extend(definite_consumed_at[id.0].iter().cloned());
            match &self.nodes[id.0].action {
                FlowAction::Bind { binding, .. } => {
                    state.retain(|place| place.root != PlaceRoot::Local(*binding));
                }
                FlowAction::Pattern { pattern, .. } => {
                    let mut bindings = HashSet::new();
                    collect_pattern_bindings(body, *pattern, &mut bindings);
                    state.retain(|place| {
                        !matches!(place.root, PlaceRoot::Local(binding) if bindings.contains(&binding))
                    });
                }
                FlowAction::ScopeExit(bindings) => {
                    state.retain(|place| {
                        !matches!(place.root, PlaceRoot::Local(binding) if bindings.contains(&binding))
                    });
                }
                _ => {}
            }
            // A write through one of several possible aliases can restore
            // any one target, so no overlapping definite-consumption proof
            // remains. May facts are killed only for a single known target.
            if calls
                .and_then(|calls| calls.get(&id))
                .is_some_and(|call| call.unresolved)
            {
                state.clear();
            }
            if let Some(call) = calls.and_then(|calls| calls.get(&id)) {
                for restored in &call.restored {
                    state.retain(|moved| !restored.overlaps(moved));
                }
            }
            for place in targets_for(id) {
                if origins.is_some() {
                    state.retain(|moved| !place.overlaps(moved));
                } else if !place.segments.contains(&Segment::DynamicIndex) {
                    state.retain(|moved| !place_covers(place, moved));
                }
            }
            if unresolved.contains(&id)
                && matches!(&self.nodes[id.0].action,
                    FlowAction::Write { value, .. } | FlowAction::Evaluate(value)
                        if matches!(&body.nodes[value.0].kind,
                            NodeKind::Form { head, .. } if head == "deref-set"))
            {
                // An unknown write may restore any consumed target. Retain
                // may facts, but none remains definitely uninitialized.
                state.clear();
            }
            for successor in &self.nodes[id.0].successors {
                let changed = match &mut definitely_before[successor.0] {
                    Some(existing) => {
                        let prior_len = existing.len();
                        existing.retain(|place| state.contains(place));
                        existing.len() != prior_len
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
        unresolved.retain(|id| before[id.0].is_some());
        FlowConsumptions {
            before,
            after,
            at: consumed_at,
            definitely_before,
            unresolved,
        }
    }

    /// Reject use or explicit destruction after a possible linear move on
    /// any reachable predecessor path. Exit obligations remain with the
    /// existing linear checker until the full ownership migration.
    #[cfg(test)]
    pub fn check_linear_consumptions(
        &self,
        body: &Body,
        types: &LinearTypes,
    ) -> Result<(), ReleaseConflict> {
        let moves = self.consumptions(body, types);
        self.check_linear_consumptions_with_moves(body, &moves)
    }

    /// Staged owner and known reference-projection checks after call effects.
    #[cfg(test)]
    pub fn check_referent_call_entry_reads(
        &self,
        body: &Body,
        types: &LinearTypes,
        calls: &[(FlowNodeId, Vec<ReferentExitEffect>, bool)],
        reads: &[ReferentRead],
    ) -> Result<(), ReleaseConflict> {
        self.check_referent_call_entry_reads_from_entry(body, types, calls, &[], reads, &[])
    }

    #[cfg(test)]
    pub fn check_referent_call_entry_reads_from_entry(
        &self,
        body: &Body,
        types: &LinearTypes,
        calls: &[(FlowNodeId, Vec<ReferentExitEffect>, bool)],
        restorations: &[(FlowNodeId, Vec<Place>)],
        reads: &[ReferentRead],
        entry_consumed: &[Place],
    ) -> Result<(), ReleaseConflict> {
        let moves = self.referent_consumptions_with_restorations(
            body,
            types,
            calls,
            restorations,
            entry_consumed,
        );
        for read in reads {
            let Some(state) = moves.before[read.event.0].as_ref() else {
                continue;
            };
            if !state.keys().any(|place| place.overlaps(&read.place)) {
                continue;
            }
            let previous = state
                .iter()
                .filter(|(place, _)| place.overlaps(&read.place))
                .flat_map(|(_, spans)| spans)
                .flatten()
                .min_by_key(|span| (span.source_id, span.start));
            {
                let mut labels = previous
                    .into_iter()
                    .map(|span| (*span, "referent was consumed here".into()))
                    .collect::<Vec<_>>();
                if let Some(span) = read.span {
                    labels.push((
                        span,
                        "callee requires initialized storage for this read".into(),
                    ));
                }
                return Err(ReleaseConflict {
                    message: "call reads a linear referent that may already be consumed".into(),
                    span: self.nodes[read.event.0].span,
                    labels,
                });
            }
        }
        Ok(())
    }

    #[cfg(test)]
    pub fn check_referent_call_consumed_entry(
        &self,
        body: &Body,
        types: &LinearTypes,
        calls: &[(FlowNodeId, Vec<ReferentExitEffect>, bool)],
        restorations: &[(FlowNodeId, Vec<Place>)],
        requirements: &[(FlowNodeId, Vec<Place>, bool)],
    ) -> Result<(), ReleaseConflict> {
        self.check_referent_call_consumed_entry_from_entry(
            body,
            types,
            calls,
            restorations,
            requirements,
            &[],
        )
    }

    #[cfg(test)]
    pub fn infer_referent_call_consumed_entry(
        &self,
        body: &Body,
        types: &LinearTypes,
        calls: &[(FlowNodeId, Vec<ReferentExitEffect>, bool)],
        restorations: &[(FlowNodeId, Vec<Place>)],
        requirements: &[(FlowNodeId, Vec<Place>, bool)],
    ) -> Result<Vec<Place>, ReleaseConflict> {
        let moves =
            self.referent_consumptions_with_restorations(body, types, calls, restorations, &[]);
        let mut inherited = Vec::new();
        for (event, places, unknown) in requirements {
            let Some(state) = moves.definitely_before[event.0].as_ref() else {
                continue;
            };
            let failure = || ReleaseConflict {
                message: "cannot infer a consumed-entry contract for this initializer call".into(),
                span: self.nodes[event.0].span,
                labels: Vec::new(),
            };
            if *unknown {
                return Err(failure());
            }
            for place in places {
                if state.iter().any(|consumed| place_covers(consumed, place)) {
                    continue;
                }
                // Only caller input storage can acquire an entry contract.
                // A live local owner requires actual local consumption.
                if !matches!(place.root, PlaceRoot::Parameter(_)) {
                    return Err(failure());
                }
                if !inherited.contains(place) {
                    inherited.push(place.clone());
                }
            }
        }
        self.check_referent_call_consumed_entry_from_entry(
            body,
            types,
            calls,
            restorations,
            requirements,
            &inherited,
        )?;
        // This validates call consumption preconditions only. Direct body
        // reads, writes, and complete exit contracts remain separate checks.
        Ok(inherited)
    }

    #[cfg(test)]
    pub fn check_referent_call_consumed_entry_from_entry(
        &self,
        body: &Body,
        types: &LinearTypes,
        calls: &[(FlowNodeId, Vec<ReferentExitEffect>, bool)],
        restorations: &[(FlowNodeId, Vec<Place>)],
        requirements: &[(FlowNodeId, Vec<Place>, bool)],
        entry_consumed: &[Place],
    ) -> Result<(), ReleaseConflict> {
        let moves = self.referent_consumptions_with_restorations(
            body,
            types,
            calls,
            restorations,
            entry_consumed,
        );
        for (event, places, unknown) in requirements {
            let Some(state) = moves.definitely_before[event.0].as_ref() else {
                continue;
            };
            if *unknown
                || places.iter().any(|required| {
                    !state
                        .iter()
                        .any(|consumed| place_covers(consumed, required))
                })
            {
                return Err(ReleaseConflict {
                    message:
                        "call requires a definitely consumed linear referent before replacement"
                            .into(),
                    span: self.nodes[event.0].span,
                    labels: Vec::new(),
                });
            }
        }
        Ok(())
    }

    /// Staged owner and known reference-projection checks after call effects.
    #[cfg(test)]
    pub fn check_owner_consumptions_with_calls(
        &self,
        body: &Body,
        types: &LinearTypes,
        calls: &[(FlowNodeId, Vec<ReferentExitEffect>, bool)],
    ) -> Result<(), ReleaseConflict> {
        self.check_owner_consumptions_with_restorations_from_entry(body, types, calls, &[], &[])
    }

    #[cfg(test)]
    pub fn check_owner_consumptions_with_restorations_from_entry(
        &self,
        body: &Body,
        types: &LinearTypes,
        calls: &[(FlowNodeId, Vec<ReferentExitEffect>, bool)],
        restorations: &[(FlowNodeId, Vec<Place>)],
        entry_consumed: &[Place],
    ) -> Result<(), ReleaseConflict> {
        let moves = self.referent_consumptions_with_restorations(
            body,
            types,
            calls,
            restorations,
            entry_consumed,
        );
        // A known outgoing consumption necessarily accesses that storage.
        // This is only a subset of entry requirements: read-only and
        // consume-then-restore callees need independent access summaries.
        for (event, effects, _) in calls {
            let Some(state) = moves.before[event.0].as_ref() else {
                continue;
            };
            if !state
                .keys()
                .any(|place| effects.iter().any(|effect| effect.place.overlaps(place)))
            {
                continue;
            }
            let previous = state
                .iter()
                .filter(|(place, _)| effects.iter().any(|effect| effect.place.overlaps(place)))
                .flat_map(|(_, spans)| spans)
                .flatten()
                .min_by_key(|span| (span.source_id, span.start));
            {
                return Err(ReleaseConflict {
                    message: "call may consume a linear referent that was already consumed".into(),
                    span: self.nodes[event.0].span,
                    labels: previous
                        .into_iter()
                        .map(|span| (*span, "referent was consumed here".into()))
                        .collect(),
                });
            }
        }
        let origins = self.loan_origins(body);
        self.check_linear_consumptions_with_origins(body, &moves, Some(&origins))
    }

    fn check_linear_consumptions_with_moves(
        &self,
        body: &Body,
        moves: &FlowConsumptions,
    ) -> Result<(), ReleaseConflict> {
        self.check_linear_consumptions_with_origins(body, moves, None)
    }

    #[cfg(test)]
    pub fn check_referent_uses_from_entry(
        &self,
        body: &Body,
        types: &LinearTypes,
        entry_consumed: &[Place],
    ) -> Result<(), ReleaseConflict> {
        let moves = self.referent_consumptions_from_entry(body, types, entry_consumed);
        let origins = self.loan_origins(body);
        self.check_linear_consumptions_with_origins(body, &moves, Some(&origins))
    }

    /// Direct-body validation under specified referent entry assumptions.
    /// This does not infer or validate interprocedural entry/exit contracts.
    #[cfg(test)]
    pub fn check_referent_body_from_entry(
        &self,
        body: &Body,
        types: &LinearTypes,
        declarations: &crate::typed_ir::Declarations,
        entry_consumed: &[Place],
    ) -> Result<(), ReleaseConflict> {
        let origins = self.loan_origins(body);
        let moves = self.consumptions_with_origins_and_calls(
            body,
            types,
            Some(&origins),
            None,
            entry_consumed,
        );
        self.check_referent_consumption_permissions_with_moves(body, types, &moves)?;
        self.check_linear_consumptions_with_origins(body, &moves, Some(&origins))?;
        self.check_referent_replacements_with_facts(body, types, declarations, &origins, &moves)
    }

    fn check_linear_consumptions_with_origins(
        &self,
        body: &Body,
        moves: &FlowConsumptions,
        origins: Option<&FlowLoanOrigins>,
    ) -> Result<(), ReleaseConflict> {
        for (index, node) in self.nodes.iter().enumerate() {
            let (place, value) = match &node.action {
                FlowAction::Read {
                    place,
                    value,
                    place_base: false,
                }
                | FlowAction::Release { place, value }
                | FlowAction::Clone { place, value }
                | FlowAction::Borrow { place, value, .. } => (place, *value),
                _ => continue,
            };
            let Some(state) = moves.before[index].as_ref() else {
                continue;
            };
            let value = match &body.nodes[value.0].kind {
                NodeKind::Form { head, children, .. }
                    if matches!(head.as_str(), "forget" | "drop") && children.len() == 2 =>
                {
                    children[1]
                }
                _ => value,
            };
            let resolved = match (origins, &place.root) {
                (Some(origins), PlaceRoot::Local(binding))
                    if (place.segments.contains(&Segment::Dereference)
                        || reads_through_reference(body, value))
                        && !origins
                            .before(FlowNodeId(index), *binding)
                            .iter()
                            .any(|origin| origin.lifetime_only) =>
                {
                    origins.projected_referents_with_slots(
                        FlowNodeId(index),
                        *binding,
                        &place.segments,
                        true,
                    )
                }
                _ => Vec::new(),
            };
            let accessed = if resolved.is_empty() {
                std::slice::from_ref(place)
            } else {
                &resolved
            };
            // Source metadata only supplies labels; it must not decide
            // whether overlapping consumed storage is a use conflict.
            if !state
                .keys()
                .any(|moved| accessed.iter().any(|place| moved.overlaps(place)))
            {
                continue;
            }
            let previous = state
                .iter()
                .filter(|(moved, _)| accessed.iter().any(|place| moved.overlaps(place)))
                .flat_map(|(_, spans)| spans)
                .flatten()
                .min_by_key(|span| (span.source_id, span.start));
            let place_name = display_linear_place(body, place);
            let message = if place.segments.is_empty() {
                format!("linear value '{place_name}' was used more than once")
            } else {
                format!("linear projection '{place_name}' was used more than once")
            };
            return Err(ReleaseConflict {
                message,
                span: node.span,
                labels: previous
                    .into_iter()
                    .map(|span| (*span, "value was consumed here".into()))
                    .collect(),
            });
        }
        Ok(())
    }

    /// Verify every indivisible linear leaf in locals and parameters has a
    /// definite consumption before replacement, lexical cleanup, or return.
    #[cfg(test)]
    pub fn check_linear_exit_obligations(
        &self,
        body: &Body,
        types: &LinearTypes,
        declarations: &crate::typed_ir::Declarations,
    ) -> Result<(), ReleaseConflict> {
        self.check_linear_exit_obligations_with_moves(body, types, declarations, None)
    }

    /// Share the move-flow solution between use checks and exit diagnostics.
    /// Keep individual results so callers retain their diagnostic priority.
    pub fn check_linear_ownership(
        &self,
        body: &Body,
        types: &LinearTypes,
        declarations: &crate::typed_ir::Declarations,
    ) -> [Result<(), ReleaseConflict>; 4] {
        // No move or destruction obligation can arise without a linear
        // binding or expression. References and Copy-only aggregates still
        // undergo the separate borrow checks.
        if !body
            .bindings
            .iter()
            .any(|binding| types.is_linear(&binding.ty))
            && !body
                .nodes
                .iter()
                .any(|node| node.ty.as_ref().is_some_and(|ty| types.is_linear(ty)))
        {
            return [Ok(()), Ok(()), Ok(()), Ok(())];
        }
        let moves = self.consumptions(body, types);
        [
            self.check_linear_releases(body, types),
            self.check_referent_consumption_permissions_with_moves(body, types, &moves)
                .and_then(|_| self.check_linear_consumptions_with_moves(body, &moves)),
            self.check_linear_exit_obligations_with_moves(body, types, declarations, Some(&moves)),
            self.check_linear_projected_replacements(body, types, declarations, &moves),
        ]
    }

    /// Access permissions are independent of referent restoration and call
    /// effects, which remain separate ownership obligations.
    #[cfg(test)]
    pub fn check_referent_consumption_permissions(
        &self,
        body: &Body,
        types: &LinearTypes,
    ) -> Result<(), ReleaseConflict> {
        let moves = self.consumptions(body, types);
        self.check_referent_consumption_permissions_with_moves(body, types, &moves)
    }

    fn check_referent_consumption_permissions_with_moves(
        &self,
        body: &Body,
        types: &LinearTypes,
        moves: &FlowConsumptions,
    ) -> Result<(), ReleaseConflict> {
        let mut origins = None;
        for (index, node) in self.nodes.iter().enumerate() {
            let event = FlowNodeId(index);
            let value = match &node.action {
                FlowAction::Release { value, .. } => *value,
                FlowAction::Read { value, place, .. } if moves.consumes_at(event, place) => *value,
                _ => continue,
            };
            let value = match &body.nodes[value.0].kind {
                NodeKind::Form { head, children, .. }
                    if matches!(head.as_str(), "forget" | "drop") && children.len() == 2 =>
                {
                    children[1]
                }
                _ => value,
            };
            if !body.nodes[value.0]
                .ty
                .as_ref()
                .is_some_and(|ty| types.is_linear(ty))
                || !reads_through_reference(body, value)
            {
                continue;
            }
            let mut operand = value;
            let mut reference = None;
            for _ in 0..128 {
                let NodeKind::Form { children, .. } = &body.nodes[operand.0].kind else {
                    break;
                };
                let Some(source) = children.get(1) else {
                    break;
                };
                if body.nodes[source.0].ty.as_ref().is_some_and(|ty| {
                    matches!(
                        ty,
                        Type::Reference { .. }
                            | Type::PinnedReference { .. }
                            | Type::Slice(_)
                            | Type::MutableSlice(_)
                    )
                }) {
                    reference = Some(*source);
                    break;
                }
                operand = *source;
            }
            let origins = origins.get_or_insert_with(|| self.loan_origins(body));
            let loans = reference.map_or_else(Vec::new, |reference| {
                origins.value_before(body, self, event, reference)
            });
            if loans.is_empty()
                || loans.iter().any(|loan| {
                    !loan.mutable || loan.pinned || loan.lifetime_only || !loan.storage.is_empty()
                })
            {
                return Err(ReleaseConflict {
                    message: if loans.iter().any(|loan| loan.lifetime_only) {
                        "cannot prove storage identity for consuming a linear referent through a lifetime-only anchor"
                    } else {
                        "consuming a linear referent requires a resolved mutable unpinned reference"
                    }.into(),
                    span: node.span,
                    labels: loans
                        .iter()
                        .filter_map(|loan| {
                            loan.span
                                .map(|span| (span, "reference originates here".into()))
                        })
                        .collect(),
                });
            }
        }
        Ok(())
    }

    #[cfg(test)]
    pub fn check_referent_replacements(
        &self,
        body: &Body,
        types: &LinearTypes,
        declarations: &crate::typed_ir::Declarations,
    ) -> Result<(), ReleaseConflict> {
        let origins = self.loan_origins(body);
        let moves = self.consumptions_with_origins(body, types, Some(&origins));
        self.check_referent_replacements_with_facts(body, types, declarations, &origins, &moves)
    }

    #[cfg(test)]
    pub fn check_referent_replacements_with_calls(
        &self,
        body: &Body,
        types: &LinearTypes,
        declarations: &crate::typed_ir::Declarations,
        calls: &[(FlowNodeId, Vec<ReferentExitEffect>, bool)],
    ) -> Result<(), ReleaseConflict> {
        let origins = self.loan_origins(body);
        let moves = self.referent_consumptions_with_calls(body, types, calls);
        self.check_referent_replacements_with_facts(body, types, declarations, &origins, &moves)
    }

    #[cfg(test)]
    fn check_referent_replacements_with_facts(
        &self,
        body: &Body,
        types: &LinearTypes,
        declarations: &crate::typed_ir::Declarations,
        origins: &FlowLoanOrigins,
        moves: &FlowConsumptions,
    ) -> Result<(), ReleaseConflict> {
        self.check_referent_replacements_and_entry_requirements(
            body,
            types,
            declarations,
            origins,
            moves,
            None,
        )
    }

    /// Infer direct-body consumed-entry obligations and validate the body
    /// under them. Calls and complete exit contracts are not handled here.
    #[cfg(test)]
    pub fn infer_direct_referent_consumed_entry(
        &self,
        body: &Body,
        types: &LinearTypes,
        declarations: &crate::typed_ir::Declarations,
    ) -> Result<Vec<Place>, ReleaseConflict> {
        let origins = self.loan_origins(body);
        let moves = self.consumptions_with_origins(body, types, Some(&origins));
        let mut requirements = Vec::new();
        self.check_referent_replacements_and_entry_requirements(
            body,
            types,
            declarations,
            &origins,
            &moves,
            Some(&mut requirements),
        )?;
        self.check_referent_body_from_entry(body, types, declarations, &requirements)?;
        Ok(requirements)
    }

    /// Combined staged inference; owned exits and escaping-reference
    /// initialization remain separate obligations before production use.
    #[cfg(test)]
    pub fn infer_referent_consumed_entry_with_call_facts(
        &self,
        body: &Body,
        types: &LinearTypes,
        declarations: &crate::typed_ir::Declarations,
        calls: &ReferentCallFacts,
    ) -> Result<Vec<Place>, ReleaseConflict> {
        let reachable = self.reachable();
        if let Some(event) = calls
            .unresolved_inputs
            .iter()
            .copied()
            .chain(
                calls
                    .effects
                    .iter()
                    .filter(|(_, _, unknown)| *unknown)
                    .map(|(event, _, _)| *event),
            )
            .find(|event| reachable.contains(event))
        {
            return Err(ReleaseConflict {
                message: "cannot infer a referent entry contract with unresolved call inputs"
                    .into(),
                span: self.nodes[event.0].span,
                labels: Vec::new(),
            });
        }
        let origins = self.loan_origins(body);
        let moves = self.referent_consumptions_with_restorations(
            body,
            types,
            &calls.effects,
            &calls.restorations,
            &[],
        );
        let mut entry = Vec::new();
        self.check_referent_replacements_and_entry_requirements(
            body,
            types,
            declarations,
            &origins,
            &moves,
            Some(&mut entry),
        )?;
        let inherited = self.infer_referent_call_consumed_entry(
            body,
            types,
            &calls.effects,
            &calls.restorations,
            &calls.consumed_inputs,
        )?;
        for place in inherited {
            if !entry.contains(&place) {
                entry.push(place);
            }
        }
        self.check_referent_call_consumed_entry_from_entry(
            body,
            types,
            &calls.effects,
            &calls.restorations,
            &calls.consumed_inputs,
            &entry,
        )?;
        self.check_owner_consumptions_with_restorations_from_entry(
            body,
            types,
            &calls.effects,
            &calls.restorations,
            &entry,
        )?;
        self.check_referent_call_entry_reads_from_entry(
            body,
            types,
            &calls.effects,
            &calls.restorations,
            &calls.read_inputs,
            &entry,
        )?;
        let seeded = self.referent_consumptions_with_restorations(
            body,
            types,
            &calls.effects,
            &calls.restorations,
            &entry,
        );
        self.check_referent_consumption_permissions_with_moves(body, types, &seeded)?;
        self.check_referent_replacements_with_facts(body, types, declarations, &origins, &seeded)?;
        Ok(entry)
    }

    #[cfg(test)]
    fn check_referent_replacements_and_entry_requirements(
        &self,
        body: &Body,
        types: &LinearTypes,
        declarations: &crate::typed_ir::Declarations,
        origins: &FlowLoanOrigins,
        moves: &FlowConsumptions,
        mut entry_requirements: Option<&mut Vec<Place>>,
    ) -> Result<(), ReleaseConflict> {
        for (index, node) in self.nodes.iter().enumerate() {
            let value = match node.action {
                FlowAction::Write { value, .. } | FlowAction::Evaluate(value) => value,
                _ => continue,
            };
            let NodeKind::Form { head, children, .. } = &body.nodes[value.0].kind else {
                continue;
            };
            if head != "deref-set" || children.len() != 3 {
                continue;
            }
            let Some(ty) = &body.nodes[children[2].0].ty else {
                continue;
            };
            let paths = types.linear_obligation_paths(ty);
            if paths.is_empty() || moves.definitely_before[index].is_none() {
                continue;
            }
            let event = FlowNodeId(index);
            let targets = origins.value_before(body, self, event, children[1]);
            let failure = |message: &str| ReleaseConflict {
                message: message.into(),
                span: node.span,
                labels: targets
                    .iter()
                    .filter_map(|origin| {
                        origin
                            .span
                            .map(|span| (span, "target reference originates here".into()))
                    })
                    .collect(),
            };
            if targets.is_empty() || moves.unresolved.contains(&event) {
                return Err(failure("cannot prove linear referent consumption before replacement: unresolved target"));
            }
            for target in targets.iter() {
                if !target.mutable
                    || target.pinned
                    || target.lifetime_only
                    || !target.storage.is_empty()
                {
                    return Err(failure(
                        "cannot prove permission to replace this linear referent",
                    ));
                }
                let mut destination = target.place.clone();
                if matches!(destination.root, PlaceRoot::Parameter(_)) {
                    if let Some(slot) = &target.parameter_storage {
                        let mut prefix = slot.clone();
                        prefix.append(&mut destination.segments);
                        destination.segments = prefix;
                    }
                }
                for path in &paths {
                    let Some(projection) =
                        linear_obligation_place(declarations, BindingId(0), ty, path)
                    else {
                        return Err(failure(
                            "cannot resolve linear referent replacement obligation",
                        ));
                    };
                    let mut leaf = destination.clone();
                    leaf.segments.extend(projection.segments);
                    if !moves.definitely_consumed_before(event, &leaf) {
                        if matches!(leaf.root, PlaceRoot::Parameter(_)) {
                            if let Some(requirements) = entry_requirements.as_deref_mut() {
                                if !requirements.contains(&leaf) {
                                    requirements.push(leaf);
                                }
                                continue;
                            }
                        }
                        return Err(failure("reference write would destroy a live linear referent; consume it explicitly first"));
                    }
                }
            }
        }
        Ok(())
    }

    fn check_linear_projected_replacements(
        &self,
        body: &Body,
        types: &LinearTypes,
        declarations: &crate::typed_ir::Declarations,
        moves: &FlowConsumptions,
    ) -> Result<(), ReleaseConflict> {
        for (index, node) in self.nodes.iter().enumerate() {
            let FlowAction::Assign { place, value } = &node.action else {
                continue;
            };
            let PlaceRoot::Local(binding) = place.root else {
                continue;
            };
            if place.segments.is_empty() {
                continue;
            }
            let Some(state) = moves.definitely_before[index].as_ref() else {
                continue;
            };
            let Some(ty) = body.nodes[value.0].ty.as_ref() else {
                continue;
            };
            for path in types.linear_obligation_paths(ty) {
                let Some(mut leaf) = linear_obligation_place(declarations, binding, ty, &path)
                else {
                    continue;
                };
                let mut segments = place.segments.clone();
                segments.append(&mut leaf.segments);
                leaf.segments = segments;
                let consumed = !leaf.segments.contains(&Segment::DynamicIndex)
                    && state.iter().any(|prior| {
                        !prior.segments.contains(&Segment::DynamicIndex)
                            && place_covers(prior, &leaf)
                    });
                if !consumed {
                    let name = display_linear_place(body, place);
                    return Err(ReleaseConflict {
                        message: format!(
                            "assignment would destroy live linear projection '{name}'; consume it explicitly first"
                        ),
                        span: node.span,
                        labels: body.bindings[binding.0].span.into_iter().map(|span| {
                            (span, "owner was declared here".into())
                        }).collect(),
                    });
                }
            }
        }
        Ok(())
    }

    fn check_linear_exit_obligations_with_moves(
        &self,
        body: &Body,
        types: &LinearTypes,
        declarations: &crate::typed_ir::Declarations,
        moves: Option<&FlowConsumptions>,
    ) -> Result<(), ReleaseConflict> {
        let obligations = body
            .bindings
            .iter()
            .enumerate()
            .flat_map(|(index, binding)| {
                let binding_id = BindingId(index);
                types
                    .linear_obligation_paths(&binding.ty)
                    .into_iter()
                    .filter_map(move |path| {
                        linear_obligation_place(declarations, binding_id, &binding.ty, &path)
                            .map(|place| (binding_id, binding.name.as_str(), place))
                    })
            })
            .collect::<Vec<_>>();
        if obligations.is_empty() {
            return Ok(());
        }
        let obligation_places = obligations
            .iter()
            .map(|(_, _, place)| place.clone())
            .collect::<HashSet<_>>();
        let (definite_before, _definite_after) =
            self.obligation_consumptions(body, types, &obligation_places);
        let computed_moves;
        let possible = match moves {
            Some(moves) => moves,
            None => {
                computed_moves = self.consumptions(body, types);
                &computed_moves
            }
        };
        let active = self.active_bindings_before(body);
        for (index, node) in self.nodes.iter().enumerate() {
            if definite_before[index].is_none() {
                continue;
            }
            let leaving = match &node.action {
                FlowAction::Assign { place, .. } if place.segments.is_empty() => {
                    let PlaceRoot::Local(binding) = place.root else {
                        continue;
                    };
                    HashSet::from([binding])
                }
                FlowAction::Return(_) => active[index]
                    .as_ref()
                    .into_iter()
                    .flatten()
                    .copied()
                    .collect::<HashSet<_>>(),
                FlowAction::ScopeExit(bindings) => bindings
                    .iter()
                    .copied()
                    .filter(|binding| {
                        active[index]
                            .as_ref()
                            .is_some_and(|active| active.contains(binding))
                    })
                    .collect(),
                _ => continue,
            };
            for (binding, name, place) in &obligations {
                if !leaving.contains(binding) {
                    continue;
                }
                let consumed = definite_before[index]
                    .as_ref()
                    .is_some_and(|state| state.contains(place));
                if !consumed {
                    let labels: Vec<(Span, String)> = possible.before[index]
                        .as_ref()
                        .into_iter()
                        .flat_map(|state| state.iter())
                        .filter(|(moved, _)| place_covers(moved, place))
                        .flat_map(|(_, spans)| spans.iter().flatten().copied())
                        .min_by_key(|span| (span.source_id, span.start))
                        .map(|span| (span, "value was consumed on only some paths".into()))
                        .into_iter()
                        .collect();
                    let binding_span = body.bindings[binding.0].span.or_else(|| {
                        self.nodes
                            .iter()
                            .find_map(|declaration| match declaration.action {
                                FlowAction::Bind {
                                    binding: declared, ..
                                } if declared == *binding => declaration.span,
                                _ => None,
                            })
                    });
                    let message = match &node.action {
                        FlowAction::Assign { .. } => format!(
                            "assignment would destroy live linear value '{name}'; consume it explicitly first"
                        ),
                        FlowAction::ScopeExit(_) => {
                            format!("linear value '{name}' must be consumed before leaving its scope")
                        }
                        FlowAction::Return(_) if !labels.is_empty() => format!(
                            "linear value '{name}' must be consumed consistently on every control-flow path"
                        ),
                        FlowAction::Return(_) => {
                            format!("linear value '{name}' must be consumed before returning")
                        }
                        _ => unreachable!(),
                    };
                    return Err(ReleaseConflict {
                        message,
                        span: if matches!(node.action, FlowAction::Assign { .. }) {
                            node.span
                        } else {
                            binding_span.or(node.span)
                        },
                        labels,
                    });
                }
            }
        }
        Ok(())
    }

    fn obligation_consumptions(
        &self,
        body: &Body,
        types: &LinearTypes,
        obligations: &HashSet<Place>,
    ) -> (Vec<Option<HashSet<Place>>>, Vec<Option<HashSet<Place>>>) {
        let mut before = vec![None; self.nodes.len()];
        let mut after = vec![None; self.nodes.len()];
        let mut queued = vec![false; self.nodes.len()];
        let mut pending = VecDeque::from([self.entry]);
        before[self.entry.0] = Some(HashSet::new());
        queued[self.entry.0] = true;
        while let Some(id) = pending.pop_front() {
            queued[id.0] = false;
            let mut state = before[id.0].as_ref().unwrap().clone();
            let node = &self.nodes[id.0];
            let transfer = match &node.action {
                FlowAction::Read {
                    value,
                    place,
                    place_base: false,
                } if matches!(place.root, PlaceRoot::Local(_))
                    && body.nodes[value.0]
                        .ty
                        .as_ref()
                        .is_some_and(|ty| types.is_linear(ty)) =>
                {
                    Some(place)
                }
                FlowAction::Release { place, value }
                    if matches!(place.root, PlaceRoot::Local(_))
                        && release_operand_is_linear(body, *value, types) =>
                {
                    Some(place)
                }
                _ => None,
            };
            if let Some(transfer) = transfer {
                state.extend(
                    obligations
                        .iter()
                        .filter(|leaf| place_covers(transfer, leaf))
                        .cloned(),
                );
            }
            if let FlowAction::Pattern { value, .. } = &node.action {
                if let Some(source) = Place::from_expression(body, *value) {
                    state.extend(
                        obligations
                            .iter()
                            .filter(|leaf| {
                                place_covers(&source, leaf)
                                    && leaf.segments[source.segments.len()..]
                                        .iter()
                                        .any(|segment| matches!(segment, Segment::Payload(_, _)))
                            })
                            .cloned(),
                    );
                }
            }
            match &node.action {
                FlowAction::Bind { binding, .. } => {
                    state.retain(|place| place.root != PlaceRoot::Local(*binding));
                }
                FlowAction::Pattern { pattern, .. } => {
                    let mut bindings = HashSet::new();
                    collect_pattern_bindings(body, *pattern, &mut bindings);
                    state.retain(|place| {
                        !matches!(place.root, PlaceRoot::Local(binding) if bindings.contains(&binding))
                    });
                }
                FlowAction::Assign { place, .. } => {
                    state.retain(|leaf| !place_covers(place, leaf) && !place_covers(leaf, place));
                }
                FlowAction::ScopeExit(bindings) => {
                    state.retain(|place| {
                        !matches!(place.root, PlaceRoot::Local(binding) if bindings.contains(&binding))
                    });
                }
                _ => {}
            }
            after[id.0] = Some(state.clone());
            for successor in &node.successors {
                let changed = match &mut before[successor.0] {
                    Some(existing) => {
                        let intersection = existing
                            .intersection(&state)
                            .cloned()
                            .collect::<HashSet<_>>();
                        if intersection != *existing {
                            *existing = intersection;
                            true
                        } else {
                            false
                        }
                    }
                    slot @ None => {
                        *slot = Some(state.clone());
                        true
                    }
                };
                if changed && !queued[successor.0] {
                    queued[successor.0] = true;
                    pending.push_back(*successor);
                }
            }
        }
        (before, after)
    }

    fn active_bindings_before(&self, body: &Body) -> Vec<Option<HashSet<BindingId>>> {
        let mut before: Vec<Option<HashSet<BindingId>>> = vec![None; self.nodes.len()];
        let mut queued = vec![false; self.nodes.len()];
        let mut pending = VecDeque::from([self.entry]);
        before[self.entry.0] = Some((0..body.parameter_count).map(BindingId).collect());
        queued[self.entry.0] = true;
        while let Some(id) = pending.pop_front() {
            queued[id.0] = false;
            let mut state = before[id.0].as_ref().unwrap().clone();
            match &self.nodes[id.0].action {
                FlowAction::Bind { binding, .. } => {
                    state.insert(*binding);
                }
                FlowAction::Pattern { pattern, .. } => {
                    collect_pattern_bindings(body, *pattern, &mut state);
                }
                FlowAction::ScopeExit(bindings) => {
                    for binding in bindings {
                        state.remove(binding);
                    }
                }
                _ => {}
            }
            for successor in &self.nodes[id.0].successors {
                let changed = match &mut before[successor.0] {
                    Some(existing) => {
                        let old_len = existing.len();
                        existing.extend(state.iter().copied());
                        existing.len() != old_len
                    }
                    slot @ None => {
                        *slot = Some(state.clone());
                        true
                    }
                };
                if changed && !queued[successor.0] {
                    queued[successor.0] = true;
                    pending.push_back(*successor);
                }
            }
        }
        before
    }

    /// Bindings guaranteed to be in lexical scope on every path reaching each
    /// node. Unlike `active_bindings_before`, this is a must-analysis and is
    /// suitable for proving a borrowed local outlives a value transfer.
    pub fn definitely_active_bindings_before(
        &self,
        body: &Body,
    ) -> Vec<Option<HashSet<BindingId>>> {
        let mut before: Vec<Option<HashSet<BindingId>>> = vec![None; self.nodes.len()];
        let mut after: Vec<Option<HashSet<BindingId>>> = vec![None; self.nodes.len()];
        let mut pending = VecDeque::from([self.entry]);
        let mut queued = vec![false; self.nodes.len()];
        before[self.entry.0] = Some((0..body.parameter_count).map(BindingId).collect());
        queued[self.entry.0] = true;
        while let Some(id) = pending.pop_front() {
            queued[id.0] = false;
            let mut state = before[id.0].as_ref().unwrap().clone();
            match &self.nodes[id.0].action {
                FlowAction::Bind { binding, .. } => {
                    state.insert(*binding);
                }
                FlowAction::Pattern { pattern, .. } => {
                    collect_pattern_bindings(body, *pattern, &mut state);
                }
                FlowAction::ScopeExit(bindings) => {
                    for binding in bindings {
                        state.remove(binding);
                    }
                }
                _ => {}
            }
            after[id.0] = Some(state.clone());
            for successor in &self.nodes[id.0].successors {
                let changed = match &mut before[successor.0] {
                    Some(existing) => {
                        let intersection = existing
                            .intersection(&state)
                            .copied()
                            .collect::<HashSet<_>>();
                        if intersection != *existing {
                            *existing = intersection;
                            true
                        } else {
                            false
                        }
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
        before
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
                PlaceRoot::Parameter(binding) => body.bindings[binding.0].name.as_str(),
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
                    let borrow_form = matches!(
                        head.as_str(),
                        "borrow" | "borrow-mut" | "pin-borrow" | "pin-borrow-mut"
                    ) && matches!(children.len(), 2 | 3)
                        && matches!(head.as_str(), "borrow-mut" | "pin-borrow-mut") == *mutable;
                    let pinned_payload_form =
                        matches!(head.as_str(), "pin-get-payload" | "pin-get-payload-mut")
                            && children.len() == 4
                            && (head == "pin-get-payload-mut") == *mutable;
                    let slice_form = matches!(head.as_str(), "slice-idx" | "slice-mut-idx")
                        && children.len() == 3
                        && (head == "slice-mut-idx") == *mutable;
                    let expected_place = if slice_form || pinned_payload_form {
                        Place::from_expression(body, *value)
                    } else {
                        Place::from_expression(body, children[1])
                    };
                    if !(borrow_form || slice_form || pinned_payload_form)
                        || expected_place.as_ref() != Some(place)
                    {
                        return Err(format!("typed flow borrow {value:?} has invalid metadata"));
                    }
                    if let PlaceRoot::Local(binding) = place.root {
                        if binding.0 >= body.bindings.len() {
                            return Err(format!("typed flow borrows invalid local {binding:?}"));
                        }
                    }
                    if let PlaceRoot::Parameter(binding) = place.root {
                        if binding.0 >= body.parameter_count {
                            return Err(format!(
                                "typed flow borrows invalid parameter {binding:?}"
                            ));
                        }
                    }
                }
                FlowAction::BorrowScopeEnd { scope } => {
                    let Some(NodeKind::Form { head, children, .. }) =
                        body.nodes.get(scope.0).map(|node| &node.kind)
                    else {
                        return Err(format!("typed flow ends invalid borrow scope {scope:?}"));
                    };
                    if !matches!(head.as_str(), "borrow" | "borrow-mut") || children.len() != 3 {
                        return Err(format!("typed flow ends invalid borrow scope {scope:?}"));
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
                FlowAction::Assign {
                    place:
                        Place {
                            root: PlaceRoot::Parameter(binding),
                            ..
                        },
                    ..
                } => {
                    return Err(format!(
                        "typed flow cannot assign to abstract parameter referent {binding:?}"
                    ));
                }
                FlowAction::Write { place, value } => {
                    let Some(NodeKind::Form { head, children, .. }) =
                        body.nodes.get(value.0).map(|node| &node.kind)
                    else {
                        return Err(format!("typed flow writes invalid node {value:?}"));
                    };
                    let valid = match head.as_str() {
                        "deref-set" | "pin-write" => {
                            children.len() == 3
                                && Place::from_dereference_write(body, children[1]).as_ref()
                                    == Some(place)
                        }
                        "pin-set-field" => {
                            children.len() == 4
                                && Place::from_pin_field_write(body, children[1], children[2])
                                    .as_ref()
                                    == Some(place)
                        }
                        _ => false,
                    };
                    if !valid {
                        return Err(format!("typed flow write {value:?} has invalid metadata"));
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
                FlowAction::Break { value, result } => {
                    if value
                        .is_some_and(|id| body.nodes.get(id.0).is_none_or(|node| node.ty.is_none()))
                    {
                        return Err(format!(
                            "typed flow break {index} references an invalid value"
                        ));
                    }
                    if result.is_some_and(|id| {
                        body.nodes
                            .get(id.0)
                            .is_none_or(|node| !matches!(node.kind, NodeKind::Loop(_)))
                    }) {
                        return Err(format!(
                            "typed flow break {index} references an invalid loop result"
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
                    if !matches!(
                        self.nodes[successor.0].action,
                        FlowAction::ScopeExit(_) | FlowAction::BorrowScopeEnd { .. }
                    ) {
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
            // Compute one word at a time in the existing snapshots. Successor
            // reads must precede the update, including for a self-loop.
            let mut changed = false;
            for word in 0..words {
                let next_after = self.nodes[id.0]
                    .successors
                    .iter()
                    .fold(0, |bits, successor| bits | before[successor.0][word]);
                let next_before = (next_after & !defs[id.0][word]) | uses[id.0][word];
                changed |= before[id.0][word] != next_before || after[id.0][word] != next_after;
                before[id.0][word] = next_before;
                after[id.0][word] = next_after;
            }
            if changed {
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

#[cfg(test)]
fn split_referent_effect_place(body: &Body, place: &Place) -> (Option<Vec<Segment>>, Vec<Segment>) {
    let PlaceRoot::Parameter(binding) = place.root else {
        return (None, place.segments.clone());
    };
    let slot = body
        .parameter_loan_slots
        .get(binding.0)
        .into_iter()
        .flatten()
        .filter(|slot| place.segments.starts_with(&slot.storage))
        .max_by_key(|slot| slot.storage.len());
    match slot {
        Some(slot) => (
            Some(slot.storage.clone()),
            place.segments[slot.storage.len()..].to_vec(),
        ),
        None => (None, place.segments.clone()),
    }
}

fn linear_obligation_place(
    declarations: &crate::typed_ir::Declarations,
    binding: BindingId,
    ty: &Type,
    path: &[crate::linearcheck::LinearProjection],
) -> Option<Place> {
    let mut place = Place::root(PlaceRoot::Local(binding));
    let mut current = ty.clone();
    for projection in path {
        current = crate::typed_ir::resolve_type(&current, &declarations.aliases).ok()?;
        match projection {
            crate::linearcheck::LinearProjection::Field(name) => {
                let field = declarations.field_id(&current, name)?;
                current = declarations.field(field).ty.clone();
                place.segments.push(Segment::Field(field));
            }
            crate::linearcheck::LinearProjection::Tuple(index) => {
                let Type::Tuple(items) = current else {
                    return None;
                };
                current = items.get(*index)?.clone();
                place.segments.push(Segment::Tuple(*index));
            }
            crate::linearcheck::LinearProjection::Payload(variant, index) => {
                let id = declarations.variant_id(&current, variant)?;
                current = declarations.variant(id).fields.get(*index)?.clone();
                place.segments.push(Segment::Payload(id, *index));
            }
            crate::linearcheck::LinearProjection::Index(index) => {
                let Type::Array(element, count) = current else {
                    return None;
                };
                if *index >= count {
                    return None;
                }
                current = *element;
                place.segments.push(Segment::Index(*index as u128));
            }
        }
    }
    Some(place)
}

fn place_covers(ancestor: &Place, descendant: &Place) -> bool {
    ancestor.root == descendant.root && descendant.segments.starts_with(&ancestor.segments)
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

fn apply_parameter_loan_summary(
    mut origin: LoanOrigin,
    summary: &crate::typed_body::ParameterLoanSummary,
) -> Option<LoanOrigin> {
    if origin.storage.len() < summary.input_storage.len()
        || !summary
            .input_storage
            .iter()
            .zip(&origin.storage)
            .all(|(expected, actual)| storage_slot_matches(expected, actual))
    {
        return None;
    }
    origin.storage.drain(..summary.input_storage.len());
    let mut storage = summary.storage.clone();
    storage.extend(origin.storage);
    origin.storage = storage;
    origin.mutable = summary.mutable;
    origin.pinned = summary.pinned;
    origin.lifetime_only |= summary.lifetime_only;
    origin
        .place
        .segments
        .extend(summary.referent_projection.iter().cloned());
    Some(origin)
}

fn global_summary_origin(summary: &crate::typed_body::ParameterLoanSummary) -> Option<LoanOrigin> {
    Some(LoanOrigin {
        place: Place {
            root: PlaceRoot::Global(summary.global?),
            segments: summary.referent_projection.clone(),
        },
        mutable: summary.mutable,
        pinned: summary.pinned,
        lifetime_only: summary.lifetime_only,
        span: None,
        borrowed_from: None,
        storage: summary.storage.clone(),
        parameter_storage: None,
    })
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
    extend_projected_origins(held, path, incoming);
}

fn extend_projected_origins(
    held: &mut Vec<LoanOrigin>,
    path: &[Segment],
    incoming: Vec<LoanOrigin>,
) {
    for mut origin in incoming {
        let mut storage = path.to_vec();
        storage.extend(origin.storage);
        origin.storage = storage;
        if !held.contains(&origin) {
            held.push(origin);
        }
    }
}

fn reference_binding(body: &Body, id: NodeId) -> Option<BindingId> {
    let PlaceRoot::Local(binding) = Place::from_expression(body, id)?.root else {
        return None;
    };
    matches!(
        body.bindings[binding.0].ty,
        Type::Reference { .. }
            | Type::PinnedReference { .. }
            | Type::Slice(_)
            | Type::MutableSlice(_)
    )
    .then_some(binding)
}

fn value_loan_origins(body: &Body, id: NodeId, state: &LoanState) -> Vec<LoanOrigin> {
    let node = &body.nodes[id.0];
    match &node.kind {
        NodeKind::Symbol {
            binding: Some(binding),
            ..
        } => state[binding.0].clone(),
        NodeKind::Form { head, children, .. }
            if matches!(
                head.as_str(),
                "borrow" | "borrow-mut" | "pin-borrow" | "pin-borrow-mut"
            ) && children.len() == 2 =>
        {
            Place::from_expression(body, children[1]).map_or_else(Vec::new, |place| {
                let borrowed_from = match &place.root {
                    PlaceRoot::Local(binding)
                        if matches!(
                            body.bindings[binding.0].ty,
                            Type::Reference { .. }
                                | Type::PinnedReference { .. }
                                | Type::Slice(_)
                                | Type::MutableSlice(_)
                        ) =>
                    {
                        Some(*binding)
                    }
                    _ => None,
                };
                let places = reborrow_source_origins(&place, state, &mut HashSet::new());
                places
                    .into_iter()
                    .map(|mut origin| {
                        origin.borrowed_from = borrowed_from;
                        origin.mutable = matches!(head.as_str(), "borrow-mut" | "pin-borrow-mut");
                        origin.pinned |= matches!(head.as_str(), "pin-borrow" | "pin-borrow-mut");
                        origin.span = node.span;
                        origin
                    })
                    .collect()
            })
        }
        NodeKind::Form { head, children, .. }
            if matches!(
                head.as_str(),
                "ptr-borrow" | "ptr-borrow-mut" | "pin-ptr-borrow" | "pin-ptr-borrow-mut"
            ) && children.len() == 3 =>
        {
            let mut origins = value_loan_origins(body, children[1], state);
            for origin in &mut origins {
                origin.lifetime_only = true;
            }
            if matches!(head.as_str(), "pin-ptr-borrow" | "pin-ptr-borrow-mut") {
                // The pinned type describes the raw pointer's referent, while
                // this tracked place is only the lifetime anchor. Do not treat
                // the anchor value itself as the pointer's pinned pointee.
                for origin in &mut origins {
                    origin.pinned = false;
                }
            }
            origins
        }
        NodeKind::Form {
            children,
            callee: Some(callee),
            ..
        } => {
            if let Some(summary) = body.call_return_origins.get(callee) {
                let mut result = Vec::new();
                for source in summary {
                    if let Some(origin) = global_summary_origin(source) {
                        merge_loan_origins(&mut result, &[origin]);
                        continue;
                    }
                    let Some(argument) = children.get(source.parameter + 1) else {
                        continue;
                    };
                    for origin in value_loan_origins(body, *argument, state) {
                        if let Some(origin) = apply_parameter_loan_summary(origin, source) {
                            merge_loan_origins(&mut result, &[origin]);
                        }
                    }
                }
                result
            } else if matches!(
                node.ty,
                Some(
                    Type::Reference { .. }
                        | Type::PinnedReference { .. }
                        | Type::Slice(_)
                        | Type::MutableSlice(_)
                )
            ) {
                let mut origins = Vec::new();
                for argument in children.iter().skip(1) {
                    for mut origin in value_loan_origins(body, *argument, state) {
                        // External/unsummarized reference-returning functions
                        // retain the conservative argument-based behavior.
                        origin.storage.clear();
                        merge_loan_origins(&mut origins, &[origin]);
                    }
                }
                origins
            } else {
                Vec::new()
            }
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
            let mut origins = children
                .get(1)
                .map(|source| value_loan_origins(body, *source, state))
                .unwrap_or_default();
            let borrowed_from = children
                .get(1)
                .and_then(|source| reference_binding(body, *source));
            for origin in &mut origins {
                if borrowed_from.is_some() {
                    origin.borrowed_from = borrowed_from;
                }
            }
            origins
        }
        NodeKind::Form { head, children, .. }
            if head == "slice-mut-split" && children.len() == 3 =>
        {
            let source = value_loan_origins(body, children[1], state);
            let mut origins = Vec::with_capacity(source.len() * 2);
            let borrowed_from = reference_binding(body, children[1]);
            for half in 0..2 {
                for origin in &source {
                    let mut origin = origin.clone();
                    origin.borrowed_from = borrowed_from;
                    origin.storage.insert(0, Segment::SliceHalf(half));
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
        NodeKind::Form { head, .. }
            if matches!(head.as_str(), "pin-get-payload" | "pin-get-payload-mut") =>
        {
            let Some(place) = Place::from_expression(body, id) else {
                return Vec::new();
            };
            let borrowed_from = match &place.root {
                PlaceRoot::Local(binding)
                    if matches!(
                        body.bindings[binding.0].ty,
                        Type::Reference { .. }
                            | Type::PinnedReference { .. }
                            | Type::Slice(_)
                            | Type::MutableSlice(_)
                    ) =>
                {
                    Some(*binding)
                }
                _ => None,
            };
            reborrow_source_origins(&place, state, &mut HashSet::new())
                .into_iter()
                .map(|mut origin| {
                    origin.borrowed_from = borrowed_from;
                    origin.mutable =
                        matches!(node.ty, Some(Type::PinnedReference { mutable: true, .. }));
                    origin.pinned = true;
                    origin.span = node.span;
                    origin
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

fn collect_result_alternatives(body: &Body, id: NodeId, output: &mut Vec<NodeId>) {
    match &body.nodes[id.0].kind {
        NodeKind::If {
            then_value,
            else_value,
            ..
        } => {
            collect_result_alternatives(body, *then_value, output);
            if let Some(value) = else_value {
                collect_result_alternatives(body, *value, output);
            }
        }
        NodeKind::Match { arms, .. } => {
            for arm in arms {
                if let NodeKind::MatchArm { values, .. } = &body.nodes[arm.0].kind {
                    if let Some(value) = values.last() {
                        collect_result_alternatives(body, *value, output);
                    }
                }
            }
        }
        NodeKind::Labeled(_, expression) => {
            collect_result_alternatives(body, *expression, output);
        }
        NodeKind::Block(instructions) => {
            if let Some(Control::Evaluate(value)) =
                instructions.last().map(|instruction| &instruction.control)
            {
                collect_result_alternatives(body, *value, output);
            }
        }
        _ => output.push(id),
    }
}

fn flow_action_has_value(action: &FlowAction, value: NodeId) -> bool {
    matches!(
        action,
        FlowAction::Evaluate(id) if *id == value
    ) || matches!(
        action,
        FlowAction::Read { value: id, .. }
            | FlowAction::Borrow { value: id, .. }
            | FlowAction::Clone { value: id, .. }
            | FlowAction::Release { value: id, .. }
            if *id == value
    )
}

fn value_projection(body: &Body, value: NodeId) -> Option<Segment> {
    let NodeKind::Form { head, children, .. } = &body.nodes[value.0].kind else {
        return None;
    };
    match head.as_str() {
        "get" => match &body.nodes[children.get(2)?.0].kind {
            NodeKind::Declaration(DeclarationId::Field(field)) => Some(Segment::Field(*field)),
            NodeKind::Literal(crate::Expr::Integer(index)) => {
                usize::try_from(*index).ok().map(Segment::Tuple)
            }
            _ => None,
        },
        "get-payload" => {
            let NodeKind::Declaration(DeclarationId::Variant(variant)) =
                body.nodes[children.get(2)?.0].kind
            else {
                return None;
            };
            let NodeKind::Literal(crate::Expr::Integer(index)) =
                &body.nodes[children.get(3)?.0].kind
            else {
                return None;
            };
            Some(Segment::Payload(variant, usize::try_from(*index).ok()?))
        }
        "index" => match &body.nodes[children.get(2)?.0].kind {
            NodeKind::Literal(crate::Expr::Integer(index)) => {
                u128::try_from(*index).ok().map(Segment::Index)
            }
            _ => Some(Segment::DynamicIndex),
        },
        _ => None,
    }
}

fn value_loan_origins_at_events(
    body: &Body,
    flow: &FlowGraph,
    before: &[Option<LoanState>],
    value: NodeId,
    state: &LoanState,
) -> Vec<LoanOrigin> {
    if matches!(body.nodes[value.0].kind, NodeKind::Loop(_)) {
        let mut result = Vec::new();
        for (index, event) in flow.nodes.iter().enumerate() {
            let FlowAction::Break {
                value: Some(break_value),
                result: Some(loop_result),
            } = &event.action
            else {
                continue;
            };
            if *loop_result == value {
                if let Some(state) = &before[index] {
                    merge_loan_origins(
                        &mut result,
                        &value_loan_origins_at_events(body, flow, before, *break_value, state),
                    );
                }
            }
        }
        if !result.is_empty() {
            return result;
        }
    }
    if matches!(
        body.nodes[value.0].kind,
        NodeKind::If { .. } | NodeKind::Match { .. } | NodeKind::Block(_) | NodeKind::Labeled(..)
    ) {
        let mut alternatives = Vec::new();
        collect_result_alternatives(body, value, &mut alternatives);
        let mut result = Vec::new();
        for alternative in alternatives {
            for (index, event) in flow.nodes.iter().enumerate() {
                if flow_action_has_value(&event.action, alternative) {
                    if let Some(state) = &before[index] {
                        merge_loan_origins(
                            &mut result,
                            &value_loan_origins_at_events(body, flow, before, alternative, state),
                        );
                    }
                }
            }
        }
        if !result.is_empty() {
            return result;
        }
    }
    if let NodeKind::Form {
        head,
        children,
        callee,
        ..
    } = &body.nodes[value.0].kind
    {
        if matches!(head.as_str(), "unsafe" | "clone") && children.len() == 2 {
            return value_loan_origins_at_events(body, flow, before, children[1], state);
        }
        if matches!(
            head.as_str(),
            "ptr-borrow" | "ptr-borrow-mut" | "pin-ptr-borrow" | "pin-ptr-borrow-mut"
        ) && children.len() == 3
        {
            let mut pointer_origins =
                value_loan_origins_at_events(body, flow, before, children[1], state);
            for origin in &mut pointer_origins {
                origin.lifetime_only = true;
            }
            if matches!(head.as_str(), "pin-ptr-borrow" | "pin-ptr-borrow-mut") {
                for origin in &mut pointer_origins {
                    origin.pinned = false;
                }
            }
            return pointer_origins;
        }
        if matches!(
            head.as_str(),
            "slice-of" | "slice-mut-of" | "slice-range" | "slice-idx" | "slice-mut-idx"
        ) {
            let mut loans = children.get(1).map_or_else(Vec::new, |source| {
                value_loan_origins_at_events(body, flow, before, *source, state)
            });
            let borrowed_from = children
                .get(1)
                .and_then(|source| reference_binding(body, *source));
            for origin in &mut loans {
                if borrowed_from.is_some() {
                    origin.borrowed_from = borrowed_from;
                }
            }
            return loans;
        }
        if head == "slice-mut-split" && children.len() == 3 {
            let source = value_loan_origins_at_events(body, flow, before, children[1], state);
            let mut result = Vec::with_capacity(source.len() * 2);
            let borrowed_from = reference_binding(body, children[1]);
            for half in 0..2 {
                for origin in &source {
                    let mut origin = origin.clone();
                    origin.borrowed_from = borrowed_from;
                    origin.storage.insert(0, Segment::SliceHalf(half));
                    merge_loan_origins(&mut result, &[origin]);
                }
            }
            return result;
        }
        if matches!(head.as_str(), "get" | "get-payload" | "index") {
            let Some(base) = children.get(1) else {
                return Vec::new();
            };
            let Some(slot) = Place::from_expression(body, value)
                .and_then(|place| place.segments.last().cloned())
                .or_else(|| value_projection(body, value))
            else {
                return Vec::new();
            };
            return value_loan_origins_at_events(body, flow, before, *base, state)
                .into_iter()
                .filter_map(|mut origin| {
                    let held_slot = origin.storage.first()?;
                    if !storage_slot_matches(&slot, held_slot) {
                        return None;
                    }
                    origin.storage.remove(0);
                    Some(origin)
                })
                .collect();
        }
        if let Some(callee) = callee {
            if let Some(summary) = body.call_return_origins.get(callee) {
                let mut result = Vec::new();
                for source in summary {
                    if let Some(origin) = global_summary_origin(source) {
                        merge_loan_origins(&mut result, &[origin]);
                        continue;
                    }
                    let Some(argument) = children.get(source.parameter + 1) else {
                        continue;
                    };
                    for origin in value_loan_origins_at_events(body, flow, before, *argument, state)
                    {
                        if let Some(origin) = apply_parameter_loan_summary(origin, source) {
                            merge_loan_origins(&mut result, &[origin]);
                        }
                    }
                }
                return result;
            }
            if body.nodes[value.0].ty.as_ref().is_some_and(|ty| {
                matches!(
                    ty,
                    Type::Reference { .. }
                        | Type::PinnedReference { .. }
                        | Type::Slice(_)
                        | Type::MutableSlice(_)
                )
            }) {
                let mut result = Vec::new();
                for argument in children.iter().skip(1) {
                    for mut origin in
                        value_loan_origins_at_events(body, flow, before, *argument, state)
                    {
                        origin.storage.clear();
                        merge_loan_origins(&mut result, &[origin]);
                    }
                }
                return result;
            }
        }
        if head == "array-repeat" {
            let Some(Type::Array(_, length)) = body.nodes[value.0].ty.as_ref() else {
                return Vec::new();
            };
            if *length == 0 {
                return Vec::new();
            }
            let Some(element) = children.get(if children.len() == 3 { 2 } else { 1 }) else {
                return Vec::new();
            };
            let mut result = value_loan_origins_at_events(body, flow, before, *element, state);
            let slot = if *length == 1 {
                Segment::Index(0)
            } else {
                Segment::DynamicIndex
            };
            for origin in &mut result {
                origin.storage.insert(0, slot.clone());
            }
            return result;
        }
        if matches!(
            head.as_str(),
            "tuple" | "array" | "array-of" | "struct-literal"
        ) || matches!(
            children.first().map(|child| &body.nodes[child.0].kind),
            Some(NodeKind::Declaration(
                DeclarationId::Aggregate(_) | DeclarationId::Variant(_)
            ))
        ) {
            let node = &body.nodes[value.0];
            let values_start = if head == "array-of" {
                2
            } else if matches!(head.as_str(), "tuple" | "array") {
                constructor_values_start(node.ty.as_ref(), children.len())
            } else {
                1
            };
            let mut result = Vec::new();
            for (index, child) in children.iter().skip(values_start).enumerate() {
                let Some(slot) = aggregate_slot(body, head, children, index) else {
                    continue;
                };
                let mut nested = value_loan_origins_at_events(body, flow, before, *child, state);
                for origin in &mut nested {
                    origin.storage.insert(0, slot.clone());
                }
                merge_loan_origins(&mut result, &nested);
            }
            return result;
        }
    }
    value_loan_origins(body, value, state)
}

/// Follow only known, direct reference origins. Unknown parameters, aggregate
/// slots, and cycles keep their original place for conservative analysis.
fn reborrow_source_origins(
    place: &Place,
    state: &LoanState,
    seen: &mut HashSet<BindingId>,
) -> Vec<LoanOrigin> {
    let segments = place
        .segments
        .iter()
        .filter(|segment| **segment != Segment::Dereference)
        .cloned()
        .collect::<Vec<_>>();
    let through_deref = place.segments.contains(&Segment::Dereference);
    if let PlaceRoot::Local(binding) = place.root {
        if seen.len() < 128 && seen.insert(binding) {
            let mut result = Vec::new();
            for origin in &state[binding.0] {
                if segments.len() < origin.storage.len()
                    || (!through_deref && segments.len() == origin.storage.len())
                    || !segments
                        .iter()
                        .zip(&origin.storage)
                        .all(|(path, slot)| storage_slot_matches(path, slot))
                {
                    continue;
                }
                let mut next = origin.clone();
                next.place
                    .segments
                    .extend_from_slice(&segments[origin.storage.len()..]);
                next.storage.clear();
                for mut resolved in reborrow_source_origins(&next.place, state, seen) {
                    resolved.lifetime_only |= next.lifetime_only;
                    resolved.pinned |= next.pinned;
                    if resolved.parameter_storage.is_none() {
                        resolved.parameter_storage = next.parameter_storage.clone();
                    }
                    if !result.contains(&resolved) {
                        result.push(resolved);
                    }
                }
            }
            seen.remove(&binding);
            if !result.is_empty() {
                return result;
            }
        }
    }
    vec![LoanOrigin {
        place: place.clone(),
        mutable: false,
        pinned: false,
        lifetime_only: false,
        span: None,
        borrowed_from: None,
        storage: Vec::new(),
        parameter_storage: None,
    }]
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
        || matches!((slot, held), (Segment::Tuple(wanted), Segment::SliceHalf(found)) if wanted == found)
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
                        let held = origin.storage.first()?;
                        if !storage_slot_matches(&slot, held) {
                            return None;
                        }
                        let mut origin = origin.clone();
                        origin.storage.remove(0);
                        if let Segment::SliceHalf(half) = held {
                            origin.place.segments.push(Segment::SliceHalf(*half));
                        }
                        Some(origin)
                    })
                    .collect::<Vec<_>>();
                distribute_pattern_origins(body, *child, &nested, state);
            }
        }
        _ => {}
    }
}

/// A matched enum discriminant rules out loans stored in every other variant.
/// Retain only origins whose payload belongs to the selected variant so a
/// consumed Ready result does not conservatively keep the Pending frame's
/// captured references alive after a match.
fn origins_selected_by_variant(
    body: &Body,
    pattern: NodeId,
    origins: &[LoanOrigin],
) -> Option<Vec<LoanOrigin>> {
    let NodeKind::Form { children, .. } = &body.nodes[pattern.0].kind else {
        return None;
    };
    let NodeKind::Declaration(DeclarationId::Variant(selected)) =
        &body.nodes[children.first()?.0].kind
    else {
        return None;
    };
    Some(
        origins
            .iter()
            .filter(|origin| {
                matches!(origin.storage.first(), Some(Segment::Payload(found, _)) if found == selected)
            })
            .cloned()
            .collect(),
    )
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

    fn cleanup_to(
        &mut self,
        depth: usize,
        borrow_scope_depth: usize,
        mut next: FlowNodeId,
    ) -> FlowNodeId {
        let scopes = self.active_borrow_scopes[borrow_scope_depth..]
            .iter()
            .rev()
            .copied()
            .collect::<Vec<_>>();
        for scope in scopes {
            next = self.push(
                FlowAction::BorrowScopeEnd { scope },
                self.body.nodes[scope.0].span,
                vec![next],
            );
        }
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
            Control::Loop(body) => self.loop_body(body, next, targets, label, span, None),
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
                    break_result: None,
                    scope_depth: self.active_scopes.len(),
                    borrow_scope_depth: self.active_borrow_scopes.len(),
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
                        break_result: None,
                        scope_depth: self.active_scopes.len(),
                        borrow_scope_depth: self.active_borrow_scopes.len(),
                    });
                    self.instruction(inner, next, &labeled, None)
                }
            }
            Control::Return(value) => {
                let cleanup = self.cleanup_to(0, 0, self.exit);
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
                let cleanup = self.cleanup_to(
                    target.scope_depth,
                    target.borrow_scope_depth,
                    target.break_to,
                );
                let end = self.push(
                    FlowAction::Break {
                        value: *value,
                        result: target.break_result,
                    },
                    span,
                    vec![cleanup],
                );
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
                    .and_then(|target| {
                        target
                            .continue_to
                            .map(|next| (next, target.scope_depth, target.borrow_scope_depth))
                    })
                    .ok_or_else(|| format!("typed flow has no continue target for {label:?}"))?;
                let end = self.push(FlowAction::Continue, span, vec![target.0]);
                Ok(self.cleanup_to(target.1, target.2, end))
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
            break_result: None,
            scope_depth: self.active_scopes.len(),
            borrow_scope_depth: self.active_borrow_scopes.len(),
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
        break_result: Option<NodeId>,
    ) -> Result<FlowNodeId, String> {
        let header = self.push(FlowAction::LoopHead, span, vec![]);
        let mut loop_targets = targets.to_vec();
        loop_targets.push(Target {
            name: label.map(str::to_owned),
            break_to: next,
            continue_to: Some(header),
            break_result,
            scope_depth: self.active_scopes.len(),
            borrow_scope_depth: self.active_borrow_scopes.len(),
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
            NodeKind::Loop(body) => self.loop_body(body, next, targets, label, span, Some(id)),
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
                if matches!(head.as_str(), "pin-get-payload" | "pin-get-payload-mut")
                    && children.len() == 4 =>
            {
                let action = Place::from_expression(self.body, id).map_or(
                    FlowAction::Evaluate(id),
                    |place| FlowAction::Borrow {
                        value: id,
                        place,
                        mutable: matches!(
                            self.body.nodes[id.0].ty,
                            Some(Type::PinnedReference { mutable: true, .. })
                        ),
                    },
                );
                let done = self.push(action, span, vec![next]);
                self.expression(children[1], done, targets, None)
            }
            NodeKind::Form { head, children, .. }
                if matches!(
                    head.as_str(),
                    "borrow" | "borrow-mut" | "pin-borrow" | "pin-borrow-mut"
                ) && children.len() == 2 =>
            {
                let action = Place::from_expression(self.body, children[1]).map_or(
                    FlowAction::Evaluate(id),
                    |place| FlowAction::Borrow {
                        value: id,
                        place,
                        mutable: matches!(head.as_str(), "borrow-mut" | "pin-borrow-mut"),
                    },
                );
                let done = self.push(action, span, vec![next]);
                self.expression(children[1], done, targets, None)
            }
            NodeKind::Form { head, children, .. }
                if matches!(head.as_str(), "slice-idx" | "slice-mut-idx")
                    && children.len() == 3 =>
            {
                let action = Place::from_expression(self.body, id).map_or(
                    FlowAction::Evaluate(id),
                    |place| FlowAction::Borrow {
                        value: id,
                        place,
                        mutable: head == "slice-mut-idx",
                    },
                );
                let done = self.push(action, span, vec![next]);
                let index = self.expression(children[2], done, targets, None)?;
                self.expression(children[1], index, targets, None)
            }
            NodeKind::Form { head, children, .. }
                if matches!(head.as_str(), "borrow" | "borrow-mut") && children.len() == 3 =>
            {
                let Some(place) = Place::from_expression(self.body, children[1]) else {
                    return Err("typed scoped borrow has no resolved place".into());
                };
                let end = self.push(FlowAction::BorrowScopeEnd { scope: id }, span, vec![next]);
                self.active_borrow_scopes.push(id);
                let body = self.expression(children[2], end, targets, None)?;
                self.active_borrow_scopes.pop();
                let start = self.push(
                    FlowAction::Borrow {
                        value: id,
                        place,
                        mutable: head == "borrow-mut",
                    },
                    span,
                    vec![body],
                );
                self.expression(children[1], start, targets, None)
            }
            NodeKind::Form { head, children, .. }
                if matches!(head.as_str(), "deref-set" | "pin-write") && children.len() == 3 =>
            {
                let action = Place::from_dereference_write(self.body, children[1]).map_or(
                    FlowAction::Evaluate(id),
                    |place| FlowAction::Write { place, value: id },
                );
                let done = self.push(action, span, vec![next]);
                let value = self.expression(children[2], done, targets, None)?;
                self.expression(children[1], value, targets, None)
            }
            NodeKind::Form { head, children, .. }
                if head == "pin-set-field" && children.len() == 4 =>
            {
                let action = Place::from_pin_field_write(self.body, children[1], children[2])
                    .map_or(FlowAction::Evaluate(id), |place| FlowAction::Write {
                        place,
                        value: id,
                    });
                let done = self.push(action, span, vec![next]);
                let value = self.expression(children[3], done, targets, None)?;
                self.expression(children[1], value, targets, None)
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

    #[test]
    fn missing_reference_origins_do_not_establish_consumption_proofs() {
        for source in [
            "(#struct Resource ((number u64))) (#linear Resource)
          (#fn inspect ((reference (#ref-mut Resource))) ()
            (#forget (#deref reference)) (#return ()))",
            "(#struct Resource ((number u64))) (#linear Resource)
             (#struct Wrapped ((item Resource)))
             (#struct Holder ((view (#ref-mut Wrapped))))
             (#fn inspect ((holder Holder)) ()
               (#forget (#get (#get holder view) item)) (#return ()))",
        ] {
            let program = crate::parse_program(source).unwrap();
            let checked = crate::CheckedProgram::validate(&program).unwrap();
            let body = &checked.declarations().bodies["inspect"];
            let flow = &checked.declarations().flows["inspect"];
            let types = LinearTypes::from_program(&program);
            let mut origins = flow.loan_origins(body);
            for state in origins.before.iter_mut().flatten() {
                for held in state {
                    held.clear();
                }
            }
            let moves = flow.consumptions_with_origins(body, &types, Some(&origins));
            let release = FlowNodeId(
                flow.nodes
                    .iter()
                    .position(|node| matches!(node.action, FlowAction::Release { .. }))
                    .unwrap(),
            );
            assert!(moves.unresolved_nodes().contains(&release));
            let returned = FlowNodeId(
                flow.nodes
                    .iter()
                    .position(|node| matches!(node.action, FlowAction::Return(_)))
                    .unwrap(),
            );
            let FlowAction::Release { place, .. } = &flow.nodes[release.0].action else {
                unreachable!()
            };
            assert!(moves.before(returned, place).is_some());
            assert!(!moves.definitely_consumed_before(returned, place));
            assert!(moves
                .dump()
                .contains(&format!("unresolved-referent {}", release.0)));
        }
    }

    #[test]
    fn unknown_reference_writes_do_not_restore_or_preserve_definite_facts() {
        let source = "(#struct Resource ((number u64))) (#linear Resource)
          (#fn inspect ((reference (#ref-mut Resource))) ()
            (#deref-set reference (#struct-literal Resource ((number 2u64))))
            (#return ()))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["inspect"];
        let mut flow = checked.declarations().flows["inspect"].clone();
        let write = flow
            .nodes
            .iter()
            .position(|node| matches!(node.action, FlowAction::Write { .. }))
            .unwrap();
        let FlowAction::Write { place, value } = flow.nodes[write].action.clone() else {
            unreachable!()
        };
        let NodeKind::Form { children, .. } = &body.nodes[value.0].kind else {
            unreachable!()
        };
        let linear_value = children[2];
        let predecessor = flow
            .nodes
            .iter()
            .position(|node| node.successors.contains(&FlowNodeId(write)))
            .unwrap();
        let moved = FlowNodeId(flow.nodes.len());
        flow.nodes.push(FlowNode {
            action: FlowAction::Read {
                value: linear_value,
                place,
                place_base: false,
            },
            successors: vec![FlowNodeId(write)],
            span: None,
        });
        for successor in &mut flow.nodes[predecessor].successors {
            if successor.0 == write {
                *successor = moved;
            }
        }
        let mut origins = flow.loan_origins(body);
        for held in origins.before[write].as_mut().unwrap() {
            held.clear();
        }
        for (index, node) in flow.nodes.iter().enumerate() {
            if flow_action_has_value(&node.action, children[1]) {
                for held in origins.before[index].as_mut().unwrap() {
                    held.clear();
                }
            }
        }
        let types = LinearTypes::from_program(&program);
        let moves = flow.consumptions_with_origins(body, &types, Some(&origins));
        let returned = FlowNodeId(
            flow.nodes
                .iter()
                .position(|node| matches!(node.action, FlowAction::Return(_)))
                .unwrap(),
        );
        let referent = Place::root(PlaceRoot::Parameter(BindingId(0)));
        assert!(moves.unresolved_nodes().contains(&FlowNodeId(write)));
        assert!(moves.before(returned, &referent).is_some());
        assert!(!moves.definitely_consumed_before(returned, &referent));
    }
    use crate::typed_place::Segment;

    #[test]
    fn definite_binding_requires_every_live_predecessor() {
        let mut body = Body::default();
        body.bindings.push(crate::typed_body::Binding {
            name: "value".into(),
            ty: crate::Type::U64,
            span: None,
        });
        body.nodes.push(crate::typed_body::Node {
            expression_id: None,
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
                expression_id: None,
                ty: Some(crate::Type::U64),
                span: None,
                kind: NodeKind::Literal(crate::Expr::Integer(value)),
            });
            body.instructions.push(Instruction {
                statement_id: None,
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
        let declarations = checked.declarations();
        let body = &declarations.bodies["main"];
        let graph = &declarations.flows["main"];
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
        let declarations = checked.declarations();
        let body = &declarations.bodies["main"];
        let graph = &declarations.flows["main"];
        let values = graph
            .nodes
            .iter()
            .filter_map(|node| match node.action {
                FlowAction::Break {
                    value: Some(value), ..
                } => Some(value),
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
            .position(|node| matches!(node.action, FlowAction::Break { value: Some(_), .. }))
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
            span: None,
        });
        body.nodes.push(crate::typed_body::Node {
            expression_id: None,
            ty: Some(crate::Type::U64),
            span: None,
            kind: NodeKind::Literal(crate::Expr::Integer(7)),
        });
        body.nodes.push(crate::typed_body::Node {
            expression_id: None,
            ty: Some(crate::Type::Unit),
            span: None,
            kind: NodeKind::Block(vec![
                Instruction {
                    statement_id: None,
                    span: None,
                    control: Control::Bind(BindingId(0), NodeId(0), false),
                },
                Instruction {
                    statement_id: None,
                    span: None,
                    control: Control::Return(Some(NodeId(0))),
                },
            ]),
        });
        body.instructions.push(Instruction {
            statement_id: None,
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
        assert!(error
            .message
            .contains("linear value 'a' was used more than once"));
        let span = error.span.unwrap();
        assert_eq!(&source[span.start..span.end], "(#forget a)");
        let first = error.labels[0].0;
        assert_eq!(&source[first.start..first.end], "b");
    }

    #[test]
    fn shared_ownership_facts_preserve_independent_check_results() {
        let source = "(#struct Resource ((value u64))) (#linear Resource)
          (#fn main () u64
            (#let a Resource (#struct-literal Resource ((value 1u64))))
            (#let b Resource (#struct-literal Resource ((value 2u64))))
            (#forget a) (#forget b) (#return 0u64))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let declarations = checked.declarations();
        let body = &declarations.bodies["main"];
        let original = &declarations.flows["main"];
        let types = LinearTypes::from_program(&program);
        let releases = original
            .nodes
            .iter()
            .enumerate()
            .filter_map(|(index, node)| {
                matches!(node.action, FlowAction::Release { .. }).then_some(index)
            })
            .collect::<Vec<_>>();
        assert_eq!(releases.len(), 2);
        for variant in 0..3 {
            let mut graph = original.clone();
            if variant == 1 {
                // Releasing a twice also leaves b unconsumed at return.
                graph.nodes[releases[1]].action = graph.nodes[releases[0]].action.clone();
            } else if variant == 2 {
                // Removing explicit destruction leaves an exit obligation.
                graph.nodes[releases[1]].action = FlowAction::Entry;
            }
            let independent = [
                graph.check_linear_releases(body, &types),
                graph.check_linear_consumptions(body, &types),
                graph.check_linear_exit_obligations(body, &types, declarations),
                graph.check_linear_projected_replacements(
                    body,
                    &types,
                    declarations,
                    &graph.consumptions(body, &types),
                ),
            ];
            let shared = graph.check_linear_ownership(body, &types, declarations);
            for (expected, actual) in independent.into_iter().zip(shared) {
                let diagnostic = |result: Result<(), ReleaseConflict>| {
                    result
                        .err()
                        .map(|error| (error.message, error.span, error.labels))
                };
                assert_eq!(
                    diagnostic(expected),
                    diagnostic(actual),
                    "variant {variant}"
                );
            }
        }
    }

    #[test]
    fn copy_only_ownership_fast_path_matches_full_checks() {
        let source = "(#fn main () u64
          (#let-mut value u64 1u64)
          (#if #true (#block (#set value 2u64) ())
            (#block (#set value 3u64) ()))
          (#let view (#ref u64) (#borrow value))
          (#return (#deref view)))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let declarations = checked.declarations();
        let body = &declarations.bodies["main"];
        let graph = &declarations.flows["main"];
        let types = LinearTypes::from_program(&program);
        graph.check_linear_releases(body, &types).unwrap();
        graph.check_linear_consumptions(body, &types).unwrap();
        graph
            .check_linear_exit_obligations(body, &types, declarations)
            .unwrap();
        for result in graph.check_linear_ownership(body, &types, declarations) {
            result.unwrap();
        }
    }

    #[test]
    fn a_copy_projection_is_rejected_after_its_linear_owner_moves() {
        let source = "(#struct Resource ((value u64)))
          (#linear Resource)
          (#struct Pair ((item Resource) (other u64)))
          (#fn main () u64
            (#let pair Pair (#struct-literal Pair
              ((item (#struct-literal Resource ((value 1u64)))) (other 2u64))))
            (#let observed u64 (#get pair other))
            (#forget pair)
            (#return observed))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let mut graph = checked.declarations().flows["main"].clone();
        let pair = BindingId(
            body.bindings
                .iter()
                .position(|binding| binding.name == "pair")
                .unwrap(),
        );
        let projection = graph
            .nodes
            .iter()
            .position(|node| match &node.action {
                FlowAction::Read {
                    value,
                    place,
                    place_base: false,
                } if place.root == PlaceRoot::Local(pair)
                    && &source[body.nodes[value.0].span.unwrap().start
                        ..body.nodes[value.0].span.unwrap().end]
                        == "(#get pair other)" =>
                {
                    true
                }
                _ => false,
            })
            .unwrap();
        let release = graph
            .nodes
            .iter()
            .position(|node| {
                matches!(&node.action, FlowAction::Release { place, .. }
                    if place.root == PlaceRoot::Local(pair))
            })
            .unwrap();
        if projection < release {
            let (before_release, release_and_after) = graph.nodes.split_at_mut(release);
            std::mem::swap(
                &mut before_release[projection].action,
                &mut release_and_after[0].action,
            );
            std::mem::swap(
                &mut before_release[projection].span,
                &mut release_and_after[0].span,
            );
        } else {
            let (before_projection, projection_and_after) = graph.nodes.split_at_mut(projection);
            std::mem::swap(
                &mut before_projection[release].action,
                &mut projection_and_after[0].action,
            );
            std::mem::swap(
                &mut before_projection[release].span,
                &mut projection_and_after[0].span,
            );
        }

        let error = graph
            .check_linear_consumptions(body, &LinearTypes::from_program(&program))
            .unwrap_err();
        assert_eq!(
            error.message,
            "linear projection 'pair.other' was used more than once"
        );
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
        let declarations = checked.declarations();
        let body = &declarations.bodies["main"];
        let graph = &declarations.flows["main"];
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
        graph
            .check_linear_exit_obligations(body, &types, declarations)
            .expect("both branch transfers satisfy the typed whole-value obligation");

        let branch_transfers = graph
            .nodes
            .iter()
            .enumerate()
            .filter_map(|(index, node)| match &node.action {
                FlowAction::Read {
                    place: read_place,
                    place_base: false,
                    ..
                } if read_place == &place => Some(FlowNodeId(index)),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(branch_transfers.len(), 2);
        let mut one_branch_skips_transfer = graph.clone();
        let FlowAction::Read { place_base, .. } =
            &mut one_branch_skips_transfer.nodes[branch_transfers[0].0].action
        else {
            unreachable!()
        };
        *place_base = true;
        let binding_span = body.bindings[token.0]
            .span
            .expect("typed binding has an identifier span");
        let error = one_branch_skips_transfer
            .check_linear_exit_obligations(body, &types, declarations)
            .unwrap_err();
        assert_eq!(error.span, Some(binding_span));
        assert_eq!(&source[binding_span.start..binding_span.end], "token");
        assert_eq!(error.labels.len(), 1);
        let consumed = error.labels[0].0;
        assert_eq!(&source[consumed.start..consumed.end], "token");
    }

    #[test]
    fn definite_consumption_survives_loop_back_edges() {
        let source = "(#struct Token ((value u64)))
          (#linear Token)
          (#fn main ((repeat bool)) ()
            (#let token Token (#struct-literal Token ((value 7u64))))
            (#forget token)
            (#let-mut again bool repeat)
            (#while again (#set again false))
            (#return ()))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let graph = &checked.declarations().flows["main"];
        let types = LinearTypes::from_program(&program);
        let token = BindingId(
            body.bindings
                .iter()
                .position(|binding| binding.name == "token")
                .unwrap(),
        );
        let condition = body
            .nodes
            .iter()
            .position(|node| matches!(&node.kind, NodeKind::Symbol { name, .. } if name == "again"))
            .map(NodeId)
            .unwrap();
        let header = graph
            .nodes
            .iter()
            .position(|node| matches!(node.action, FlowAction::Branch(value) if value == condition))
            .map(FlowNodeId)
            .unwrap();
        let place = Place::root(PlaceRoot::Local(token));
        let obligations = HashSet::from([place.clone()]);
        let (before, _) = graph.obligation_consumptions(body, &types, &obligations);
        assert!(before[header.0].as_ref().unwrap().contains(&place));
    }

    #[test]
    fn loop_only_consumption_is_not_definite_after_zero_iteration_path() {
        let source = "(#struct Token ((value u64))) (#linear Token)";
        let program = crate::parse_program(source).unwrap();
        let types = LinearTypes::from_program(&program);
        let mut body = Body::default();
        body.bindings.push(crate::typed_body::Binding {
            name: "token".into(),
            ty: Type::Named("Token".into()),
            span: None,
        });
        body.nodes.push(crate::typed_body::Node {
            expression_id: None,
            ty: Some(Type::Named("Token".into())),
            span: None,
            kind: NodeKind::Symbol {
                name: "token".into(),
                binding: Some(BindingId(0)),
            },
        });
        body.nodes.push(crate::typed_body::Node {
            expression_id: None,
            ty: Some(Type::Bool),
            span: None,
            kind: NodeKind::Symbol {
                name: "false".into(),
                binding: None,
            },
        });
        let place = Place::root(PlaceRoot::Local(BindingId(0)));
        let graph = FlowGraph {
            nodes: vec![
                FlowNode {
                    action: FlowAction::Entry,
                    successors: vec![FlowNodeId(1)],
                    span: None,
                },
                FlowNode {
                    action: FlowAction::Branch(NodeId(1)),
                    successors: vec![FlowNodeId(2), FlowNodeId(3)],
                    span: None,
                },
                FlowNode {
                    action: FlowAction::Read {
                        value: NodeId(0),
                        place: place.clone(),
                        place_base: false,
                    },
                    successors: vec![FlowNodeId(1)],
                    span: None,
                },
                FlowNode {
                    action: FlowAction::Return(None),
                    successors: vec![FlowNodeId(4)],
                    span: None,
                },
                FlowNode {
                    action: FlowAction::Exit,
                    successors: vec![],
                    span: None,
                },
            ],
            entry: FlowNodeId(0),
            exit: FlowNodeId(4),
        };
        let (before, _) =
            graph.obligation_consumptions(&body, &types, &HashSet::from([place.clone()]));
        assert!(!before[FlowNodeId(3).0].as_ref().unwrap().contains(&place));
    }

    #[test]
    fn typed_exit_obligations_allow_complete_struct_field_consumption() {
        let source = "(#struct Token ((value u64)))
          (#linear Token)
          (#struct Pair ((left Token) (right Token)))
          (#fn main () ()
            (#let a Token (#struct-literal Token ((value 1u64))))
            (#let b Token (#struct-literal Token ((value 2u64))))
            (#let pair Pair (#struct-literal Pair ((left a) (right b))))
            (#let left Token (#get pair left))
            (#forget left)
            (#let right Token (#get pair right))
            (#forget right)
            (#return ()))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let declarations = checked.declarations();
        let body = &declarations.bodies["main"];
        let graph = &declarations.flows["main"];
        let types = LinearTypes::from_program(&program);
        graph
            .check_linear_exit_obligations(body, &types, declarations)
            .expect("consuming both linear fields satisfies the Pair obligation");

        let mut missing_right_field = graph.clone();
        let right = declarations
            .field_id(&Type::Named("Pair".into()), "right")
            .unwrap();
        let transfer =
            missing_right_field
                .nodes
                .iter_mut()
                .find_map(|node| match &mut node.action {
                    FlowAction::Read {
                        place, place_base, ..
                    } if place.segments == [Segment::Field(right)] => {
                        *place_base = true;
                        Some(())
                    }
                    _ => None,
                });
        assert!(
            transfer.is_some(),
            "expected a typed transfer of Pair.right"
        );
        assert!(missing_right_field
            .check_linear_exit_obligations(body, &types, declarations)
            .is_err());
    }

    #[test]
    fn typed_match_transfers_enum_payload_obligations_to_arm_bindings() {
        let source = "(#struct Token ((value u64)))
          (#linear Token)
          (#enum Choice ((Owned Token) Empty))
          (#fn main () ()
            (#let choice Choice
              (Owned (#struct-literal Token ((value 1u64)))))
            (#match choice
              (#case (Owned payload) (#forget payload))
              (#case Empty ()))
            (#return ()))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let declarations = checked.declarations();
        let body = &declarations.bodies["main"];
        let graph = &declarations.flows["main"];
        let types = LinearTypes::from_program(&program);
        graph
            .check_linear_exit_obligations(body, &types, declarations)
            .expect("the match arm consumes the active enum payload");

        let mut missing_arm_transfer = graph.clone();
        let choice = BindingId(
            body.bindings
                .iter()
                .position(|binding| binding.name == "choice")
                .unwrap(),
        );
        let release =
            missing_arm_transfer
                .nodes
                .iter_mut()
                .find_map(|node| match &mut node.action {
                    FlowAction::Release { place, .. }
                        if matches!(place.root, PlaceRoot::Local(_)) =>
                    {
                        *place = Place::root(PlaceRoot::Local(choice));
                        Some(())
                    }
                    _ => None,
                });
        assert!(release.is_some());
        assert!(missing_arm_transfer
            .check_linear_exit_obligations(body, &types, declarations)
            .is_err());
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
            matches!(node.action, FlowAction::Borrow { value: id, .. }
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
            pinned: false,
            span: None,
            borrowed_from: None,
            storage,
            parameter_storage: None,
            lifetime_only: false,
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
        let source =
            "(#fn choose ((condition bool) (first (#ref u64)) (second (#ref u64))) (#ref u64)
          (#return (#if condition first second)))
          (#fn main () u64
            (#let left u64 1u64)
            (#let right u64 2u64)
            (#let selected (#ref u64)
              (#call choose (: condition true : first (#borrow left) : second (#borrow right))))
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
    fn reference_parameters_are_external_origins_on_typed_flow() {
        let source = "(#fn pass ((source (#ref u64))) (#ref u64)
          (#let alias (#ref u64) source)
          (#return alias))
          (#fn inspect ((source (#ref-mut u64))) u64
            (#return (#deref source)))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["pass"];
        assert_eq!(body.parameter_count, 1);
        let graph = &checked.declarations().flows["pass"];
        let alias = BindingId(
            body.bindings
                .iter()
                .position(|binding| binding.name == "alias")
                .unwrap(),
        );
        let bind = graph
            .nodes
            .iter()
            .position(
                |node| matches!(node.action, FlowAction::Bind { binding, .. } if binding == alias),
            )
            .map(FlowNodeId)
            .unwrap();
        let origins = graph.loan_origins(body);
        let held = origins.after(bind, alias);
        assert_eq!(held.len(), 1);
        assert_eq!(held[0].place.root, PlaceRoot::Parameter(BindingId(0)));
        assert!(
            held[0].span.is_none(),
            "parameter origins are caller-provided"
        );

        let inspect = &checked.declarations().bodies["inspect"];
        let inspect_flow = &checked.declarations().flows["inspect"];
        let inspect_origins = inspect_flow.loan_origins(inspect);
        assert_eq!(
            inspect_origins
                .before(inspect_flow.entry, BindingId(0))
                .len(),
            1
        );
        assert!(inspect_origins.before(inspect_flow.entry, BindingId(0))[0].mutable);
    }

    #[test]
    fn aggregate_return_origins_flow_through_chains_of_checked_calls() {
        let source = "(#struct RefBox ((value (#ref u64))))
          (#fn wrap ((value (#ref u64))) RefBox
            (#return (#struct-literal RefBox ((value value)))))
          (#fn wrap-again ((value (#ref u64))) RefBox
            (#return (#call wrap (: value value))))
          (#fn project ((box RefBox)) (#ref u64)
            (#return (#get box value)))
          (#fn project-again ((box RefBox)) (#ref u64)
            (#return (#call project (: box box))))
          (#fn main () u64
            (#let owner u64 9u64)
            (#let boxed RefBox
              (#call wrap-again (: value (#borrow owner))))
            (#let selected (#ref u64)
              (#call project-again (: box boxed)))
            (#return (#deref selected)))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let graph = &checked.declarations().flows["main"];
        let boxed = BindingId(
            body.bindings
                .iter()
                .position(|binding| binding.name == "boxed")
                .unwrap(),
        );
        let owner = BindingId(
            body.bindings
                .iter()
                .position(|binding| binding.name == "owner")
                .unwrap(),
        );
        let bind = graph
            .nodes
            .iter()
            .position(
                |node| matches!(node.action, FlowAction::Bind { binding, .. } if binding == boxed),
            )
            .map(FlowNodeId)
            .unwrap();
        let loans = graph.loan_origins(body);
        let held = loans.after(bind, boxed);
        assert_eq!(held.len(), 1);
        assert_eq!(held[0].place.root, PlaceRoot::Local(owner));
        assert_eq!(held[0].storage.len(), 1);
        let selected = BindingId(
            body.bindings
                .iter()
                .position(|binding| binding.name == "selected")
                .unwrap(),
        );
        let selected_bind = graph
            .nodes
            .iter()
            .position(|node| {
                matches!(node.action, FlowAction::Bind { binding, .. } if binding == selected)
            })
            .map(FlowNodeId)
            .unwrap();
        let selected_origins = loans.after(selected_bind, selected);
        assert_eq!(selected_origins.len(), 1);
        assert_eq!(selected_origins[0].place.root, PlaceRoot::Local(owner));
        assert!(selected_origins[0].storage.is_empty());
    }

    #[test]
    fn aggregate_call_return_cannot_hide_a_local_borrow_escape() {
        let source = "(#struct RefBox ((value (#ref u64))))
          (#fn wrap ((value (#ref u64))) RefBox
            (#return (#struct-literal RefBox ((value value)))))
          (#fn wrap-again ((value (#ref u64))) RefBox
            (#return (#call wrap (: value value))))
          (#fn bad () RefBox
            (#let owner u64 9u64)
            (#return (#call wrap-again (: value (#borrow owner)))))";
        let program = crate::parse_program(source).unwrap();
        let error = crate::CheckedProgram::validate(&program)
            .err()
            .expect("returning the reference-bearing aggregate must fail");
        assert!(
            error.contains("cannot return a value retaining a reference to local 'owner'"),
            "expected typed interprocedural escape diagnostic, got: {error}"
        );
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
        assert_eq!(held.len(), 1);
        assert!(held.iter().all(|origin| origin.storage.is_empty()));
        assert_eq!(
            &source[held[0].span.unwrap().start..held[0].span.unwrap().end],
            "(#borrow left)"
        );
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
            .position(
                |node| matches!(node.action, FlowAction::Borrow { value, .. } if value == index),
            )
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
    fn loop_branch_snapshots_retain_returned_parameter_loans() {
        let source = "(#enum State ((Working (#ref u64)) (Finished (#ref u64))))
          (#fn finish ((source (#ref u64))) (#ref u64)
            (#let-mut state State (Working source))
            (#let-mut stopped bool false)
            (#while (#bool.== stopped false)
              (#set state (#match state
                (#case (Working held) (#block (#set stopped true) (Finished held)))
                (#case (Finished unused) (#unreachable)))))
            (#return (#match state
              (#case (Finished result) result)
              (#case (Working unused) (#unreachable)))))
          (#fn main () (#ref u64)
            (#let owner u64 42u64)
            (#return (#call finish (: source (#borrow owner)))))";
        let program = crate::parse_program(source).unwrap();
        let error = crate::CheckedProgram::validate_with_span(&program)
            .err()
            .unwrap();
        assert!(
            error.0.contains("reference") && error.0.contains("owner"),
            "{error:?}"
        );
        assert!(error.2.is_some(), "{error:?}");
        let safe = source
            .replace(
                "(#fn main () (#ref u64)\n            (#let owner u64 42u64)",
                "(#fn main ((owner (#ref u64))) (#ref u64)",
            )
            .replace("(: source (#borrow owner))", "(: source owner)");
        crate::CheckedProgram::validate(&crate::parse_program(&safe).unwrap()).unwrap();
    }

    #[test]
    fn early_exit_does_not_require_consuming_uninitialized_later_locals() {
        let source = "(#struct Token ((value u64))) (#linear Token)
          (#fn main ((early bool)) u64
            (#if early (#block (#return 5u64)) ())
            (#let token Token (#struct-literal Token ((value 42u64))))
            (#forget token)
            (#return 42u64))";
        let program = crate::parse_program(source).unwrap();
        crate::CheckedProgram::validate(&program).unwrap();
        let missing = source.replace("(#forget token)", "()");
        let error = crate::CheckedProgram::validate(&crate::parse_program(&missing).unwrap())
            .err()
            .unwrap();
        assert!(
            error.contains("token") && error.contains("consum"),
            "{error}"
        );
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
    fn liveness_preserves_bindings_across_multiple_bitset_words() {
        let mut source = String::from("(#fn main () u64 ");
        for index in 0..130 {
            source.push_str(&format!("(#let value{index} u64 {index}u64) "));
        }
        for index in 0..129 {
            source.push_str(&format!("(#forget value{index}) "));
        }
        source.push_str("(#return value129))");
        let program = crate::parse_program(&source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let graph = &checked.declarations().flows["main"];
        let liveness = &checked.declarations().liveness["main"];
        let last = BindingId(
            body.bindings
                .iter()
                .position(|b| b.name == "value129")
                .unwrap(),
        );
        let bound = graph
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| {
                matches!(node.action, FlowAction::Bind { binding, .. } if binding == last)
                    .then_some(FlowNodeId(index))
            })
            .unwrap();
        assert_eq!(liveness.before(bound).len(), 129);
        assert_eq!(liveness.after(bound).len(), 130);
        assert!(!liveness.before(bound).contains(&last));
        assert!(liveness.after(bound).contains(&last));
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
            .filter(|node| matches!(node.action, FlowAction::Break { .. }))
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
