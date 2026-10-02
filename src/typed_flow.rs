//! Stable, address-free control flow over the checked body arena.
//! Ownership passes can share these edges instead of reconstructing branch
//! and loop behavior independently from syntax.

use std::collections::{HashMap, HashSet, VecDeque};

use crate::linearcheck::LinearTypes;
use crate::typed_body::{
    BindingId, Body, Control, Instruction, NodeId, NodeKind, NumericOpcode, PlaceRoot, Projection,
};
#[cfg(test)]
use crate::typed_ir::VariantId;
use crate::typed_ir::{DeclarationId, FieldId};
#[cfg(test)]
use crate::typed_place::owned_output_projection;
use crate::typed_place::{reads_through_reference, Place, Segment};
use crate::{Span, Type};

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) struct FlowNodeId(pub usize);

#[cfg(test)]
type CallResultRefinement = (
    Vec<(FlowNodeId, NodeId, Vec<Segment>)>,
    VariantId,
    Vec<FlowNodeId>,
);

#[cfg(test)]
type VariantState = HashMap<Place, VariantId>;
#[cfg(test)]
type VariantContext<'a> = (
    &'a FlowGraph,
    &'a FlowLoanOrigins,
    FlowNodeId,
    &'a [Option<VariantState>],
);

#[cfg(test)]
fn captured_variant_events(context: VariantContext<'_>, value: NodeId) -> Vec<FlowNodeId> {
    let (flow, origins, event, _) = context;
    let matches = |index: usize| {
        matches!(flow.nodes[index].action,
        FlowAction::Evaluate(found) | FlowAction::Read { value: found, .. }
        | FlowAction::Clone { value: found, .. } | FlowAction::Borrow { value: found, .. } if found == value)
    };
    if matches(event.0) {
        return Vec::new();
    }
    origins.events_by_value[value.0]
        .iter()
        .copied()
        .filter(|index| origins.before[*index].is_some() && matches(*index))
        .map(FlowNodeId)
        .collect()
}

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
    #[cfg(test)]
    worklist_visits: usize,
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
    /// Output storage positions that still select the original input slot.
    /// Constructor-created positions have no correspondence to input slots.
    pub storage_inputs: Vec<Option<usize>>,
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
            && self.storage_inputs == other.storage_inputs
    }
}

impl Eq for LoanOrigin {}

impl LoanOrigin {
    #[cfg(test)]
    pub fn parameter_summary(&self) -> Option<crate::typed_body::ParameterLoanSummary> {
        let (parameter, global) = match self.place.root {
            PlaceRoot::Parameter(binding) => (binding.0, None),
            PlaceRoot::Global(global) => (0, Some(global)),
            PlaceRoot::Local(_) => return None,
        };
        Some(crate::typed_body::ParameterLoanSummary {
            parameter,
            global,
            mutable: self.mutable,
            pinned: self.pinned,
            lifetime_only: self.lifetime_only,
            referent_projection: self.place.segments.clone(),
            input_storage: self.parameter_storage.clone().unwrap_or_default(),
            storage: self.storage.clone(),
            storage_inputs: self.storage_inputs.clone(),
        })
    }
    /// Keep the identity of a parameter's stored pointee separate from its
    /// output value slot and subsequent physical referent projections.
    pub fn referent_place(&self) -> Place {
        let mut place = self.place.clone();
        if matches!(place.root, PlaceRoot::Parameter(_)) {
            if let Some(slot) = &self.parameter_storage {
                let mut segments = slot.clone();
                segments.append(&mut place.segments);
                place.segments = segments;
            }
        }
        place
    }

    fn project_storage(&mut self, selected: &Segment) -> Option<usize> {
        let input = self.storage_inputs.first().copied().flatten();
        if let Some(slot) = input.and_then(|index| {
            self.parameter_storage
                .as_mut()
                .and_then(|slots| slots.get_mut(index))
        }) {
            // Static selection refines a symbolic array slot. A dynamic
            // selection cannot weaken an already known input identity.
            if !matches!(selected, Segment::DynamicIndex | Segment::SliceDynamicIndex) {
                *slot = selected.clone();
            }
        }
        self.storage.remove(0);
        if !self.storage_inputs.is_empty() {
            self.storage_inputs.remove(0);
        }
        input
    }

    fn drain_storage(&mut self, count: usize) {
        self.storage.drain(..count);
        self.storage_inputs
            .drain(..count.min(self.storage_inputs.len()));
    }

    fn clear_storage(&mut self) {
        self.storage.clear();
        self.storage_inputs.clear();
    }

    fn prepend_storage(&mut self, path: &[Segment]) {
        if !self.storage_inputs.is_empty() {
            let mut inputs = vec![None; path.len()];
            inputs.append(&mut self.storage_inputs);
            self.storage_inputs = inputs;
        }
        let mut storage = path.to_vec();
        storage.append(&mut self.storage);
        self.storage = storage;
    }
}

#[cfg(not(test))]
type LoanState = Vec<Vec<LoanOrigin>>;

#[cfg(test)]
#[derive(Clone)]
struct LoanState {
    bindings: Vec<Vec<LoanOrigin>>,
    // Parameter input pointer slots and owned global storage have distinct
    // roots. These keys are not positions in the output value being stored.
    parameter_contents: Option<HashMap<(PlaceRoot, Vec<Segment>), Vec<LoanOrigin>>>,
    // Globals have no symbolic parameter seed. Only every-path concrete writes
    // establish known contents; a may-write cannot invent the old provenance.
    global_known_contents: HashMap<crate::typed_ir::GlobalId, HashSet<Vec<Segment>>>,
}

#[cfg(test)]
impl From<Vec<Vec<LoanOrigin>>> for LoanState {
    fn from(bindings: Vec<Vec<LoanOrigin>>) -> Self {
        Self {
            bindings,
            parameter_contents: None,
            global_known_contents: HashMap::new(),
        }
    }
}

#[cfg(test)]
impl std::ops::Deref for LoanState {
    type Target = Vec<Vec<LoanOrigin>>;
    fn deref(&self) -> &Self::Target {
        &self.bindings
    }
}

#[cfg(test)]
impl std::ops::DerefMut for LoanState {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.bindings
    }
}

fn empty_loan_state(count: usize) -> LoanState {
    #[cfg(test)]
    {
        vec![Vec::new(); count].into()
    }
    #[cfg(not(test))]
    {
        vec![Vec::new(); count]
    }
}

/// Borrowed solver snapshots and their source-ordered expression-event index.
/// Copying this view does not allocate or retain an additional index.
#[derive(Clone, Copy)]
struct LoanSnapshots<'a> {
    before: &'a [Option<LoanState>],
    events_by_value: &'a [Vec<usize>],
}

impl<'a> LoanSnapshots<'a> {
    fn new(before: &'a [Option<LoanState>], events_by_value: &'a [Vec<usize>]) -> Self {
        Self {
            before,
            events_by_value,
        }
    }
}

impl std::ops::Index<usize> for LoanSnapshots<'_> {
    type Output = Option<LoanState>;

    fn index(&self, index: usize) -> &Self::Output {
        &self.before[index]
    }
}

/// Direct reference origins at each typed flow point. This is a may-analysis,
/// not yet an enforcing borrow check; indirect provenance and destructured
/// payloads still need the full IR-04 transfer.
pub(crate) struct FlowLoanOrigins {
    #[cfg(test)]
    variants: std::cell::OnceCell<Vec<Option<HashMap<Place, VariantId>>>>,
    #[cfg(test)]
    clear_refinements: Vec<Option<CallResultRefinement>>,
    before: Vec<Option<LoanState>>,
    after: Vec<Option<LoanState>>,
    // Reuse the solver's dense, source-ordered snapshot dependency index.
    // Break events are indexed by both their value and loop result, so queries
    // retain the original action filter.
    events_by_value: Vec<Vec<usize>>,
}

#[derive(Clone, Debug)]
#[cfg(test)]
pub(crate) struct LoanStore {
    pub destination: LoanOrigin,
    pub incoming: Vec<LoanOrigin>,
    pub definitely_written: bool,
    pub variants: HashMap<Vec<Segment>, VariantId>,
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
    local_pin_accesses: HashMap<NodeId, Place>,
    /// Resolved direct consuming accesses, independent of later restoration.
    #[cfg(test)]
    resolved_at: Vec<HashSet<Place>>,
    definitely_before: Vec<Option<HashSet<Place>>>,
    /// Indirect accesses lacking provenance; never an ownership proof.
    unresolved: HashSet<FlowNodeId>,
}

#[cfg(test)]
#[derive(Clone, Debug)]
pub(crate) struct ReferentExitEffect {
    pub place: Place,
    pub input_storage: Option<Vec<Segment>>,
    pub referent_projection: Vec<Segment>,
    pub definitely_consumed: bool,
    pub consumption_spans: Vec<Option<Span>>,
}

#[cfg(test)]
#[derive(Clone, Debug)]
pub(crate) struct ReferentFunctionEffects {
    pub has_normal_return: bool,
    pub effects: Vec<ReferentExitEffect>,
    /// Unknown reachable accesses, including paths without a normal return.
    pub unresolved: Vec<FlowNodeId>,
    pub reads: Vec<ReferentRead>,
    pub unresolved_reads: Vec<FlowNodeId>,
    pub entry_reads: Vec<ReferentRead>,
    /// Actual consuming accesses, even when restoration clears exit effects.
    pub consuming_accesses: Vec<ReferentRead>,
    pub restored_from_consumed_entry: Vec<Place>,
    pub consumed_entry: Vec<Place>,
    /// Exit storage state under the inferred consumed-entry assumptions, not
    /// evidence that the function actually consumed this storage.
    pub effects_from_consumed_entry: Vec<ReferentExitEffect>,
    /// Complete exit effects for an explicitly selected returned constructor.
    /// A missing outcome is unknown, not evidence of initialized storage.
    pub variant_exits: HashMap<VariantId, ReferentVariantExit>,
}

#[cfg(test)]
#[derive(Clone, Debug)]
pub(crate) struct ReferentVariantExit {
    pub has_normal_return: bool,
    pub effects: Vec<ReferentExitEffect>,
    /// Exact restoration guaranteed only after selecting this result.
    pub restored: Vec<ReferentExitEffect>,
    /// None means consumed-entry assumptions were not inferred/checked.
    pub effects_from_consumed_entry: Option<Vec<ReferentExitEffect>>,
    /// Exact input requirements selecting the consumed-entry profile.
    pub consumed_entry: Vec<ReferentExitEffect>,
    pub unresolved: Vec<FlowNodeId>,
}

#[cfg(test)]
impl ReferentFunctionEffects {
    pub fn possibly_initialized_inputs(&self) -> Vec<Place> {
        self.consumed_entry
            .iter()
            .filter(|input| {
                !self.effects_from_consumed_entry.iter().any(|effect| {
                    effect.definitely_consumed && definite_place_covers(&effect.place, input)
                })
            })
            .cloned()
            .collect()
    }
}

/// Independent read facts, not outgoing consumption or complete entry
/// requirements. Prior initialization writes must be considered separately.
/// Consuming-access contracts reuse this identity descriptor without treating
/// those facts as read-entry requirements or outgoing consumption effects.
#[cfg(test)]
#[derive(Clone, Debug)]
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
    /// Mapped accesses survive callee restoration; they do not transfer state.
    pub consuming_accesses: Vec<ReferentRead>,
    pub unresolved_inputs: Vec<FlowNodeId>,
    /// None keeps the conservative consumed-input fallback for manual facts.
    pub possible_restorations: Option<Vec<(FlowNodeId, Vec<Place>)>>,
}

#[derive(Default)]
struct CallConsumptionFacts {
    possible: Vec<(Place, Vec<Option<Span>>)>,
    definite: Vec<Place>,
    unresolved: bool,
    restored: Vec<Place>,
    possibly_restored: Vec<Place>,
    #[cfg(test)]
    outcomes: Vec<CallOutcomeSource>,
}

#[cfg(test)]
struct CallOutcomeSource {
    event: FlowNodeId,
    effects: Vec<ReferentExitEffect>,
    restored: Vec<Place>,
    consumed_entry: Vec<Place>,
}

#[cfg(test)]
fn outcome_candidates(
    outcomes: &[CallOutcomeSource],
    calls: &HashMap<FlowNodeId, CallConsumptionFacts>,
) -> Vec<Place> {
    let mut candidates = Vec::new();
    for outcome in outcomes {
        let original = &calls[&outcome.event];
        for place in original
            .possible
            .iter()
            .map(|(place, _)| place)
            .chain(&original.restored)
            .chain(&original.possibly_restored)
            .chain(outcome.effects.iter().map(|effect| &effect.place))
            .chain(&outcome.restored)
            .chain(&outcome.consumed_entry)
        {
            if !candidates.contains(place) {
                candidates.push(place.clone());
            }
        }
    }
    candidates
}

#[cfg(test)]
fn refine_outcome_may(
    facts: &CallConsumptionFacts,
    calls: &HashMap<FlowNodeId, CallConsumptionFacts>,
    before: &[Option<HashMap<Place, Vec<Option<Span>>>>],
    state: &mut HashMap<Place, Vec<Option<Span>>>,
) -> bool {
    if facts.outcomes.is_empty() {
        return true;
    }
    let candidates = outcome_candidates(&facts.outcomes, calls);
    let mut joined: HashMap<Place, Vec<Option<Span>>> = HashMap::new();
    for outcome in &facts.outcomes {
        let Some(entry) = &before[outcome.event.0] else {
            return false;
        };
        let original = &calls[&outcome.event];
        let mut branch = entry
            .iter()
            .filter(|(place, _)| {
                candidates
                    .iter()
                    .any(|candidate| place_covers(candidate, place))
            })
            .map(|(place, spans)| (place.clone(), spans.clone()))
            .collect::<HashMap<_, _>>();
        let prior = branch.clone();
        branch.retain(|place, _| {
            !original
                .restored
                .iter()
                .chain(&outcome.restored)
                .chain(&outcome.consumed_entry)
                .any(|restored| place_covers(restored, place))
        });
        for effect in &outcome.effects {
            let held = branch.entry(effect.place.clone()).or_default();
            for span in &effect.consumption_spans {
                if !held.contains(span) {
                    held.push(*span);
                }
            }
            // A seeded consumed-entry fact inherits the caller's destruction
            // site, rather than losing that diagnostic to an anonymous seed.
            if effect.consumption_spans.iter().all(Option::is_none) {
                for (place, spans) in &prior {
                    if place.overlaps(&effect.place) {
                        for span in spans {
                            if !held.contains(span) {
                                held.push(*span);
                            }
                        }
                    }
                }
            }
        }
        for (place, spans) in branch {
            let held = joined.entry(place).or_default();
            for span in spans {
                if !held.contains(&span) {
                    held.push(span);
                }
            }
        }
    }
    state.retain(|place, _| {
        !candidates
            .iter()
            .any(|candidate| place_covers(candidate, place))
    });
    state.extend(joined);
    true
}

#[cfg(test)]
fn refine_outcome_must(
    facts: &CallConsumptionFacts,
    calls: &HashMap<FlowNodeId, CallConsumptionFacts>,
    before: &[Option<HashSet<Place>>],
    state: &mut HashSet<Place>,
) -> bool {
    if facts.outcomes.is_empty() {
        return true;
    }
    let candidates = outcome_candidates(&facts.outcomes, calls);
    let mut joined: Option<HashSet<Place>> = None;
    for outcome in &facts.outcomes {
        let Some(entry) = &before[outcome.event.0] else {
            return false;
        };
        let original = &calls[&outcome.event];
        let mut branch = entry
            .iter()
            .filter(|place| {
                candidates
                    .iter()
                    .any(|candidate| place_covers(candidate, place))
            })
            .cloned()
            .collect::<HashSet<_>>();
        branch.retain(|place| {
            !original
                .restored
                .iter()
                .chain(&outcome.restored)
                .chain(&original.possibly_restored)
                .chain(&outcome.consumed_entry)
                .any(|restored| restored.overlaps(place))
        });
        branch.extend(
            outcome
                .effects
                .iter()
                .filter(|effect| effect.definitely_consumed)
                .map(|effect| effect.place.clone()),
        );
        if let Some(held) = &mut joined {
            held.retain(|place| branch.contains(place));
        } else {
            joined = Some(branch);
        }
    }
    state.retain(|place| {
        !candidates
            .iter()
            .any(|candidate| place_covers(candidate, place))
    });
    state.extend(joined.unwrap_or_default());
    true
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
    #[cfg(test)]
    fn reachable_loop_breaks(&self, flow: &FlowGraph, result: NodeId) -> Vec<(FlowNodeId, NodeId)> {
        self.events_by_value[result.0]
            .iter()
            .filter_map(|index| {
                if self.before[*index].is_none() {
                    return None;
                }
                match flow.nodes[*index].action {
                    FlowAction::Break {
                        value: Some(value),
                        result: Some(found),
                    } if found == result => Some((FlowNodeId(*index), value)),
                    _ => None,
                }
            })
            .collect()
    }

    /// Proven final callee clears or an exact direct destructive access.
    /// Empty contents are not an initialization or ownership proof.
    #[cfg(test)]
    fn clears_before(&self, body: &Body, flow: &FlowGraph, event: FlowNodeId) -> Vec<LoanOrigin> {
        let Some(state) = &self.before[event.0] else {
            return Vec::new();
        };
        if state.parameter_contents.is_none() {
            return Vec::new();
        }
        if let Some(refinement) = &self.clear_refinements[event.0] {
            return correlated_call_variant_clears(
                body,
                flow,
                LoanSnapshots::new(&self.before, &self.events_by_value),
                refinement,
            );
        }
        let value = match flow.nodes[event.0].action {
            FlowAction::Release { value, .. } | FlowAction::Evaluate(value) => value,
            _ => return Vec::new(),
        };
        let NodeKind::Form {
            children, callee, ..
        } = &body.nodes[value.0].kind
        else {
            return Vec::new();
        };
        if callee.is_some() {
            return call_parameter_clears(
                body,
                flow,
                LoanSnapshots::new(&self.before, &self.events_by_value),
                value,
                state,
            );
        }
        let destinations = if body.consuming_releases.contains(&value) {
            released_reference_destinations(
                body,
                flow,
                LoanSnapshots::new(&self.before, &self.events_by_value),
                children[1],
                state,
            )
        } else if body.consuming_pin_reads.contains(&value) {
            self.value_before(body, flow, event, children[1])
        } else {
            Vec::new()
        };
        if one_concrete_store_destination(&destinations) {
            destinations
        } else {
            Vec::new()
        }
    }

    /// Actual direct or substituted callee stores at this reachable event.
    #[cfg(test)]
    pub fn stores_before(
        &self,
        body: &Body,
        flow: &FlowGraph,
        event: FlowNodeId,
    ) -> Vec<LoanStore> {
        let Some(state) = self.before[event.0].as_ref() else {
            return Vec::new();
        };
        let value = match flow.nodes[event.0].action {
            FlowAction::Write { value, .. } | FlowAction::Evaluate(value) => value,
            _ => return Vec::new(),
        };
        let NodeKind::Form {
            head,
            children,
            callee,
            ..
        } = &body.nodes[value.0].kind
        else {
            return Vec::new();
        };
        if callee.is_some() {
            return call_loan_stores(
                body,
                flow,
                LoanSnapshots::new(&self.before, &self.events_by_value),
                value,
                state,
            );
        }
        let (source, field) = match (head.as_str(), children.len()) {
            ("deref-set" | "pin-write", 3) => (children[2], None),
            ("pin-set-field", 4) => {
                let NodeKind::Declaration(DeclarationId::Field(field)) =
                    body.nodes[children[2].0].kind
                else {
                    return Vec::new();
                };
                (children[3], Some(field))
            }
            _ => return Vec::new(),
        };
        let incoming = self.value_before(body, flow, event, source);
        let mut destinations = self.value_before(body, flow, event, children[1]);
        for destination in &mut destinations {
            if let Some(field) = field {
                destination.place.segments.push(Segment::Field(field));
            }
        }
        let definitely_written = one_concrete_store_destination(&destinations);
        destinations
            .into_iter()
            .map(|destination| LoanStore {
                destination,
                incoming: incoming.clone(),
                definitely_written,
                variants: HashMap::new(),
            })
            .collect()
    }
    pub fn value_before(
        &self,
        body: &Body,
        flow: &FlowGraph,
        node: FlowNodeId,
        value: NodeId,
    ) -> Vec<LoanOrigin> {
        if matches!(body.nodes[value.0].kind, NodeKind::Loop(_)) {
            let mut loop_results = Vec::new();
            for &index in &self.events_by_value[value.0] {
                let event = &flow.nodes[index];
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
                    for &event_index in &self.events_by_value[alternative.0] {
                        let candidate = &flow.nodes[event_index];
                        if flow_action_has_value(&candidate.action, alternative) {
                            if let Some(state) = &self.before[event_index] {
                                evaluated = true;
                                merge_loan_origins(
                                    &mut loop_results,
                                    &value_loan_origins_at_events(
                                        body,
                                        flow,
                                        LoanSnapshots::new(&self.before, &self.events_by_value),
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
                            LoanSnapshots::new(&self.before, &self.events_by_value),
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
            for &index in &self.events_by_value[alternative.0] {
                let event = &flow.nodes[index];
                if !flow_action_has_value(&event.action, alternative) {
                    continue;
                }
                if let Some(state) = &self.before[index] {
                    merge_loan_origins(
                        &mut results,
                        &value_loan_origins_at_events(
                            body,
                            flow,
                            LoanSnapshots::new(&self.before, &self.events_by_value),
                            alternative,
                            state,
                        ),
                    );
                }
            }
        }
        if results.is_empty() {
            self.before[node.0].as_ref().map_or_else(Vec::new, |state| {
                value_loan_origins_at_events(
                    body,
                    flow,
                    LoanSnapshots::new(&self.before, &self.events_by_value),
                    value,
                    state,
                )
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
        self.projected_referents_with_slots(node, binding, segments, true)
    }

    fn projected_referents_with_slots(
        &self,
        node: FlowNodeId,
        binding: BindingId,
        segments: &[Segment],
        parameter_slots: bool,
    ) -> Vec<Place> {
        let origin_place = |origin: &LoanOrigin| {
            if parameter_slots {
                origin.referent_place()
            } else {
                origin.place.clone()
            }
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
                || !segments
                    .iter()
                    .zip(&origin.storage)
                    .all(|(selected, stored)| storage_slot_matches(selected, stored))
            {
                continue;
            }
            let mut selected = origin.clone();
            for segment in &segments[..origin.storage.len()] {
                selected.project_storage(segment);
            }
            let mut place = origin_place(&selected);
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
        let binding_count = self
            .before
            .iter()
            .flatten()
            .next()
            .map_or(0, |state| state.len());
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
            #[cfg(test)]
            Segment::ThreadCapture(_, index) => {
                output.push_str(&format!(".<thread-capture:{index}>"));
            }
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

#[cfg(test)]
pub(crate) type VariantBounds = HashMap<Vec<Segment>, HashSet<VariantId>>;

#[cfg(test)]
fn join_variant_bounds(held: &mut VariantBounds, incoming: &VariantBounds) {
    held.retain(|path, variants| {
        if let Some(other) = incoming.get(path) {
            variants.extend(other);
            true
        } else {
            false
        }
    });
}

impl FlowGraph {
    /// Output-relative variant upper bounds for every reachable normal return.
    /// Unknown alternatives remove bounds rather than guessing a shape.
    #[cfg(test)]
    pub fn returned_variant_bounds(&self, body: &Body, origins: &FlowLoanOrigins) -> VariantBounds {
        let states = self.variant_facts_with_origins(body, origins);
        let mut returned: Option<VariantBounds> = None;
        for (index, event) in self.nodes.iter().enumerate() {
            let FlowAction::Return(Some(value)) = event.action else {
                continue;
            };
            if states[index].is_none() {
                continue;
            }
            let mut pending = vec![(FlowNodeId(index), value, Vec::new())];
            while let Some((event, value, ancestors)) = pending.pop() {
                let Some(state) = &states[event.0] else {
                    continue;
                };
                let mut alternatives = Vec::new();
                collect_result_alternatives(body, value, &mut alternatives);
                for alternative in alternatives {
                    let key = (event, alternative);
                    if ancestors.contains(&key) {
                        // A recursive alias is unknown, not an alternative
                        // that can be silently dropped from the intersection.
                        returned = Some(HashMap::new());
                        continue;
                    }
                    let mut next_ancestors = ancestors.clone();
                    next_ancestors.push(key);
                    if matches!(body.nodes[alternative.0].kind, NodeKind::Loop(_)) {
                        let breaks = origins.reachable_loop_breaks(self, alternative);
                        if !breaks.is_empty() {
                            pending.extend(
                                breaks
                                    .into_iter()
                                    .map(|(event, value)| (event, value, next_ancestors.clone())),
                            );
                            continue;
                        }
                    }
                    let value_facts = value_variant_bounds(
                        body,
                        alternative,
                        state,
                        Some((self, origins, event, &states)),
                    );
                    if let NodeKind::Symbol {
                        binding: Some(binding),
                        ..
                    } = body.nodes[alternative.0].kind
                    {
                        if value_facts.is_empty() {
                            if let Some(definitions) = self.unchanged_local_definitions(
                                body,
                                origins,
                                event,
                                binding,
                                alternative,
                            ) {
                                pending.extend(
                                    definitions.into_iter().map(|(event, value)| {
                                        (event, value, next_ancestors.clone())
                                    }),
                                );
                                continue;
                            }
                        }
                    }
                    let facts = value_facts;
                    if let Some(held) = &mut returned {
                        join_variant_bounds(held, &facts);
                    } else {
                        returned = Some(facts);
                    }
                }
            }
        }
        returned.unwrap_or_default()
    }

    /// Must-known enum constructors in owned storage. This staged table uses
    /// actual write/outcome summaries, never callee restoration alone.
    /// Borrowed writes require one exact concrete referent from loan snapshots.
    #[cfg(test)]
    pub fn variant_facts(&self, body: &Body) -> Vec<Option<HashMap<Place, VariantId>>> {
        self.variant_facts_with_origins(body, &self.loan_origins(body))
    }

    #[cfg(test)]
    fn variant_facts_with_origins(
        &self,
        body: &Body,
        origins: &FlowLoanOrigins,
    ) -> Vec<Option<HashMap<Place, VariantId>>> {
        let refinements = self.call_result_refinements(body);
        let mut dependencies = vec![Vec::new(); self.nodes.len()];
        let mut snapshot_users = vec![Vec::new(); self.nodes.len()];
        for (index, node) in self.nodes.iter().enumerate() {
            let value = match node.action {
                FlowAction::Bind { value, .. }
                | FlowAction::Assign { value, .. }
                | FlowAction::Pattern { value, .. }
                | FlowAction::Write { value, .. } => value,
                _ => continue,
            };
            dependencies[index] = self.variant_snapshot_dependencies(body, origins, value);
            dependencies[index].retain(|event| event.0 != index);
            for event in &dependencies[index] {
                snapshot_users[event.0].push(FlowNodeId(index));
            }
        }
        let mut before = vec![None; self.nodes.len()];
        before[self.entry.0] = Some(HashMap::new());
        let mut pending = VecDeque::from([self.entry]);
        let mut queued = vec![false; self.nodes.len()];
        queued[self.entry.0] = true;
        while let Some(event) = pending.pop_front() {
            queued[event.0] = false;
            if dependencies[event.0]
                .iter()
                .any(|source| before[source.0].is_none())
            {
                continue;
            }
            let mut state = before[event.0].as_ref().unwrap().clone();
            let node = &self.nodes[event.0];
            match &node.action {
                FlowAction::Pattern { pattern, value } => {
                    if let Some((calls, variant, region)) = &refinements[event.0] {
                        let stores = joined_call_variant_stores(
                            body,
                            self,
                            LoanSnapshots::new(&origins.before, &origins.events_by_value),
                            calls,
                            *variant,
                        );
                        for store in stores {
                            let destination = store.destination.referent_place();
                            if region.iter().any(|event| match &self.nodes[event.0].action {
                                FlowAction::Assign { place, .. } | FlowAction::Release { place, .. } =>
                                    place.root == destination.root || matches!(destination.root, PlaceRoot::Parameter(_)),
                                FlowAction::ScopeExit(bindings) => matches!(destination.root,
                                    PlaceRoot::Local(binding) | PlaceRoot::Parameter(binding) if bindings.contains(&binding)),
                                _ => false,
                            }) {
                                continue;
                            }
                            apply_store_variant_facts(&mut state, &store);
                        }
                    }
                    if let (Some(variant), Some(place)) = (
                        constructor_variant_at_storage(body, *pattern, &[]),
                        Place::from_expression(body, *value),
                    ) {
                        // A successful arm establishes the discriminant of
                        // this owned place, not merely its constructor syntax.
                        // Do not invent facts for computed or aliased targets.
                        if !place.segments.iter().any(|segment| {
                            matches!(segment, Segment::DynamicIndex | Segment::SliceDynamicIndex)
                        }) && !matches!(
                            body.nodes[value.0].ty,
                            Some(
                                Type::Reference { .. }
                                    | Type::PinnedReference { .. }
                                    | Type::RawPointer { .. }
                            )
                        ) {
                            state.insert(place, variant);
                        }
                    }
                    let incoming = value_variant_facts(
                        body,
                        *value,
                        &state,
                        Some((self, origins, event, &before)),
                    );
                    distribute_pattern_variants(body, *pattern, &incoming, &mut state);
                }
                FlowAction::Bind { binding, value } => {
                    let target = Place::root(PlaceRoot::Local(*binding));
                    let incoming = value_variant_facts(
                        body,
                        *value,
                        &state,
                        Some((self, origins, event, &before)),
                    );
                    state.retain(|place, _| !target.overlaps(place));
                    for (mut place, variant) in incoming {
                        place.root = target.root.clone();
                        state.insert(place, variant);
                    }
                }
                FlowAction::Assign {
                    place: target,
                    value,
                } => {
                    if matches!(target.root, PlaceRoot::Local(binding)
                        if matches!(body.bindings[binding.0].ty,
                            Type::Reference { .. } | Type::PinnedReference { .. }))
                    {
                        state.clear();
                    } else {
                        let incoming = value_variant_facts(
                            body,
                            *value,
                            &state,
                            Some((self, origins, event, &before)),
                        );
                        state.retain(|place, _| !target.overlaps(place));
                        if !target.segments.iter().any(|segment| {
                            matches!(segment, Segment::DynamicIndex | Segment::SliceDynamicIndex)
                        }) {
                            for (place, variant) in incoming {
                                let mut destination = target.clone();
                                destination.segments.extend(place.segments);
                                state.insert(destination, variant);
                            }
                        }
                    }
                }
                FlowAction::Release { place: target, .. } => {
                    state.retain(|place, _| !target.overlaps(place));
                    if let PlaceRoot::Local(binding) = target.root {
                        for referent in
                            origins.projected_referents(event, binding, &target.segments)
                        {
                            state.retain(|place, _| !referent.overlaps(place));
                        }
                    }
                }
                FlowAction::ScopeExit(bindings) => {
                    state.retain(|place, _| {
                        !matches!(place.root,
                        PlaceRoot::Local(binding) if bindings.contains(&binding))
                    });
                }
                FlowAction::Write { value, .. } | FlowAction::Evaluate(value)
                    if matches!(&body.nodes[value.0].kind, NodeKind::Form { head, children, .. }
                        if (matches!(head.as_str(), "deref-set" | "pin-write") && children.len() == 3)
                            || (head == "pin-set-field" && children.len() == 4)) =>
                {
                    let NodeKind::Form { head, children, .. } = &body.nodes[value.0].kind else {
                        unreachable!()
                    };
                    let mut targets = origins.value_before(body, self, event, children[1]);
                    let source = if head == "pin-set-field" {
                        let NodeKind::Declaration(DeclarationId::Field(field)) =
                            body.nodes[children[2].0].kind
                        else {
                            unreachable!()
                        };
                        for target in &mut targets {
                            target.place.segments.push(Segment::Field(field));
                        }
                        children[3]
                    } else {
                        children[2]
                    };
                    if one_concrete_store_destination(&targets) {
                        let target = targets[0].referent_place();
                        let incoming = value_variant_facts(
                            body,
                            source,
                            &state,
                            Some((self, origins, event, &before)),
                        );
                        state.retain(|place, _| !target.overlaps(place));
                        for (place, variant) in incoming {
                            let mut destination = target.clone();
                            destination.segments.extend(place.segments);
                            state.insert(destination, variant);
                        }
                    } else {
                        state.clear();
                    }
                }
                FlowAction::Write { .. } => state.clear(),
                FlowAction::Evaluate(value)
                    if matches!(&body.nodes[value.0].kind,
                    NodeKind::Form { head, .. } if head == "pin-read") =>
                {
                    state.clear()
                }
                FlowAction::Evaluate(value)
                    if matches!(
                        &body.nodes[value.0].kind,
                        NodeKind::Form {
                            callee: Some(_),
                            ..
                        }
                    ) =>
                {
                    state.clear();
                    for store in origins.stores_before(body, self, event) {
                        apply_store_variant_facts(&mut state, &store);
                    }
                }
                FlowAction::Evaluate(value)
                    if matches!(&body.nodes[value.0].kind,
                        NodeKind::Form { head, .. } if matches!(head.as_str(), "ptr-write" | "linux-syscall")) =>
                {
                    // Raw or kernel writes may alias any previously known tag.
                    state.clear();
                }
                _ => {}
            }
            for successor in &node.successors {
                let changed = match &mut before[successor.0] {
                    None => {
                        before[successor.0] = Some(state.clone());
                        true
                    }
                    Some(previous) => {
                        let count = previous.len();
                        previous.retain(|place, variant| state.get(place) == Some(variant));
                        previous.len() != count
                    }
                };
                if changed && !queued[successor.0] {
                    queued[successor.0] = true;
                    pending.push_back(*successor);
                }
                if changed {
                    for user in &snapshot_users[successor.0] {
                        if before[user.0].is_some() && !queued[user.0] {
                            queued[user.0] = true;
                            pending.push_back(*user);
                        }
                    }
                }
            }
        }
        before
    }

    #[cfg(test)]
    fn variant_snapshot_dependencies(
        &self,
        body: &Body,
        origins: &FlowLoanOrigins,
        value: NodeId,
    ) -> Vec<FlowNodeId> {
        let mut pending = vec![value];
        let mut seen = HashSet::new();
        let mut events = HashSet::new();
        while let Some(value) = pending.pop() {
            if !seen.insert(value) {
                continue;
            }
            for index in &origins.events_by_value[value.0] {
                if origins.before[*index].is_some()
                    && matches!(self.nodes[*index].action,
                    FlowAction::Evaluate(found) | FlowAction::Read { value: found, .. }
                    | FlowAction::Clone { value: found, .. } | FlowAction::Borrow { value: found, .. } if found == value)
                {
                    events.insert(FlowNodeId(*index));
                }
            }
            match &body.nodes[value.0].kind {
                NodeKind::Form { children, .. } => pending.extend(children.iter().copied()),
                NodeKind::If {
                    then_value,
                    else_value,
                    ..
                } => {
                    pending.push(*then_value);
                    pending.extend(*else_value);
                }
                NodeKind::Match { arms, .. } => pending.extend(arms.iter().copied()),
                NodeKind::MatchArm { values, .. } => pending.extend(values.last().copied()),
                NodeKind::Block(instructions) => {
                    if let Some(Control::Evaluate(value)) =
                        instructions.last().map(|instruction| &instruction.control)
                    {
                        pending.push(*value);
                    }
                }
                NodeKind::Loop(_) => {
                    for node in &self.nodes {
                        if let FlowAction::Break {
                            value: Some(source),
                            result: Some(result),
                        } = node.action
                        {
                            if result == value {
                                pending.push(source);
                            }
                        }
                    }
                }
                NodeKind::Labeled(_, inner) => pending.push(*inner),
                _ => {}
            }
        }
        let mut events = events.into_iter().collect::<Vec<_>>();
        events.sort_by_key(|event| event.0);
        events
    }

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
        #[cfg(test)]
        {
            if body.staged_parameter_contents {
                self.solve_loan_origins(body, true, true, true)
            } else {
                self.solve_loan_origins(body, false, false, false)
            }
        }
        #[cfg(not(test))]
        {
            self.solve_loan_origins(body)
        }
    }

    /// May-store experiment. Not a production replacement until conditional
    /// clearing and definite storage restoration are established.
    #[cfg(test)]
    pub fn staged_store_loan_origins(&self, body: &Body) -> FlowLoanOrigins {
        self.solve_loan_origins(body, true, false, false)
    }

    /// Refine direct call results only while their destination contents are
    /// still the contents written by that call. This remains test-only.
    #[cfg(test)]
    pub fn staged_variant_store_loan_origins(&self, body: &Body) -> FlowLoanOrigins {
        self.solve_loan_origins(body, true, true, false)
    }

    #[cfg(test)]
    /// Actual pointee contents experiment, not an initialization/restoration
    /// proof or a production replacement for interprocedural return checking.
    pub fn staged_parameter_store_loan_origins(&self, body: &Body) -> FlowLoanOrigins {
        self.solve_loan_origins(body, true, true, true)
    }

    /// Task captures remain borrowed until their linear handle is consumed,
    /// even when the handle has no future reads. Ordinary reference NLL is not
    /// sufficient for an independently running worker.
    #[cfg(test)]
    pub fn check_pending_task_loans(
        &self,
        body: &Body,
        types: &LinearTypes,
        origins: &FlowLoanOrigins,
        call_reads: &[ReferentRead],
        consuming_accesses: &[ReferentRead],
    ) -> Result<(), ReleaseConflict> {
        if !origins.before.iter().flatten().any(|state| {
            state.iter().flatten().any(|loan| {
                loan.storage
                    .iter()
                    .any(|slot| matches!(slot, Segment::ThreadCapture(_, _)))
            })
        }) {
            return Ok(());
        }
        let active = self.active_bindings_before(body);
        let moves = self.consumptions_with_origins(body, types, Some(origins));
        for (index, node) in self.nodes.iter().enumerate() {
            let event = FlowNodeId(index);
            let Some(bindings) = &active[index] else {
                continue;
            };
            let Some(consumed) = &moves.definitely_before[index] else {
                continue;
            };
            let mut accesses = Vec::new();
            let resolve = |place: &Place| {
                if let PlaceRoot::Local(binding) = place.root {
                    let projected = origins.projected_referents(event, binding, &place.segments);
                    if !projected.is_empty() {
                        return projected;
                    }
                }
                vec![place.clone()]
            };
            match &node.action {
                FlowAction::Read {
                    value,
                    place,
                    place_base: false,
                } => {
                    let exclusive = body.nodes[value.0]
                        .ty
                        .as_ref()
                        .is_some_and(|ty| types.is_linear(ty));
                    accesses.extend(
                        resolve(place)
                            .into_iter()
                            .map(|place| (place, exclusive, node.span)),
                    );
                }
                FlowAction::Clone { place, .. } => {
                    accesses.extend(
                        resolve(place)
                            .into_iter()
                            .map(|place| (place, false, node.span)),
                    );
                }
                FlowAction::Borrow { place, mutable, .. } => {
                    accesses.extend(
                        resolve(place)
                            .into_iter()
                            .map(|place| (place, *mutable, node.span)),
                    );
                }
                FlowAction::Release { place, value } => {
                    let exclusive = release_operand_is_linear(body, *value, types);
                    accesses.extend(
                        resolve(place)
                            .into_iter()
                            .map(|place| (place, exclusive, node.span)),
                    );
                }
                FlowAction::Assign { place, .. } => {
                    accesses.extend(
                        resolve(place)
                            .into_iter()
                            .map(|place| (place, true, node.span)),
                    );
                }
                _ => {}
            }
            for store in origins.stores_before(body, self, event) {
                accesses.push((store.destination.referent_place(), true, node.span));
            }
            if let FlowAction::Evaluate(value) = node.action {
                // Acquiring another task capture conflicts even if its worker
                // never actually reads or writes the captured referent.
                if matches!(
                    body.nodes[value.0].kind,
                    NodeKind::Form {
                        callee: Some(_),
                        ..
                    }
                ) {
                    for loan in origins.value_before(body, self, event, value) {
                        if loan
                            .storage
                            .iter()
                            .any(|slot| matches!(slot, Segment::ThreadCapture(_, _)))
                        {
                            accesses.push((loan.referent_place(), loan.mutable, node.span));
                        }
                    }
                }
                if let Some(state) = &origins.before[index] {
                    for clear in call_parameter_clears(
                        body,
                        self,
                        LoanSnapshots::new(&origins.before, &origins.events_by_value),
                        value,
                        state,
                    ) {
                        accesses.push((clear.referent_place(), true, node.span));
                    }
                }
            }
            for (reads, exclusive) in [(call_reads, false), (consuming_accesses, true)] {
                for read in reads.iter().filter(|read| read.event == event) {
                    accesses.push((read.place.clone(), exclusive, node.span.or(read.span)));
                }
            }
            for binding in bindings {
                for loan in origins.before(event, *binding) {
                    let Some(capture) = loan
                        .storage
                        .iter()
                        .position(|slot| matches!(slot, Segment::ThreadCapture(_, _)))
                    else {
                        continue;
                    };
                    let holder = Place {
                        root: PlaceRoot::Local(*binding),
                        segments: loan.storage[..capture].to_vec(),
                    };
                    if consumed.iter().any(|place| place_covers(place, &holder)) {
                        continue;
                    }
                    let referent = loan.referent_place();
                    for (place, exclusive, span) in &accesses {
                        if referent.overlaps(place)
                            && (*exclusive || (loan.mutable && !loan.lifetime_only))
                        {
                            return Err(ReleaseConflict {
                                message: format!(
                                    "cannot access `{}` while pending task `{}` holds a {} borrow",
                                    display_linear_place(body, place),
                                    body.bindings[binding.0].name,
                                    if loan.mutable { "mutable" } else { "shared" }
                                ),
                                span: *span,
                                labels: loan
                                    .span
                                    .into_iter()
                                    .map(|span| (span, "borrow retained by pending task".into()))
                                    .collect(),
                            });
                        }
                    }
                }
            }
        }
        Ok(())
    }

    #[cfg(test)]
    fn call_result_refinements(&self, body: &Body) -> Vec<Option<CallResultRefinement>> {
        let reachable = self.reachable();
        let mut predecessors = vec![Vec::new(); self.nodes.len()];
        for event in &reachable {
            for successor in &self.nodes[event.0].successors {
                predecessors[successor.0].push(*event);
            }
        }
        self.nodes
            .iter()
            .enumerate()
            .map(|(index, node)| {
                let FlowAction::Pattern { pattern, value } = node.action else {
                    return None;
                };
                let variant = constructor_variant_at_storage(body, pattern, &[])?;
                let sources =
                    self.call_result_producers(body, value, FlowNodeId(index), &predecessors)?;
                let mut calls = Vec::new();
                for (call, path) in sources {
                    let NodeKind::Form {
                        callee: Some(callee),
                        ..
                    } = &body.nodes[call.0].kind
                    else {
                        return None;
                    };
                    // A checked ownership outcome is also a valid source of
                    // result correlation for bodyless compiler operations.
                    // It does not manufacture reference-storage transfers.
                    if !path.is_empty() {
                        if !body
                            .call_output_variant_exits
                            .borrow()
                            .get(callee)
                            .is_some_and(|groups| groups.contains_key(&(path.clone(), variant)))
                        {
                            return None;
                        }
                    } else if body
                        .call_store_variants
                        .get(callee)
                        .and_then(|variants| variants.get(&variant))
                        .is_none()
                        && body
                            .call_variant_exits
                            .borrow()
                            .get(callee)
                            .and_then(|variants| variants.get(&variant))
                            .is_none()
                    {
                        return None;
                    }
                    let mut evaluations =
                        self.nodes.iter().enumerate().filter_map(|(index, node)| {
                            matches!(node.action, FlowAction::Evaluate(found) if found == call)
                                .then_some(FlowNodeId(index))
                        });
                    let call_event = evaluations.next()?;
                    if evaluations.next().is_some() {
                        return None;
                    }
                    calls.push((call_event, call, path));
                }
                // Different alternatives must be mutually exclusive. A later
                // call's variant is not determined by matching an earlier one.
                if calls.len() > 1 {
                    for (event, _, _) in &calls {
                        let mut pending = self.nodes[event.0].successors.clone();
                        let mut visited = HashSet::new();
                        while let Some(next) = pending.pop() {
                            if next == FlowNodeId(index) {
                                continue;
                            }
                            if calls.iter().any(|(event, _, _)| *event == next) {
                                return None;
                            }
                            if visited.insert(next) {
                                pending.extend(self.nodes[next.0].successors.iter().copied());
                            }
                        }
                    }
                }
                let mut pending = predecessors[index].clone();
                let mut visited = HashSet::new();
                let mut region = Vec::new();
                let mut reached_call = false;
                while let Some(event) = pending.pop() {
                    if calls.iter().any(|(call_event, _, _)| event == *call_event) {
                        reached_call = true;
                        continue;
                    }
                    if !visited.insert(event) {
                        continue;
                    }
                    // Do not classify effects by builtin spelling here. Until
                    // every form has an effect contract, non-constructor form
                    // evaluation can invalidate the storage correlation.
                    match &self.nodes[event.0].action {
                        FlowAction::Entry | FlowAction::Write { .. } => return None,
                        FlowAction::Evaluate(value) => {
                            if let NodeKind::Form { children, .. } = &body.nodes[value.0].kind {
                                // Constructor evaluation is pure; operand
                                // effects have their own graph events.
                                if !matches!(
                                    children.first().map(|id| &body.nodes[id.0].kind),
                                    Some(NodeKind::Declaration(
                                        DeclarationId::Variant(_) | DeclarationId::Aggregate(_)
                                    ))
                                ) && owned_output_projection(body, *value).is_none()
                                {
                                    return None;
                                }
                            }
                        }
                        _ => {}
                    }
                    region.push(event);
                    pending.extend(predecessors[event.0].iter().copied());
                }
                reached_call.then_some((calls, variant, region))
            })
            .collect()
    }

    #[cfg(test)]
    fn call_result_sources(
        &self,
        body: &Body,
        value: NodeId,
        use_event: FlowNodeId,
        predecessors: &[Vec<FlowNodeId>],
    ) -> Option<Vec<NodeId>> {
        self.call_result_producers(body, value, use_event, predecessors)?
            .into_iter()
            .map(|(call, path)| path.is_empty().then_some(call))
            .collect()
    }

    /// Identify an actual call and the owned output storage selected from it.
    /// Nonempty paths are not interchangeable with root outcome contracts.
    #[cfg(test)]
    fn call_result_producers(
        &self,
        body: &Body,
        value: NodeId,
        use_event: FlowNodeId,
        predecessors: &[Vec<FlowNodeId>],
    ) -> Option<Vec<(NodeId, Vec<Segment>)>> {
        let reachable = self.reachable();
        let mut pending_values = vec![(value, use_event, Vec::new(), Vec::new())];
        let mut calls = Vec::new();
        while let Some((value, use_event, mut bindings, mut path)) = pending_values.pop() {
            // Reference handles do not have their referent's owned output
            // layout. Following them needs a separate provenance proof.
            if reads_through_reference(body, value)
                || matches!(
                    body.nodes[value.0].ty.as_ref(),
                    Some(
                        Type::Reference { .. }
                            | Type::PinnedReference { .. }
                            | Type::RawPointer { .. }
                            | Type::Slice(_)
                            | Type::MutableSlice(_)
                    )
                )
            {
                return None;
            }
            if let Some((base, slot)) = owned_output_projection(body, value) {
                path.insert(0, slot);
                pending_values.push((base, use_event, bindings, path));
                continue;
            }
            if matches!(body.nodes[value.0].kind, NodeKind::Loop(_)) {
                let mut found = false;
                for (index, node) in self.nodes.iter().enumerate() {
                    let event = FlowNodeId(index);
                    if !reachable.contains(&event) {
                        continue;
                    }
                    if let FlowAction::Break {
                        value: Some(source),
                        result: Some(result),
                    } = node.action
                    {
                        if result == value {
                            found = true;
                            pending_values.push((source, event, bindings.clone(), path.clone()));
                        }
                    }
                }
                if !found {
                    return None;
                }
                continue;
            }
            let mut alternatives = Vec::new();
            collect_result_alternatives(body, value, &mut alternatives);
            if alternatives.is_empty() {
                return None;
            }
            if alternatives != [value] {
                for alternative in alternatives {
                    let mut evaluations =
                        self.nodes.iter().enumerate().filter_map(|(index, node)| {
                            flow_action_has_value(&node.action, alternative)
                                .then_some(FlowNodeId(index))
                        });
                    let event = evaluations.next()?;
                    if evaluations.next().is_some() {
                        return None;
                    }
                    pending_values.push((alternative, event, bindings.clone(), path.clone()));
                }
                continue;
            }
            if matches!(
                body.nodes[value.0].kind,
                NodeKind::Form {
                    callee: Some(_),
                    ..
                }
            ) {
                let source = (value, path);
                if !calls.contains(&source) {
                    calls.push(source);
                }
                continue;
            }
            let place = Place::from_expression(body, value)?;
            let PlaceRoot::Local(binding) = place.root else {
                return None;
            };
            if place.segments.iter().any(|segment| {
                !matches!(
                    segment,
                    Segment::Field(_)
                        | Segment::Tuple(_)
                        | Segment::Payload(_, _)
                        | Segment::Index(_)
                )
            }) || bindings.contains(&binding)
            {
                return None;
            }
            let mut selected = place.segments;
            selected.append(&mut path);
            path = selected;
            bindings.push(binding);
            let mut definitions =
                self.nodes
                    .iter()
                    .enumerate()
                    .filter_map(|(index, node)| match node.action {
                        FlowAction::Bind {
                            binding: found,
                            value,
                        } if found == binding => Some((FlowNodeId(index), value, Vec::new())),
                        FlowAction::Pattern { pattern, value } => {
                            pattern_binding_path(body, pattern, binding)
                                .map(|path| (FlowNodeId(index), value, path))
                        }
                        _ => None,
                    });
            let (definition, source, mut source_path) = definitions.next()?;
            if definitions.next().is_some() {
                return None;
            }
            let mut pending = predecessors[use_event.0].clone();
            let mut visited = HashSet::new();
            let mut reached_definition = false;
            while let Some(event) = pending.pop() {
                if event == definition {
                    reached_definition = true;
                    continue;
                }
                if !visited.insert(event) {
                    continue;
                }
                match &self.nodes[event.0].action {
                    FlowAction::Entry => return None,
                    FlowAction::Assign { place, .. } | FlowAction::Release { place, .. }
                        if place.root == PlaceRoot::Local(binding) =>
                    {
                        return None
                    }
                    FlowAction::ScopeExit(bindings) if bindings.contains(&binding) => return None,
                    _ => {}
                }
                pending.extend(predecessors[event.0].iter().copied());
            }
            if !reached_definition {
                return None;
            }
            source_path.append(&mut path);
            pending_values.push((source, definition, bindings, source_path));
        }
        (!calls.is_empty()).then_some(calls)
    }

    /// Contents destruction proven on every normal return, separately from
    /// writes and initialization. Unknown effects invalidate prior proofs.
    #[cfg(test)]
    pub fn parameter_clear_summaries(
        &self,
        body: &Body,
        origins: &FlowLoanOrigins,
    ) -> Vec<crate::typed_body::ParameterLoanSummary> {
        let clears = (0..self.nodes.len())
            .map(|index| origins.clears_before(body, self, FlowNodeId(index)))
            .collect::<Vec<_>>();
        let stores = (0..self.nodes.len())
            .map(|index| origins.stores_before(body, self, FlowNodeId(index)))
            .collect::<Vec<_>>();
        let mut candidates = Vec::new();
        for clear in clears.iter().flatten() {
            let Some(summary) = clear.parameter_summary() else {
                continue;
            };
            let place = clear.referent_place();
            if !candidates.iter().any(|(known, _)| *known == place) {
                candidates.push((place, summary));
            }
        }
        if candidates.is_empty() {
            return Vec::new();
        }
        let mut before = vec![None; self.nodes.len()];
        before[self.entry.0] = Some(vec![false; candidates.len()]);
        let mut pending = VecDeque::from([self.entry]);
        let mut queued = vec![false; self.nodes.len()];
        queued[self.entry.0] = true;
        while let Some(event) = pending.pop_front() {
            queued[event.0] = false;
            let mut state = before[event.0].as_ref().unwrap().clone();
            // Calls may restore storage through aliases. Their proved final
            // clears are applied below, but prior clears are not preserved.
            let invalidates = match self.nodes[event.0].action {
                FlowAction::Evaluate(value) => match &body.nodes[value.0].kind {
                    NodeKind::Form {
                        head,
                        children,
                        callee,
                        numeric,
                        ..
                    } => {
                        callee.is_some()
                            || (numeric.is_none()
                                && !matches!(
                                    head.as_str(),
                                    "forget"
                                        | "drop"
                                        | "pin-read"
                                        | "pin-write"
                                        | "pin-set-field"
                                        | "deref"
                                        | "deref-set"
                                        | "get"
                                        | "get-payload"
                                        | "index"
                                        | "unsafe"
                                        | "borrow"
                                        | "borrow-mut"
                                        | "pin-borrow"
                                        | "pin-borrow-mut"
                                )
                                && !children.first().is_some_and(|id| {
                                    matches!(
                                        body.nodes[id.0].kind,
                                        NodeKind::Declaration(
                                            DeclarationId::Aggregate(_) | DeclarationId::Variant(_)
                                        )
                                    )
                                }))
                    }
                    _ => false,
                },
                FlowAction::Write { .. } => stores[event.0].is_empty(),
                _ => false,
            };
            if invalidates {
                state.fill(false);
            }
            for store in &stores[event.0] {
                let place = store.destination.referent_place();
                for ((candidate, _), cleared) in candidates.iter().zip(&mut state) {
                    if place.overlaps(candidate) {
                        *cleared = false;
                    }
                }
            }
            for clear in &clears[event.0] {
                let place = clear.referent_place();
                for ((candidate, _), cleared) in candidates.iter().zip(&mut state) {
                    if place_covers(&place, candidate) {
                        *cleared = true;
                    }
                }
            }
            for successor in &self.nodes[event.0].successors {
                let changed = match &mut before[successor.0] {
                    Some(held) => {
                        let mut changed = false;
                        for (held, incoming) in held.iter_mut().zip(&state) {
                            if *held && !incoming {
                                *held = false;
                                changed = true;
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
                    queued[successor.0] = true;
                    pending.push_back(*successor);
                }
            }
        }
        let mut returned: Option<Vec<bool>> = None;
        for (index, node) in self.nodes.iter().enumerate() {
            if !matches!(node.action, FlowAction::Return(_)) {
                continue;
            }
            let Some(state) = &before[index] else {
                continue;
            };
            if let Some(held) = &mut returned {
                for (held, incoming) in held.iter_mut().zip(state) {
                    *held &= incoming;
                }
            } else {
                returned = Some(state.clone());
            }
        }
        candidates
            .into_iter()
            .zip(returned.unwrap_or_default())
            .filter_map(|((_, summary), cleared)| cleared.then_some(summary))
            .collect()
    }

    /// Final reference contents on normal returns. Missing paths retain the
    /// caller's entry contents; every-path writes may replace those contents.
    #[cfg(test)]
    pub fn parameter_store_summaries(
        &self,
        body: &Body,
        origins: &FlowLoanOrigins,
    ) -> Vec<crate::typed_body::ParameterStoreSummary> {
        use crate::typed_body::ParameterStoreSummary;
        let variant_states = self.variant_facts_with_origins(body, origins);
        let events = (0..self.nodes.len())
            .map(|index| {
                let event = FlowNodeId(index);
                let mut stores = origins.stores_before(body, self, event);
                if let (
                    Some(state),
                    FlowAction::Write { value, .. } | FlowAction::Evaluate(value),
                ) = (&variant_states[index], &self.nodes[index].action)
                {
                    if let NodeKind::Form {
                        head,
                        children,
                        callee: None,
                        ..
                    } = &body.nodes[value.0].kind
                    {
                        let source = match (head.as_str(), children.len()) {
                            ("deref-set" | "pin-write", 3) => Some(children[2]),
                            ("pin-set-field", 4) => Some(children[3]),
                            _ => None,
                        };
                        if let Some(source) = source {
                            let variants = value_variant_facts(
                                body,
                                source,
                                state,
                                Some((self, origins, event, &variant_states)),
                            )
                            .into_iter()
                            .map(|(place, variant)| (place.segments, variant))
                            .collect::<HashMap<_, _>>();
                            for store in &mut stores {
                                store.variants = variants.clone();
                            }
                        }
                    }
                }
                stores
            })
            .collect::<Vec<_>>();
        let mut destinations = Vec::new();
        for store in events.iter().flatten() {
            let Some(summary) = store.destination.parameter_summary() else {
                continue;
            };
            let place = store.destination.referent_place();
            if !destinations.iter().any(|(known, _)| *known == place) {
                destinations.push((place, summary));
            }
        }
        if destinations.is_empty() {
            return Vec::new();
        }
        type Contents = Vec<ParameterStoreSummary>;
        let empty = destinations
            .iter()
            .map(|(_, destination)| ParameterStoreSummary {
                destination: destination.clone(),
                sources: Vec::new(),
                definitely_written: false,
                variants: HashMap::new(),
            })
            .collect::<Contents>();
        let merge = |held: &mut Contents, incoming: &Contents| {
            let mut changed = false;
            for (held, incoming) in held.iter_mut().zip(incoming) {
                let count = held.variants.len();
                held.variants
                    .retain(|path, variant| incoming.variants.get(path) == Some(variant));
                changed |= count != held.variants.len();
                if held.definitely_written && !incoming.definitely_written {
                    held.definitely_written = false;
                    changed = true;
                }
                for source in &incoming.sources {
                    if !held.sources.contains(source) {
                        held.sources.push(source.clone());
                        changed = true;
                    }
                }
            }
            changed
        };
        let mut before = vec![None; self.nodes.len()];
        before[self.entry.0] = Some(empty);
        let mut queued = vec![false; self.nodes.len()];
        queued[self.entry.0] = true;
        let mut pending = VecDeque::from([self.entry]);
        while let Some(event) = pending.pop_front() {
            queued[event.0] = false;
            let mut state = before[event.0].as_ref().unwrap().clone();
            for store in &events[event.0] {
                let place = store.destination.referent_place();
                let incoming = store
                    .incoming
                    .iter()
                    .filter_map(LoanOrigin::parameter_summary)
                    .collect::<Vec<_>>();
                for ((candidate, _), held) in destinations.iter().zip(&mut state) {
                    if !place.overlaps(candidate) {
                        continue;
                    }
                    if candidate.segments.len() >= place.segments.len() {
                        let relative = &candidate.segments[place.segments.len()..];
                        let selected_variants = store
                            .variants
                            .iter()
                            .filter_map(|(path, variant)| {
                                path.strip_prefix(relative)
                                    .map(|path| (path.to_vec(), *variant))
                            })
                            .collect::<HashMap<_, _>>();
                        if store.definitely_written {
                            held.variants = selected_variants;
                        } else {
                            held.variants.retain(|path, variant| {
                                selected_variants.get(path) == Some(variant)
                            });
                        }
                        let selected = incoming
                            .iter()
                            .filter_map(|source| {
                                if source.storage.len() < relative.len()
                                    || !relative.iter().zip(&source.storage).all(
                                        |(wanted, actual)| storage_slot_matches(wanted, actual),
                                    )
                                {
                                    return None;
                                }
                                let mut source = source.clone();
                                source.storage.drain(..relative.len());
                                let count = relative.len().min(source.storage_inputs.len());
                                source.storage_inputs.drain(..count);
                                Some(source)
                            })
                            .collect::<Vec<_>>();
                        if store.definitely_written {
                            held.sources.clear();
                            held.definitely_written = true;
                        }
                        for source in selected {
                            if !held.sources.contains(&source) {
                                held.sources.push(source);
                            }
                        }
                    } else {
                        let relative = &place.segments[candidate.segments.len()..];
                        let target = Place {
                            root: candidate.root.clone(),
                            segments: relative.to_vec(),
                        };
                        held.variants.retain(|path, _| {
                            !target.overlaps(&Place {
                                root: candidate.root.clone(),
                                segments: path.clone(),
                            })
                        });
                        if store.definitely_written {
                            for (path, variant) in &store.variants {
                                let mut selected = relative.to_vec();
                                selected.extend_from_slice(path);
                                held.variants.insert(selected, *variant);
                            }
                        }
                        if store.definitely_written {
                            held.sources
                                .retain(|source| !source.storage.starts_with(relative));
                        }
                        for source in &incoming {
                            let mut source = source.clone();
                            let mut storage = relative.to_vec();
                            storage.append(&mut source.storage);
                            source.storage = storage;
                            let mut inputs = vec![None; relative.len()];
                            inputs.append(&mut source.storage_inputs);
                            source.storage_inputs = inputs;
                            if !held.sources.contains(&source) {
                                held.sources.push(source);
                            }
                        }
                    }
                }
            }
            for successor in &self.nodes[event.0].successors {
                let changed = match &mut before[successor.0] {
                    Some(held) => merge(held, &state),
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
        let mut returned = None;
        for (index, node) in self.nodes.iter().enumerate() {
            if !matches!(node.action, FlowAction::Return(_)) {
                continue;
            }
            let Some(state) = &before[index] else {
                continue;
            };
            match &mut returned {
                Some(held) => {
                    merge(held, state);
                }
                slot @ None => {
                    *slot = Some(state.clone());
                }
            }
        }
        returned.unwrap_or_default()
    }

    /// Conditional final contents for explicit returned enum constructors.
    /// Unknown return values remain possible for every selected variant.
    /// Original event IDs and all writes after construction are preserved.
    #[cfg(test)]
    pub fn parameter_store_variant_summaries(
        &self,
        body: &Body,
        origins: &FlowLoanOrigins,
    ) -> HashMap<VariantId, Vec<crate::typed_body::ParameterStoreSummary>> {
        self.return_variant_graphs(body)
            .into_iter()
            .map(|(variant, filtered)| (variant, filtered.parameter_store_summaries(body, origins)))
            .collect()
    }

    #[cfg(test)]
    pub fn parameter_output_store_variant_summaries(
        &self,
        body: &Body,
        origins: &FlowLoanOrigins,
    ) -> HashMap<(Vec<Segment>, VariantId), Vec<crate::typed_body::ParameterStoreSummary>> {
        self.return_output_variant_graphs(body)
            .into_iter()
            .map(|(selector, graph)| (selector, graph.parameter_store_summaries(body, origins)))
            .collect()
    }

    #[cfg(test)]
    pub fn parameter_output_clear_variant_summaries(
        &self,
        body: &Body,
        origins: &FlowLoanOrigins,
    ) -> HashMap<(Vec<Segment>, VariantId), Vec<crate::typed_body::ParameterLoanSummary>> {
        self.return_output_variant_graphs(body)
            .into_iter()
            .map(|(selector, graph)| (selector, graph.parameter_clear_summaries(body, origins)))
            .collect()
    }

    /// Remove only incompatible explicit constructors. Unknown alternatives
    /// remain possible for every selected variant; event IDs stay unchanged.
    #[cfg(test)]
    fn return_variant_graphs(&self, body: &Body) -> HashMap<VariantId, Self> {
        self.return_output_variant_graphs(body)
            .into_iter()
            .filter_map(|((path, variant), graph)| path.is_empty().then_some((variant, graph)))
            .collect()
    }

    #[cfg(test)]
    fn return_output_variant_graphs(
        &self,
        body: &Body,
    ) -> HashMap<(Vec<Segment>, VariantId), Self> {
        let origins = self.staged_parameter_store_loan_origins(body);
        let states = self.variant_facts_with_origins(body, &origins);
        let mut alternatives = Vec::new();
        for node in &self.nodes {
            if let FlowAction::Return(Some(value)) = node.action {
                collect_result_alternatives(body, value, &mut alternatives);
            }
        }
        // Loop result values live at break events rather than at the loop's
        // merged evaluation node. Include nested loop alternatives without
        // inventing a result for a loop with no reachable value break.
        let mut visited = HashSet::new();
        let mut constructors = HashMap::new();
        while let Some(value) = alternatives.pop() {
            if !visited.insert(value) {
                continue;
            }
            if matches!(body.nodes[value.0].kind, NodeKind::Loop(_)) {
                for node in &self.nodes {
                    if let FlowAction::Break {
                        value: Some(break_value),
                        result: Some(result),
                    } = node.action
                    {
                        if result == value {
                            collect_result_alternatives(body, break_value, &mut alternatives);
                        }
                    }
                }
            } else {
                let mut observed: Option<HashMap<Place, VariantId>> = None;
                for index in &origins.events_by_value[value.0] {
                    if !matches!(self.nodes[*index].action,
                        FlowAction::Read { value: found, .. } | FlowAction::Evaluate(found)
                        | FlowAction::Clone { value: found, .. } if found == value)
                    {
                        continue;
                    }
                    let Some(state) = &states[*index] else {
                        continue;
                    };
                    let facts = value_variant_facts(
                        body,
                        value,
                        state,
                        Some((self, &origins, FlowNodeId(*index), &states)),
                    );
                    if let Some(held) = &mut observed {
                        held.retain(|place, variant| facts.get(place) == Some(variant));
                    } else {
                        observed = Some(facts);
                    }
                }
                let variants = observed
                    .unwrap_or_else(|| value_variant_facts(body, value, &HashMap::new(), None))
                    .into_iter()
                    .map(|(place, variant)| (place.segments, variant))
                    .collect::<HashMap<_, _>>();
                if !variants.is_empty() {
                    constructors.insert(value, variants);
                }
            }
        }
        let variants = constructors
            .values()
            .flat_map(|facts| facts.iter().map(|(path, variant)| (path.clone(), *variant)))
            .collect::<HashSet<_>>();
        let mut result = HashMap::new();
        for selected in variants {
            let mut filtered = self.clone();
            for node in &mut filtered.nodes {
                if constructors.iter().any(|(value, facts)| {
                    facts
                        .get(&selected.0)
                        .is_some_and(|variant| *variant != selected.1)
                        && flow_action_has_value(&node.action, *value)
                }) {
                    node.successors.clear();
                }
            }
            result.insert(selected, filtered);
        }
        result
    }

    fn solve_loan_origins(
        &self,
        body: &Body,
        #[cfg(test)] include_call_stores: bool,
        #[cfg(test)] include_variant_stores: bool,
        #[cfg(test)] include_parameter_contents: bool,
    ) -> FlowLoanOrigins {
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
                if result != value {
                    events_by_value[result.0].push(index);
                }
            }
        }
        // Dense value IDs let every consumer reuse one visitation table.
        // The event index plus one is a unique, nonzero traversal stamp.
        let mut dependency_stamps = vec![0; body.nodes.len()];
        let mut dependencies = Vec::new();
        let mut pending_values = Vec::new();
        for (consumer_index, consumer) in self.nodes.iter().enumerate() {
            let value = match consumer.action {
                FlowAction::Bind { value, .. }
                | FlowAction::Assign { value, .. }
                | FlowAction::Pattern { value, .. }
                | FlowAction::Write { value, .. } => value,
                #[cfg(test)]
                FlowAction::Evaluate(value)
                    if include_call_stores
                        && matches!(
                            &body.nodes[value.0].kind,
                            NodeKind::Form {
                                callee: Some(_),
                                ..
                            }
                        ) =>
                {
                    value
                }
                _ => continue,
            };
            dependencies.clear();
            pending_values.push(value);
            while let Some(value) = pending_values.pop() {
                if dependency_stamps[value.0] == consumer_index + 1 {
                    continue;
                }
                dependency_stamps[value.0] = consumer_index + 1;
                dependencies.push(value);
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
            for value in &dependencies {
                for event_index in &events_by_value[value.0] {
                    snapshot_users[*event_index].push(FlowNodeId(consumer_index));
                }
            }
        }
        #[cfg(test)]
        let refinements = if include_variant_stores {
            self.call_result_refinements(body)
        } else {
            vec![None; self.nodes.len()]
        };
        #[cfg(test)]
        for (event, refinement) in refinements.iter().enumerate() {
            if let Some((calls, _, _)) = refinement {
                for (call_event, _, _) in calls {
                    snapshot_users[call_event.0].push(FlowNodeId(event));
                }
            }
        }
        let mut empty = empty_loan_state(body.bindings.len());
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
                    storage_inputs: (0..slot.storage.len()).map(Some).collect(),
                    lifetime_only: false,
                });
            }
        }
        #[cfg(test)]
        if include_parameter_contents {
            empty.parameter_contents = Some(seed_parameter_contents(body));
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
            #[cfg(test)]
            if include_parameter_contents {
                let released = match self.nodes[id.0].action {
                    FlowAction::Release { value, .. } | FlowAction::Evaluate(value)
                        if body.consuming_releases.contains(&value) =>
                    {
                        Some(value)
                    }
                    _ => None,
                };
                if let Some(value) = released {
                    let NodeKind::Form { children, .. } = &body.nodes[value.0].kind else {
                        unreachable!()
                    };
                    let destinations = released_reference_destinations(
                        body,
                        self,
                        LoanSnapshots::new(&before, &events_by_value),
                        children[1],
                        &state,
                    );
                    if one_concrete_store_destination(&destinations) {
                        for destination in destinations {
                            store_parameter_contents(&mut state, &destination, Vec::new(), true);
                        }
                    }
                }
            }
            match &self.nodes[id.0].action {
                FlowAction::Bind { binding, value } => {
                    state[binding.0] = value_loan_origins_at_events(
                        body,
                        self,
                        LoanSnapshots::new(&before, &events_by_value),
                        *value,
                        &state,
                    );
                }
                FlowAction::Pattern { pattern, value } => {
                    #[cfg(test)]
                    if let Some((calls, variant, region)) = &refinements[id.0] {
                        // Clear old reference contents before installing the
                        // completed worker's replacement contents.
                        if include_parameter_contents {
                            for clear in correlated_call_variant_clears(
                                body,
                                self,
                                LoanSnapshots::new(&before, &events_by_value),
                                refinements[id.0].as_ref().unwrap(),
                            ) {
                                store_parameter_contents(&mut state, &clear, Vec::new(), true);
                                if let PlaceRoot::Local(binding) = clear.place.root {
                                    replace_projected_origins(
                                        &mut state[binding.0],
                                        &clear.place.segments,
                                        Vec::new(),
                                    );
                                }
                            }
                        }
                        for store in joined_call_variant_stores(
                            body,
                            self,
                            LoanSnapshots::new(&before, &events_by_value),
                            calls,
                            *variant,
                        ) {
                            if store.destination.lifetime_only
                                || region
                                    .iter()
                                    .any(|event| match &self.nodes[event.0].action {
                                        FlowAction::Assign { place, .. }
                                        | FlowAction::Release { place, .. } => {
                                            place.root == store.destination.place.root
                                                || matches!(
                                                    store.destination.place.root,
                                                    PlaceRoot::Parameter(_)
                                                )
                                        }
                                        FlowAction::ScopeExit(bindings) => {
                                            match store.destination.place.root {
                                                PlaceRoot::Local(target)
                                                | PlaceRoot::Parameter(target) => {
                                                    bindings.contains(&target)
                                                }
                                                _ => true,
                                            }
                                        }
                                        _ => false,
                                    })
                            {
                                continue;
                            }
                            if include_parameter_contents {
                                store_parameter_contents(
                                    &mut state,
                                    &store.destination,
                                    store.incoming.clone(),
                                    store.definitely_written,
                                );
                            }
                            if let PlaceRoot::Local(target) = store.destination.place.root {
                                if store.definitely_written {
                                    replace_projected_origins(
                                        &mut state[target.0],
                                        &store.destination.place.segments,
                                        store.incoming,
                                    );
                                } else {
                                    extend_projected_origins(
                                        &mut state[target.0],
                                        &store.destination.place.segments,
                                        store.incoming,
                                    );
                                }
                            }
                        }
                    }
                    let origins = value_loan_origins_at_events(
                        body,
                        self,
                        LoanSnapshots::new(&before, &events_by_value),
                        *value,
                        &state,
                    );
                    distribute_pattern_origins(body, *pattern, &origins, &mut state);
                    if let (Some(place), Some(selected)) = (
                        Place::from_expression(body, *value),
                        origins_selected_by_variant(body, *pattern, &origins),
                    ) {
                        if let PlaceRoot::Local(binding) = place.root {
                            // A projected discriminant refines only that
                            // stored enum, not its owner's unrelated slots.
                            // Reference bindings hold addresses, not payloads.
                            if !matches!(
                                body.bindings[binding.0].ty,
                                Type::Reference { .. }
                                    | Type::PinnedReference { .. }
                                    | Type::Slice(_)
                                    | Type::MutableSlice(_)
                            ) && !place.segments.iter().any(|segment| {
                                matches!(
                                    segment,
                                    Segment::Dereference
                                        | Segment::DynamicIndex
                                        | Segment::SliceDynamicIndex
                                )
                            }) {
                                replace_projected_origins(
                                    &mut state[binding.0],
                                    &place.segments,
                                    selected,
                                );
                            }
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
                    let incoming = value_loan_origins_at_events(
                        body,
                        self,
                        LoanSnapshots::new(&before, &events_by_value),
                        *value,
                        &state,
                    );
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
                    let incoming = value_loan_origins_at_events(
                        body,
                        self,
                        LoanSnapshots::new(&before, &events_by_value),
                        source,
                        &state,
                    );
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
                                            body,
                                            self,
                                            LoanSnapshots::new(&before, &events_by_value),
                                            target,
                                            snapshot,
                                        ),
                                    );
                                }
                            }
                            origins
                        }
                        NodeKind::Form { head, children, .. }
                            if head == "pin-set-field" && children.len() == 4 =>
                        {
                            let mut origins = value_loan_origins_at_events(
                                body,
                                self,
                                LoanSnapshots::new(&before, &events_by_value),
                                children[1],
                                &state,
                            );
                            if let NodeKind::Declaration(DeclarationId::Field(field)) =
                                body.nodes[children[2].0].kind
                            {
                                for origin in &mut origins {
                                    origin.place.segments.push(Segment::Field(field));
                                }
                            } else {
                                origins.clear();
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
                    #[cfg(test)]
                    let parameter_strong = one_concrete_store_destination(&destinations);
                    for origin in destinations {
                        // Parameter roots describe external pointees, not
                        // the local reference handles indexed by LoanState.
                        if origin.lifetime_only {
                            continue;
                        }
                        #[cfg(test)]
                        store_parameter_contents(
                            &mut state,
                            &origin,
                            incoming.clone(),
                            parameter_strong,
                        );
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
                #[cfg(test)]
                FlowAction::Evaluate(value)
                    if include_parameter_contents
                        && body.consuming_pin_reads.contains(value)
                        && matches!(&body.nodes[value.0].kind,
                            NodeKind::Form { head, children, .. }
                            if head == "pin-read" && children.len() == 2) =>
                {
                    let NodeKind::Form { children, .. } = &body.nodes[value.0].kind else {
                        unreachable!()
                    };
                    let destinations = value_loan_origins_at_events(
                        body,
                        self,
                        LoanSnapshots::new(&before, &events_by_value),
                        children[1],
                        &state,
                    );
                    if one_concrete_store_destination(&destinations) {
                        for destination in destinations {
                            store_parameter_contents(&mut state, &destination, Vec::new(), true);
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
                #[cfg(test)]
                FlowAction::Evaluate(value)
                    if include_call_stores
                        && matches!(
                            &body.nodes[value.0].kind,
                            NodeKind::Form {
                                callee: Some(_),
                                ..
                            }
                        ) =>
                {
                    let clears = if include_parameter_contents {
                        call_parameter_clears(
                            body,
                            self,
                            LoanSnapshots::new(&before, &events_by_value),
                            *value,
                            &state,
                        )
                    } else {
                        Vec::new()
                    };
                    let stores = call_loan_stores(
                        body,
                        self,
                        LoanSnapshots::new(&before, &events_by_value),
                        *value,
                        &state,
                    );
                    for store in stores {
                        if store.destination.lifetime_only {
                            continue;
                        }
                        store_parameter_contents(
                            &mut state,
                            &store.destination,
                            store.incoming.clone(),
                            store.definitely_written,
                        );
                        if let PlaceRoot::Local(binding) = store.destination.place.root {
                            if store.definitely_written {
                                replace_projected_origins(
                                    &mut state[binding.0],
                                    &store.destination.place.segments,
                                    store.incoming,
                                );
                            } else {
                                extend_projected_origins(
                                    &mut state[binding.0],
                                    &store.destination.place.segments,
                                    store.incoming,
                                );
                            }
                        }
                    }
                    for clear in clears {
                        store_parameter_contents(&mut state, &clear, Vec::new(), true);
                        if let PlaceRoot::Local(binding) = clear.place.root {
                            replace_projected_origins(
                                &mut state[binding.0],
                                &clear.place.segments,
                                Vec::new(),
                            );
                        }
                    }
                }
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
        FlowLoanOrigins {
            before,
            after,
            events_by_value,
            #[cfg(test)]
            variants: std::cell::OnceCell::new(),
            #[cfg(test)]
            clear_refinements: if include_parameter_contents {
                refinements
            } else {
                vec![None; self.nodes.len()]
            },
        }
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

    /// Production ownership can already resolve whole local pinned storage.
    /// Projected, parameter, global, ambiguous and anchored targets still
    /// require the full referent-contract migration; never guess their roots.
    pub fn local_pin_accesses(&self, body: &Body, types: &LinearTypes) -> HashMap<NodeId, Place> {
        if !body.nodes.iter().any(|node| matches!(&node.kind,
            NodeKind::Form { head, children, .. }
                if (head == "pin-read" && node.ty.as_ref().is_some_and(|ty| types.is_linear(ty)))
                || (head == "pin-write" && children.get(1).and_then(|id| body.nodes[id.0].ty.as_ref()).is_some_and(|ty|
                    matches!(ty, Type::PinnedReference { target, .. } if types.is_linear(target)))))
        ) { return HashMap::new(); }
        let origins = self.loan_origins(body);
        let mut accesses = HashMap::new();
        for (index, event) in self.nodes.iter().enumerate() {
            let value = match event.action {
                FlowAction::Evaluate(value) | FlowAction::Write { value, .. } => value,
                _ => continue,
            };
            let NodeKind::Form { head, children, .. } = &body.nodes[value.0].kind else {
                continue;
            };
            if !matches!(head.as_str(), "pin-read" | "pin-write") || children.len() < 2 {
                continue;
            }
            let targets = origins.value_before(body, self, FlowNodeId(index), children[1]);
            let Some(first) = targets.first() else {
                continue;
            };
            if !matches!(first.place.root, PlaceRoot::Local(_))
                || targets.iter().any(|target| {
                    target.lifetime_only
                        || !target.storage.is_empty()
                        || !target.place.segments.is_empty()
                        || target.place != first.place
                })
            {
                continue;
            }
            accesses.insert(value, first.place.clone());
        }
        accesses
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
            if let FlowAction::Evaluate(value) = node.action {
                if matches!(&body.nodes[value.0].kind, NodeKind::Form { head, .. } if head == "pin-read")
                {
                    let places = dereferenced_value_places(body, self, event, value, &origins)
                        .unwrap_or_default();
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
                    continue;
                }
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
            let places = dereferenced_value_places(body, self, event, *value, &origins)
                .unwrap_or_else(|| match &place.root {
                    PlaceRoot::Local(binding)
                        if !origins
                            .before(event, *binding)
                            .iter()
                            .any(|origin| origin.lifetime_only) =>
                    {
                        origins.projected_referents_with_slots(
                            event,
                            *binding,
                            &place.segments,
                            true,
                        )
                    }
                    _ => Vec::new(),
                });
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

    #[cfg(test)]
    fn referent_consuming_accesses_from_moves(
        &self,
        body: &Body,
        moves: &FlowConsumptions,
    ) -> Vec<ReferentRead> {
        let reachable = self.reachable();
        let mut accesses = Vec::new();
        for (index, places) in moves.resolved_at.iter().enumerate() {
            let event = FlowNodeId(index);
            if !reachable.contains(&event) || places.is_empty() {
                continue;
            }
            for place in places {
                if !matches!(place.root, PlaceRoot::Parameter(_) | PlaceRoot::Global(_)) {
                    continue;
                }
                let (input_storage, referent_projection) = split_referent_effect_place(body, place);
                accesses.push(ReferentRead {
                    event,
                    place: place.clone(),
                    input_storage,
                    referent_projection,
                    span: self.nodes[index].span,
                });
            }
        }
        accesses.sort_by_key(|access| (access.event.0, format!("{:?}", access.place)));
        accesses
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
        let moves = self.referent_consumptions(body, types);
        let exits = self.referent_exit_effects_from_moves(body, &moves);
        let mut summary = self.referent_function_effects_from_exits(body, exits);
        summary.consuming_accesses = self.referent_consuming_accesses_from_moves(body, &moves);
        self.retain_unresolved_referent_accesses(&mut summary, &moves);
        summary
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
        let mut summary = self.referent_function_effects_from_exits(body, exits);
        summary.consuming_accesses = self.referent_consuming_accesses_from_moves(body, &moves);
        self.retain_unresolved_referent_accesses(&mut summary, &moves);
        summary
    }

    /// Summarize all paths that can normally return each explicit outcome.
    /// Unknown alternatives participate in every group; consumed-entry states
    /// remain distinct from the initialized-entry profile.
    #[cfg(test)]
    pub fn referent_variant_exit_effects(
        &self,
        body: &Body,
        types: &LinearTypes,
        calls: &[(FlowNodeId, Vec<ReferentExitEffect>, bool)],
        restorations: &[(FlowNodeId, Vec<Place>)],
        consumed_entry: Option<&[Place]>,
        possible_restorations: &[(FlowNodeId, Vec<Place>)],
    ) -> HashMap<VariantId, ReferentVariantExit> {
        self.referent_output_variant_exit_effects(
            body,
            types,
            calls,
            restorations,
            consumed_entry,
            possible_restorations,
        )
        .into_iter()
        .filter_map(|((path, variant), exit)| path.is_empty().then_some((variant, exit)))
        .collect()
    }

    #[cfg(test)]
    pub fn referent_output_variant_exit_effects(
        &self,
        body: &Body,
        types: &LinearTypes,
        calls: &[(FlowNodeId, Vec<ReferentExitEffect>, bool)],
        restorations: &[(FlowNodeId, Vec<Place>)],
        consumed_entry: Option<&[Place]>,
        possible_restorations: &[(FlowNodeId, Vec<Place>)],
    ) -> HashMap<(Vec<Segment>, VariantId), ReferentVariantExit> {
        self.return_output_variant_graphs(body)
            .into_iter()
            .map(|(variant, filtered)| {
                let summary = filtered.referent_function_effects_with_restorations(
                    body,
                    types,
                    calls,
                    restorations,
                );
                let effects_from_consumed_entry = consumed_entry.map(|entry| {
                    filtered.referent_exit_state_from_entry(
                        body,
                        types,
                        calls,
                        restorations,
                        entry,
                        possible_restorations,
                    )
                });
                (
                    variant,
                    ReferentVariantExit {
                        restored: filtered
                            .referent_restoration_guarantees_with_calls(
                                body,
                                types,
                                calls,
                                restorations,
                            )
                            .into_iter()
                            .map(|place| {
                                let (input_storage, referent_projection) =
                                    split_referent_effect_place(body, &place);
                                ReferentExitEffect {
                                    place,
                                    input_storage,
                                    referent_projection,
                                    definitely_consumed: true,
                                    consumption_spans: Vec::new(),
                                }
                            })
                            .collect(),
                        has_normal_return: summary.has_normal_return,
                        effects: summary.effects,
                        effects_from_consumed_entry,
                        consumed_entry: consumed_entry
                            .unwrap_or_default()
                            .iter()
                            .map(|place| {
                                let (input_storage, referent_projection) =
                                    split_referent_effect_place(body, place);
                                ReferentExitEffect {
                                    place: place.clone(),
                                    input_storage,
                                    referent_projection,
                                    definitely_consumed: true,
                                    consumption_spans: Vec::new(),
                                }
                            })
                            .collect(),
                        unresolved: summary.unresolved,
                    },
                )
            })
            .collect()
    }

    /// An access is not made safe by never reaching a normal return. Keep
    /// unknown direct and mapped call accesses independently of exit facts.
    #[cfg(test)]
    fn retain_unresolved_referent_accesses(
        &self,
        summary: &mut ReferentFunctionEffects,
        moves: &FlowConsumptions,
    ) {
        let reachable = self.reachable();
        summary.unresolved.extend(
            moves
                .unresolved
                .iter()
                .copied()
                .filter(|event| reachable.contains(event)),
        );
        summary.unresolved.sort_by_key(|event| event.0);
        summary.unresolved.dedup();
    }

    /// Preserve residual entry assumptions separately from initialized-entry
    /// effects. A surviving seed does not imply an access by the callee.
    #[cfg(test)]
    pub fn referent_exit_state_from_entry(
        &self,
        body: &Body,
        types: &LinearTypes,
        calls: &[(FlowNodeId, Vec<ReferentExitEffect>, bool)],
        restorations: &[(FlowNodeId, Vec<Place>)],
        consumed_entry: &[Place],
        possible_restorations: &[(FlowNodeId, Vec<Place>)],
    ) -> Vec<ReferentExitEffect> {
        let moves = self.referent_consumptions_with_partial_restorations(
            body,
            types,
            calls,
            restorations,
            consumed_entry,
            possible_restorations,
        );
        let exits = self.referent_exit_effects_from_moves(body, &moves);
        self.referent_function_effects_from_exits(body, exits)
            .effects
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
            consuming_accesses: Vec::new(),
            restored_from_consumed_entry: Vec::new(),
            consumed_entry: Vec::new(),
            effects_from_consumed_entry: Vec::new(),
            variant_exits: HashMap::new(),
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
            consuming_accesses: Vec::new(),
            restored_from_consumed_entry: Vec::new(),
            consumed_entry: Vec::new(),
            effects_from_consumed_entry: Vec::new(),
            variant_exits: HashMap::new(),
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
    pub fn map_initialized_referent_call_reads_with_origins(
        &self,
        body: &Body,
        event: FlowNodeId,
        call: NodeId,
        reads: &[ReferentRead],
        origins: &FlowLoanOrigins,
    ) -> (Vec<ReferentRead>, bool) {
        // An explicitly unsafe pointer borrow promises a valid initialized
        // reference, but its tracked owner is only a lifetime anchor. Discharge
        // ordinary reads at that boundary without inventing a physical place.
        // Do not use this adapter for consumed-entry, consumption, restoration,
        // or nested referent contents: those require actual referent identities.
        self.map_referent_call_reads_with_unsafe_boundary(body, event, call, reads, origins, true)
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
        self.map_referent_call_reads_with_unsafe_boundary(body, event, call, reads, origins, false)
    }

    #[cfg(test)]
    fn map_referent_call_reads_with_unsafe_boundary(
        &self,
        body: &Body,
        event: FlowNodeId,
        call: NodeId,
        reads: &[ReferentRead],
        origins: &FlowLoanOrigins,
        initialized_unsafe_reads: bool,
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
            consuming_accesses: Vec::new(),
            restored_from_consumed_entry: Vec::new(),
            consumed_entry: Vec::new(),
            effects_from_consumed_entry: Vec::new(),
            variant_exits: HashMap::new(),
        };
        let (mapped, unknown) = self.map_referent_call_effects_with_unsafe_boundary(
            body,
            event,
            call,
            &summary,
            origins,
            initialized_unsafe_reads,
        );
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
        self.map_referent_call_effects_with_unsafe_boundary(
            body, event, call, summary, origins, false,
        )
    }

    #[cfg(test)]
    fn map_referent_call_effects_with_unsafe_boundary(
        &self,
        body: &Body,
        event: FlowNodeId,
        call: NodeId,
        summary: &ReferentFunctionEffects,
        origins: &FlowLoanOrigins,
        initialized_unsafe_reads: bool,
    ) -> (Vec<ReferentExitEffect>, bool) {
        let NodeKind::Form { children, .. } = &body.nodes[call.0].kind else {
            return (Vec::new(), true);
        };
        let mut unknown = !summary.unresolved.is_empty();
        let mut mapped = Vec::new();
        let variants = summary
            .effects
            .iter()
            .any(|effect| {
                effect.input_storage.as_ref().is_some_and(|slot| {
                    slot.iter()
                        .any(|segment| matches!(segment, Segment::Payload(_, _)))
                })
            })
            .then(|| {
                origins
                    .variants
                    .get_or_init(|| self.variant_facts_with_origins(body, origins))
            });
        for effect in &summary.effects {
            let mut places = Vec::new();
            let mut unsafe_initialized = false;
            let mut incomplete = false;
            let mut inactive = false;
            let mut conditional = false;
            match effect.place.root {
                PlaceRoot::Global(_) => places.push(effect.place.clone()),
                PlaceRoot::Parameter(parameter) => {
                    if let (Some(argument), Some(slot)) =
                        (children.get(parameter.0 + 1), &effect.input_storage)
                    {
                        let mut alternatives = Vec::new();
                        collect_call_input_components(body, *argument, slot, &mut alternatives);
                        for alternative in alternatives {
                            let (alternative, selected_slot) = match alternative {
                                CallInputComponent::Selected(value, slot) => (value, slot),
                                CallInputComponent::Inactive => {
                                    inactive = true;
                                    continue;
                                }
                                CallInputComponent::Missing => {
                                    incomplete = true;
                                    continue;
                                }
                            };
                            let sources = origins.value_before(body, self, event, alternative);
                            let state = variants.and_then(|facts| facts[event.0].as_ref());
                            if selected_slot.first() != Some(&Segment::Dereference)
                                && selected_slot
                                    .iter()
                                    .any(|slot| matches!(slot, Segment::Payload(_, _)))
                                && !Place::from_expression(body, alternative).is_some_and(|place| {
                                    state.is_some_and(|state| {
                                        known_variant_slot(state, &place, &selected_slot)
                                    })
                                })
                            {
                                conditional = true;
                            }
                            if selected_slot.first() != Some(&Segment::Dereference)
                                && Place::from_expression(body, alternative).is_some_and(|place| {
                                    state.is_some_and(|state| {
                                        inactive_variant_slot(state, &place, &selected_slot)
                                    })
                                })
                            {
                                inactive = true;
                                continue;
                            }
                            let mut selected_alternative = false;
                            let mut inactive_alternative = false;
                            for source in sources {
                                if initialized_unsafe_reads
                                    && !effect.definitely_consumed
                                    && selected_slot.is_empty()
                                    && !effect.referent_projection.contains(&Segment::Dereference)
                                    && source.lifetime_only
                                    && source.storage.is_empty()
                                {
                                    unsafe_initialized = true;
                                    selected_alternative = true;
                                    continue;
                                }
                                if selected_slot.first() == Some(&Segment::Dereference)
                                    && selected_slot[1..]
                                        .iter()
                                        .any(|slot| matches!(slot, Segment::Payload(_, _)))
                                    && !state.is_some_and(|state| {
                                        known_variant_slot(
                                            state,
                                            &source.place,
                                            &selected_slot[1..],
                                        )
                                    })
                                {
                                    conditional = true;
                                }
                                if selected_slot.first() == Some(&Segment::Dereference)
                                    && !source.lifetime_only
                                    && source.storage.is_empty()
                                    && state.is_some_and(|state| {
                                        inactive_variant_slot(
                                            state,
                                            &source.place,
                                            &selected_slot[1..],
                                        )
                                    })
                                {
                                    inactive = true;
                                    inactive_alternative = true;
                                    continue;
                                }
                                let crosses_referent = selected_slot
                                    .iter()
                                    .position(|segment| *segment == Segment::Dereference)
                                    .is_some_and(|boundary| {
                                        source.storage.len() >= boundary
                                            && selected_slot[..boundary]
                                                .iter()
                                                .zip(&source.storage)
                                                .all(|(wanted, held)| {
                                                    storage_slot_matches(wanted, held)
                                                })
                                    });
                                let selected = origins.before[event.0]
                                    .as_ref()
                                    .map(|state| {
                                        select_summary_inputs(source, &selected_slot, state)
                                    })
                                    .unwrap_or_default();
                                if crosses_referent && selected.is_empty() {
                                    incomplete = true;
                                }
                                for origin in selected {
                                    if !origin.storage.is_empty() {
                                        continue;
                                    }
                                    if origin.lifetime_only {
                                        incomplete = true;
                                        continue;
                                    }
                                    let mut place = origin.referent_place();
                                    place
                                        .segments
                                        .extend(effect.referent_projection.iter().cloned());
                                    selected_alternative = true;
                                    if !places.contains(&place) {
                                        places.push(place);
                                    }
                                }
                            }
                            if !selected_alternative && !inactive_alternative {
                                incomplete = true;
                            }
                        }
                    } else {
                        incomplete = true;
                    }
                }
                _ => incomplete = true,
            }
            if places.is_empty() && !inactive && !unsafe_initialized {
                incomplete = true;
            }
            let definite = effect.definitely_consumed
                && places.len() == 1
                && !incomplete
                && !inactive
                && !conditional;
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
        self.referent_consumptions_with_partial_restorations(
            body,
            types,
            calls,
            restorations,
            entry_consumed,
            &[],
        )
    }

    /// A possibly initializing call invalidates must-consumed facts only.
    /// It cannot erase may-consumed facts or prove a definite restoration.
    #[cfg(test)]
    pub fn referent_consumptions_with_partial_restorations(
        &self,
        body: &Body,
        types: &LinearTypes,
        calls: &[(FlowNodeId, Vec<ReferentExitEffect>, bool)],
        restorations: &[(FlowNodeId, Vec<Place>)],
        entry_consumed: &[Place],
        possible_restorations: &[(FlowNodeId, Vec<Place>)],
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
                        possibly_restored: Vec::new(),
                        outcomes: Vec::new(),
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
        for (event, restored) in possible_restorations {
            calls
                .entry(*event)
                .or_default()
                .possibly_restored
                .extend(restored.iter().cloned());
        }
        let origins = self.loan_origins(body);
        // A fresh matched outcome can prove that a callee's conditional
        // destructive access actually happened. Empty loan contents alone
        // cannot establish this: use only the separately inferred consuming
        // clear contracts and their correlation/invalidation checks.
        for (index, refinement) in origins.clear_refinements.iter().enumerate() {
            let Some((sources, _, _)) = refinement else {
                continue;
            };
            let event = FlowNodeId(index);
            let spans = sources
                .iter()
                .map(|(source, _, _)| self.nodes[source.0].span)
                .collect::<Vec<_>>();
            for clear in origins.clears_before(body, self, event) {
                let place = clear.referent_place();
                let facts = calls.entry(event).or_default();
                facts.possible.push((place.clone(), spans.clone()));
                if !facts.definite.contains(&place) {
                    facts.definite.push(place);
                }
            }
            let outcomes = self.mapped_outcome_refinement(
                body,
                types,
                &origins,
                refinement.as_ref().unwrap(),
                &calls,
            );
            if !outcomes.is_empty() {
                calls.entry(event).or_default().outcomes = outcomes;
            }
        }
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

    #[cfg(test)]
    fn mapped_outcome_refinement(
        &self,
        body: &Body,
        types: &LinearTypes,
        origins: &FlowLoanOrigins,
        refinement: &CallResultRefinement,
        calls: &HashMap<FlowNodeId, CallConsumptionFacts>,
    ) -> Vec<CallOutcomeSource> {
        let (sources, variant, region) = refinement;
        let contracts = body.call_variant_exits.borrow();
        let mut outcomes = Vec::new();
        let output_contracts = body.call_output_variant_exits.borrow();
        for (event, call, path) in sources {
            let Some(original) = calls.get(event) else {
                return Vec::new();
            };
            if original.unresolved {
                return Vec::new();
            }
            let NodeKind::Form {
                callee: Some(callee),
                ..
            } = &body.nodes[call.0].kind
            else {
                return Vec::new();
            };
            let outcome = if path.is_empty() {
                contracts.get(callee).and_then(|groups| groups.get(variant))
            } else {
                output_contracts
                    .get(callee)
                    .and_then(|groups| groups.get(&(path.clone(), *variant)))
            };
            let Some(outcome) = outcome else {
                return Vec::new();
            };
            if !outcome.has_normal_return || !outcome.unresolved.is_empty() {
                return Vec::new();
            }
            let effects = outcome
                .effects_from_consumed_entry
                .as_ref()
                .unwrap_or(&outcome.effects);
            let map = |effects: &[ReferentExitEffect]| {
                let adapter = ReferentFunctionEffects {
                    has_normal_return: true,
                    effects: effects.to_vec(),
                    unresolved: Vec::new(),
                    reads: Vec::new(),
                    unresolved_reads: Vec::new(),
                    entry_reads: Vec::new(),
                    consuming_accesses: Vec::new(),
                    restored_from_consumed_entry: Vec::new(),
                    consumed_entry: Vec::new(),
                    effects_from_consumed_entry: Vec::new(),
                    variant_exits: HashMap::new(),
                };
                self.map_referent_call_effects_with_origins(body, *event, *call, &adapter, origins)
            };
            let (effects, unknown) = map(effects);
            if unknown {
                return Vec::new();
            }
            let (required, unknown) = map(&outcome.consumed_entry);
            let (restored, restoration_unknown) = map(&outcome.restored);
            // Conditional initialization cannot restore all possible aliases
            // when the callee actually writes only one. Require exact inputs.
            if unknown
                || restoration_unknown
                || restored.len() != outcome.restored.len()
                || restored.iter().any(|effect| !effect.definitely_consumed)
                || required.len() != outcome.consumed_entry.len()
                || required.iter().any(|effect| !effect.definitely_consumed)
            {
                return Vec::new();
            }
            outcomes.push(CallOutcomeSource {
                event: *event,
                effects,
                restored: restored.into_iter().map(|effect| effect.place).collect(),
                consumed_entry: required.into_iter().map(|effect| effect.place).collect(),
            });
        }
        let candidates = outcome_candidates(&outcomes, calls);
        if candidates.is_empty()
            || candidates.iter().any(|place| {
                place.segments.iter().any(|segment| {
                    matches!(
                        segment,
                        Segment::DynamicIndex | Segment::SliceDynamicIndex | Segment::SliceHalf(_)
                    )
                })
            })
        {
            return Vec::new();
        }
        if region
            .iter()
            .any(|event| match &self.nodes[event.0].action {
                FlowAction::Release { .. } => true,
                FlowAction::Read {
                    value,
                    place,
                    place_base: false,
                    ..
                } => {
                    body.nodes[value.0]
                        .ty
                        .as_ref()
                        .is_some_and(|ty| types.is_linear(ty))
                        && (reads_through_reference(body, *value)
                            || candidates
                                .iter()
                                .any(|candidate| candidate.root == place.root))
                }
                FlowAction::Assign { place, .. } => candidates.iter().any(|candidate| {
                    candidate.root == place.root
                        || matches!(candidate.root, PlaceRoot::Parameter(_))
                }),
                FlowAction::ScopeExit(bindings) => {
                    candidates.iter().any(|candidate| match candidate.root {
                        PlaceRoot::Local(binding) | PlaceRoot::Parameter(binding) => {
                            bindings.contains(&binding)
                        }
                        _ => false,
                    })
                }
                _ => false,
            })
        {
            return Vec::new();
        }
        outcomes
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
        let local_pin_accesses = if origins.is_none() {
            self.local_pin_accesses(body, types)
        } else {
            HashMap::new()
        };
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
            if let Some(places) = dereferenced_value_places(body, self, id, value, origins) {
                return if places.is_empty() {
                    (vec![place.clone()], true)
                } else {
                    (places, false)
                };
            }
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
        #[cfg(test)]
        let mut resolved_at = vec![HashSet::new(); self.nodes.len()];
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
                        NodeKind::Form { head, .. } if matches!(head.as_str(), "deref-set" | "pin-write")) =>
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
                                let place = loan.referent_place();
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
        }).or_else(|| (!local_pin_accesses.is_empty()).then(|| self.nodes.iter().map(|node| match &node.action {
            FlowAction::Assign { place, .. } => vec![place.clone()],
            FlowAction::Write { value, .. } | FlowAction::Evaluate(value)
                if matches!(&body.nodes[value.0].kind, NodeKind::Form { head, .. } if head == "pin-write") =>
                    local_pin_accesses.get(value).cloned().into_iter().collect(),
            _ => Vec::new(),
        }).collect::<Vec<_>>()));
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
        #[cfg(test)]
        let outcome_users = {
            let mut users = vec![Vec::new(); self.nodes.len()];
            if let Some(calls) = calls {
                for (event, facts) in calls {
                    for source in &facts.outcomes {
                        users[source.event.0].push(*event);
                    }
                }
            }
            users
        };
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
            #[cfg(test)]
            if calls.and_then(|calls| calls.get(&id)).is_some_and(|facts| {
                !refine_outcome_may(facts, calls.unwrap(), &before, &mut state)
            }) {
                // Never publish a conservative fallback before required
                // source snapshots exist: union joins could retain it forever.
                continue;
            }
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
                        #[cfg(test)]
                        resolved_at[id.0].extend(referents.iter().cloned());
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
                        #[cfg(test)]
                        resolved_at[id.0].extend(referents.iter().cloned());
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
                FlowAction::Evaluate(value)
                    if origins.is_none()
                        && local_pin_accesses.contains_key(value)
                        && matches!(&body.nodes[value.0].kind, NodeKind::Form { head, .. } if head == "pin-read")
                        && body.nodes[value.0]
                            .ty
                            .as_ref()
                            .is_some_and(|ty| types.is_linear(ty)) =>
                {
                    let place = local_pin_accesses[value].clone();
                    consumed_at[id.0].insert(place.clone());
                    #[cfg(test)]
                    resolved_at[id.0].insert(place.clone());
                    let spans = state.entry(place).or_default();
                    if !spans.contains(&node.span) {
                        spans.push(node.span);
                    }
                }
                FlowAction::Evaluate(value)
                    if origins.is_some()
                        && matches!(&body.nodes[value.0].kind, NodeKind::Form { head, .. } if head == "pin-read")
                        && body.nodes[value.0]
                            .ty
                            .as_ref()
                            .is_some_and(|ty| types.is_linear(ty)) =>
                {
                    let NodeKind::Form { children, .. } = &body.nodes[value.0].kind else {
                        unreachable!()
                    };
                    let (referents, unknown) =
                        if let Some(mut place) = Place::from_expression(body, children[1]) {
                            place.segments.push(Segment::Dereference);
                            consumed_at[id.0].insert(place.clone());
                            resolve(id, &place, *value)
                        } else {
                            let places =
                                dereferenced_value_places(body, self, id, *value, origins.unwrap())
                                    .unwrap_or_default();
                            let unknown = places.is_empty();
                            consumed_at[id.0].extend(places.iter().cloned());
                            (places, unknown)
                        };
                    #[cfg(test)]
                    resolved_at[id.0].extend(referents.iter().cloned());
                    if unknown {
                        unresolved.insert(id);
                    }
                    if !unknown && referents.len() == 1 {
                        definite_consumed_at.as_mut().unwrap()[id.0].insert(referents[0].clone());
                    }
                    for referent in referents {
                        let spans = state.entry(referent).or_default();
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
                #[cfg(test)]
                if changed {
                    for consumer in &outcome_users[successor.0] {
                        if before[consumer.0].is_some() && !queued[consumer.0] {
                            pending.push_back(*consumer);
                            queued[consumer.0] = true;
                        }
                    }
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
            #[cfg(test)]
            if calls.and_then(|calls| calls.get(&id)).is_some_and(|facts| {
                !refine_outcome_must(facts, calls.unwrap(), &definitely_before, &mut state)
            }) {
                continue;
            }
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
                for restored in call.restored.iter().chain(&call.possibly_restored) {
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
                            NodeKind::Form { head, .. } if matches!(head.as_str(), "deref-set" | "pin-write")))
            {
                // An unknown write may restore any consumed target. Retain
                // may facts, but none remains definitely uninitialized.
                state.clear();
            }
            for successor in &self.nodes[id.0].successors {
                let changed = match &mut definitely_before[successor.0] {
                    Some(existing) => intersect_consumed_coverage(existing, &state),
                    slot @ None => {
                        *slot = Some(state.clone());
                        true
                    }
                };
                if changed && !queued[successor.0] {
                    pending.push_back(*successor);
                    queued[successor.0] = true;
                }
                #[cfg(test)]
                if changed {
                    for consumer in &outcome_users[successor.0] {
                        if definitely_before[consumer.0].is_some() && !queued[consumer.0] {
                            pending.push_back(*consumer);
                            queued[consumer.0] = true;
                        }
                    }
                }
            }
        }
        unresolved.retain(|id| before[id.0].is_some());
        FlowConsumptions {
            before,
            after,
            at: consumed_at,
            local_pin_accesses,
            #[cfg(test)]
            resolved_at,
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
                if state
                    .iter()
                    .any(|consumed| definite_place_covers(consumed, place))
                {
                    continue;
                }
                // Only caller input storage can acquire an entry contract.
                // A live local owner requires actual local consumption.
                if !matches!(place.root, PlaceRoot::Parameter(_)) || has_dynamic_projection(place) {
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
        self.check_referent_call_consumed_entry_with_moves(requirements, &moves)
    }

    #[cfg(test)]
    fn check_referent_call_consumed_entry_with_moves(
        &self,
        requirements: &[(FlowNodeId, Vec<Place>, bool)],
        moves: &FlowConsumptions,
    ) -> Result<(), ReleaseConflict> {
        for (event, places, unknown) in requirements {
            let Some(state) = moves.definitely_before[event.0].as_ref() else {
                continue;
            };
            if *unknown
                || places.iter().any(|required| {
                    !state
                        .iter()
                        .any(|consumed| definite_place_covers(consumed, required))
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
        // Whole-local pinned moves must also invalidate reads/reborrows via
        // aliases of that storage. Resolve only owned local roots here;
        // symbolic parameter referents still need the staged call contracts.
        let local_origins = (origins.is_none() && !moves.local_pin_accesses.is_empty())
            .then(|| self.loan_origins(body));
        let resolving_origins = origins.or(local_origins.as_ref());
        for (index, node) in self.nodes.iter().enumerate() {
            let pinned_read_place = match node.action {
                FlowAction::Evaluate(value)
                    if matches!(&body.nodes[value.0].kind,
                    NodeKind::Form { head, .. } if head == "pin-read") =>
                {
                    resolving_origins
                        .and_then(|origins| {
                            dereferenced_value_places(body, self, FlowNodeId(index), value, origins)
                        })
                        .and_then(|places| places.into_iter().next())
                        .or_else(|| {
                            moves.at[index]
                                .iter()
                                .find(|place| {
                                    matches!(place.root, PlaceRoot::Local(_))
                                        && place.segments.is_empty()
                                })
                                .cloned()
                        })
                }
                _ => None,
            };
            let (place, value) = match &node.action {
                FlowAction::Read {
                    place,
                    value,
                    place_base: false,
                }
                | FlowAction::Release { place, value }
                | FlowAction::Clone { place, value }
                | FlowAction::Borrow { place, value, .. } => (place, *value),
                FlowAction::Evaluate(value) if pinned_read_place.is_some() => {
                    (pinned_read_place.as_ref().unwrap(), *value)
                }
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
            let mut resolved = resolving_origins
                .and_then(|origins| {
                    dereferenced_value_places(body, self, FlowNodeId(index), value, origins)
                })
                .unwrap_or_else(|| match (resolving_origins, &place.root) {
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
                });
            if local_origins.is_some() {
                resolved.retain(|place| matches!(place.root, PlaceRoot::Local(_)));
            }
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
        self.check_linear_exit_obligations_with_moves(body, types, declarations, None, false)
    }

    /// Share the move-flow solution between use checks and exit diagnostics.
    /// Keep individual results so callers retain their diagnostic priority.
    #[cfg(test)]
    pub fn check_linear_ownership(
        &self,
        body: &Body,
        types: &LinearTypes,
        declarations: &crate::typed_ir::Declarations,
    ) -> [Result<(), ReleaseConflict>; 4] {
        self.check_linear_ownership_with_local_pin_accesses(body, types, declarations)
            .0
    }

    /// Return the checked local-target facts from the same ownership solution
    /// for the syntax adapter, rather than solving loan origins a second time.
    pub fn check_linear_ownership_with_local_pin_accesses(
        &self,
        body: &Body,
        types: &LinearTypes,
        declarations: &crate::typed_ir::Declarations,
    ) -> ([Result<(), ReleaseConflict>; 4], HashMap<NodeId, Place>) {
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
            return ([Ok(()), Ok(()), Ok(()), Ok(())], HashMap::new());
        }
        let moves = self.consumptions(body, types);
        let results = [
            self.check_guard_preview_consumptions(body, &moves)
                .and_then(|_| self.check_linear_releases(body, types)),
            self.check_referent_consumption_permissions_with_moves(body, types, &moves)
                .and_then(|_| self.check_linear_consumptions_with_moves(body, &moves)),
            self.check_linear_exit_obligations_with_moves(
                body,
                types,
                declarations,
                Some(&moves),
                false,
            ),
            self.check_linear_projected_replacements(body, types, declarations, &moves),
        ];
        (results, moves.local_pin_accesses)
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
        let fallback_restorations = calls
            .consumed_inputs
            .iter()
            .map(|(event, places, _)| (*event, places.clone()))
            .collect::<Vec<_>>();
        let possible_restorations = calls
            .possible_restorations
            .as_deref()
            .unwrap_or(&fallback_restorations);
        let origins = self.loan_origins(body);
        let moves = self.referent_consumptions_with_partial_restorations(
            body,
            types,
            &calls.effects,
            &calls.restorations,
            &[],
            possible_restorations,
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
        // Access requirements, not outgoing storage state, decide whether a
        // callee may be invoked on consumed input. Initializing then consuming
        // a referent produces a consumed exit without reading its entry value.
        self.check_referent_call_entry_reads_from_entry(
            body,
            types,
            &calls.effects,
            &calls.restorations,
            &calls.read_inputs,
            &entry,
        )?;
        let seeded = self.referent_consumptions_with_partial_restorations(
            body,
            types,
            &calls.effects,
            &calls.restorations,
            &entry,
            possible_restorations,
        );
        self.check_referent_call_consumed_entry_with_moves(&calls.consumed_inputs, &seeded)?;
        let consuming_accesses = calls
            .consuming_accesses
            .iter()
            .map(|access| (access.event, access.place.clone()))
            .collect::<Vec<_>>();
        self.check_guard_preview_consumptions_with_calls(body, &seeded, &consuming_accesses)?;
        self.check_linear_consumptions_with_origins(body, &seeded, Some(&origins))?;
        self.check_referent_consumption_permissions_with_moves(body, types, &seeded)?;
        self.check_referent_replacements_with_facts(body, types, declarations, &origins, &seeded)?;
        self.check_stored_reference_provenance(body, declarations, &origins, &seeded)?;
        self.check_call_argument_reference_provenance(body, declarations, &origins, &seeded)?;
        self.check_returned_referents_initialized(body, declarations, &origins, &seeded)?;
        self.check_linear_exit_obligations_with_moves(
            body,
            types,
            declarations,
            Some(&seeded),
            true,
        )?;
        Ok(entry)
    }

    /// Validate physical referents of escaping reference slots, not the
    /// lifetime-only anchors carried by unsafe pointer-derived references.
    /// Mandatory static slots require provenance in every result alternative;
    /// Constructor trees and definite discriminant facts identify active enum
    /// payloads. Unknown variants require origins for every possible payload;
    /// lack of a definite discriminant cannot prove a payload inactive.
    #[cfg(test)]
    fn check_returned_referents_initialized(
        &self,
        body: &Body,
        declarations: &crate::typed_ir::Declarations,
        origins: &FlowLoanOrigins,
        moves: &FlowConsumptions,
    ) -> Result<(), ReleaseConflict> {
        for (index, node) in self.nodes.iter().enumerate() {
            let FlowAction::Return(Some(value)) = node.action else {
                continue;
            };
            let Some(state) = moves.before[index].as_ref() else {
                continue;
            };
            let event = FlowNodeId(index);
            if self.value_missing_reference_provenance(body, declarations, origins, event, value) {
                return Err(ReleaseConflict {
                    message:
                        "cannot prove initialization of returned reference: missing slot provenance"
                            .into(),
                    span: node.span,
                    labels: Vec::new(),
                });
            }
            let snapshots = self
                .transparent_return_alternatives(body, origins, event, value)
                .unwrap_or_else(|| vec![(event, value)]);
            for (snapshot, alternative) in snapshots {
                let state = if snapshot == event {
                    state
                } else {
                    moves.after[snapshot.0].as_ref().unwrap_or(state)
                };
                let returned = origins.value_before(body, self, snapshot, alternative);
                for origin in returned {
                    if origin.lifetime_only {
                        continue;
                    }
                    let place = origin.referent_place();
                    let conflicts = state
                        .iter()
                        .filter(|(consumed, _)| consumed.overlaps(&place))
                        .collect::<Vec<_>>();
                    if conflicts.is_empty() {
                        continue;
                    }
                    let previous = conflicts
                        .iter()
                        .flat_map(|(_, spans)| spans.iter())
                        .flatten()
                        .min_by_key(|span| (span.source_id, span.start));
                    return Err(ReleaseConflict {
                        message: "returned reference may point to a consumed linear referent"
                            .into(),
                        span: node.span,
                        labels: previous
                            .into_iter()
                            .map(|span| (*span, "referent was consumed here".into()))
                            .collect(),
                    });
                }
            }
        }
        Ok(())
    }

    /// Preserve branch-specific origins and consumption only when evaluation
    /// is followed by structural merge/scope nodes and this exact return.
    /// A later operand, mutation, call, or loop edge needs the merged proof;
    /// an earlier snapshot alone cannot establish initialization at escape.
    #[cfg(test)]
    fn transparent_return_alternatives(
        &self,
        body: &Body,
        origins: &FlowLoanOrigins,
        returned: FlowNodeId,
        value: NodeId,
    ) -> Option<Vec<(FlowNodeId, NodeId)>> {
        let mut alternatives = Vec::new();
        collect_result_alternatives(body, value, &mut alternatives);
        if alternatives.len() < 2 {
            return None;
        }
        let mut snapshots = Vec::new();
        for alternative in alternatives {
            for &index in &origins.events_by_value[alternative.0] {
                if origins.before[index].is_none()
                    || !flow_action_has_value(&self.nodes[index].action, alternative)
                {
                    continue;
                }
                let mut current = FlowNodeId(index);
                let mut seen = HashSet::new();
                let transparent = loop {
                    if !seen.insert(current) {
                        break false;
                    }
                    let [next] = self.nodes[current.0].successors.as_slice() else {
                        break false;
                    };
                    if *next == returned {
                        break true;
                    }
                    match self.nodes[next.0].action {
                        FlowAction::ScopeExit(_) => {}
                        FlowAction::Evaluate(value)
                            if matches!(
                                body.nodes[value.0].kind,
                                NodeKind::If { .. }
                                    | NodeKind::Match { .. }
                                    | NodeKind::Block(_)
                                    | NodeKind::Labeled(_, _)
                            ) => {}
                        _ => break false,
                    }
                    current = *next;
                };
                if !transparent {
                    return None;
                }
                snapshots.push((FlowNodeId(index), alternative));
            }
        }
        (!snapshots.is_empty()).then_some(snapshots)
    }

    #[cfg(test)]
    fn value_missing_reference_provenance(
        &self,
        body: &Body,
        declarations: &crate::typed_ir::Declarations,
        origins: &FlowLoanOrigins,
        event: FlowNodeId,
        value: NodeId,
    ) -> bool {
        self.value_missing_reference_provenance_inner(
            body,
            declarations,
            origins,
            event,
            value,
            &mut HashSet::new(),
        )
    }

    #[cfg(test)]
    /// Find every reaching whole-value definition only while the local is
    /// unchanged. Unknown writes/calls and parameter entry stop the proof;
    /// a merged origin union is not a substitute for checking each source.
    fn unchanged_local_definitions(
        &self,
        body: &Body,
        origins: &FlowLoanOrigins,
        event: FlowNodeId,
        binding: BindingId,
        read_value: NodeId,
    ) -> Option<Vec<(FlowNodeId, NodeId)>> {
        let mut predecessors = vec![Vec::new(); self.nodes.len()];
        for (index, node) in self.nodes.iter().enumerate() {
            if origins.before[index].is_some() {
                for successor in &node.successors {
                    predecessors[successor.0].push(FlowNodeId(index));
                }
            }
        }
        let at_read = matches!(self.nodes[event.0].action,
            FlowAction::Read { value, .. } if value == read_value);
        let mut pending = predecessors[event.0]
            .iter()
            .map(|event| (*event, at_read))
            .collect::<Vec<_>>();
        let mut seen = HashSet::new();
        let mut definitions = Vec::new();
        let target = Place::root(PlaceRoot::Local(binding));
        while let Some((previous, mut passed_read)) = pending.pop() {
            if !seen.insert((previous, passed_read)) {
                continue;
            }
            if matches!(self.nodes[previous.0].action,
                FlowAction::Read { value, .. } if value == read_value)
            {
                passed_read = true;
            }
            match &self.nodes[previous.0].action {
                FlowAction::Bind {
                    binding: found,
                    value,
                } if *found == binding => {
                    if !passed_read {
                        return None;
                    }
                    definitions.push((previous, *value));
                    continue;
                }
                FlowAction::Assign { place, value } if *place == target => {
                    if !passed_read {
                        return None;
                    }
                    definitions.push((previous, *value));
                    continue;
                }
                FlowAction::Assign { place, .. } | FlowAction::Release { place, .. }
                    if place.overlaps(&target) =>
                {
                    return None
                }
                FlowAction::Write { .. } | FlowAction::Entry => return None,
                FlowAction::ScopeExit(bindings) if bindings.contains(&binding) => return None,
                FlowAction::Evaluate(value)
                    if matches!(
                        &body.nodes[value.0].kind,
                        NodeKind::Form {
                            callee: Some(_),
                            ..
                        }
                    ) || matches!(&body.nodes[value.0].kind,
                    NodeKind::Form { head, .. } if matches!(head.as_str(), "ptr-write" | "linux-syscall" | "pin-read")) =>
                {
                    return None
                }
                FlowAction::Pattern { pattern, .. } => {
                    let mut bindings = HashSet::new();
                    collect_pattern_bindings(body, *pattern, &mut bindings);
                    if bindings.contains(&binding) {
                        return None;
                    }
                }
                _ => {}
            }
            pending.extend(
                predecessors[previous.0]
                    .iter()
                    .map(|event| (*event, passed_read)),
            );
        }
        (!definitions.is_empty()).then_some(definitions)
    }

    #[cfg(test)]
    fn value_missing_reference_provenance_inner(
        &self,
        body: &Body,
        declarations: &crate::typed_ir::Declarations,
        origins: &FlowLoanOrigins,
        event: FlowNodeId,
        value: NodeId,
        visiting: &mut HashSet<(FlowNodeId, NodeId)>,
    ) -> bool {
        for alternative in returned_provenance_components(body, value) {
            let Some(ty) = &body.nodes[alternative.0].ty else {
                continue;
            };
            let slots = declarations.reference_storage_slots(ty);
            if slots.is_empty() {
                continue;
            }
            if matches!(body.nodes[alternative.0].kind, NodeKind::Loop(_)) {
                let key = (event, alternative);
                if !visiting.contains(&key) {
                    let breaks = origins.reachable_loop_breaks(self, alternative);
                    if !breaks.is_empty() {
                        visiting.insert(key);
                        let missing = breaks.into_iter().any(|(break_event, source)| {
                            self.value_missing_reference_provenance_inner(
                                body,
                                declarations,
                                origins,
                                break_event,
                                source,
                                visiting,
                            )
                        });
                        visiting.remove(&key);
                        if missing {
                            return true;
                        }
                        continue;
                    }
                }
            }
            if let NodeKind::Symbol {
                binding: Some(binding),
                ..
            } = body.nodes[alternative.0].kind
            {
                let key = (event, alternative);
                if !visiting.contains(&key) {
                    if let Some(definitions) =
                        self.unchanged_local_definitions(body, origins, event, binding, alternative)
                    {
                        visiting.insert(key);
                        let missing = definitions.into_iter().any(|(definition, source)| {
                            self.value_missing_reference_provenance_inner(
                                body,
                                declarations,
                                origins,
                                definition,
                                source,
                                visiting,
                            )
                        });
                        visiting.remove(&key);
                        if missing {
                            return true;
                        }
                        continue;
                    }
                }
            }
            let alternative_origins = origins.value_before(body, self, event, alternative);
            let variant_states = origins
                .variants
                .get_or_init(|| self.variant_facts_with_origins(body, origins));
            let stored_variants = variant_states[event.0].as_ref().map(|state| {
                value_variant_facts(
                    body,
                    alternative,
                    state,
                    Some((self, origins, event, variant_states)),
                )
            });
            let stored_bounds = variant_states[event.0].as_ref().map(|state| {
                value_variant_bounds(
                    body,
                    alternative,
                    state,
                    Some((self, origins, event, variant_states)),
                )
            });
            for slot in slots {
                if slot.storage.iter().enumerate().any(|(index, segment)| {
                    matches!(segment, Segment::Payload(variant, _)
                        if constructor_variant_at_storage(body, alternative, &slot.storage[..index])
                            .or_else(|| stored_variants.as_ref()?.get(&Place {
                                root: PlaceRoot::Local(BindingId(0)),
                                segments: slot.storage[..index].to_vec(),
                            }).copied()).is_some_and(|selected| selected != *variant)
                            || stored_bounds.as_ref().and_then(|bounds| bounds.get(&slot.storage[..index]))
                                .is_some_and(|possible| !possible.is_empty() && !possible.contains(variant)))
                }) {
                    continue;
                }
                if !alternative_origins.iter().any(|origin| {
                    origin.storage.len() == slot.storage.len()
                        && slot
                            .storage
                            .iter()
                            .zip(&origin.storage)
                            .all(|(expected, actual)| storage_slot_matches(expected, actual))
                }) {
                    return true;
                }
            }
        }
        false
    }

    #[cfg(test)]
    fn check_call_argument_reference_provenance(
        &self,
        body: &Body,
        declarations: &crate::typed_ir::Declarations,
        origins: &FlowLoanOrigins,
        moves: &FlowConsumptions,
    ) -> Result<(), ReleaseConflict> {
        for (index, node) in self.nodes.iter().enumerate() {
            let FlowAction::Evaluate(value) = node.action else {
                continue;
            };
            if moves.before[index].is_none() {
                continue;
            }
            let NodeKind::Form {
                children,
                callee: Some(_),
                ..
            } = &body.nodes[value.0].kind
            else {
                continue;
            };
            for argument in children.iter().skip(1) {
                if self.value_missing_reference_provenance(
                    body,
                    declarations,
                    origins,
                    FlowNodeId(index),
                    *argument,
                ) {
                    return Err(ReleaseConflict {
                        message: "cannot pass reference-bearing argument: missing slot provenance"
                            .into(),
                        span: node.span,
                        labels: Vec::new(),
                    });
                }
            }
        }
        Ok(())
    }

    #[cfg(test)]
    fn check_stored_reference_provenance(
        &self,
        body: &Body,
        declarations: &crate::typed_ir::Declarations,
        origins: &FlowLoanOrigins,
        moves: &FlowConsumptions,
    ) -> Result<(), ReleaseConflict> {
        for (index, node) in self.nodes.iter().enumerate() {
            let value = match node.action {
                FlowAction::Bind { value, .. }
                | FlowAction::Assign { value, .. }
                | FlowAction::Write { value, .. } => value,
                FlowAction::Evaluate(value)
                    if matches!(&body.nodes[value.0].kind,
                    NodeKind::Form { head, .. } if matches!(head.as_str(), "deref-set" | "pin-write")) =>
                {
                    value
                }
                _ => continue,
            };
            if moves.before[index].is_none() {
                continue;
            }
            let value = match &body.nodes[value.0].kind {
                NodeKind::Form { head, children, .. }
                    if matches!(head.as_str(), "deref-set" | "pin-write")
                        && children.len() == 3 =>
                {
                    children[2]
                }
                _ => value,
            };
            if self.value_missing_reference_provenance(
                body,
                declarations,
                origins,
                FlowNodeId(index),
                value,
            ) {
                return Err(ReleaseConflict {
                    message: "cannot transfer reference-bearing value: missing slot provenance"
                        .into(),
                    span: node.span,
                    labels: Vec::new(),
                });
            }
        }
        Ok(())
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
            if !matches!(head.as_str(), "deref-set" | "pin-write") || children.len() != 3 {
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
                    || (target.pinned != (head == "pin-write"))
                    || target.lifetime_only
                    || !target.storage.is_empty()
                {
                    return Err(failure(
                        "cannot prove permission to replace this linear referent",
                    ));
                }
                let destination = target.referent_place();
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
                    let consumed = moves.definitely_before[event.0]
                        .as_ref()
                        .is_some_and(|state| {
                            state
                                .iter()
                                .any(|prior| definite_place_covers(prior, &leaf))
                        });
                    if !consumed {
                        if has_dynamic_projection(&leaf) {
                            return Err(failure("cannot prove linear referent consumption before replacement: dynamic target identity"));
                        }
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
        let local_pin_accesses = &moves.local_pin_accesses;
        for (index, node) in self.nodes.iter().enumerate() {
            let (place, value, pinned_write) = match &node.action {
                FlowAction::Assign { place, value } => (place, *value, false),
                FlowAction::Write { value, .. } | FlowAction::Evaluate(value) if matches!(&body.nodes[value.0].kind, NodeKind::Form { head, .. } if head == "pin-write") =>
                {
                    let Some(place) = local_pin_accesses.get(value) else {
                        continue;
                    };
                    let NodeKind::Form { children, .. } = &body.nodes[value.0].kind else {
                        unreachable!();
                    };
                    (place, children[2], true)
                }
                _ => continue,
            };
            let PlaceRoot::Local(binding) = place.root else {
                continue;
            };
            if place.segments.is_empty() && !pinned_write {
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
                            "{} would destroy live linear projection '{name}'; consume it explicitly first",
                            if pinned_write { "pin-write" } else { "assignment" }
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
        referent_exit_facts: bool,
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
        let computed_moves;
        let possible = match moves {
            Some(moves) => moves,
            None => {
                computed_moves = self.consumptions(body, types);
                &computed_moves
            }
        };
        let syntactic_before = (!referent_exit_facts).then(|| {
            self.obligation_consumptions_with_local_pin_accesses(
                body,
                types,
                &obligation_places,
                &possible.local_pin_accesses,
            )
            .0
        });
        let active = self.active_bindings_before(body);
        let preview_cleanup = self
            .guard_preview_boundaries(body)
            .into_iter()
            .map(|(_, _, cleanup, _)| cleanup)
            .collect::<HashSet<_>>();
        let definite_before = if referent_exit_facts {
            &possible.definitely_before
        } else {
            syntactic_before.as_ref().unwrap()
        };
        for (index, node) in self.nodes.iter().enumerate() {
            if definite_before[index].is_none() {
                continue;
            }
            if preview_cleanup.contains(&FlowNodeId(index)) {
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
                let consumed = definite_before[index].as_ref().is_some_and(|state| {
                    if referent_exit_facts {
                        state.iter().any(|consumed| {
                            !consumed.segments.iter().any(|segment| {
                                matches!(
                                    segment,
                                    Segment::DynamicIndex | Segment::SliceDynamicIndex
                                )
                            }) && place_covers(consumed, place)
                        })
                    } else {
                        state.contains(place)
                    }
                });
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

    /// Preview bindings disappear when a guard fails; they acquire owning
    /// cleanup obligations only on the arm body path.
    fn guard_preview_boundaries(
        &self,
        body: &Body,
    ) -> Vec<(FlowNodeId, FlowNodeId, FlowNodeId, Vec<BindingId>)> {
        let mut boundaries = Vec::new();
        for arm in &body.nodes {
            let NodeKind::MatchArm { pattern, values } = &arm.kind else {
                continue;
            };
            if values.len() != 2 {
                continue;
            }
            let NodeKind::Form { head, children, .. } = &body.nodes[values[0].0].kind else {
                continue;
            };
            if head != "when" || children.len() != 2 {
                continue;
            }
            let mut bindings = HashSet::new();
            collect_pattern_bindings(body, *pattern, &mut bindings);
            if bindings.is_empty() {
                continue;
            }
            for (index, node) in self.nodes.iter().enumerate() {
                if !matches!(node.action, FlowAction::Branch(value) if value == children[1]) {
                    continue;
                }
                let Some(cleanup) = node.successors.get(1).copied() else {
                    continue;
                };
                let FlowAction::ScopeExit(exiting) = &self.nodes[cleanup.0].action else {
                    continue;
                };
                if exiting.iter().copied().collect::<HashSet<_>>() != bindings {
                    continue;
                }
                if let Some((bound, _)) = self.nodes.iter().enumerate().find(|(_, node)| {
                    matches!(node.action, FlowAction::Pattern { pattern: found, .. } if found == *pattern)
                }) {
                    boundaries.push((FlowNodeId(bound), FlowNodeId(index), cleanup, exiting.clone()));
                }
            }
        }
        boundaries
    }

    fn check_guard_preview_consumptions(
        &self,
        body: &Body,
        moves: &FlowConsumptions,
    ) -> Result<(), ReleaseConflict> {
        self.check_guard_preview_consumptions_with_calls(body, moves, &[])
    }

    fn check_guard_preview_consumptions_with_calls(
        &self,
        body: &Body,
        moves: &FlowConsumptions,
        consuming_accesses: &[(FlowNodeId, Place)],
    ) -> Result<(), ReleaseConflict> {
        for (bound, decision, _, bindings) in self.guard_preview_boundaries(body) {
            let mut pending = self.nodes[bound.0].successors.clone();
            let mut seen = HashSet::new();
            while let Some(event) = pending.pop() {
                if event == decision || !seen.insert(event) || moves.before[event.0].is_none() {
                    continue;
                }
                if moves.at[event.0].iter().chain(consuming_accesses.iter()
                    .filter(|(access_event, _)| *access_event == event).map(|(_, place)| place)).any(|place| {
                    matches!(place.root, PlaceRoot::Local(binding) if bindings.contains(&binding))
                }) {
                    return Err(ReleaseConflict {
                        message: "match guard cannot consume a preview payload before arm selection".into(),
                        span: self.nodes[event.0].span,
                        labels: Vec::new(),
                    });
                }
                pending.extend(self.nodes[event.0].successors.iter().copied());
            }
        }
        Ok(())
    }

    #[cfg(test)]
    fn obligation_consumptions(
        &self,
        body: &Body,
        types: &LinearTypes,
        obligations: &HashSet<Place>,
    ) -> (Vec<Option<HashSet<Place>>>, Vec<Option<HashSet<Place>>>) {
        let local_pin_accesses = self.local_pin_accesses(body, types);
        self.obligation_consumptions_with_local_pin_accesses(
            body,
            types,
            obligations,
            &local_pin_accesses,
        )
    }

    fn obligation_consumptions_with_local_pin_accesses(
        &self,
        body: &Body,
        types: &LinearTypes,
        obligations: &HashSet<Place>,
        local_pin_accesses: &HashMap<NodeId, Place>,
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
                FlowAction::Evaluate(value)
                    if matches!(&body.nodes[value.0].kind, NodeKind::Form { head, .. } if head == "pin-read")
                        && body.nodes[value.0]
                            .ty
                            .as_ref()
                            .is_some_and(|ty| types.is_linear(ty)) =>
                {
                    local_pin_accesses.get(value)
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
                FlowAction::Write { value, .. } | FlowAction::Evaluate(value) if matches!(&body.nodes[value.0].kind, NodeKind::Form { head, .. } if head == "pin-write") => {
                    if let Some(target) = local_pin_accesses.get(value) {
                        state.retain(|leaf| {
                            !place_covers(target, leaf) && !place_covers(leaf, target)
                        });
                    }
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
                    .then(|| place.clone())
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
        self.liveness_in_order(body, &self.reachable_postorder())
    }

    /// Successors precede predecessors except at cycle back edges. Dense
    /// visitation avoids hashing event IDs and the explicit stack avoids
    /// recursion on large generated bodies.
    fn reachable_postorder(&self) -> Vec<FlowNodeId> {
        let mut visited = vec![false; self.nodes.len()];
        let mut stack = vec![(self.entry, 0usize)];
        let mut order = Vec::new();
        visited[self.entry.0] = true;
        while let Some((id, next)) = stack.last_mut() {
            if let Some(successor) = self.nodes[id.0].successors.get(*next).copied() {
                *next += 1;
                if !visited[successor.0] {
                    visited[successor.0] = true;
                    stack.push((successor, 0));
                }
            } else {
                order.push(*id);
                stack.pop();
            }
        }
        order
    }

    fn liveness_in_order(&self, body: &Body, reachable: &[FlowNodeId]) -> FlowLiveness {
        let count = body.bindings.len();
        let words = count.div_ceil(64);
        let mut before = vec![vec![0u64; words]; self.nodes.len()];
        let mut after = before.clone();
        // These immutable transfer masks need no per-event allocation.
        // Keep only the externally queried snapshots as separate rows.
        let mut uses = vec![0u64; self.nodes.len() * words];
        let mut defs = vec![0u64; self.nodes.len() * words];
        let mut predecessors = vec![Vec::<FlowNodeId>::new(); self.nodes.len()];
        for id in reachable {
            let node = &self.nodes[id.0];
            for successor in &node.successors {
                predecessors[successor.0].push(*id);
            }
            let set = |bits: &mut [u64], binding: BindingId| {
                bits[id.0 * words + binding.0 / 64] |= 1u64 << (binding.0 % 64);
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
        for id in reachable {
            queued[id.0] = true;
        }
        #[cfg(test)]
        let mut worklist_visits = 0;
        while let Some(id) = pending.pop_front() {
            #[cfg(test)]
            {
                worklist_visits += 1;
            }
            queued[id.0] = false;
            // Compute one word at a time in the existing snapshots. Successor
            // reads must precede the update, including for a self-loop.
            let mut changed = false;
            for word in 0..words {
                let next_after = self.nodes[id.0]
                    .successors
                    .iter()
                    .fold(0, |bits, successor| bits | before[successor.0][word]);
                let offset = id.0 * words + word;
                let next_before = (next_after & !defs[offset]) | uses[offset];
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
            #[cfg(test)]
            worklist_visits,
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
pub(crate) fn split_referent_effect_place(
    body: &Body,
    place: &Place,
) -> (Option<Vec<Segment>>, Vec<Segment>) {
    let PlaceRoot::Parameter(binding) = place.root else {
        return (None, place.segments.clone());
    };
    let slot = body
        .parameter_referent_loan_slots
        .get(binding.0)
        .into_iter()
        .flatten()
        .chain(
            body.parameter_loan_slots
                .get(binding.0)
                .into_iter()
                .flatten(),
        )
        .filter(|slot| {
            slot.storage.len() <= place.segments.len()
                && slot
                    .storage
                    .iter()
                    .zip(&place.segments)
                    .all(|(schema, actual)| storage_slot_matches(schema, actual))
        })
        .max_by_key(|slot| slot.storage.len());
    match slot {
        Some(slot) => (
            Some(place.segments[..slot.storage.len()].to_vec()),
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

/// Meet definite consumed regions, retaining structural leaves covered on
/// both paths even when one path consumed their whole parent. Probe prefix
/// identities in the sets instead of comparing every pair of places.
fn intersect_consumed_coverage(held: &mut HashSet<Place>, incoming: &HashSet<Place>) -> bool {
    if held.is_subset(incoming) {
        return false;
    }
    if incoming.is_subset(held) {
        held.clone_from(incoming);
        return true;
    }
    let common = held
        .union(incoming)
        .filter(|place| {
            consumed_coverage_contains(held, place) && consumed_coverage_contains(incoming, place)
        })
        .cloned()
        .collect::<HashSet<_>>();
    if common == *held {
        false
    } else {
        *held = common;
        true
    }
}

fn consumed_coverage_contains(consumed: &HashSet<Place>, place: &Place) -> bool {
    if consumed.contains(place) {
        return true;
    }
    if place
        .segments
        .iter()
        .any(|segment| matches!(segment, Segment::DynamicIndex | Segment::SliceDynamicIndex))
    {
        return false;
    }
    let mut parent = place.clone();
    while let Some(segment) = parent.segments.pop() {
        // A stored reference's pointee and a slice-region token are not
        // structural parts of their containing value. Exact facts above
        // remain available, but a consumed container cannot invent them.
        if !matches!(
            segment,
            Segment::Field(_) | Segment::Tuple(_) | Segment::Payload(_, _) | Segment::Index(_)
        ) {
            return false;
        }
        if consumed.contains(&parent) {
            return true;
        }
    }
    false
}

#[cfg(test)]
fn has_dynamic_projection(place: &Place) -> bool {
    place
        .segments
        .iter()
        .any(|segment| matches!(segment, Segment::DynamicIndex | Segment::SliceDynamicIndex))
}

/// A wildcard names possible storage, not an identity shared by independent
/// index evaluations. A known consumed parent can still cover any child.
#[cfg(test)]
fn definite_place_covers(ancestor: &Place, descendant: &Place) -> bool {
    !has_dynamic_projection(ancestor) && place_covers(ancestor, descendant)
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

#[cfg(test)]
fn pattern_binding_path(body: &Body, id: NodeId, binding: BindingId) -> Option<Vec<Segment>> {
    match &body.nodes[id.0].kind {
        NodeKind::Symbol {
            binding: Some(found),
            ..
        } if *found == binding => Some(Vec::new()),
        NodeKind::Labeled(_, inner) => pattern_binding_path(body, *inner, binding),
        NodeKind::Form { head, children, .. } => {
            for (index, child) in children.iter().skip(1).enumerate() {
                if let Some(mut path) = pattern_binding_path(body, *child, binding) {
                    path.insert(0, aggregate_slot(body, head, children, index)?);
                    return Some(path);
                }
            }
            None
        }
        _ => None,
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
    for (held, other) in existing.iter_mut().zip(incoming.iter()) {
        changed |= merge_loan_origins(held, other);
    }
    #[cfg(test)]
    if let (Some(held), Some(other)) = (
        &mut existing.parameter_contents,
        &incoming.parameter_contents,
    ) {
        for (key, contents) in other {
            changed |= merge_loan_origins(held.entry(key.clone()).or_default(), contents);
        }
    }
    #[cfg(test)]
    existing.global_known_contents.retain(|global, paths| {
        let previous = paths.clone();
        let Some(other) = incoming.global_known_contents.get(global) else {
            changed |= !paths.is_empty();
            return false;
        };
        let candidates = previous.iter().chain(other);
        *paths = candidates
            .filter(|path| {
                previous.iter().any(|prefix| path.starts_with(prefix))
                    && other.iter().any(|prefix| path.starts_with(prefix))
            })
            .cloned()
            .collect();
        changed |= *paths != previous;
        !paths.is_empty()
    });
    changed
}

#[cfg(test)]
fn seed_parameter_contents(body: &Body) -> HashMap<(PlaceRoot, Vec<Segment>), Vec<LoanOrigin>> {
    let mut contents = HashMap::new();
    for (parameter, slots) in body.parameter_referent_loan_slots.iter().enumerate() {
        for slot in slots {
            let Some(boundary) = slot
                .storage
                .iter()
                .rposition(|segment| *segment == Segment::Dereference)
            else {
                continue;
            };
            let key = (
                PlaceRoot::Parameter(BindingId(parameter)),
                slot.storage[..boundary].to_vec(),
            );
            let held = LoanOrigin {
                place: Place::root(PlaceRoot::Parameter(BindingId(parameter))),
                mutable: slot.mutable,
                pinned: slot.pinned,
                span: None,
                borrowed_from: None,
                storage: slot.storage[boundary + 1..].to_vec(),
                parameter_storage: Some(slot.storage.clone()),
                storage_inputs: (boundary + 1..slot.storage.len()).map(Some).collect(),
                lifetime_only: false,
            };
            merge_loan_origins(contents.entry(key).or_default(), &[held]);
        }
    }
    contents
}

#[cfg(test)]
fn loaded_parameter_value_origins(origin: &LoanOrigin, state: &LoanState) -> Vec<LoanOrigin> {
    if !matches!(
        origin.place.root,
        PlaceRoot::Parameter(_) | PlaceRoot::Global(_)
    ) {
        return Vec::new();
    }
    if origin.lifetime_only || !origin.storage.is_empty() {
        return Vec::new();
    }
    if let PlaceRoot::Global(global) = origin.place.root {
        if !state
            .global_known_contents
            .get(&global)
            .is_some_and(|paths| {
                paths
                    .iter()
                    .any(|path| origin.place.segments.starts_with(path))
            })
        {
            return Vec::new();
        }
    }
    let Some(contents) = &state.parameter_contents else {
        return Vec::new();
    };
    let key = (
        origin.place.root.clone(),
        origin.parameter_storage.clone().unwrap_or_default(),
    );
    let mut result = Vec::new();
    // Symbolic array input slots can match concrete selections. Retain their
    // entry facts conservatively rather than treating a missing exact key as
    // an empty pointee or specializing a source to the destination's index.
    for ((input_parameter, input), values) in contents {
        if *input_parameter != key.0
            || input.len() != key.1.len()
            || !key
                .1
                .iter()
                .zip(input)
                .all(|(wanted, actual)| storage_slot_matches(wanted, actual))
        {
            continue;
        }
        for held in values {
            let path = &origin.place.segments;
            if held.storage.len() < path.len()
                || !path
                    .iter()
                    .zip(&held.storage)
                    .all(|(wanted, actual)| storage_slot_matches(wanted, actual))
            {
                continue;
            }
            let mut loaded = held.clone();
            for selected in path {
                loaded.project_storage(selected);
            }
            loaded.mutable &= origin.mutable;
            merge_loan_origins(&mut result, &[loaded]);
        }
    }
    result
}

#[cfg(test)]
fn store_parameter_contents(
    state: &mut LoanState,
    destination: &LoanOrigin,
    incoming: Vec<LoanOrigin>,
    strong: bool,
) {
    if !matches!(
        destination.place.root,
        PlaceRoot::Parameter(_) | PlaceRoot::Global(_)
    ) {
        return;
    }
    if destination.lifetime_only || !destination.storage.is_empty() {
        return;
    }
    if let PlaceRoot::Global(global) = destination.place.root {
        let known = state.global_known_contents.entry(global).or_default();
        let path = &destination.place.segments;
        if strong
            && !path.iter().any(|segment| {
                matches!(segment, Segment::DynamicIndex | Segment::SliceDynamicIndex)
            })
        {
            known.insert(path.clone());
        } else {
            known.retain(|held| {
                !destination.place.overlaps(&Place {
                    root: PlaceRoot::Global(global),
                    segments: held.clone(),
                })
            });
        }
    }
    let Some(contents) = &mut state.parameter_contents else {
        return;
    };
    let key = (
        destination.place.root.clone(),
        destination.parameter_storage.clone().unwrap_or_default(),
    );
    let held = contents.entry(key).or_default();
    if strong {
        replace_projected_origins(held, &destination.place.segments, incoming);
    } else {
        extend_projected_origins(held, &destination.place.segments, incoming);
    }
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

/// Resolve the container storage destroyed by a release, not any reference
/// pointees retained inside the released value. Unresolved paths stay empty.
#[cfg(test)]
fn released_reference_destinations(
    body: &Body,
    flow: &FlowGraph,
    before: LoanSnapshots<'_>,
    value: NodeId,
    state: &LoanState,
) -> Vec<LoanOrigin> {
    if let NodeKind::Declaration(DeclarationId::Global(global)) = body.nodes[value.0].kind {
        // An owned global value can be explicitly consumed under #unsafe.
        // This is a destruction destination, not a mutable borrow of an
        // immutable global; it must never become reference-value provenance.
        return vec![global_storage_address(global, body.nodes[value.0].span)];
    }
    if matches!(
        body.nodes[value.0].ty,
        Some(Type::Reference { .. } | Type::PinnedReference { .. })
    ) {
        return value_loan_origins_at_events(body, flow, before, value, state);
    }
    let NodeKind::Form { head, children, .. } = &body.nodes[value.0].kind else {
        return Vec::new();
    };
    let Some(base) = children.get(1) else {
        return Vec::new();
    };
    if head == "deref" && children.len() == 2 {
        return value_loan_origins_at_events(body, flow, before, *base, state);
    }
    if head == "unsafe" && children.len() == 2 {
        return released_reference_destinations(body, flow, before, *base, state);
    }
    if matches!(head.as_str(), "get" | "get-payload" | "index") {
        let Some(slot) = value_projection(body, value) else {
            return Vec::new();
        };
        let mut destinations = released_reference_destinations(body, flow, before, *base, state);
        for origin in &mut destinations {
            origin.place.segments.push(slot.clone());
        }
        return destinations;
    }
    Vec::new()
}

fn dereferenced_value_places(
    body: &Body,
    flow: &FlowGraph,
    event: FlowNodeId,
    value: NodeId,
    origins: &FlowLoanOrigins,
) -> Option<Vec<Place>> {
    let NodeKind::Form { head, children, .. } = &body.nodes[value.0].kind else {
        return None;
    };
    if !matches!(head.as_str(), "deref" | "pin-read") || children.len() != 2 {
        return None;
    }
    let loans = origins.value_before(body, flow, event, children[1]);
    if loans
        .iter()
        .any(|loan| loan.lifetime_only || !loan.storage.is_empty())
    {
        return Some(Vec::new());
    }
    let mut places = Vec::new();
    for loan in loans {
        let place = loan.referent_place();
        if !places.contains(&place) {
            places.push(place);
        }
    }
    Some(places)
}

fn apply_parameter_loan_summary(
    origin: LoanOrigin,
    summary: &crate::typed_body::ParameterLoanSummary,
    state: &LoanState,
) -> Vec<LoanOrigin> {
    select_summary_inputs_with_slots(origin, &summary.input_storage, state)
        .into_iter()
        .map(|selected| {
            let mut origin = selected.origin;
            let mut storage = summary.storage.clone();
            let mut inputs = vec![None; storage.len()];
            for (output, input) in summary.storage_inputs.iter().enumerate() {
                if let Some(input) = input {
                    if let Some(slot) = selected.slots.get(*input) {
                        storage[output] = slot.clone();
                    }
                    inputs[output] = selected.inputs.get(*input).copied().flatten();
                }
            }
            storage.extend(origin.storage);
            origin.storage = storage;
            inputs.extend(origin.storage_inputs);
            origin.storage_inputs = inputs;
            if origin.storage_inputs.iter().all(Option::is_none) {
                origin.storage_inputs.clear();
            }
            origin.mutable = summary.mutable;
            origin.pinned = summary.pinned;
            origin.lifetime_only |= summary.lifetime_only;
            origin
                .place
                .segments
                .extend(summary.referent_projection.iter().cloned());
            origin
        })
        .collect()
}

#[cfg(test)]
fn apply_store_variant_facts(state: &mut HashMap<Place, VariantId>, store: &LoanStore) {
    let destination = store.destination.referent_place();
    state.retain(|place, _| !destination.overlaps(place));
    if !store.definitely_written || store.destination.lifetime_only {
        return;
    }
    for (path, variant) in &store.variants {
        let mut place = destination.clone();
        place.segments.extend_from_slice(path);
        if !place
            .segments
            .iter()
            .any(|segment| matches!(segment, Segment::DynamicIndex | Segment::SliceDynamicIndex))
        {
            state.insert(place, *variant);
        }
    }
}

#[cfg(test)]
fn joined_call_variant_stores(
    body: &Body,
    flow: &FlowGraph,
    before: LoanSnapshots<'_>,
    calls: &[(FlowNodeId, NodeId, Vec<Segment>)],
    variant: VariantId,
) -> Vec<LoanStore> {
    let mut result: Option<Vec<LoanStore>> = None;
    for (event, call, path) in calls {
        let Some(entry) = &before[event.0] else {
            return Vec::new();
        };
        let NodeKind::Form {
            callee: Some(callee),
            ..
        } = &body.nodes[call.0].kind
        else {
            return Vec::new();
        };
        let summaries = if path.is_empty() {
            body.call_store_variants
                .get(callee)
                .and_then(|groups| groups.get(&variant))
        } else {
            body.call_output_store_variants
                .get(callee)
                .and_then(|groups| groups.get(&(path.clone(), variant)))
        };
        let Some(summaries) = summaries else {
            return Vec::new();
        };
        let stores = substitute_call_stores(body, flow, before, *call, entry, summaries)
            .into_iter()
            .filter(|store| {
                !store.destination.lifetime_only
                    && matches!(
                        store.destination.place.root,
                        PlaceRoot::Local(_) | PlaceRoot::Parameter(_) | PlaceRoot::Global(_)
                    )
            })
            .collect::<Vec<_>>();
        if let Some(common) = &mut result {
            for held in common.iter_mut() {
                let mut definitely_written = false;
                for incoming in &stores {
                    if incoming.destination.referent_place() == held.destination.referent_place() {
                        definitely_written |= incoming.definitely_written;
                        merge_loan_origins(&mut held.incoming, &incoming.incoming);
                        held.variants
                            .retain(|path, variant| incoming.variants.get(path) == Some(variant));
                    }
                }
                held.definitely_written &= definitely_written;
                if !held.definitely_written {
                    held.variants.clear();
                }
            }
            for mut incoming in stores {
                if !common.iter().any(|held| {
                    held.destination.referent_place() == incoming.destination.referent_place()
                }) {
                    incoming.definitely_written = false;
                    common.push(incoming);
                }
            }
        } else {
            result = Some(stores);
        }
    }
    result.unwrap_or_default()
}

#[cfg(test)]
fn call_parameter_clears(
    body: &Body,
    flow: &FlowGraph,
    before: LoanSnapshots<'_>,
    value: NodeId,
    state: &LoanState,
) -> Vec<LoanOrigin> {
    let NodeKind::Form {
        callee: Some(callee),
        children,
        ..
    } = &body.nodes[value.0].kind
    else {
        return Vec::new();
    };
    let Some(clears) = body.call_parameter_clears.get(callee) else {
        return Vec::new();
    };
    substitute_call_clears(body, flow, before, state, children, clears)
}

#[cfg(test)]
fn substitute_call_clears(
    body: &Body,
    flow: &FlowGraph,
    before: LoanSnapshots<'_>,
    state: &LoanState,
    children: &[NodeId],
    clears: &[crate::typed_body::ParameterLoanSummary],
) -> Vec<LoanOrigin> {
    let mut result = Vec::new();
    for clear in clears {
        let destinations = if let Some(global) = global_summary_origin(clear) {
            vec![global]
        } else {
            children
                .get(clear.parameter + 1)
                .map_or_else(Vec::new, |argument| {
                    value_loan_origins_at_events(body, flow, before, *argument, state)
                        .into_iter()
                        .flat_map(|origin| apply_parameter_loan_summary(origin, clear, state))
                        .collect()
                })
        };
        if one_concrete_store_destination(&destinations) {
            merge_loan_origins(&mut result, &destinations);
        }
    }
    result
}

/// Never erase fresh contents on the strength of an old outcome tag.
#[cfg(test)]
fn correlated_call_variant_clears(
    body: &Body,
    flow: &FlowGraph,
    before: LoanSnapshots<'_>,
    refinement: &CallResultRefinement,
) -> Vec<LoanOrigin> {
    let (calls, variant, region) = refinement;
    joined_call_variant_clears(body, flow, before, calls, *variant)
        .into_iter()
        .filter(|clear| {
            !region
                .iter()
                .any(|event| match &flow.nodes[event.0].action {
                    FlowAction::Release { .. } => true,
                    FlowAction::Assign { place, .. } => {
                        place.root == clear.place.root
                            || matches!(clear.place.root, PlaceRoot::Parameter(_))
                    }
                    FlowAction::ScopeExit(bindings) => match clear.place.root {
                        PlaceRoot::Local(binding) | PlaceRoot::Parameter(binding) => {
                            bindings.contains(&binding)
                        }
                        _ => true,
                    },
                    _ => false,
                })
        })
        .collect()
}

/// Matching mutually exclusive calls proves only their common physical clears.
#[cfg(test)]
fn joined_call_variant_clears(
    body: &Body,
    flow: &FlowGraph,
    before: LoanSnapshots<'_>,
    calls: &[(FlowNodeId, NodeId, Vec<Segment>)],
    variant: VariantId,
) -> Vec<LoanOrigin> {
    let mut result: Option<Vec<LoanOrigin>> = None;
    for (event, call, path) in calls {
        let Some(entry) = &before[event.0] else {
            return Vec::new();
        };
        let NodeKind::Form {
            callee: Some(callee),
            children,
            ..
        } = &body.nodes[call.0].kind
        else {
            return Vec::new();
        };
        let summaries = if path.is_empty() {
            body.call_clear_variants
                .get(callee)
                .and_then(|groups| groups.get(&variant))
        } else {
            body.call_output_clear_variants
                .get(callee)
                .and_then(|groups| groups.get(&(path.clone(), variant)))
        };
        let Some(summaries) = summaries else {
            return Vec::new();
        };
        let clears = substitute_call_clears(body, flow, before, entry, children, summaries);
        if let Some(common) = &mut result {
            common.retain(|held| {
                clears
                    .iter()
                    .any(|incoming| incoming.referent_place() == held.referent_place())
            });
        } else {
            result = Some(
                clears
                    .into_iter()
                    .filter(|clear| {
                        matches!(
                            clear.place.root,
                            PlaceRoot::Local(_) | PlaceRoot::Parameter(_) | PlaceRoot::Global(_)
                        )
                    })
                    .collect(),
            );
        }
    }
    result.unwrap_or_default()
}

#[cfg(test)]
fn call_loan_stores(
    body: &Body,
    flow: &FlowGraph,
    before: LoanSnapshots<'_>,
    value: NodeId,
    state: &LoanState,
) -> Vec<LoanStore> {
    let NodeKind::Form {
        callee: Some(callee),
        ..
    } = &body.nodes[value.0].kind
    else {
        return Vec::new();
    };
    let Some(stores) = body.call_store_origins.get(callee) else {
        return Vec::new();
    };
    substitute_call_stores(body, flow, before, value, state, stores)
}

#[cfg(test)]
fn substitute_call_stores(
    body: &Body,
    flow: &FlowGraph,
    before: LoanSnapshots<'_>,
    value: NodeId,
    state: &LoanState,
    stores: &[crate::typed_body::ParameterStoreSummary],
) -> Vec<LoanStore> {
    let NodeKind::Form { children, .. } = &body.nodes[value.0].kind else {
        return Vec::new();
    };
    let substitute = |summary: &crate::typed_body::ParameterLoanSummary| {
        if let Some(origin) = global_summary_origin(summary) {
            return vec![origin];
        }
        children
            .get(summary.parameter + 1)
            .into_iter()
            .flat_map(|argument| {
                value_loan_origins_at_events(body, flow, before, *argument, state)
                    .into_iter()
                    .flat_map(|origin| apply_parameter_loan_summary(origin, summary, state))
            })
            .collect::<Vec<_>>()
    };
    let mut result = Vec::new();
    for store in stores {
        let mut incoming = Vec::new();
        let mut complete = true;
        for source in &store.sources {
            let selected = substitute(source);
            complete &= !selected.is_empty();
            merge_loan_origins(&mut incoming, &selected);
        }
        let destinations = substitute(&store.destination);
        let definitely_written =
            store.definitely_written && complete && one_concrete_store_destination(&destinations);
        for destination in destinations {
            result.push(LoanStore {
                destination,
                incoming: incoming.clone(),
                definitely_written,
                variants: store.variants.clone(),
            });
        }
    }
    // Apply whole-storage effects before refinements of their fields.
    result.sort_by_key(|store| store.destination.referent_place().segments.len());
    result
}

#[cfg(test)]
fn one_concrete_store_destination(destinations: &[LoanOrigin]) -> bool {
    let Some(first) = destinations.first() else {
        return false;
    };
    let place = first.referent_place();
    destinations.iter().all(|destination| {
        !destination.lifetime_only
            && destination.mutable
            && destination.storage.is_empty()
            && destination.referent_place() == place
    }) && !place.segments.iter().any(|segment| {
        matches!(
            segment,
            Segment::DynamicIndex | Segment::SliceDynamicIndex | Segment::SliceHalf(_)
        )
    })
}

#[cfg(test)]
fn select_summary_inputs(
    origin: LoanOrigin,
    path: &[Segment],
    state: &LoanState,
) -> Vec<LoanOrigin> {
    select_summary_inputs_with_slots(origin, path, state)
        .into_iter()
        .map(|selected| selected.origin)
        .collect()
}

struct SelectedLoan {
    origin: LoanOrigin,
    slots: Vec<Segment>,
    inputs: Vec<Option<usize>>,
}

fn select_summary_inputs_with_slots(
    origin: LoanOrigin,
    path: &[Segment],
    state: &LoanState,
) -> Vec<SelectedLoan> {
    let Some((head, tail)) = path.split_first() else {
        return vec![SelectedLoan {
            origin,
            slots: Vec::new(),
            inputs: Vec::new(),
        }];
    };
    if *head == Segment::Dereference && origin.storage.is_empty() && !origin.lifetime_only {
        #[cfg(test)]
        if matches!(origin.place.root, PlaceRoot::Global(_)) && state.parameter_contents.is_some() {
            let mut result = Vec::new();
            for loaded in loaded_parameter_value_origins(&origin, state) {
                for mut selected in select_summary_inputs_with_slots(loaded, tail, state) {
                    selected.slots.insert(0, Segment::Dereference);
                    selected.inputs.insert(0, None);
                    result.push(selected);
                }
            }
            return result;
        }
        if matches!(origin.place.root, PlaceRoot::Parameter(_)) {
            #[cfg(test)]
            if state.parameter_contents.is_some() {
                let mut result = Vec::new();
                for loaded in loaded_parameter_value_origins(&origin, state) {
                    for mut selected in select_summary_inputs_with_slots(loaded, tail, state) {
                        selected.slots.insert(0, Segment::Dereference);
                        selected.inputs.insert(0, None);
                        result.push(selected);
                    }
                }
                return result;
            }
            let mut loaded = origin;
            let storage = loaded.parameter_storage.get_or_insert_with(Vec::new);
            storage.push(Segment::Dereference);
            storage.append(&mut loaded.place.segments);
            let tail_start = storage.len();
            storage.extend_from_slice(tail);
            let mut inputs = vec![None];
            inputs.extend((tail_start..tail_start + tail.len()).map(Some));
            return vec![SelectedLoan {
                origin: loaded,
                slots: path.to_vec(),
                inputs,
            }];
        }
        if let PlaceRoot::Local(binding) = origin.place.root {
            let mut result = Vec::new();
            for held in &state[binding.0] {
                let prefix = &origin.place.segments;
                if held.storage.len() < prefix.len()
                    || !prefix
                        .iter()
                        .zip(&held.storage)
                        .all(|(expected, actual)| storage_slot_matches(expected, actual))
                {
                    continue;
                }
                let mut loaded = held.clone();
                loaded.drain_storage(prefix.len());
                loaded.mutable &= origin.mutable;
                for mut selected in select_summary_inputs_with_slots(loaded, tail, state) {
                    selected.slots.insert(0, Segment::Dereference);
                    selected.inputs.insert(0, None);
                    result.push(selected);
                }
            }
            return result;
        }
        return Vec::new();
    }
    let mut selected = origin;
    if selected
        .storage
        .first()
        .is_some_and(|actual| storage_slot_matches(head, actual))
    {
        let actual = if matches!(head, Segment::DynamicIndex | Segment::SliceDynamicIndex) {
            selected.storage[0].clone()
        } else {
            head.clone()
        };
        let input = selected.project_storage(&actual);
        let mut result = select_summary_inputs_with_slots(selected, tail, state);
        for selected in &mut result {
            selected.slots.insert(0, actual.clone());
            selected.inputs.insert(0, input);
        }
        result
    } else {
        Vec::new()
    }
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
        storage_inputs: Vec::new(),
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
        origin.prepend_storage(path);
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

/// A borrowed container's address is not the referent of a reference stored
/// in one of its fields. Load known local storage slots instead of projecting
/// the container address into a fictitious pointee identity.
fn projected_value_origins(
    body: &Body,
    base: NodeId,
    value: NodeId,
    slot: &Segment,
    incoming: Vec<LoanOrigin>,
    state: &LoanState,
) -> Vec<LoanOrigin> {
    let borrowed_container = matches!(
        body.nodes[base.0].ty,
        Some(Type::Reference { .. } | Type::PinnedReference { .. })
    );
    let mut result = Vec::new();
    for mut origin in incoming {
        if let Some(held) = origin.storage.first() {
            if storage_slot_matches(slot, held) {
                origin.project_storage(slot);
                merge_loan_origins(&mut result, &[origin]);
            }
            continue;
        }
        if !borrowed_container || origin.lifetime_only {
            continue;
        }
        #[cfg(test)]
        if matches!(origin.place.root, PlaceRoot::Global(_)) && state.parameter_contents.is_some() {
            origin.place.segments.push(slot.clone());
            merge_loan_origins(&mut result, &loaded_parameter_value_origins(&origin, state));
            continue;
        }
        if matches!(origin.place.root, PlaceRoot::Parameter(_)) {
            #[cfg(test)]
            if state.parameter_contents.is_some() {
                origin.place.segments.push(slot.clone());
                merge_loan_origins(&mut result, &loaded_parameter_value_origins(&origin, state));
                continue;
            }
            // A loaded aggregate may retain several reference slots. Select
            // only value slots below this projection, not loans reachable
            // through another reference boundary. These symbolic loads are
            // substituted against actual caller storage by return summaries.
            let PlaceRoot::Parameter(parameter) = origin.place.root else {
                unreachable!();
            };
            let mut prefix = origin.parameter_storage.clone().unwrap_or_default();
            prefix.push(Segment::Dereference);
            prefix.extend_from_slice(&origin.place.segments);
            prefix.push(slot.clone());
            let mut selected_schema = false;
            if let Some(schema) = body.parameter_referent_loan_slots.get(parameter.0) {
                for seed in schema {
                    if seed.storage.len() < prefix.len()
                        || !prefix
                            .iter()
                            .zip(&seed.storage)
                            .all(|(wanted, actual)| storage_slot_matches(wanted, actual))
                    {
                        continue;
                    }
                    let remaining = &seed.storage[prefix.len()..];
                    if remaining.contains(&Segment::Dereference) {
                        continue;
                    }
                    let mut loaded = origin.clone();
                    loaded.place.segments.clear();
                    let mut input_storage = prefix.clone();
                    input_storage.extend_from_slice(remaining);
                    loaded.parameter_storage = Some(input_storage);
                    loaded.storage = remaining.to_vec();
                    loaded.storage_inputs = (prefix.len()..prefix.len() + remaining.len())
                        .map(Some)
                        .collect();
                    loaded.mutable &= seed.mutable;
                    loaded.pinned = seed.pinned;
                    merge_loan_origins(&mut result, &[loaded]);
                    selected_schema = true;
                }
            }
            if selected_schema {
                continue;
            }
            if let Some(Type::Reference { mutable, .. } | Type::PinnedReference { mutable, .. }) =
                &body.nodes[value.0].ty
            {
                origin
                    .parameter_storage
                    .get_or_insert_with(Vec::new)
                    .push(Segment::Dereference);
                origin
                    .parameter_storage
                    .as_mut()
                    .unwrap()
                    .extend(origin.place.segments.drain(..));
                origin
                    .parameter_storage
                    .as_mut()
                    .unwrap()
                    .push(slot.clone());
                origin.mutable &= *mutable;
                origin.pinned =
                    matches!(body.nodes[value.0].ty, Some(Type::PinnedReference { .. }));
                merge_loan_origins(&mut result, &[origin]);
            }
            continue;
        }
        let PlaceRoot::Local(binding) = origin.place.root else {
            continue;
        };
        let mut path = origin.place.segments.clone();
        path.push(slot.clone());
        for held in &state[binding.0] {
            if held.storage.len() < path.len()
                || !path
                    .iter()
                    .zip(&held.storage)
                    .all(|(wanted, actual)| storage_slot_matches(wanted, actual))
            {
                continue;
            }
            let mut loaded = held.clone();
            loaded.drain_storage(path.len());
            // A shared container cannot lend exclusive access to an inner
            // mutable reference. Preserve the loaded pointee's own pin flag.
            loaded.mutable &= origin.mutable;
            merge_loan_origins(&mut result, &[loaded]);
        }
    }
    result
}

/// Loading a local value transfers its retained reference slots, not the
/// address used to reach the value. Parameter/global storage has no local
/// slot contents here and remains unresolved rather than inventing loans.
fn loaded_local_value_origins(incoming: &[LoanOrigin], state: &LoanState) -> Vec<LoanOrigin> {
    let mut result = Vec::new();
    for origin in incoming {
        if origin.lifetime_only || !origin.storage.is_empty() {
            continue;
        }
        let PlaceRoot::Local(binding) = origin.place.root else {
            continue;
        };
        let path = &origin.place.segments;
        for held in &state[binding.0] {
            if held.storage.len() < path.len()
                || !path
                    .iter()
                    .zip(&held.storage)
                    .all(|(wanted, actual)| storage_slot_matches(wanted, actual))
            {
                continue;
            }
            let mut loaded = held.clone();
            for selected in path {
                loaded.project_storage(selected);
            }
            loaded.mutable &= origin.mutable;
            merge_loan_origins(&mut result, &[loaded]);
        }
    }
    result
}

/// Whole-value loads can describe retained parameter slots without
/// equating their pointees with the borrowed container address. This is not a
/// pinned move/restore contract: preserving value provenance alone does not
/// establish referent initialization or variant-conditioned call effects.
fn dereference_value_origins(
    body: &Body,
    incoming: Vec<LoanOrigin>,
    state: &LoanState,
) -> Vec<LoanOrigin> {
    let mut result = loaded_local_value_origins(&incoming, state);
    for origin in incoming {
        if origin.lifetime_only || !origin.storage.is_empty() {
            continue;
        }
        #[cfg(test)]
        if state.parameter_contents.is_some()
            && matches!(
                origin.place.root,
                PlaceRoot::Parameter(_) | PlaceRoot::Global(_)
            )
        {
            merge_loan_origins(&mut result, &loaded_parameter_value_origins(&origin, state));
            continue;
        }
        let PlaceRoot::Parameter(parameter) = origin.place.root else {
            continue;
        };
        let mut prefix = origin.parameter_storage.clone().unwrap_or_default();
        prefix.push(Segment::Dereference);
        prefix.extend_from_slice(&origin.place.segments);
        for slot in body
            .parameter_referent_loan_slots
            .get(parameter.0)
            .into_iter()
            .flatten()
        {
            if slot.storage.len() < prefix.len()
                || !prefix
                    .iter()
                    .zip(&slot.storage)
                    .all(|(wanted, actual)| storage_slot_matches(wanted, actual))
            {
                continue;
            }
            let remaining = &slot.storage[prefix.len()..];
            if remaining.contains(&Segment::Dereference) {
                continue;
            }
            let mut loaded = origin.clone();
            loaded.place.segments.clear();
            loaded.parameter_storage = Some(slot.storage.clone());
            loaded.storage = remaining.to_vec();
            loaded.storage_inputs = (prefix.len()..slot.storage.len()).map(Some).collect();
            loaded.mutable &= slot.mutable;
            loaded.pinned = slot.pinned;
            merge_loan_origins(&mut result, &[loaded]);
        }
    }
    result
}

/// Select possible element contents rather than loading the entire backing
/// array as one element. Slice ranges and split views retain a region anchor,
/// not an exact offset mapping: even literal indexes must not fabricate a
/// physical element identity or a definite restoration destination.
#[cfg(test)]
fn project_slice_element_origins(origins: &mut [LoanOrigin], state: &LoanState) {
    if state.parameter_contents.is_none() {
        return;
    }
    for origin in origins {
        if origin.storage.is_empty() && !origin.lifetime_only {
            origin.place.segments.push(Segment::DynamicIndex);
        }
    }
}

#[cfg(test)]
fn global_storage_address(global: crate::typed_ir::GlobalId, span: Option<Span>) -> LoanOrigin {
    LoanOrigin {
        place: Place::root(PlaceRoot::Global(global)),
        mutable: true,
        pinned: false,
        lifetime_only: false,
        span,
        borrowed_from: None,
        storage: Vec::new(),
        parameter_storage: None,
        storage_inputs: Vec::new(),
    }
}

fn value_loan_origins(body: &Body, id: NodeId, state: &LoanState) -> Vec<LoanOrigin> {
    let node = &body.nodes[id.0];
    match &node.kind {
        NodeKind::Symbol {
            binding: Some(binding),
            ..
        } => state[binding.0].clone(),
        #[cfg(test)]
        NodeKind::Declaration(DeclarationId::Global(global)) => {
            loaded_parameter_value_origins(&global_storage_address(*global, node.span), state)
        }
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
                        merge_loan_origins(
                            &mut result,
                            &apply_parameter_loan_summary(origin, source, state),
                        );
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
                        origin.clear_storage();
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
            if matches!(head.as_str(), "deref" | "pin-read") && children.len() == 2 =>
        {
            let incoming = value_loan_origins(body, children[1], state);
            dereference_value_origins(body, incoming, state)
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
            #[cfg(test)]
            if matches!(head.as_str(), "slice-idx" | "slice-mut-idx") {
                project_slice_element_origins(&mut origins, state);
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
                    origin.prepend_storage(&[Segment::SliceHalf(half)]);
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
            projected_value_origins(
                body,
                *base,
                id,
                &slot,
                value_loan_origins(body, *base, state),
                state,
            )
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
                origin.prepend_storage(&[slot.clone()]);
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
                    origin.prepend_storage(&[slot.clone()]);
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
    before: LoanSnapshots<'_>,
    value: NodeId,
    state: &LoanState,
) -> Vec<LoanOrigin> {
    if matches!(body.nodes[value.0].kind, NodeKind::Loop(_)) {
        let mut result = Vec::new();
        for &index in &before.events_by_value[value.0] {
            let event = &flow.nodes[index];
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
            for &index in &before.events_by_value[alternative.0] {
                let event = &flow.nodes[index];
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
        if matches!(head.as_str(), "deref" | "pin-read") && children.len() == 2 {
            // Moving from a parameter consumes its contents at Evaluate. A
            // later Bind must transfer the value from the pre-move snapshot,
            // not reload either empty storage or a subsequent replacement.
            #[cfg(test)]
            let state = if body.consuming_pin_reads.contains(&value)
                && state.parameter_contents.is_some()
            {
                before.events_by_value[value.0]
                    .iter()
                    .find_map(|&index| {
                        let event = &flow.nodes[index];
                        matches!(event.action, FlowAction::Evaluate(id) if id == value)
                            .then(|| before[index].as_ref())
                            .flatten()
                    })
                    .unwrap_or(state)
            } else {
                state
            };
            let incoming = value_loan_origins_at_events(body, flow, before, children[1], state);
            return dereference_value_origins(body, incoming, state);
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
            #[cfg(test)]
            if matches!(head.as_str(), "slice-idx" | "slice-mut-idx") {
                project_slice_element_origins(&mut loans, state);
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
                    origin.prepend_storage(&[Segment::SliceHalf(half)]);
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
            return projected_value_origins(
                body,
                *base,
                value,
                &slot,
                value_loan_origins_at_events(body, flow, before, *base, state),
                state,
            );
        }
        if let Some(callee) = callee {
            #[cfg(test)]
            let state = if body
                .call_store_origins
                .get(callee)
                .is_some_and(|stores| stores.iter().any(|store| store.definitely_written))
                || body
                    .call_parameter_clears
                    .get(callee)
                    .is_some_and(|clears| !clears.is_empty())
                || body
                    .call_clear_variants
                    .get(callee)
                    .is_some_and(|groups| groups.values().any(|clears| !clears.is_empty()))
            {
                // Return summaries selecting entry storage must not observe
                // the caller's state after this call has already cleared it.
                before.events_by_value[value.0]
                    .iter()
                    .find_map(|&index| {
                        let node = &flow.nodes[index];
                        matches!(node.action, FlowAction::Evaluate(id) if id == value)
                            .then(|| before[index].as_ref())
                            .flatten()
                    })
                    .unwrap_or(state)
            } else {
                state
            };
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
                        merge_loan_origins(
                            &mut result,
                            &apply_parameter_loan_summary(origin, source, state),
                        );
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
                        origin.clear_storage();
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
                origin.prepend_storage(&[slot.clone()]);
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
                    origin.prepend_storage(&[slot.clone()]);
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
                next.clear_storage();
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
        storage_inputs: Vec::new(),
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

#[cfg(test)]
enum CallInputComponent {
    Selected(NodeId, Vec<Segment>),
    Missing,
    /// A resolved constructor of another variant in the same enum.
    Inactive,
}

#[cfg(test)]
fn inactive_variant_slot(
    state: &HashMap<Place, VariantId>,
    base: &Place,
    path: &[Segment],
) -> bool {
    let mut place = base.clone();
    for segment in path {
        if let Segment::Payload(wanted, _) = segment {
            if state
                .get(&place)
                .is_some_and(|actual| actual.owner == wanted.owner && actual != wanted)
            {
                return true;
            }
        }
        place.segments.push(segment.clone());
    }
    false
}

#[cfg(test)]
fn value_variant_bounds(
    body: &Body,
    value: NodeId,
    state: &HashMap<Place, VariantId>,
    context: Option<VariantContext<'_>>,
) -> VariantBounds {
    if let Some((flow, origins, _, snapshots)) = context {
        let events = captured_variant_events(context.unwrap(), value);
        if !events.is_empty() {
            let mut common = None;
            for event in events {
                let Some(state) = &snapshots[event.0] else {
                    return HashMap::new();
                };
                let incoming = value_variant_bounds(
                    body,
                    value,
                    state,
                    Some((flow, origins, event, snapshots)),
                );
                if let Some(held) = &mut common {
                    join_variant_bounds(held, &incoming);
                } else {
                    common = Some(incoming);
                }
            }
            return common.unwrap_or_default();
        }
    }
    if matches!(
        body.nodes[value.0].ty,
        Some(Type::Reference { .. } | Type::PinnedReference { .. } | Type::RawPointer { .. })
    ) {
        return HashMap::new();
    }
    let mut alternatives = Vec::new();
    collect_result_alternatives(body, value, &mut alternatives);
    if alternatives.len() != 1 || alternatives[0] != value {
        let mut result = None;
        for alternative in alternatives {
            let incoming = value_variant_bounds(body, alternative, state, context);
            if let Some(held) = &mut result {
                join_variant_bounds(held, &incoming);
            } else {
                result = Some(incoming);
            }
        }
        return result.unwrap_or_default();
    }
    let mut result = value_variant_facts(body, value, state, context)
        .into_iter()
        .map(|(place, variant)| (place.segments, HashSet::from([variant])))
        .collect::<VariantBounds>();
    let NodeKind::Form {
        head,
        children,
        callee,
        ..
    } = &body.nodes[value.0].kind
    else {
        return result;
    };
    if let Some(callee) = callee {
        return body
            .call_return_variant_bounds
            .get(callee)
            .cloned()
            .unwrap_or_default();
    }
    if matches!(head.as_str(), "unsafe" | "clone") && children.len() == 2 {
        return value_variant_bounds(body, children[1], state, context);
    }
    let start = if matches!(head.as_str(), "tuple" | "array" | "array-of") {
        constructor_values_start(body.nodes[value.0].ty.as_ref(), children.len())
    } else {
        1
    };
    for (index, child) in children.iter().skip(start).enumerate() {
        let Some(slot) = aggregate_slot(body, head, children, index) else {
            continue;
        };
        for (mut path, variants) in value_variant_bounds(body, *child, state, context) {
            path.insert(0, slot.clone());
            result.insert(path, variants);
        }
    }
    result
}

#[cfg(test)]
fn value_variant_facts(
    body: &Body,
    value: NodeId,
    state: &HashMap<Place, VariantId>,
    context: Option<VariantContext<'_>>,
) -> HashMap<Place, VariantId> {
    if let Some((flow, origins, _, snapshots)) = context {
        let events = captured_variant_events(context.unwrap(), value);
        if !events.is_empty() {
            let mut common: Option<HashMap<Place, VariantId>> = None;
            for event in events {
                let Some(state) = &snapshots[event.0] else {
                    return HashMap::new();
                };
                let incoming = value_variant_facts(
                    body,
                    value,
                    state,
                    Some((flow, origins, event, snapshots)),
                );
                if let Some(held) = &mut common {
                    held.retain(|place, variant| incoming.get(place) == Some(variant));
                } else {
                    common = Some(incoming);
                }
            }
            return common.unwrap_or_default();
        }
    }
    if let NodeKind::Declaration(DeclarationId::Variant(variant)) = body.nodes[value.0].kind {
        return HashMap::from([(Place::root(PlaceRoot::Local(BindingId(0))), variant)]);
    }
    // Enum facts describe owned value storage, not a reference's address slot.
    // Borrowing an enum must not turn its discriminant into a pointer fact.
    if matches!(
        body.nodes[value.0].ty,
        Some(Type::Reference { .. } | Type::PinnedReference { .. } | Type::RawPointer { .. })
    ) {
        return HashMap::new();
    }
    if let Some(source) = Place::from_expression(body, value) {
        let sources = if reads_through_reference(body, value) {
            match (context, source.root) {
                (Some((_, origins, event, _)), PlaceRoot::Local(binding)) => {
                    origins.projected_referents(event, binding, &source.segments)
                }
                _ => Vec::new(),
            }
        } else {
            vec![source]
        };
        let mut common: Option<HashMap<Place, VariantId>> = None;
        for source in sources {
            let selected = state
                .iter()
                .filter_map(|(place, variant)| {
                    (place.root == source.root && place.segments.starts_with(&source.segments))
                        .then(|| {
                            (
                                Place {
                                    root: PlaceRoot::Local(BindingId(0)),
                                    segments: place.segments[source.segments.len()..].to_vec(),
                                },
                                *variant,
                            )
                        })
                })
                .collect::<HashMap<_, _>>();
            if let Some(held) = &mut common {
                held.retain(|path, variant| selected.get(path) == Some(variant));
            } else {
                common = Some(selected);
            }
        }
        return common.unwrap_or_default();
    }
    let NodeKind::Form {
        head,
        children,
        callee,
        ..
    } = &body.nodes[value.0].kind
    else {
        return HashMap::new();
    };
    if let Some(callee) = callee {
        return body
            .call_return_variants
            .get(callee)
            .map_or_else(HashMap::new, |facts| {
                facts
                    .iter()
                    .map(|(path, variant)| {
                        (
                            Place {
                                root: PlaceRoot::Local(BindingId(0)),
                                segments: path.clone(),
                            },
                            *variant,
                        )
                    })
                    .collect()
            });
    }
    if matches!(head.as_str(), "unsafe" | "clone") && children.len() == 2 {
        return value_variant_facts(body, children[1], state, context);
    }
    let mut result = HashMap::new();
    if let Some(NodeKind::Declaration(DeclarationId::Variant(variant))) =
        children.first().map(|id| &body.nodes[id.0].kind)
    {
        result.insert(Place::root(PlaceRoot::Local(BindingId(0))), *variant);
    }
    let start = if matches!(head.as_str(), "tuple" | "array" | "array-of") {
        constructor_values_start(body.nodes[value.0].ty.as_ref(), children.len())
    } else {
        1
    };
    for (index, child) in children.iter().skip(start).enumerate() {
        let Some(slot) = aggregate_slot(body, head, children, index) else {
            continue;
        };
        for (mut place, variant) in value_variant_facts(body, *child, state, context) {
            place.segments.insert(0, slot.clone());
            result.insert(place, variant);
        }
    }
    result
}

#[cfg(test)]
fn distribute_pattern_variants(
    body: &Body,
    pattern: NodeId,
    incoming: &HashMap<Place, VariantId>,
    state: &mut HashMap<Place, VariantId>,
) {
    match &body.nodes[pattern.0].kind {
        NodeKind::Symbol {
            binding: Some(binding),
            ..
        } => {
            let root = PlaceRoot::Local(*binding);
            state.retain(|place, _| place.root != root);
            for (place, variant) in incoming {
                state.insert(
                    Place {
                        root: root.clone(),
                        segments: place.segments.clone(),
                    },
                    *variant,
                );
            }
        }
        NodeKind::Form { head, children, .. } => {
            for (index, child) in children.iter().skip(1).enumerate() {
                let Some(slot) = aggregate_slot(body, head, children, index) else {
                    continue;
                };
                let nested = incoming
                    .iter()
                    .filter_map(|(place, variant)| {
                        (place.segments.first() == Some(&slot)).then(|| {
                            (
                                Place {
                                    root: PlaceRoot::Local(BindingId(0)),
                                    segments: place.segments[1..].to_vec(),
                                },
                                *variant,
                            )
                        })
                    })
                    .collect();
                distribute_pattern_variants(body, *child, &nested, state);
            }
        }
        _ => {}
    }
}

#[cfg(test)]
fn known_variant_slot(state: &HashMap<Place, VariantId>, base: &Place, path: &[Segment]) -> bool {
    let mut place = base.clone();
    for segment in path {
        if let Segment::Payload(wanted, _) = segment {
            if state.get(&place) != Some(wanted) {
                return false;
            }
        }
        place.segments.push(segment.clone());
    }
    true
}

#[cfg(test)]
fn collect_call_input_components(
    body: &Body,
    value: NodeId,
    path: &[Segment],
    output: &mut Vec<CallInputComponent>,
) {
    let mut alternatives = Vec::new();
    collect_result_alternatives(body, value, &mut alternatives);
    for alternative in alternatives {
        if let NodeKind::Form { head, children, .. } = &body.nodes[alternative.0].kind {
            if matches!(head.as_str(), "unsafe" | "clone") && children.len() == 2 {
                collect_call_input_components(body, children[1], path, output);
                continue;
            }
            if let Some((selected, tail)) = path.split_first() {
                if let (
                    Segment::Payload(wanted, _),
                    Some(NodeKind::Declaration(DeclarationId::Variant(actual))),
                ) = (selected, children.first().map(|id| &body.nodes[id.0].kind))
                {
                    if wanted != actual && wanted.owner == actual.owner {
                        // This alternative cannot contain the requested
                        // payload. It contributes no effect, not an unknown
                        // reference and never definite consumption.
                        output.push(CallInputComponent::Inactive);
                        continue;
                    }
                }
                if head == "array-repeat"
                    && matches!(selected, Segment::Index(_) | Segment::DynamicIndex)
                {
                    let valid = matches!(body.nodes[alternative.0].ty.as_ref(), Some(Type::Array(_, length))
                    if *length > 0 && match selected {
                        Segment::Index(index) => *index < *length as u128,
                        _ => true,
                    });
                    if !valid {
                        output.push(CallInputComponent::Missing);
                        continue;
                    }
                    if let Some(element) = children.get(if children.len() == 3 { 2 } else { 1 }) {
                        collect_call_input_components(body, *element, tail, output);
                        continue;
                    }
                }
                if aggregate_slot(body, head, children, 0).is_some() {
                    let start = if matches!(head.as_str(), "array" | "array-of" | "tuple") {
                        constructor_values_start(
                            body.nodes[alternative.0].ty.as_ref(),
                            children.len(),
                        )
                    } else {
                        1
                    };
                    let mut found = false;
                    for (index, child) in children.iter().skip(start).enumerate() {
                        if aggregate_slot(body, head, children, index)
                            .is_some_and(|slot| storage_slot_matches(selected, &slot))
                        {
                            found = true;
                            collect_call_input_components(body, *child, tail, output);
                        }
                    }
                    if found {
                        continue;
                    }
                    output.push(CallInputComponent::Missing);
                    continue;
                }
            }
        }
        output.push(CallInputComponent::Selected(alternative, path.to_vec()));
    }
}

#[cfg(test)]
fn returned_provenance_components(body: &Body, value: NodeId) -> Vec<NodeId> {
    let mut pending = vec![value];
    let mut seen = HashSet::new();
    let mut components = Vec::new();
    while let Some(value) = pending.pop() {
        let mut alternatives = Vec::new();
        collect_result_alternatives(body, value, &mut alternatives);
        for alternative in alternatives {
            if !seen.insert(alternative) {
                continue;
            }
            components.push(alternative);
            let NodeKind::Form { head, children, .. } = &body.nodes[alternative.0].kind else {
                continue;
            };
            if matches!(head.as_str(), "unsafe" | "clone") && children.len() == 2 {
                pending.push(children[1]);
            } else if head == "array-repeat" {
                if matches!(body.nodes[alternative.0].ty, Some(Type::Array(_, length)) if length > 0)
                {
                    if let Some(child) = children.get(if children.len() == 3 { 2 } else { 1 }) {
                        pending.push(*child);
                    }
                }
            } else if aggregate_slot(body, head, children, 0).is_some() {
                let start = if matches!(head.as_str(), "array" | "array-of" | "tuple") {
                    constructor_values_start(body.nodes[alternative.0].ty.as_ref(), children.len())
                } else {
                    1
                };
                pending.extend(children.iter().skip(start).copied());
            }
        }
    }
    components
}

#[cfg(test)]
fn constructor_variant_at_storage(
    body: &Body,
    mut value: NodeId,
    storage: &[Segment],
) -> Option<crate::typed_ir::VariantId> {
    for segment in storage {
        let NodeKind::Form { head, children, .. } = &body.nodes[value.0].kind else {
            return None;
        };
        let start = if matches!(head.as_str(), "array" | "array-of" | "tuple") {
            constructor_values_start(body.nodes[value.0].ty.as_ref(), children.len())
        } else {
            1
        };
        value = children
            .iter()
            .skip(start)
            .enumerate()
            .find_map(|(index, child)| {
                (aggregate_slot(body, head, children, index).as_ref() == Some(segment))
                    .then_some(*child)
            })?;
    }
    let node = match &body.nodes[value.0].kind {
        NodeKind::Form { children, .. } => &body.nodes[children.first()?.0].kind,
        node => node,
    };
    match node {
        NodeKind::Declaration(DeclarationId::Variant(variant)) => Some(*variant),
        _ => None,
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
                        origin.project_storage(&slot);
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
    fn global_contents_keep_identity_and_do_not_invent_unknown_entry_loans() {
        let program =
            crate::parse_program("(#static Shared u64 0u64) (#fn main () u64 (#return 0u64))")
                .unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let id = checked.declarations().global_id("Shared").unwrap();
        let origin = |root| LoanOrigin {
            place: Place::root(root),
            mutable: true,
            pinned: false,
            lifetime_only: false,
            span: None,
            borrowed_from: None,
            storage: Vec::new(),
            parameter_storage: None,
            storage_inputs: Vec::new(),
        };
        let global = origin(PlaceRoot::Global(id));
        let parameter = origin(PlaceRoot::Parameter(BindingId(0)));
        let first = origin(PlaceRoot::Parameter(BindingId(1)));
        let second = origin(PlaceRoot::Parameter(BindingId(2)));
        let mut state = empty_loan_state(0);
        state.parameter_contents = Some(HashMap::new());
        assert!(loaded_parameter_value_origins(&global, &state).is_empty());
        store_parameter_contents(&mut state, &global, vec![first.clone()], false);
        assert!(
            loaded_parameter_value_origins(&global, &state).is_empty(),
            "a may-write cannot manufacture unknown entry provenance"
        );
        store_parameter_contents(&mut state, &global, vec![first.clone()], true);
        store_parameter_contents(&mut state, &parameter, vec![second.clone()], true);
        assert_eq!(loaded_parameter_value_origins(&global, &state), vec![first]);
        assert_eq!(
            loaded_parameter_value_origins(&parameter, &state),
            vec![second.clone()]
        );
        store_parameter_contents(&mut state, &global, Vec::new(), true);
        assert!(loaded_parameter_value_origins(&global, &state).is_empty());
        assert_eq!(
            loaded_parameter_value_origins(&parameter, &state),
            vec![second]
        );
    }

    #[test]
    fn global_contents_are_known_only_for_every_path_concrete_coverage() {
        let program =
            crate::parse_program("(#static Shared u64 0u64) (#fn main () u64 (#return 0u64))")
                .unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let global = checked.declarations().global_id("Shared").unwrap();
        let address = |segments| LoanOrigin {
            place: Place {
                root: PlaceRoot::Global(global),
                segments,
            },
            mutable: true,
            pinned: false,
            lifetime_only: false,
            span: None,
            borrowed_from: None,
            storage: Vec::new(),
            parameter_storage: None,
            storage_inputs: Vec::new(),
        };
        let mut whole = empty_loan_state(0);
        whole.parameter_contents = Some(HashMap::new());
        store_parameter_contents(&mut whole, &address(vec![]), Vec::new(), true);
        let mut field = empty_loan_state(0);
        field.parameter_contents = Some(HashMap::new());
        store_parameter_contents(
            &mut field,
            &address(vec![Segment::Tuple(0)]),
            Vec::new(),
            true,
        );
        assert!(merge_loan_states(&mut whole, &field));
        assert_eq!(
            whole.global_known_contents[&global],
            HashSet::from([vec![Segment::Tuple(0)]])
        );
        let mut unknown = empty_loan_state(0);
        unknown.parameter_contents = Some(HashMap::new());
        assert!(merge_loan_states(&mut whole, &unknown));
        assert!(!whole.global_known_contents.contains_key(&global));
        store_parameter_contents(
            &mut whole,
            &address(vec![Segment::DynamicIndex]),
            Vec::new(),
            true,
        );
        assert!(
            whole.global_known_contents[&global].is_empty(),
            "dynamic writes are not exact coverage"
        );
    }

    #[test]
    fn definite_consumption_meet_preserves_only_structural_coverage() {
        let root = Place::root(PlaceRoot::Local(BindingId(0)));
        let place = |segments| Place {
            root: root.root.clone(),
            segments,
        };
        let child = place(vec![Segment::Tuple(0)]);
        for (left, right) in [(root.clone(), child.clone()), (child.clone(), root.clone())] {
            let changed = left != child;
            let mut held = HashSet::from([left]);
            assert_eq!(
                intersect_consumed_coverage(&mut held, &HashSet::from([right])),
                changed
            );
            assert_eq!(held, HashSet::from([child.clone()]));
        }
        for boundary in [
            Segment::Dereference,
            Segment::DynamicIndex,
            Segment::SliceIndex(0),
            Segment::SliceDynamicIndex,
            Segment::SliceHalf(0),
        ] {
            let mut held = HashSet::from([root.clone()]);
            let incoming = HashSet::from([place(vec![boundary, Segment::Tuple(0)])]);
            assert!(intersect_consumed_coverage(&mut held, &incoming));
            assert!(held.is_empty());
        }
        let mut held = HashSet::from([child.clone()]);
        assert!(intersect_consumed_coverage(
            &mut held,
            &HashSet::from([place(vec![Segment::Tuple(1)])])
        ));
        assert!(held.is_empty());
        let mut held = HashSet::from([root.clone()]);
        assert!(intersect_consumed_coverage(
            &mut held,
            &HashSet::from([Place::root(PlaceRoot::Local(BindingId(1)))])
        ));
        assert!(held.is_empty());

        // Structural members of an already identified pointee remain parts
        // of that pointee; the join cannot cross its address boundary.
        let pointee = place(vec![Segment::Dereference]);
        let member = place(vec![Segment::Dereference, Segment::Tuple(0)]);
        let mut held = HashSet::from([pointee]);
        assert!(intersect_consumed_coverage(
            &mut held,
            &HashSet::from([member.clone()])
        ));
        assert_eq!(held, HashSet::from([member]));

        let exact_unknown = place(vec![Segment::DynamicIndex]);
        let mut held = HashSet::from([exact_unknown.clone()]);
        assert!(!intersect_consumed_coverage(
            &mut held,
            &HashSet::from([exact_unknown])
        ));
    }

    #[test]
    fn reaching_provenance_definitions_do_not_cross_later_operand_effects() {
        for (effect, expected) in [
            ("()", true),
            ("(#block (#set value 2u64) ())", false),
            ("(#block (#call touch ()) ())", false),
        ] {
            let source = format!(
                "(#fn touch () () (#return ()))
              (#fn inspect () (#tuple u64 ())
                (#let-mut value u64 1u64)
                (#let pair (#tuple u64 ()) (#tuple value {effect}))
                (#return pair))"
            );
            let program = crate::parse_program(&source).unwrap();
            let checked = crate::CheckedProgram::validate(&program).unwrap();
            let declarations = checked.declarations();
            let body = &declarations.bodies["inspect"];
            let flow = &declarations.flows["inspect"];
            let binding = |name: &str| {
                BindingId(
                    body.bindings
                        .iter()
                        .position(|binding| binding.name == name)
                        .unwrap(),
                )
            };
            let value_binding = binding("value");
            let event = flow
                .nodes
                .iter()
                .position(|node| {
                    matches!(node.action,
                FlowAction::Bind { binding: found, .. } if found == binding("pair"))
                })
                .unwrap();
            let read = flow
                .nodes
                .iter()
                .find_map(|node| match &node.action {
                    FlowAction::Read { value, place, .. }
                        if place.root == PlaceRoot::Local(value_binding) =>
                    {
                        Some(*value)
                    }
                    _ => None,
                })
                .unwrap();
            assert_eq!(
                flow.unchanged_local_definitions(
                    body,
                    &flow.loan_origins(body),
                    FlowNodeId(event),
                    value_binding,
                    read
                )
                .is_some(),
                expected,
                "{effect}"
            );
        }
    }

    #[test]
    fn loaded_parameter_pointees_have_distinct_access_paths_from_the_container() {
        let program = crate::parse_program(
            "(#struct Views (: left (#pin-ref u64) : right (#pin-ref u64)))
             (#fn inspect (: source (#ref Views)) u64
               (#let loaded Views (#deref source))
               (#let left u64 (#unsafe (#pin-read (#get loaded left))))
               (#let right u64 (#unsafe (#pin-read (#get loaded right))))
               (#forget loaded)
               (#return (#u64.+.wrap left right)))",
        )
        .unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let declarations = checked.declarations();
        let body = &declarations.bodies["inspect"];
        let flow = &declarations.flows["inspect"];
        let origins = flow.loan_origins(body);
        let loaded = BindingId(
            body.bindings
                .iter()
                .position(|binding| binding.name == "loaded")
                .unwrap(),
        );
        let mut accesses = Vec::new();
        for (index, node) in flow.nodes.iter().enumerate() {
            let FlowAction::Evaluate(value) = node.action else {
                continue;
            };
            if !matches!(&body.nodes[value.0].kind,
                NodeKind::Form { head, .. } if head == "pin-read")
            {
                continue;
            }
            let places =
                dereferenced_value_places(body, flow, FlowNodeId(index), value, &origins).unwrap();
            assert_eq!(places.len(), 1);
            let NodeKind::Form { children, .. } = &body.nodes[value.0].kind else {
                unreachable!()
            };
            let NodeKind::Form {
                children: projection,
                ..
            } = &body.nodes[children[1].0].kind
            else {
                unreachable!()
            };
            let NodeKind::Declaration(crate::typed_ir::DeclarationId::Field(field)) =
                body.nodes[projection[2].0].kind
            else {
                unreachable!()
            };
            assert_eq!(
                origins.projected_referents(
                    FlowNodeId(index),
                    loaded,
                    &[Segment::Field(field), Segment::Dereference]
                ),
                places,
                "production projected accesses must preserve the same input identity"
            );
            let held = origins
                .before(FlowNodeId(index), loaded)
                .iter()
                .find(|origin| origin.storage == vec![Segment::Field(field)])
                .unwrap();
            assert_eq!(
                held.referent_place(),
                places[0],
                "held-loan comparisons must use the same identity as accesses"
            );
            accesses.push(places[0].clone());
        }
        let source = PlaceRoot::Parameter(BindingId(0));
        assert_eq!(accesses.len(), 2);
        for place in &accesses {
            assert_eq!(place.root, source);
            assert_ne!(
                *place,
                Place::root(source.clone()),
                "a stored pointee must not collapse to the container address"
            );
        }
        assert_ne!(accesses[0], accesses[1]);
        for field in ["left", "right"] {
            let expected = vec![
                Segment::Dereference,
                Segment::Field(
                    declarations
                        .field_id(&Type::Named("Views".into()), field)
                        .unwrap(),
                ),
            ];
            assert!(accesses.iter().any(|place| place.segments == expected));
        }
    }

    #[test]
    fn whole_local_loads_specialize_selected_slots_and_do_not_invent_pointees() {
        let address = LoanOrigin {
            place: Place {
                root: PlaceRoot::Local(BindingId(0)),
                segments: vec![Segment::Index(1)],
            },
            mutable: false,
            pinned: true,
            span: None,
            borrowed_from: None,
            storage: Vec::new(),
            parameter_storage: None,
            storage_inputs: Vec::new(),
            lifetime_only: false,
        };
        let held = LoanOrigin {
            place: Place::root(PlaceRoot::Parameter(BindingId(0))),
            mutable: true,
            pinned: true,
            span: None,
            borrowed_from: None,
            storage: vec![Segment::DynamicIndex],
            parameter_storage: Some(vec![Segment::DynamicIndex]),
            storage_inputs: vec![Some(0)],
            lifetime_only: false,
        };
        let state: LoanState = vec![vec![held]].into();
        let mut wrapped = state[0][0].clone();
        let input_identity = wrapped.referent_place();
        wrapped.prepend_storage(&[Segment::Tuple(7)]);
        assert_eq!(
            wrapped.referent_place(),
            input_identity,
            "constructor output slots must not alter original pointee identity"
        );
        wrapped.place.segments.push(Segment::Index(4));
        assert_eq!(
            wrapped.referent_place().segments,
            vec![Segment::DynamicIndex, Segment::Index(4)],
            "input identity precedes physical referent projections"
        );
        wrapped.place.root = PlaceRoot::Local(BindingId(0));
        assert_eq!(
            wrapped.referent_place().segments,
            vec![Segment::Index(4)],
            "parameter metadata cannot prefix an actual local storage root"
        );
        let loaded = loaded_local_value_origins(std::slice::from_ref(&address), &state);
        assert_eq!(loaded.len(), 1);
        assert_eq!(loaded[0].place.root, PlaceRoot::Parameter(BindingId(0)));
        assert_eq!(loaded[0].parameter_storage, Some(vec![Segment::Index(1)]));
        assert!(loaded[0].storage.is_empty());
        assert!(loaded[0].storage_inputs.is_empty());
        assert!(
            !loaded[0].mutable,
            "a shared address cannot grant exclusivity"
        );
        assert!(loaded[0].pinned, "the stored pointee's pin flag survives");
        let incoming = vec![address.clone(); 128];
        let original_incoming = incoming.clone();
        let original_contents = state[0].clone();
        let mut repeated = loaded_local_value_origins(&incoming, &state);
        assert_eq!(
            repeated, loaded,
            "duplicate inputs keep output deduplication"
        );
        repeated[0].place.segments.push(Segment::Index(99));
        assert_eq!(incoming, original_incoming, "loading borrows input origins");
        assert_eq!(
            state[0], original_contents,
            "selected outputs own their loans"
        );
        for missing in [
            LoanOrigin {
                lifetime_only: true,
                ..address.clone()
            },
            LoanOrigin {
                storage: vec![Segment::Tuple(0)],
                ..address.clone()
            },
            LoanOrigin {
                place: Place::root(PlaceRoot::Parameter(BindingId(0))),
                ..address.clone()
            },
            LoanOrigin {
                place: Place {
                    root: PlaceRoot::Local(BindingId(0)),
                    segments: vec![Segment::Tuple(0)],
                },
                ..address.clone()
            },
        ] {
            assert!(loaded_local_value_origins(&[missing], &state).is_empty());
        }
        assert!(loaded_local_value_origins(&[address], &empty_loan_state(1)).is_empty());
    }

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
                for held in state.iter_mut() {
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
        for held in origins.before[write].as_mut().unwrap().iter_mut() {
            held.clear();
        }
        for (index, node) in flow.nodes.iter().enumerate() {
            if flow_action_has_value(&node.action, children[1]) {
                for held in origins.before[index].as_mut().unwrap().iter_mut() {
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
            storage_inputs: Vec::new(),
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
    fn summary_dereference_slots_load_actual_local_loans() {
        let origin = |root, storage| LoanOrigin {
            place: Place::root(root),
            mutable: true,
            pinned: false,
            lifetime_only: false,
            span: None,
            borrowed_from: None,
            storage,
            parameter_storage: None,
            storage_inputs: Vec::new(),
        };
        let state: LoanState = vec![
            vec![
                origin(PlaceRoot::Local(BindingId(1)), vec![Segment::Tuple(0)]),
                origin(PlaceRoot::Local(BindingId(2)), vec![Segment::Tuple(1)]),
            ],
            vec![],
            vec![],
        ]
        .into();
        let container = origin(PlaceRoot::Local(BindingId(0)), vec![]);
        let path = [Segment::Dereference, Segment::Tuple(1)];
        let loaded = super::select_summary_inputs(container.clone(), &path, &state);
        assert_eq!(loaded.len(), 1);
        assert_eq!(loaded[0].place.root, PlaceRoot::Local(BindingId(2)));
        assert!(loaded[0].storage.is_empty());
        assert!(loaded[0].mutable);
        let mut shared = container.clone();
        shared.mutable = false;
        assert!(!super::select_summary_inputs(shared, &path, &state)[0].mutable);
        let mut anchor = container;
        anchor.lifetime_only = true;
        assert!(super::select_summary_inputs(anchor, &path, &state).is_empty());
        let external = origin(PlaceRoot::Parameter(BindingId(0)), vec![]);
        let symbolic = super::select_summary_inputs(external, &path, &state);
        assert_eq!(
            symbolic[0].parameter_storage.as_deref(),
            Some(path.as_slice())
        );
        assert!(symbolic[0].place.segments.is_empty());
        assert_eq!(symbolic[0].place.root, PlaceRoot::Parameter(BindingId(0)));
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
    fn projected_variant_refinement_preserves_sibling_reference_slots() {
        let source = "(#enum Choice ((Left (#ref u64)) (Right (#ref u64))))
            (#struct Envelope ((choice Choice) (sibling (#ref u64))))
            (#fn inspect ((frame Envelope)) u64
              (#let result u64 (#match (#get frame choice)
                (#case (Left left) (#block
                  (#let sibling-left (#ref u64) (#get frame sibling))
                  (#u64.+.wrap (#deref left) (#deref sibling-left))))
                (#case (Right right) (#block
                  (#let sibling-right (#ref u64) (#get frame sibling))
                  (#u64.+.wrap (#deref right) (#deref sibling-right))))))
              (#forget frame) (#return result))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let declarations = checked.declarations();
        let body = &declarations.bodies["inspect"];
        let graph = &declarations.flows["inspect"];
        let origins = graph.loan_origins(body);
        let ty = Type::Named("Envelope".into());
        let choice = Segment::Field(declarations.field_id(&ty, "choice").unwrap());
        let sibling = Segment::Field(declarations.field_id(&ty, "sibling").unwrap());
        let mut arms = 0;
        for (index, event) in graph.nodes.iter().enumerate() {
            let FlowAction::Pattern { pattern, .. } = event.action else {
                continue;
            };
            let NodeKind::Form { children, .. } = &body.nodes[pattern.0].kind else {
                continue;
            };
            let NodeKind::Declaration(DeclarationId::Variant(selected)) =
                body.nodes[children[0].0].kind
            else {
                continue;
            };
            let held = origins.after(FlowNodeId(index), BindingId(0));
            assert_eq!(held.len(), 2, "{held:?}");
            assert!(held
                .iter()
                .any(|origin| origin.storage == vec![sibling.clone()]));
            assert!(held.iter().any(
                |origin| origin.storage == vec![choice.clone(), Segment::Payload(selected, 0)]
            ));
            arms += 1;
        }
        assert_eq!(arms, 2);
    }

    #[test]
    fn matching_borrowed_enum_values_does_not_replace_the_address_loan() {
        let source = "(#enum Choice ((Left (#ref u64)) (Right (#ref u64))))
            (#fn inspect ((choice (#ref Choice))) (#ref Choice)
              (#let value u64 (#match (#deref choice)
                (#case (Left left) (#deref left))
                (#case (Right right) (#deref right))))
              (#return choice))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["inspect"];
        let graph = &checked.declarations().flows["inspect"];
        let origins = graph.loan_origins(body);
        for (index, event) in graph.nodes.iter().enumerate() {
            if matches!(event.action, FlowAction::Pattern { .. }) {
                let held = origins.after(FlowNodeId(index), BindingId(0));
                assert_eq!(held.len(), 1);
                assert!(held[0].storage.is_empty());
                assert_eq!(
                    held[0].place,
                    Place::root(PlaceRoot::Parameter(BindingId(0)))
                );
            }
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
    fn correlated_return_snapshots_require_a_transparent_suffix() {
        let program = crate::parse_program(
            "(#struct Resource ((number u64))) (#linear Resource)
             (#fn choose ((left (#ref-mut Resource)) (right (#ref-mut Resource))
                          (selected bool)) (#ref-mut Resource)
               (#return (#if selected
                 (#block (#forget (#deref left)) right)
                 (#block (#forget (#deref right)) left))))",
        )
        .unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["choose"];
        let graph = &checked.declarations().flows["choose"];
        let (returned, value) = graph
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| {
                if let FlowAction::Return(Some(value)) = node.action {
                    Some((FlowNodeId(index), value))
                } else {
                    None
                }
            })
            .unwrap();
        let origins = graph.loan_origins(body);
        assert_eq!(
            graph
                .transparent_return_alternatives(body, &origins, returned, value)
                .unwrap()
                .len(),
            2
        );
        let (place, effect) = graph
            .nodes
            .iter()
            .find_map(|node| {
                if let FlowAction::Release { place, value } = &node.action {
                    Some((place.clone(), *value))
                } else {
                    None
                }
            })
            .unwrap();
        for action in [
            FlowAction::Assign {
                place: place.clone(),
                value: effect,
            },
            FlowAction::Write {
                place: place.clone(),
                value: effect,
            },
            FlowAction::Release {
                place: place.clone(),
                value: effect,
            },
            FlowAction::Evaluate(effect),
            FlowAction::Read {
                place,
                value: effect,
                place_base: false,
            },
            FlowAction::LoopHead,
        ] {
            let mut changed = graph.clone();
            let barrier = FlowNodeId(changed.nodes.len());
            for node in &mut changed.nodes {
                for successor in &mut node.successors {
                    if *successor == returned {
                        *successor = barrier;
                    }
                }
            }
            changed.nodes.push(FlowNode {
                action,
                successors: vec![returned],
                span: None,
            });
            assert!(changed
                .transparent_return_alternatives(body, &origins, returned, value)
                .is_none());
        }

        // One safe evaluation of a value must not hide a second evaluation
        // whose path performs an effect before the same return.
        let original = graph
            .transparent_return_alternatives(body, &origins, returned, value)
            .unwrap()[0]
            .0;
        let mut changed = graph.clone();
        let barrier = FlowNodeId(changed.nodes.len());
        let duplicate = FlowNodeId(barrier.0 + 1);
        let fork = FlowNodeId(barrier.0 + 2);
        for node in &mut changed.nodes {
            for successor in &mut node.successors {
                if *successor == original {
                    *successor = fork;
                }
            }
        }
        changed.nodes.push(FlowNode {
            action: FlowAction::Evaluate(effect),
            successors: vec![returned],
            span: None,
        });
        changed.nodes.push(FlowNode {
            action: graph.nodes[original.0].action.clone(),
            successors: vec![barrier],
            span: graph.nodes[original.0].span,
        });
        changed.nodes.push(FlowNode {
            action: FlowAction::Branch(value),
            successors: vec![original, duplicate],
            span: None,
        });
        let origins = changed.loan_origins(body);
        assert!(origins.before[duplicate.0].is_some());
        assert!(changed
            .transparent_return_alternatives(body, &origins, returned, value)
            .is_none());
    }

    #[test]
    fn staged_parameter_releases_preserve_copy_and_dynamic_contents() {
        for (source, name) in [
            (
                "(#struct Part (: view (#ref u64)))
              (#fn consume (: target (#ref-mut Part)) () (#forget (#deref target)) (#return ()))",
                "copy",
            ),
            (
                "(#struct Part (: view (#ref u64))) (#linear Part)
              (#fn consume (: target (#ref-mut (#array Part 2)) : index usize) ()
                (#forget (#index target index)) (#return ()))",
                "dynamic",
            ),
        ] {
            let program = crate::parse_program(source).unwrap();
            let checked = crate::CheckedProgram::validate(&program).unwrap();
            let body = &checked.declarations().bodies["consume"];
            let flow = &checked.declarations().flows["consume"];
            let origins = flow.staged_parameter_store_loan_origins(body);
            let event = flow
                .nodes
                .iter()
                .position(|node| matches!(node.action, FlowAction::Release { .. }))
                .unwrap();
            let before = origins.before[event].as_ref().unwrap();
            let after = origins.after[event].as_ref().unwrap();
            let initial = loaded_parameter_value_origins(&before[0][0], before);
            assert!(!initial.is_empty());
            assert_eq!(
                loaded_parameter_value_origins(&after[0][0], after),
                initial,
                "{name}"
            );
            assert_eq!(after[0].len(), 1);
        }
    }

    #[test]
    fn staged_nested_parameter_release_keeps_the_outer_pointer_slot() {
        let source = "(#struct Part (: view (#ref u64))) (#linear Part)
            (#struct Outer (: inner (#ref-mut Part)))
            (#fn consume (: target (#ref-mut Outer)) ()
              (#forget (#deref (#get target inner))) (#return ()))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["consume"];
        let flow = &checked.declarations().flows["consume"];
        let origins = flow.staged_parameter_store_loan_origins(body);
        let event = flow
            .nodes
            .iter()
            .position(|node| {
                matches!(node.action, FlowAction::Release { value, .. }
            if body.consuming_releases.contains(&value))
            })
            .unwrap();
        for (state, expected_inner) in [
            (origins.before[event].as_ref().unwrap(), 1),
            (origins.after[event].as_ref().unwrap(), 0),
        ] {
            let outer = loaded_parameter_value_origins(&state[0][0], state);
            assert_eq!(outer.len(), 1);
            let mut inner_pointer = outer[0].clone();
            let slot = inner_pointer.storage[0].clone();
            inner_pointer.project_storage(&slot);
            assert_eq!(
                loaded_parameter_value_origins(&inner_pointer, state).len(),
                expected_inner
            );
            assert_eq!(state[0].len(), 1);
        }
    }

    #[test]
    fn staged_parameter_releases_clear_container_storage_not_stored_pointees() {
        for (release, expected) in [
            ("(#forget (#deref target))", 0),
            ("(#forget (#get target left))", 1),
            (
                "(#let alias (#ref-mut Pair) target) (#forget (#deref alias))",
                0,
            ),
            (
                "(#let alias (#ref-mut Pair) (#if selected target other)) (#forget (#deref alias))",
                2,
            ),
            ("(#forget (#unsafe (#deref target)))", 0),
        ] {
            let source = format!(
                "(#struct Part (: view (#ref u64))) (#linear Part)
                 (#struct Pair (: left Part : right Part))
                 (#fn consume (: target (#ref-mut Pair) : other (#ref-mut Pair) : selected bool) () {release} (#return ()))"
            );
            let program = crate::parse_program(&source).unwrap();
            let checked = crate::CheckedProgram::validate(&program).unwrap();
            let body = &checked.declarations().bodies["consume"];
            let flow = &checked.declarations().flows["consume"];
            let origins = flow.staged_parameter_store_loan_origins(body);
            let event = flow
                .nodes
                .iter()
                .position(|node| {
                    matches!(node.action, FlowAction::Release { value, .. } | FlowAction::Evaluate(value)
                if body.consuming_releases.contains(&value))
                })
                .unwrap();
            let before = origins.before[event].as_ref().unwrap();
            let after = origins.after[event].as_ref().unwrap();
            assert_eq!(
                loaded_parameter_value_origins(&before[0][0], before).len(),
                2
            );
            let remaining = loaded_parameter_value_origins(&after[0][0], after);
            assert_eq!(remaining.len(), expected, "{release}: {remaining:?}");
            if expected == 1 {
                let field = checked
                    .declarations()
                    .field_id(&Type::Named("Pair".into()), "right")
                    .unwrap();
                assert_eq!(remaining[0].storage.first(), Some(&Segment::Field(field)));
            }
            assert_eq!(after[0].len(), 1);
            assert_eq!(after[0][0].place.root, PlaceRoot::Parameter(BindingId(0)));
            assert_eq!(loaded_parameter_value_origins(&after[1][0], after).len(), 2);
        }
    }

    #[test]
    fn staged_parameter_pin_move_empties_only_contents_until_restored() {
        let source = include_str!("../examples/parameter_pin_restore.lim");
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["replace"];
        let flow = &checked.declarations().flows["replace"];
        let origins = flow.staged_parameter_store_loan_origins(body);
        for (index, event) in flow.nodes.iter().enumerate() {
            let value = match event.action {
                FlowAction::Evaluate(value) if body.consuming_pin_reads.contains(&value) => value,
                FlowAction::Write { value, .. }
                    if matches!(&body.nodes[value.0].kind,
                    NodeKind::Form { head, .. } if head == "pin-write") =>
                {
                    value
                }
                _ => continue,
            };
            let state = origins.after[index].as_ref().unwrap();
            let address = &state[0][0];
            let held = loaded_parameter_value_origins(address, state);
            if body.consuming_pin_reads.contains(&value) {
                assert!(held.is_empty(), "moved contents survived: {held:?}");
            } else {
                assert_eq!(held.len(), 1);
                assert_eq!(held[0].parameter_summary().unwrap().parameter, 1);
            }
            assert_eq!(state[0].len(), 1);
            assert_eq!(address.place.root, PlaceRoot::Parameter(BindingId(0)));
        }
    }

    #[test]
    fn loan_snapshot_event_index_matches_full_scans() {
        for source in [
            include_str!("../examples/callee_variant_branch_clear.lim"),
            include_str!("../examples/callee_variant_loop_clear.lim"),
        ] {
            let program = crate::parse_program(source).unwrap();
            let checked = crate::CheckedProgram::validate(&program).unwrap();
            for (name, body) in &checked.declarations().bodies {
                let graph = &checked.declarations().flows[name];
                let origins = graph.loan_origins(body);
                for value in 0..body.nodes.len() {
                    let scanned = graph
                        .nodes
                        .iter()
                        .enumerate()
                        .filter_map(|(index, node)| {
                            flow_action_has_value(&node.action, NodeId(value)).then_some(index)
                        })
                        .collect::<Vec<_>>();
                    let indexed = origins.events_by_value[value]
                        .iter()
                        .copied()
                        .filter(|index| {
                            flow_action_has_value(&graph.nodes[*index].action, NodeId(value))
                        })
                        .collect::<Vec<_>>();
                    assert_eq!(indexed, scanned, "{name}: value {value}");
                }
            }
        }
    }

    #[test]
    fn recursive_loan_snapshot_queries_match_exhaustive_candidates() {
        for source in [
            include_str!("../examples/callee_variant_branch_clear.lim"),
            include_str!("../examples/callee_variant_loop_clear.lim"),
            include_str!("../examples/large_reference_projections.lim"),
        ] {
            let program = crate::parse_program(source).unwrap();
            let checked = crate::CheckedProgram::validate(&program).unwrap();
            for (name, body) in &checked.declarations().bodies {
                let graph = &checked.declarations().flows[name];
                let origins = graph.loan_origins(body);
                // Visiting every event for every expression reproduces the old
                // recursive scans; action and reachable-snapshot filters remain.
                let exhaustive = vec![(0..graph.nodes.len()).collect::<Vec<_>>(); body.nodes.len()];
                let indexed = LoanSnapshots::new(&origins.before, &origins.events_by_value);
                let scanned = LoanSnapshots::new(&origins.before, &exhaustive);
                for (value, candidates) in origins.events_by_value.iter().enumerate() {
                    assert!(candidates.windows(2).all(|pair| pair[0] < pair[1]));
                    for &event in candidates {
                        let Some(state) = &origins.before[event] else {
                            continue;
                        };
                        assert_eq!(
                            value_loan_origins_at_events(
                                body,
                                graph,
                                indexed,
                                NodeId(value),
                                state
                            ),
                            value_loan_origins_at_events(
                                body,
                                graph,
                                scanned,
                                NodeId(value),
                                state
                            ),
                            "{name}: value {value}, event {event}"
                        );
                    }
                    let loop_breaks = |events: &[usize]| {
                        events.iter().copied().filter(|&event| {
                            matches!(graph.nodes[event].action,
                                FlowAction::Break { result: Some(result), .. } if result == NodeId(value))
                        }).collect::<Vec<_>>()
                    };
                    assert_eq!(loop_breaks(candidates), loop_breaks(&exhaustive[value]));
                }
            }
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
    fn staged_parameter_clears_and_missing_contents_do_not_resurrect_schema_loans() {
        let program = crate::parse_program(
            "(#enum Choice ((Empty) (Full (#ref u64))))
            (#fn clear (: target (#ref-mut Choice)) Choice
              (#deref-set target (Empty)) (#return (#deref target)))
            (#fn read (: target (#ref Choice)) Choice (#return (#deref target)))",
        )
        .unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        for name in ["clear", "read"] {
            let body = &checked.declarations().bodies[name];
            let graph = &checked.declarations().flows[name];
            let mut origins = graph.staged_parameter_store_loan_origins(body);
            let (event, value) = graph
                .nodes
                .iter()
                .enumerate()
                .find_map(|(index, node)| {
                    if let FlowAction::Return(Some(value)) = node.action {
                        Some((FlowNodeId(index), value))
                    } else {
                        None
                    }
                })
                .unwrap();
            if name == "read" {
                assert!(!origins.value_before(body, graph, event, value).is_empty());
                for state in origins.before.iter_mut().flatten() {
                    state.parameter_contents.as_mut().unwrap().clear();
                }
            }
            assert!(
                origins.value_before(body, graph, event, value).is_empty(),
                "{name}"
            );
            assert_eq!(origins.before(event, BindingId(0)).len(), 1);
        }
    }

    #[test]
    fn matched_call_result_producers_preserve_payload_paths_and_reject_reassignment() {
        for (pattern, selected, index, overwrite, unknown) in [
            ("(#tuple first second)", "first", 0, false, false),
            ("(#tuple first second)", "second", 1, false, false),
            ("(#tuple first second)", "first", 0, true, true),
            ("pair", "(#get pair 0)", 0, false, false),
            ("pair", "(#get pair 1)", 1, false, false),
            (
                "(#tuple first second)",
                "(#deref (#borrow first))",
                0,
                false,
                true,
            ),
        ] {
            let source = format!(
                "(#enum Outcome ((Ready) (Pending)))
                 (#enum Envelope ((Packet (#tuple Outcome Outcome))))
                 (#fn build () Envelope (#return (Packet (#tuple (Ready) (Pending)))))
                 (#fn main () u64
                   (#return (#match (#call build ())
                     (#case (Packet {pattern})
                       (#block (#let-mut alias Outcome {selected})
                         {} (#match alias (#case (Ready) 42u64) (#case (Pending) 0u64)))))))",
                if overwrite {
                    "(#set alias (Pending))"
                } else {
                    ""
                }
            );
            let program = crate::parse_program(&source).unwrap();
            let checked = crate::CheckedProgram::validate(&program).unwrap();
            crate::generate_assembly(&program).unwrap();
            let declarations = checked.declarations();
            let body = &declarations.bodies["main"];
            let graph = &declarations.flows["main"];
            let mut predecessors = vec![Vec::new(); graph.nodes.len()];
            for (event, node) in graph.nodes.iter().enumerate() {
                for successor in &node.successors {
                    predecessors[successor.0].push(FlowNodeId(event));
                }
            }
            let (event, value) = graph
                .nodes
                .iter()
                .enumerate()
                .find_map(|(index, node)| {
                    let FlowAction::Pattern { pattern, value } = node.action else {
                        return None;
                    };
                    let variant = constructor_variant_at_storage(body, pattern, &[])?;
                    (declarations.variant(variant).name == "Ready")
                        .then_some((FlowNodeId(index), value))
                })
                .unwrap();
            let result = graph.call_result_producers(body, value, event, &predecessors);
            for (index, node) in body.nodes.iter().enumerate() {
                if matches!(&node.kind, NodeKind::Form { head, .. } if head == "borrow") {
                    assert!(graph
                        .call_result_producers(body, NodeId(index), event, &predecessors)
                        .is_none());
                }
            }
            if unknown {
                assert!(result.is_none());
                continue;
            }
            let producers = result.unwrap();
            assert_eq!(producers.len(), 1);
            let (call, path) = &producers[0];
            assert!(matches!(
                body.nodes[call.0].kind,
                NodeKind::Form {
                    callee: Some(_),
                    ..
                }
            ));
            let [Segment::Payload(packet, 0), Segment::Tuple(slot)] = path.as_slice() else {
                panic!("wrong output path: {path:?}");
            };
            assert_eq!(declarations.variant(*packet).name, "Packet");
            assert_eq!(*slot, index);
            // A nested constructor cannot select a root-only effect contract.
            assert!(graph
                .call_result_sources(body, value, event, &predecessors)
                .is_none());
        }
    }

    #[test]
    fn call_result_producers_do_not_follow_implicit_reference_field_reads() {
        let program = crate::parse_program(
            "(#enum Outcome ((Ready) (Pending)))
             (#struct Pair ((first Outcome) (second Outcome)))
             (#fn factory () Pair (#return (#struct-literal Pair (: first (Ready) : second (Pending)))))
             (#fn main () u64
               (#let packet Pair (#call factory ()))
               (#let result u64 (#match (#get (#borrow packet) first)
                 (#case (Ready) 42u64) (#case (Pending) 0u64)))
               (#forget packet) (#return result))"
        ).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        crate::generate_assembly(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let flow = &checked.declarations().flows["main"];
        let mut predecessors = vec![Vec::new(); flow.nodes.len()];
        for (event, node) in flow.nodes.iter().enumerate() {
            for successor in &node.successors {
                predecessors[successor.0].push(FlowNodeId(event));
            }
        }
        let (event, value) = flow
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| {
                let FlowAction::Pattern { value, .. } = node.action else {
                    return None;
                };
                Some((FlowNodeId(index), value))
            })
            .unwrap();
        assert!(reads_through_reference(body, value));
        assert!(flow
            .call_result_producers(body, value, event, &predecessors)
            .is_none());
    }

    #[test]
    fn loop_call_result_sources_need_a_reachable_value_break() {
        let program = crate::parse_program(
            "(#enum Outcome ((Ready) (Pending)))
            (#fn finish () Outcome (#return (Ready)))
            (#fn main () u64 (#let result Outcome (#loop (#break (#call finish ()))))
              (#forget result) (#return 42u64))",
        )
        .unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let mut graph = checked.declarations().flows["main"].clone();
        let value = body
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| {
                matches!(node.kind, NodeKind::Loop(_)).then_some(NodeId(index))
            })
            .unwrap();
        let mut predecessors = vec![Vec::new(); graph.nodes.len()];
        for (index, node) in graph.nodes.iter().enumerate() {
            for successor in &node.successors {
                predecessors[successor.0].push(FlowNodeId(index));
            }
        }
        assert!(graph
            .call_result_sources(body, value, graph.exit, &predecessors)
            .is_some());
        for node in &mut graph.nodes {
            if matches!(node.action, FlowAction::Break { result: Some(found), .. } if found == value)
            {
                node.action = FlowAction::Diverge;
                node.successors.clear();
            }
        }
        assert!(graph
            .call_result_sources(body, value, graph.exit, &predecessors)
            .is_none());
    }

    #[test]
    fn liveness_postorder_matches_other_worklist_orders() {
        let mut wide = String::from("(#fn main () u64 ");
        for index in 0..130 {
            wide.push_str(&format!("(#let value{index} u64 {index}u64) "));
        }
        for index in 0..129 {
            wide.push_str(&format!("(#forget value{index}) "));
        }
        wide.push_str("(#return value129))");
        for source in [
            "(#fn main () u64 (#return 42u64))",
            wide.as_str(),
            "(#fn main () u64 (#let-mut counter u64 0u64)
             (#while (#u64.< counter 3u64)
               (#set counter (#u64.+.wrap counter 1u64))) (#return counter))",
            "(#enum Choice ((Some u64) None))
             (#fn main () u64 (#let flag bool (#bool.&& true false))
               (#return (#if flag (#match (Some 42u64)
                 (#case (Some value) value) (#case None 0u64)) 0u64)))",
            "(#fn main () u64 (#return 42u64) (#let unreachable u64 1u64)
             (#return unreachable))",
            include_str!("../examples/labeled_loop.lim"),
        ] {
            let program = crate::parse_program(source).unwrap();
            let checked = crate::CheckedProgram::validate(&program).unwrap();
            for (name, graph) in &checked.declarations().flows {
                let body = &checked.declarations().bodies[name];
                let order = graph.reachable_postorder();
                let reachable = graph.reachable();
                assert_eq!(order.len(), reachable.len());
                assert_eq!(order.iter().copied().collect::<HashSet<_>>(), reachable);
                assert_eq!(order, graph.reachable_postorder());
                let expected = graph.liveness(body);
                let mut alternative = order.clone();
                alternative.reverse();
                for scheduling in [alternative, reachable.into_iter().collect()] {
                    let actual = graph.liveness_in_order(body, &scheduling);
                    assert_eq!(actual.before, expected.before, "{name}");
                    assert_eq!(actual.after, expected.after, "{name}");
                    if source == wide {
                        assert_eq!(expected.worklist_visits, order.len());
                        assert!(actual.worklist_visits > expected.worklist_visits);
                    }
                }
            }
        }
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
