//! Actual caller relationships for references stored inside a borrowed owner.
//!
//! A parameter's pointer-slot name is not its physical referent. Preserve the
//! storage slot and the owner-relative pointee separately before attempting a
//! context-sensitive callee check. Internal owner accesses are checked before
//! granting a narrowly keyed permission for that call's exact retained child
//! slot; this does not replace ordinary checking or initialization/retirement
//! contracts.
//! Ordinary validation uses this as an additional rejection gate. Entry-tag
//! guards distinguish conditional initialization from overwriting a retained
//! pointee. Owner reads, clones, and reborrows are also compared with the
//! incoming child's capability, including nested ordinary calls. These checks
//! authorize only the checked internal-child case. State-dependent enum
//! permissions and external child relationships remain separate obligations.

use crate::typed_body::{BindingId, Body, NodeId, NodeKind, PlaceRoot};
use crate::typed_flow::{FlowAction, FlowGraph, FlowLoanOrigins, FlowNodeId, LoanOrigin};
use crate::typed_ir::{resolve_type, Declarations, FunctionId};
use crate::typed_place::{Place, Segment};
use crate::Type;
use std::collections::{HashMap, HashSet};

const MAX_INTERNAL_OWNER_DEPTH: usize = 64;

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub(crate) struct Alias {
    pub parameter: BindingId,
    /// Position of the child pointer in the incoming parameter value.
    pub storage: Vec<Segment>,
    /// Incoming pointer whose actual pointee owns the child's target.
    pub owner_input: Vec<Segment>,
    /// Physical projection from that owner's pointee, not from the child slot.
    pub projection: Vec<Segment>,
    pub mutable: bool,
    pub pinned: bool,
    /// Actual caller slot and referent represented by this callee-relative
    /// alias. Used to grant only a call whose internal-owner check succeeded.
    pub caller_slot: Option<Place>,
    pub caller_referent: Place,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct InternalReborrowPermission {
    pub call: NodeId,
    pub slot: Place,
    pub referent: Place,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub(crate) struct Plan {
    pub callee: FunctionId,
    pub aliases: Vec<Alias>,
}

/// One immutable-declaration analysis run, never a persistent compiler cache.
#[derive(Default)]
pub(crate) struct Cache {
    baseline: HashMap<FunctionId, std::rc::Rc<FlowLoanOrigins>>,
    entry_tags: HashMap<FunctionId, std::rc::Rc<EntryTags>>,
    // Write-only staging must not cache permission for observation checks.
    checked: HashSet<(Plan, bool)>,
    writes: HashMap<FunctionId, Vec<GuardedWrite>>,
    observations: HashMap<FunctionId, Vec<GuardedObservation>>,
}

type EntryTags = Vec<HashMap<Place, crate::typed_ir::VariantId>>;

fn cached_entry_tags(
    callee: FunctionId,
    body: &Body,
    flow: &FlowGraph,
    origins: &FlowLoanOrigins,
    cache: &mut Cache,
) -> std::rc::Rc<EntryTags> {
    cache
        .entry_tags
        .entry(callee)
        .or_insert_with(|| std::rc::Rc::new(entry_guards(body, flow, origins)))
        .clone()
}

#[derive(Clone, Eq, PartialEq, Hash)]
struct GuardedWrite {
    target: crate::typed_body::ParameterLoanSummary,
    guards: Vec<(
        crate::typed_body::ParameterLoanSummary,
        crate::typed_ir::VariantId,
    )>,
}

#[derive(Clone, Eq, PartialEq, Hash)]
struct GuardedObservation {
    target: crate::typed_body::ParameterLoanSummary,
    /// Shared reads/borrows conflict only with an exclusive incoming loan.
    /// An exclusive borrow also conflicts with a shared incoming loan.
    exclusive: bool,
    guards: Vec<(
        crate::typed_body::ParameterLoanSummary,
        crate::typed_ir::VariantId,
    )>,
    span: Option<crate::Span>,
}

/// Non-destructive access through a reference, not a read of its pointer slot.
/// Preserve evaluated receiver snapshots and keep the pointee input separate
/// from the slot that contains the pointer. Raw lifetime anchors are not reads.
fn observations_at(
    body: &Body,
    flow: &FlowGraph,
    origins: &FlowLoanOrigins,
    event: FlowNodeId,
    moves: &crate::typed_flow::FlowConsumptions,
) -> Vec<(LoanOrigin, bool)> {
    let address = |value| origins.address_before(body, flow, event, value);
    let (targets, exclusive) = match &flow.nodes[event.0].action {
        FlowAction::Read {
            value,
            place,
            place_base: false,
        } if !moves.consumes_at(event, place)
            && crate::typed_place::reads_through_reference(body, *value) =>
        {
            (address(*value), false)
        }
        FlowAction::Clone { value, .. } => {
            let NodeKind::Form {
                children,
                callee: None,
                ..
            } = &body.nodes[value.0].kind
            else {
                return Vec::new();
            };
            if !crate::typed_place::reads_through_reference(body, children[1]) {
                return Vec::new();
            }
            (address(children[1]), false)
        }
        FlowAction::Borrow { value, mutable, .. } => {
            let NodeKind::Form {
                head,
                children,
                callee: None,
                ..
            } = &body.nodes[value.0].kind
            else {
                return Vec::new();
            };
            if !matches!(
                head.as_str(),
                "borrow" | "borrow-mut" | "pin-borrow" | "pin-borrow-mut" | "pin" | "pin-shared"
            ) || !crate::typed_place::reads_through_reference(body, children[1])
            {
                return Vec::new();
            }
            (address(children[1]), *mutable)
        }
        FlowAction::Evaluate(value) => {
            let NodeKind::Form {
                head,
                children,
                callee: None,
                ..
            } = &body.nodes[value.0].kind
            else {
                return Vec::new();
            };
            if head != "deref" || children.len() != 2 {
                return Vec::new();
            }
            (origins.value_before(body, flow, event, children[1]), false)
        }
        _ => return Vec::new(),
    };
    observation_alternatives(targets)
        .into_iter()
        .filter(|target| {
            !target.lifetime_only && !target.owned_allocation && target.storage.is_empty()
        })
        .map(|target| (target, exclusive))
        .collect()
}

/// A joined reference value can arrive either from an incoming child loan or
/// from a fresh borrow on an earlier path. The fresh borrow is checked where
/// it is created; accessing this same handle must not invent a second access
/// through its owner. Preserve distinct incoming families and distinct input
/// slots: equal addresses alone are not proof that two handles are the same.
fn observation_alternatives(targets: Vec<LoanOrigin>) -> Vec<LoanOrigin> {
    if !targets.iter().any(|target| target.entry_loan.is_some()) {
        return targets;
    }
    targets
        .iter()
        .filter(|target| {
            target.entry_loan.is_some()
                || !targets.iter().any(|other| {
                    other.entry_loan.is_some()
                        && other.place == target.place
                        && other.parameter_storage == target.parameter_storage
                        && other.storage == target.storage
                        && other.mutable == target.mutable
                        && other.pinned == target.pinned
                        && other.lifetime_only == target.lifetime_only
                        && other.owned_allocation == target.owned_allocation
                })
        })
        .cloned()
        .collect()
}

/// Acyclic read/reborrow footprints retain entry guards and deepest source
/// locations. Repeated calls share analysis and deduplicate semantic effects.
fn guarded_observations(
    callee: FunctionId,
    declarations: &Declarations,
    types: &crate::linearcheck::LinearTypes,
    cache: &mut Cache,
    pending: &mut HashSet<FunctionId>,
) -> Result<Vec<GuardedObservation>, String> {
    if let Some(effects) = cache.observations.get(&callee) {
        return Ok(effects.clone());
    }
    let name = declarations
        .function_name(callee)
        .ok_or("missing checked callee")?;
    let Some(body) = declarations.bodies.get(name) else {
        return Ok(Vec::new());
    };
    if !pending.insert(callee) {
        return Err("recursive internal-loan checking is not permitted".into());
    }
    let flow = &declarations.flows[name];
    let origins = cache
        .baseline
        .entry(callee)
        .or_insert_with(|| std::rc::Rc::new(flow.loan_origins(body)))
        .clone();
    let moves = flow.consumptions(body, types);
    let entry = cached_entry_tags(callee, body, flow, &origins, cache);
    let mut output = Vec::new();
    let mut events = flow.reachable().into_iter().collect::<Vec<_>>();
    events.sort_unstable_by_key(|event| event.0);
    for event in events {
        let guards = entry[event.0]
            .iter()
            .filter_map(|(place, variant)| {
                physical_summary(body, place).map(|summary| (summary, *variant))
            })
            .collect::<Vec<_>>();
        let node = &flow.nodes[event.0];
        if let FlowAction::Evaluate(value) = node.action {
            if let NodeKind::Form {
                callee: Some(target),
                children,
                ..
            } = &body.nodes[value.0].kind
            {
                for effect in guarded_observations(*target, declarations, types, cache, pending)? {
                    let mut mapped_guards = guards.clone();
                    for (guard, variant) in &effect.guards {
                        let mapped = map_write_input(body, flow, &origins, event, children, guard);
                        if mapped.len() == 1 && !mapped[0].lifetime_only {
                            if let Some(guard) = mapped[0].parameter_summary() {
                                mapped_guards.push((guard, *variant));
                            }
                        }
                    }
                    for target in
                        map_write_input(body, flow, &origins, event, children, &effect.target)
                    {
                        if target.lifetime_only || !target.storage.is_empty() {
                            continue;
                        }
                        if let Some(target) = target.parameter_summary() {
                            output.push(GuardedObservation {
                                target,
                                exclusive: effect.exclusive,
                                guards: mapped_guards.clone(),
                                span: effect.span.or(node.span),
                            });
                        }
                    }
                }
                continue;
            }
        }
        for (target, exclusive) in observations_at(body, flow, &origins, event, &moves) {
            if let Some(target) = target.parameter_summary() {
                output.push(GuardedObservation {
                    target,
                    exclusive,
                    guards: guards.clone(),
                    span: node.span,
                });
            }
        }
    }
    pending.remove(&callee);
    let mut seen = HashSet::new();
    output.retain_mut(|effect| {
        effect.guards.sort_unstable();
        effect.guards.dedup();
        seen.insert((
            effect.target.clone(),
            effect.exclusive,
            effect.guards.clone(),
        ))
    });
    cache.observations.insert(callee, output.clone());
    Ok(output)
}

fn map_write_input(
    body: &Body,
    flow: &FlowGraph,
    origins: &FlowLoanOrigins,
    event: FlowNodeId,
    children: &[NodeId],
    summary: &crate::typed_body::ParameterLoanSummary,
) -> Vec<LoanOrigin> {
    if let Some(global) = crate::typed_flow::global_summary_origin(summary) {
        return vec![global];
    }
    // Newly allocated storage is local to the callee, not an input slot.
    // The unused `parameter` of a global/fresh identity is never an argument.
    if summary.fresh_allocation.is_some() {
        return vec![];
    }
    origins.apply_summary_before(
        body,
        flow,
        event,
        *children
            .get(summary.parameter + 1)
            .expect("checked write parameter identity"),
        summary,
    )
}

fn physical_summary(body: &Body, place: &Place) -> Option<crate::typed_body::ParameterLoanSummary> {
    let (parameter, global) = match place.root {
        PlaceRoot::Parameter(parameter) => (parameter.0, None),
        PlaceRoot::Global(global) => (0, Some(global)),
        _ => return None,
    };
    let (input, projection) = crate::typed_flow::split_referent_effect_place(body, place);
    Some(crate::typed_body::ParameterLoanSummary {
        fresh_allocation: None,
        owned_allocation: false,
        parameter,
        global,
        mutable: true,
        pinned: false,
        lifetime_only: false,
        maybe_absent: false,
        word_stored: false,
        word_view_address: false,
        reborrow: false,
        referent_projection: projection,
        input_storage: input.unwrap_or_default(),
        storage: vec![],
        storage_inputs: vec![],
    })
}

/// Facts about entry tags, not the tags after an initializer has overwritten
/// them. Once established before any possible mutation, an entry fact remains
/// a path constraint even after a destructive read clears current tag facts.
fn entry_guards(body: &Body, flow: &FlowGraph, origins: &FlowLoanOrigins) -> EntryTags {
    #[derive(Clone, Default)]
    struct State {
        guards: HashMap<Place, crate::typed_ir::VariantId>,
        changed: HashSet<Place>,
        unknown: bool,
    }
    let mut before = vec![None::<State>; flow.nodes.len()];
    let mut result = vec![HashMap::new(); flow.nodes.len()];
    before[flow.entry.0] = Some(State::default());
    let mut pending = std::collections::VecDeque::from([flow.entry]);
    let mut queued = vec![false; flow.nodes.len()];
    queued[flow.entry.0] = true;
    while let Some(event) = pending.pop_front() {
        queued[event.0] = false;
        let mut state = before[event.0].as_ref().unwrap().clone();
        if !state.unknown {
            for (place, variant) in origins
                .variants_before(body, flow, event)
                .into_iter()
                .flat_map(|facts| facts.iter())
            {
                if matches!(place.root, PlaceRoot::Parameter(_))
                    && !state.changed.iter().any(|changed| changed.overlaps(place))
                {
                    state.guards.insert(place.clone(), *variant);
                }
            }
        }
        result[event.0] = state.guards.clone();
        let node = &flow.nodes[event.0];
        state.changed.extend(
            origins
                .stores_before(body, flow, event)
                .into_iter()
                .map(|store| store.destination.referent_place()),
        );
        match node.action {
            FlowAction::Evaluate(value) => {
                if let NodeKind::Form {
                    head,
                    callee,
                    children,
                    ..
                } = &body.nodes[value.0].kind
                {
                    if callee.is_some() {
                        match origins.call_tag_mutations(body, flow, event, value) {
                            Some(targets) => state
                                .changed
                                .extend(targets.into_iter().map(|target| target.referent_place())),
                            None => state.unknown = true,
                        }
                    } else if head == "pin-read" && body.consuming_pin_reads.contains(&value) {
                        state.changed.extend(
                            origins
                                .value_before(body, flow, event, children[1])
                                .into_iter()
                                .map(|target| target.referent_place()),
                        );
                    } else if matches!(head.as_str(), "ptr-write" | "linux-syscall" | "asm") {
                        state.unknown = true;
                    }
                }
            }
            FlowAction::Release { ref place, .. } => {
                if let PlaceRoot::Local(binding) = place.root {
                    state.changed.extend(origins.projected_referents(
                        event,
                        binding,
                        &place.segments,
                    ));
                }
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
                    let old_guards = previous.guards.len();
                    previous
                        .guards
                        .retain(|place, variant| state.guards.get(place) == Some(variant));
                    let old_changed = previous.changed.len();
                    previous.changed.extend(state.changed.iter().cloned());
                    let old_unknown = previous.unknown;
                    previous.unknown |= state.unknown;
                    old_guards != previous.guards.len()
                        || old_changed != previous.changed.len()
                        || old_unknown != previous.unknown
                }
            };
            if changed && !queued[successor.0] {
                queued[successor.0] = true;
                pending.push_back(*successor);
            }
        }
    }
    result
}

/// All reachable writes, including paths that never return. Final store
/// summaries alone erase an initializer's entry-tag guard and are insufficient
/// for checking a caller's retained loan against that initializer.
fn guarded_writes(
    callee: FunctionId,
    declarations: &Declarations,
    types: &crate::linearcheck::LinearTypes,
    cache: &mut Cache,
    pending: &mut HashSet<FunctionId>,
) -> Result<Vec<GuardedWrite>, String> {
    if let Some(writes) = cache.writes.get(&callee) {
        return Ok(writes.clone());
    }
    let name = declarations.function_name(callee).expect("resolved callee");
    let body = declarations
        .bodies
        .get(name)
        .ok_or("cannot inspect internally borrowed callee")?;
    if !pending.insert(callee) {
        return Err("recursive internal-loan checking is not permitted".into());
    }
    let flow = &declarations.flows[name];
    let baseline = cache
        .baseline
        .entry(callee)
        .or_insert_with(|| std::rc::Rc::new(flow.loan_origins(body)))
        .clone();
    let moves = flow.consumptions(body, types);
    let entry = cached_entry_tags(callee, body, flow, &baseline, cache);
    let mut output = Vec::new();
    let mut events = flow.reachable().into_iter().collect::<Vec<_>>();
    events.sort_by_key(|event| event.0);
    for event in events {
        let node = &flow.nodes[event.0];
        let guards = entry[event.0]
            .iter()
            .filter_map(|(place, variant)| {
                physical_summary(body, place).map(|summary| (summary, *variant))
            })
            .collect::<Vec<_>>();
        if let FlowAction::Evaluate(value) = node.action {
            if let NodeKind::Form {
                callee: Some(target),
                children,
                ..
            } = &body.nodes[value.0].kind
            {
                for write in guarded_writes(*target, declarations, types, cache, pending)? {
                    let targets =
                        map_write_input(body, flow, &baseline, event, children, &write.target);
                    let mut mapped_guards = guards.clone();
                    for (guard, variant) in &write.guards {
                        let targets =
                            map_write_input(body, flow, &baseline, event, children, guard);
                        if targets.len() == 1 && !targets[0].lifetime_only {
                            if let Some(guard) = targets[0].parameter_summary() {
                                mapped_guards.push((guard, *variant));
                            }
                        }
                    }
                    for target in targets.into_iter().filter(|target| !target.lifetime_only) {
                        if let Some(target) = target.parameter_summary() {
                            output.push(GuardedWrite {
                                target,
                                guards: mapped_guards.clone(),
                            });
                        }
                    }
                }
                continue;
            }
        }
        let mut targets = baseline
            .stores_before(body, flow, event)
            .into_iter()
            .map(|store| store.destination)
            .collect::<Vec<_>>();
        match &node.action {
            FlowAction::Read {
                place,
                place_base: false,
                ..
            } if moves.consumes_at(event, place) => {
                if let PlaceRoot::Local(binding) = place.root {
                    targets.extend(baseline.projected_origins(event, binding, &place.segments));
                }
            }
            FlowAction::Release { place, .. } => {
                if let PlaceRoot::Local(binding) = place.root {
                    targets.extend(baseline.projected_origins(event, binding, &place.segments));
                } else if let Some(summary) = physical_summary(body, place) {
                    if let Some(global) = crate::typed_flow::global_summary_origin(&summary) {
                        targets.push(global);
                    }
                }
            }
            FlowAction::Evaluate(value) if body.consuming_pin_reads.contains(value) => {
                if let NodeKind::Form { children, .. } = &body.nodes[value.0].kind {
                    targets.extend(baseline.value_before(body, flow, event, children[1]));
                }
            }
            FlowAction::Evaluate(value) => {
                // Global forgets are Evaluate events, not local Release events.
                if let NodeKind::Form {
                    head,
                    callee: None,
                    children,
                    ..
                } = &body.nodes[value.0].kind
                {
                    if head == "forget" {
                        if let Some(place) = Place::from_expression(body, children[1]) {
                            if let Some(summary) = physical_summary(body, &place) {
                                if let Some(global) =
                                    crate::typed_flow::global_summary_origin(&summary)
                                {
                                    targets.push(global);
                                }
                            }
                        }
                    }
                }
            }
            _ => {}
        }
        for target in targets.into_iter().filter(|target| !target.lifetime_only) {
            if let Some(target) = target.parameter_summary() {
                output.push(GuardedWrite {
                    target,
                    guards: guards.clone(),
                });
            }
        }
    }
    pending.remove(&callee);
    // Repeated calls in an acyclic DAG must not expand their identical
    // footprints exponentially. Guard order is not a semantic distinction.
    let mut seen = HashSet::new();
    output.retain_mut(|write| {
        write.guards.sort_unstable();
        write.guards.dedup();
        seen.insert(write.clone())
    });
    cache.writes.insert(callee, output.clone());
    Ok(output)
}

#[cfg(test)]
fn check_calls(
    body: &Body,
    flow: &FlowGraph,
    declarations: &Declarations,
    types: &crate::linearcheck::LinearTypes,
    cache: &std::cell::OnceCell<FlowLoanOrigins>,
) -> Result<(), crate::typed_borrow::BorrowConflict> {
    let mut checked = Cache::default();
    check_calls_cached(body, flow, declarations, types, cache, &mut checked).map(|_| ())
}

pub(crate) fn check_calls_cached(
    body: &Body,
    flow: &FlowGraph,
    declarations: &Declarations,
    types: &crate::linearcheck::LinearTypes,
    cache: &std::cell::OnceCell<FlowLoanOrigins>,
    checked: &mut Cache,
) -> Result<Vec<InternalReborrowPermission>, crate::typed_borrow::BorrowConflict> {
    let mut permissions = Vec::new();
    for (index, node) in flow.nodes.iter().enumerate() {
        let FlowAction::Evaluate(value) = node.action else {
            continue;
        };
        let NodeKind::Form {
            callee: Some(callee),
            children,
            ..
        } = &body.nodes[value.0].kind
        else {
            continue;
        };
        let name = declarations
            .function_name(*callee)
            .expect("resolved function identity");
        if declarations.bodies.get(name).is_some_and(|target| {
            target
                .parameter_referent_loan_slots
                .iter()
                .all(Vec::is_empty)
        }) {
            continue;
        }
        let origins = cache.get_or_init(|| flow.loan_origins(body));
        let event = FlowNodeId(index);
        let mut plan =
            Plan::for_call(body, flow, event, value, origins, declarations).map_err(|message| {
                crate::typed_borrow::BorrowConflict {
                    message,
                    span: node.span,
                    labels: vec![],
                }
            })?;
        // A conditional reference exists only if each payload on its storage
        // and target paths is active. Remove an alias only when a checked tag
        // proves it inactive. Unknown tags remain possible aliases; whether
        // they can be checked depends on whether their storage provenance is
        // path-correlated with the target (handled below).
        plan.aliases.retain(|alias| {
            storage_payload_status(body, flow, event, value, origins, alias) != Some(false)
                && projection_payload_status(body, flow, event, value, origins, alias)
                    != Some(false)
        });
        if plan.aliases.is_empty() {
            continue;
        }
        if let Err((parameter, mut error)) =
            plan.check_owner_accesses_inner(declarations, types, &mut Vec::new(), checked, true)
        {
            if let Some(span) = error.span {
                error.labels.push((
                    span,
                    "callee accesses the internally borrowed owner here".into(),
                ));
            }
            error.span = children
                .get(parameter.0 + 1)
                .and_then(|argument| body.nodes[argument.0].span)
                .or(node.span);
            return Err(error);
        }
        permissions.extend(plan.aliases.iter().filter_map(|alias| {
            alias
                .caller_slot
                .clone()
                .map(|slot| InternalReborrowPermission {
                    call: value,
                    slot,
                    referent: alias.caller_referent.clone(),
                })
        }));
    }
    Ok(permissions)
}

fn static_path(path: &[Segment]) -> bool {
    path.iter().all(|segment| {
        matches!(
            segment,
            Segment::Field(_) | Segment::Tuple(_) | Segment::Payload(_, _) | Segment::Index(_)
        )
    })
}

fn static_storage_path(path: &[Segment]) -> bool {
    path.iter().all(|segment| {
        matches!(
            segment,
            Segment::Field(_)
                | Segment::Tuple(_)
                | Segment::Payload(_, _)
                | Segment::Index(_)
                | Segment::Dereference
        )
    })
}

fn is_owner_pointer(ty: &Type) -> bool {
    matches!(
        ty,
        Type::Reference { .. }
            | Type::PinnedReference { .. }
            | Type::PinOwned(_)
            | Type::PinShared(_)
    )
}

/// An access reached by selecting the exact reference slot represented by an
/// incoming family is a use/reborrow of that loan, not a fresh access through
/// the containing owner. Retain the slot test separately from referent-place
/// overlap: sibling slots that happen to point at the same address remain
/// conflicting families.
fn access_uses_alias_storage(body: &Body, alias: &Alias, access: &LoanOrigin) -> bool {
    let Some(span) = access.span else {
        return false;
    };
    let Some((id, node)) = body
        .nodes
        .iter()
        .enumerate()
        .find(|(_, node)| node.span == Some(span))
    else {
        return false;
    };
    if !matches!(
        node.kind,
        NodeKind::Form { head: ref name, .. }
            if matches!(name.as_str(), "pin-get-payload" | "pin-get-payload-mut" | "pin-get-payload-unchecked" | "pin-get-payload-unchecked-mut")
    ) {
        return false;
    }
    let Some(mut place) = Place::from_expression(body, NodeId(id)) else {
        return false;
    };
    if place.root != PlaceRoot::Parameter(alias.parameter) {
        return false;
    }
    let parameter_ty = &body.bindings[alias.parameter.0].ty;
    if matches!(
        parameter_ty,
        Type::Reference { .. }
            | Type::PinnedReference { .. }
            | Type::Slice(_)
            | Type::MutableSlice(_)
    ) && place.segments.first() != Some(&Segment::Dereference)
    {
        place.segments.insert(0, Segment::Dereference);
    }
    place.segments == alias.storage
}

/// `Some(true)` means all payloads are known active, `Some(false)` means at
/// least one is known inactive, and `None` means the caller cannot prove the
/// state. Unknown is deliberately distinct from inactive.
fn projection_payload_status(
    body: &Body,
    flow: &FlowGraph,
    event: FlowNodeId,
    value: NodeId,
    origins: &FlowLoanOrigins,
    alias: &Alias,
) -> Option<bool> {
    payload_path_status(
        body,
        flow,
        event,
        value,
        origins,
        alias,
        &alias.projection,
        false,
    )
}

fn storage_payload_status(
    body: &Body,
    flow: &FlowGraph,
    event: FlowNodeId,
    value: NodeId,
    origins: &FlowLoanOrigins,
    alias: &Alias,
) -> Option<bool> {
    payload_path_status(
        body,
        flow,
        event,
        value,
        origins,
        alias,
        &alias.storage,
        true,
    )
}

fn payload_path_status(
    body: &Body,
    flow: &FlowGraph,
    event: FlowNodeId,
    value: NodeId,
    origins: &FlowLoanOrigins,
    alias: &Alias,
    path: &[Segment],
    crosses_owner_deref: bool,
) -> Option<bool> {
    let payloads = path
        .iter()
        .enumerate()
        .filter_map(|(index, segment)| match segment {
            Segment::Payload(variant, _) => Some((index, *variant)),
            _ => None,
        })
        .collect::<Vec<_>>();
    if payloads.is_empty() {
        return Some(true);
    }
    let NodeKind::Form { children, .. } = &body.nodes[value.0].kind else {
        return None;
    };
    let Some(argument) = children.get(alias.parameter.0 + 1) else {
        return None;
    };
    let Some(facts) = origins.variants_before(body, flow, event) else {
        return None;
    };
    let parents = origins.value_before(body, flow, event, *argument);
    let mut unknown = false;
    for (index, wanted) in payloads {
        let status = if crosses_owner_deref {
            nested_payload_status(
                body, event, origins, alias, path, index, wanted, facts, &parents,
            )
        } else {
            let statuses = parents
                .iter()
                .filter(|parent| !parent.lifetime_only && !parent.owned_allocation)
                .map(|parent| {
                    let mut place = parent.referent_place();
                    place.segments.extend_from_slice(&path[..index]);
                    payload_fact(facts, &place, wanted)
                })
                .collect::<Vec<_>>();
            combine_payload_candidates(&statuses)
        };
        match status {
            Some(false) => return Some(false),
            Some(true) => {}
            None => unknown = true,
        }
    }
    if unknown {
        None
    } else {
        Some(true)
    }
}

fn nested_payload_status(
    body: &Body,
    event: FlowNodeId,
    origins: &FlowLoanOrigins,
    alias: &Alias,
    path: &[Segment],
    payload_index: usize,
    wanted: crate::typed_ir::VariantId,
    facts: &HashMap<Place, crate::typed_ir::VariantId>,
    parents: &[LoanOrigin],
) -> Option<bool> {
    let boundaries = path[..payload_index]
        .iter()
        .enumerate()
        .filter_map(|(index, segment)| (*segment == Segment::Dereference).then_some(index))
        .collect::<Vec<_>>();
    let first = *boundaries.first()?;
    let mut statuses = Vec::new();
    let pointers = parents
        .iter()
        .filter(|parent| {
            !parent.lifetime_only && !parent.owned_allocation && parent.storage == alias.owner_input
        })
        .cloned()
        .collect::<Vec<_>>();
    if pointers.is_empty() {
        return None;
    }
    for pointer in pointers {
        let mut current = vec![pointer];
        let mut previous = first;
        for boundary in boundaries.iter().skip(1) {
            let slot = &path[previous + 1..*boundary];
            if slot.is_empty() {
                current.clear();
                break;
            }
            let next = current
                .iter()
                .flat_map(|owner| origins.pointee_before(body, event, owner))
                .filter(|nested| {
                    !nested.lifetime_only && !nested.owned_allocation && nested.storage == slot
                })
                .collect::<Vec<_>>();
            if next.is_empty() {
                current.clear();
                break;
            }
            current = next;
            previous = *boundary;
        }
        if current.is_empty() {
            statuses.push(None);
            continue;
        }
        let suffix = &path[previous + 1..payload_index];
        for owner in current {
            let mut place = owner.referent_place();
            place.segments.extend_from_slice(suffix);
            statuses.push(payload_fact(facts, &place, wanted));
        }
    }
    combine_payload_candidates(&statuses)
}

fn payload_fact(
    facts: &HashMap<Place, crate::typed_ir::VariantId>,
    place: &Place,
    wanted: crate::typed_ir::VariantId,
) -> Option<bool> {
    facts
        .get(place)
        .filter(|actual| actual.owner == wanted.owner)
        .map(|actual| *actual == wanted)
}

fn combine_payload_candidates(statuses: &[Option<bool>]) -> Option<bool> {
    if statuses.contains(&Some(true)) {
        Some(true)
    } else if !statuses.is_empty() && statuses.iter().all(|status| *status == Some(false)) {
        Some(false)
    } else {
        None
    }
}

fn same_pointer_root(parent: &LoanOrigin, child: &LoanOrigin) -> bool {
    parent.place.root == child.place.root
        && (!matches!(parent.place.root, PlaceRoot::Parameter(_))
            || parent.parameter_storage == child.parameter_storage)
}

/// Validate source identities rather than reinterpreting a name as a field.
fn project(mut ty: Type, path: &[Segment], declarations: &Declarations) -> Result<Type, String> {
    for segment in path {
        ty = resolve_type(&ty, &declarations.aliases)?;
        ty = match (segment, ty) {
            (
                Segment::Dereference,
                Type::Reference { target, .. }
                | Type::PinnedReference { target, .. }
                | Type::PinOwned(target)
                | Type::PinShared(target),
            ) => *target,
            (Segment::Field(id), Type::Named(owner)) => {
                let field = declarations
                    .structs
                    .get(&owner)
                    .and_then(|fields| fields.get(id.index))
                    .ok_or("incoming self-loan lost its checked field")?;
                if declarations.field_id(&Type::Named(owner), &field.name) != Some(*id) {
                    return Err("incoming self-loan lost its field identity".into());
                }
                field.ty.clone()
            }
            (Segment::Tuple(index), Type::Tuple(elements)) => elements
                .get(*index)
                .cloned()
                .ok_or("incoming self-loan tuple index is out of bounds")?,
            (Segment::Payload(id, index), Type::Named(owner)) => {
                let variant = declarations
                    .enums
                    .get(&owner)
                    .and_then(|variants| variants.get(id.index))
                    .ok_or("incoming self-loan lost its checked variant")?;
                if declarations.variant_id(&Type::Named(owner), &variant.name) != Some(*id) {
                    return Err("incoming self-loan lost its variant identity".into());
                }
                variant
                    .fields
                    .get(*index)
                    .cloned()
                    .ok_or("incoming self-loan payload index is out of bounds")?
            }
            (Segment::Index(index), Type::Array(element, length)) if *index < length as u128 => {
                *element
            }
            (Segment::Index(_), Type::Slice(element) | Type::MutableSlice(element)) => *element,
            (segment, ty) => {
                return Err(format!(
                    "incoming self-loan cannot project {segment:?} from {ty:?}"
                ))
            }
        };
    }
    resolve_type(&ty, &declarations.aliases)
}

fn crosses_numeric_word_boundary(ty: &Type, path: &[Segment], declarations: &Declarations) -> bool {
    path.iter().enumerate().any(|(index, segment)| {
        if *segment != Segment::Dereference || index == 0
            || !matches!(path[index - 1], Segment::Index(_)) {
            return false;
        }
        matches!(project(ty.clone(), &path[..index], declarations), Ok(Type::U64))
            && matches!(project(ty.clone(), &path[..index - 1], declarations),
                Ok(Type::Array(element, _) | Type::Slice(element) | Type::MutableSlice(element)) if *element == Type::U64)
    })
}

impl Alias {
    /// An incoming family exists only in the entry constructors containing its
    /// owner target AND its pointer storage. A later constructor assignment
    /// cannot establish such an entry fact or revive an impossible family.
    fn excluded_at_entry(&self, facts: &HashMap<Place, crate::typed_ir::VariantId>) -> bool {
        let contradicts = |path: &[Segment]| {
            path.iter().enumerate().any(|(index, segment)| {
                let Segment::Payload(wanted, _) = segment else {
                    return false;
                };
                let mut segments = self.owner_input.clone();
                segments.extend_from_slice(&path[..index]);
                facts
                    .get(&Place {
                        root: PlaceRoot::Parameter(self.parameter),
                        segments,
                    })
                    .is_some_and(|actual| actual.owner == wanted.owner && actual != wanted)
            })
        };
        let mut storage_prefix = self.owner_input.clone();
        storage_prefix.push(Segment::Dereference);
        contradicts(&self.projection)
            || self
                .storage
                .strip_prefix(storage_prefix.as_slice())
                .is_some_and(contradicts)
    }

    pub fn validate(
        &self,
        parameter_type: &Type,
        declarations: &Declarations,
    ) -> Result<(), String> {
        let mut prefix = self.owner_input.clone();
        prefix.push(Segment::Dereference);
        if !static_storage_path(&self.owner_input)
            || !self.storage.starts_with(&prefix)
            || !static_storage_path(&self.storage[prefix.len()..])
        {
            return Err("incoming self-loan storage is not inside its owner pointee".into());
        }
        let owner = project(parameter_type.clone(), &self.owner_input, declarations)?;
        let target = match owner {
            Type::Reference { target, .. } | Type::PinnedReference { target, .. } => target,
            Type::PinOwned(target) | Type::PinShared(target) => target,
            _ => return Err("incoming self-loan owner is not an addressable owner".into()),
        };
        let child = project(parameter_type.clone(), &self.storage, declarations)?;
        let (target_type, mutable, pinned) = match child {
            Type::Reference { target, mutable } => (*target, mutable, false),
            Type::PinnedReference { target, mutable } => (*target, mutable, true),
            _ => return Err("incoming self-loan storage is not a reference slot".into()),
        };
        if (self.mutable && !mutable) || pinned != self.pinned {
            return Err("incoming self-loan changed its reference capability".into());
        }
        if !static_path(&self.projection) {
            return Err("incoming self-loan needs its selected address snapshot".into());
        }
        let leaf = project(*target, &self.projection, declarations)?;
        if leaf != target_type {
            return Err("incoming self-loan disagrees with its checked pointee type".into());
        }
        Ok(())
    }
}

impl Plan {
    pub fn for_call(
        body: &Body,
        flow: &FlowGraph,
        event: FlowNodeId,
        value: NodeId,
        origins: &FlowLoanOrigins,
        declarations: &Declarations,
    ) -> Result<Self, String> {
        Self::for_call_excluding_entry_families(
            body,
            flow,
            event,
            value,
            origins,
            declarations,
            &HashSet::new(),
        )
    }

    fn for_call_excluding_entry_families(
        body: &Body,
        flow: &FlowGraph,
        event: FlowNodeId,
        value: NodeId,
        origins: &FlowLoanOrigins,
        declarations: &Declarations,
        excluded: &HashSet<usize>,
    ) -> Result<Self, String> {
        let NodeKind::Form {
            callee: Some(callee),
            children,
            ..
        } = &body.nodes[value.0].kind
        else {
            return Err("incoming self-loans require an actual resolved call".into());
        };
        declarations
            .function_name(*callee)
            .ok_or("incoming self-loan callee identity disappeared")?;
        let target = &declarations.function(*callee).signature;
        if children.len() != target.parameters.len() + 1 {
            return Err("incoming self-loan call argument identities changed".into());
        }
        let mut aliases = Vec::new();
        for (parameter, argument) in children.iter().skip(1).enumerate() {
            let ty = &target.parameters[parameter];
            for parent in origins.value_before(body, flow, event, *argument) {
                if parent.lifetime_only
                    || parent
                        .entry_loan
                        .is_some_and(|family| excluded.contains(&family))
                    || !static_storage_path(&parent.storage)
                    || !static_path(&parent.place.segments)
                {
                    continue;
                }
                let pointer = match project(ty.clone(), &parent.storage, declarations) {
                    Ok(pointer) => pointer,
                    Err(error) => {
                        // Word backing carries decoded-owner provenance past
                        // numeric cells, not declared typed pointer fields.
                        // Reject other malformed paths instead of hiding them.
                        if crosses_numeric_word_boundary(ty, &parent.storage, declarations) {
                            continue;
                        }
                        return Err(error);
                    }
                };
                if !is_owner_pointer(&pointer) {
                    continue;
                }
                let mut pending = vec![(parent.clone(), parent.storage.clone(), 0usize)];
                let mut visited = HashSet::new();
                while let Some((owner, owner_input, depth)) = pending.pop() {
                    let key = (
                        owner.place.clone(),
                        owner.parameter_storage.clone(),
                        owner.storage.clone(),
                        owner_input.clone(),
                        owner.mutable,
                        owner.pinned,
                    );
                    if !visited.insert(key) {
                        continue;
                    }
                    if depth >= MAX_INTERNAL_OWNER_DEPTH {
                        return Err(format!(
                            "nested internal-reference chain exceeds {MAX_INTERNAL_OWNER_DEPTH} levels"
                        ));
                    }
                    let Ok(owner_type) = project(ty.clone(), &owner_input, declarations) else {
                        // Provenance can also carry pointers reachable from
                        // neighboring parameters or opaque capture storage.
                        // Follow only paths that resolve inside this argument's
                        // checked type; those others are not nested owner slots.
                        continue;
                    };
                    if !is_owner_pointer(&owner_type) {
                        continue;
                    }
                    for child in origins.pointee_before(body, event, &owner) {
                        if child.lifetime_only
                            || child
                                .entry_loan
                                .is_some_and(|family| excluded.contains(&family))
                            || !static_storage_path(&child.storage)
                            || !static_path(&child.place.segments)
                        {
                            continue;
                        }
                        let mut storage = owner_input.clone();
                        storage.push(Segment::Dereference);
                        storage.extend_from_slice(&child.storage);
                        let Ok(child_type) = project(ty.clone(), &storage, declarations) else {
                            continue;
                        };
                        if !is_owner_pointer(&child_type) {
                            continue;
                        }
                        if same_pointer_root(&owner, &child)
                            && child.place.segments.starts_with(&owner.place.segments)
                        {
                            let alias = Alias {
                                parameter: BindingId(parameter),
                                storage: storage.clone(),
                                owner_input: owner_input.clone(),
                                projection: child.place.segments[owner.place.segments.len()..]
                                    .to_vec(),
                                mutable: child.mutable,
                                pinned: child.pinned,
                                caller_slot: static_storage_path(&child.storage).then(|| {
                                    let mut slot = owner.place.clone();
                                    slot.segments.extend_from_slice(&child.storage);
                                    slot
                                }),
                                caller_referent: child.referent_place(),
                            };
                            alias.validate(ty, declarations)?;
                            if !aliases.contains(&alias) {
                                aliases.push(alias);
                            }
                        }
                        // A reference held by this owner grants access to a
                        // second object as well. Follow it so references stored
                        // in that object remain associated with this call's
                        // named parameter and nested storage path.
                        pending.push((child, storage, depth + 1));
                    }
                }
            }
        }
        Ok(Self {
            callee: *callee,
            aliases,
        })
    }

    /// This is an additional rejection check, NOT a proof granting a parent
    /// reborrow. In particular it does not waive existing direct/call checks.
    /// Callee entry seeds are may-aliases; definite replacement may retire them,
    /// but a branch-only clear must not erase a retained child.
    #[cfg(test)]
    pub fn check_owner_accesses(
        &self,
        declarations: &Declarations,
        types: &crate::linearcheck::LinearTypes,
    ) -> Result<(), crate::typed_borrow::BorrowConflict> {
        self.check_owner_accesses_inner(
            declarations,
            types,
            &mut Vec::new(),
            &mut Cache::default(),
            true,
        )
        .map_err(|(_, error)| error)
    }

    fn check_owner_accesses_inner(
        &self,
        declarations: &Declarations,
        types: &crate::linearcheck::LinearTypes,
        stack: &mut Vec<FunctionId>,
        cache: &mut Cache,
        check_observations: bool,
    ) -> Result<(), (BindingId, crate::typed_borrow::BorrowConflict)> {
        use crate::typed_borrow::BorrowConflict;
        if self.aliases.is_empty() || cache.checked.contains(&(self.clone(), check_observations)) {
            return Ok(());
        }
        let name = declarations
            .function_name(self.callee)
            .expect("checked callee identity");
        let Some(body) = declarations.bodies.get(name) else {
            return Err((
                self.aliases[0].parameter,
                BorrowConflict {
                    message:
                        "cannot inspect callee access to an owner containing internal references"
                            .into(),
                    span: None,
                    labels: vec![],
                },
            ));
        };
        if stack.contains(&self.callee) {
            return Err((
                self.aliases[0].parameter,
                BorrowConflict {
                    message: "recursive internal-loan checking is not permitted".into(),
                    span: None,
                    labels: vec![],
                },
            ));
        }
        stack.push(self.callee);
        let flow = &declarations.flows[name];
        let origins = flow.loan_origins_with_entry_aliases(body, &self.aliases);
        let baseline = cache
            .baseline
            .entry(self.callee)
            .or_insert_with(|| std::rc::Rc::new(flow.loan_origins(body)))
            .clone();
        let entry = cached_entry_tags(self.callee, body, flow, &baseline, cache);
        let consumptions = flow.consumptions(body, types);
        let live = flow.liveness(body);
        for (index, node) in flow.nodes.iter().enumerate() {
            let event = FlowNodeId(index);
            let current_variants = origins.variants_before(body, flow, event);
            let live_bindings = live
                .before(event)
                .into_iter()
                .filter(|binding| {
                    binding.0 >= body.parameter_count
                        && !consumptions.definitely_consumed_before(
                            event,
                            &Place::root(PlaceRoot::Local(*binding)),
                        )
                })
                .collect::<Vec<_>>();
            // Preserve the selected child loan's identity for writes as well
            // as reads; a write through that child is not an owner write.
            let mut writes = observation_alternatives(
                origins
                    .stores_before(body, flow, event)
                    .into_iter()
                    .map(|store| store.destination)
                    .collect::<Vec<_>>(),
            );
            let mut guarded = Vec::new();
            let mut observations = if check_observations {
                observations_at(body, flow, &origins, event, &consumptions)
            } else {
                Vec::new()
            }
            .into_iter()
            .map(|(target, exclusive)| (target, exclusive, Vec::new(), node.span))
            .collect::<Vec<_>>();
            if let FlowAction::Evaluate(value) = node.action {
                if let NodeKind::Form {
                    callee: Some(target),
                    children,
                    ..
                } = &body.nodes[value.0].kind
                {
                    let effects =
                        guarded_writes(*target, declarations, types, cache, &mut HashSet::new())
                            .map_err(|message| {
                                (
                                    self.aliases[0].parameter,
                                    BorrowConflict {
                                        message,
                                        span: node.span,
                                        labels: vec![],
                                    },
                                )
                            })?;
                    writes.clear();
                    for effect in effects {
                        let targets = observation_alternatives(map_write_input(
                            body,
                            flow,
                            &origins,
                            event,
                            children,
                            &effect.target,
                        ));
                        let mut guards = Vec::new();
                        for (guard, variant) in effect.guards {
                            let mapped =
                                map_write_input(body, flow, &origins, event, children, &guard);
                            if mapped.len() == 1 && !mapped[0].lifetime_only {
                                guards.push((mapped[0].clone(), variant));
                            }
                        }
                        guarded.extend(targets.into_iter().map(|target| (target, guards.clone())));
                    }
                    let effects = if check_observations {
                        guarded_observations(
                            *target,
                            declarations,
                            types,
                            cache,
                            &mut HashSet::new(),
                        )
                        .map_err(|message| {
                            (
                                self.aliases[0].parameter,
                                BorrowConflict {
                                    message,
                                    span: node.span,
                                    labels: vec![],
                                },
                            )
                        })?
                    } else {
                        Vec::new()
                    };
                    for effect in effects {
                        let mut guards = Vec::new();
                        for (guard, variant) in effect.guards {
                            let mapped =
                                map_write_input(body, flow, &origins, event, children, &guard);
                            if mapped.len() == 1 && !mapped[0].lifetime_only {
                                guards.push((mapped[0].clone(), variant));
                            }
                        }
                        let mapped_targets = observation_alternatives(map_write_input(
                            body,
                            flow,
                            &origins,
                            event,
                            children,
                            &effect.target,
                        ));
                        observations.extend(
                            mapped_targets
                                .into_iter()
                                .filter(|target| !target.lifetime_only && target.storage.is_empty())
                                .map(|target| {
                                    (
                                        target,
                                        effect.exclusive,
                                        guards.clone(),
                                        effect.span.or(node.span),
                                    )
                                }),
                        );
                    }
                }
            }
            match &node.action {
                FlowAction::Read {
                    place,
                    place_base: false,
                    ..
                } if consumptions.consumes_at(event, place) => {
                    if let PlaceRoot::Local(binding) = place.root {
                        writes.extend(observation_alternatives(origins.projected_origins(
                            event,
                            binding,
                            &place.segments,
                        )));
                    }
                }
                FlowAction::Release { place, .. } => {
                    if let PlaceRoot::Local(binding) = place.root {
                        writes.extend(observation_alternatives(origins.projected_origins(
                            event,
                            binding,
                            &place.segments,
                        )));
                    }
                }
                FlowAction::Evaluate(value) if body.consuming_pin_reads.contains(value) => {
                    if let NodeKind::Form { children, .. } = &body.nodes[value.0].kind {
                        writes.extend(observation_alternatives(origins.value_before(
                            body,
                            flow,
                            event,
                            children[1],
                        )));
                    }
                }
                _ => {}
            }
            for (family, alias) in self.aliases.iter().enumerate() {
                if !origins.entry_alias_retained_before(
                    event,
                    family,
                    alias,
                    &live_bindings,
                    current_variants,
                ) {
                    continue;
                }
                if alias.excluded_at_entry(&entry[event.0]) {
                    continue;
                }
                // An incoming pointer into a particular enum payload cannot
                // coexist with a checked different constructor of that same
                // physical owner. This is a path constraint, not retirement
                // of a copied pointer or a permission to replace its owner.
                // In particular, clearing the pointer's *storage* does not
                // prove that copies of it ceased to borrow the referent.
                if baseline
                    .variants_before(body, flow, event)
                    .is_some_and(|facts| {
                        alias.projection.iter().enumerate().any(|(index, segment)| {
                            let Segment::Payload(wanted, _) = segment else {
                                return false;
                            };
                            let mut segments = alias.owner_input.clone();
                            segments.extend_from_slice(&alias.projection[..index]);
                            facts
                                .get(&Place {
                                    root: PlaceRoot::Parameter(alias.parameter),
                                    segments,
                                })
                                .is_some_and(|actual| {
                                    actual.owner == wanted.owner && actual != wanted
                                })
                        })
                    })
                {
                    continue;
                }
                let held = Place {
                    root: PlaceRoot::Parameter(alias.parameter),
                    segments: alias.projection.clone(),
                };
                let overlaps = |write: &LoanOrigin| {
                    write.place.root == held.root
                        && write.parameter_storage.as_deref() == Some(alias.owner_input.as_slice())
                        && write.place.overlaps(&held)
                };
                let incompatible = |guard: &LoanOrigin, actual: crate::typed_ir::VariantId| {
                    guard.place.root == held.root
                        && guard.parameter_storage.as_deref() == Some(alias.owner_input.as_slice())
                        && alias.projection.iter().enumerate().any(|(index, segment)| {
                            matches!(segment, Segment::Payload(wanted, _)
                                if wanted.owner == actual.owner && *wanted != actual
                                    && guard.place.segments == alias.projection[..index])
                        })
                };
                if writes.iter().any(|write| {
                    write.entry_loan != Some(family)
                        && !access_uses_alias_storage(body, alias, write)
                        && overlaps(write)
                }) || guarded.iter().any(|(write, guards)| {
                    write.entry_loan != Some(family)
                        && !access_uses_alias_storage(body, alias, write)
                        && overlaps(write)
                        && !guards
                            .iter()
                            .any(|(guard, variant)| incompatible(guard, *variant))
                }) {
                    return Err((alias.parameter, BorrowConflict {
                        message: format!("cannot mutate or consume an owner while its stored internal reference is retained in '{name}'"),
                        span: node.span, labels: vec![],
                    }));
                }
                if let Some((_, _, _, span)) =
                    observations.iter().find(|(target, exclusive, guards, _)| {
                        target.entry_loan != Some(family)
                            && !access_uses_alias_storage(body, alias, target)
                            && (alias.mutable || *exclusive)
                            && overlaps(target)
                            && !guards
                                .iter()
                                .any(|(guard, variant)| incompatible(guard, *variant))
                    })
                {
                    return Err((alias.parameter, BorrowConflict {
                        message: format!("cannot read or reborrow an owner while its stored conflicting reference is retained in '{name}'"),
                        span: span.or(node.span), labels: vec![],
                    }));
                }
            }
            if let FlowAction::Evaluate(value) = node.action {
                if matches!(
                    body.nodes[value.0].kind,
                    NodeKind::Form {
                        callee: Some(_),
                        ..
                    }
                ) {
                    // Carry the parent's proved entry constraints into nested
                    // contexts. Exclude only those run-local incoming families,
                    // never a fresh borrow of the same address or sibling loan.
                    let excluded = self
                        .aliases
                        .iter()
                        .enumerate()
                        .filter_map(|(family, alias)| {
                            alias.excluded_at_entry(&entry[event.0]).then_some(family)
                        })
                        .collect::<HashSet<_>>();
                    let nested = Self::for_call_excluding_entry_families(
                        body,
                        flow,
                        event,
                        value,
                        &origins,
                        declarations,
                        &excluded,
                    )
                    .map_err(|message| {
                        (
                            self.aliases[0].parameter,
                            BorrowConflict {
                                message,
                                span: node.span,
                                labels: vec![],
                            },
                        )
                    })?;
                    if let Err((parameter, error)) = nested.check_owner_accesses_inner(
                        declarations,
                        types,
                        stack,
                        cache,
                        check_observations,
                    ) {
                        let NodeKind::Form { children, .. } = &body.nodes[value.0].kind else {
                            unreachable!()
                        };
                        let parameter = origins
                            .value_before(body, flow, event, children[parameter.0 + 1])
                            .into_iter()
                            .find_map(|origin| match origin.place.root {
                                PlaceRoot::Parameter(parameter)
                                    if self
                                        .aliases
                                        .iter()
                                        .any(|alias| alias.parameter == parameter) =>
                                {
                                    Some(parameter)
                                }
                                _ => None,
                            })
                            .unwrap_or(self.aliases[0].parameter);
                        return Err((parameter, error));
                    }
                }
            }
        }
        stack.pop();
        cache.checked.insert((self.clone(), check_observations));
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::typed_flow::FlowAction;

    const SOURCE: &str = "
      (#struct Link () ((value #u64) (state #u32) (view (#pin-ref #u64))))
      (#fn install ((target (#pin-ref-mut Link))) (#pin-ref-mut Link)
        (#let view (#pin-ref #u64) (#pin-borrow (#get target value)))
        (#pin-set-field target view view) (#return target))
      (#fn tick ((target (#pin-ref-mut Link))) (#pin-ref-mut Link)
        (#pin-set-field target state 2u32) (#return target))
      (#fn driver ((outside (#pin-ref #u64))) #u64
        (#let-mut link Link (#struct-literal Link ((value 42u64) (state 0u32) (view outside))))
        (#let-mut running (#pin-ref-mut Link) (#pin-borrow-mut link))
        (#let installed (#pin-ref-mut Link) (#call install ((target running))))
        (#set running installed)
        (#let updated (#pin-ref-mut Link) (#call tick ((target running))))
        (#set running updated)
        (#pin-set-field running view outside)
        (#drop running) (#forget link) (#return 0u64))";

    fn fixture(source: &str) -> Declarations {
        let program = crate::parse_program(source).unwrap();
        let mut declarations = crate::typecheck::resolve_program_for_analysis(&program, false)
            .unwrap_or_else(|error| panic!("{error:?}\n{source}"));
        declarations.staged_parameter_contents_summaries();
        declarations
    }

    #[test]
    fn selected_payload_snapshot_access_and_reinitialization_are_distinct() {
        let source = r#"
          (#enum Choice () ((Choice.Good #u64) (Choice.Bad #u64)))
          (#enum Address () (Address.Empty (Address.Full (#pin-ref-mut #u64))))
          (#struct Frame () ((owner Choice) (address Address) (pc #u32)))
          (#fn select ((owner (#pin-ref-mut Choice))) (#pin-ref-mut #u64)
            (#return (#unsafe (#pin-get-payload-unchecked-mut owner Choice.Good))))
          (#fn install ((target (#pin-ref-mut Frame))) (#pin-ref-mut Frame)
            (#let selected (#pin-ref-mut #u64)
              (#unsafe (#pin-get-payload-unchecked-mut (#pin-borrow-mut (#get target owner)) Choice.Good)))
            (#unsafe (#pin-write (#pin-borrow-mut (#get target address)) (Address.Full selected)))
            (#return target))
          (#fn resume ((target (#pin-ref-mut Frame))) (#pin-ref-mut Frame)
            INITIALIZE
            (#unsafe (#pin-write
              (#deref (#unsafe (#pin-get-payload-unchecked-mut (#pin-borrow-mut (#get target address)) Address.Full)))
              42u64))
            (#unsafe (#pin-write (#pin-borrow-mut (#get target address)) Address.Empty))
            (#return target))
          (#fn driver () ()
            (#let-mut frame Frame
              (#struct-literal Frame ((owner (Choice.Good 0u64)) (address Address.Empty) (pc 1u32))))
            (#let installed (#pin-ref-mut Frame)
              (#call install ((target (#pin-borrow-mut frame)))))
            (#let resumed (#pin-ref-mut Frame) (#call resume ((target installed))))
            (#drop resumed) (#forget frame) (#return ()))
        "#;
        for (initialize, conflicting_access) in [
            ("", None),
            (
                "(#if (#u32::eq (#get target pc) 0u32)
                  (#block
                    (#assert (#variant-is (#pin-borrow (#get target address)) Address.Empty))
                    (#unsafe (#pin-write (#pin-borrow-mut (#get target owner)) (Choice.Good 9u64)))
                    (#let selected (#pin-ref-mut #u64)
                      (#unsafe (#pin-get-payload-unchecked-mut (#pin-borrow-mut (#get target owner)) Choice.Good)))
                    (#unsafe (#pin-write (#pin-borrow-mut (#get target address)) (Address.Full selected)))
                    ()) ())",
                None,
            ),
            (
                "(#if (#u32::eq (#get target pc) 0u32)
                  (#block
                    (#let selected (#pin-ref-mut #u64)
                      (#unsafe (#pin-get-payload-unchecked-mut (#pin-borrow-mut (#get target owner)) Choice.Good)))
                    (#unsafe (#pin-write (#pin-borrow-mut (#get target address)) (Address.Full selected)))
                    ()) ())",
                Some("(#pin-borrow-mut (#get target owner))"),
            ),
            (
                "(#unsafe (#pin-write (#pin-borrow-mut (#get target owner)) (Choice.Good 9u64)))",
                Some("(#pin-write (#pin-borrow-mut (#get target owner)) (Choice.Good 9u64))"),
            ),
            (
                "(#unsafe (#pin-write (#pin-borrow-mut (#get target owner)) (Choice.Good 9u64)))
                  (#assert (#variant-is (#pin-borrow (#get target address)) Address.Empty))",
                Some("(#pin-write (#pin-borrow-mut (#get target owner)) (Choice.Good 9u64))"),
            ),
        ] {
            for helper in [false, true] {
                let mut source = source.replace("INITIALIZE", initialize);
                if helper {
                    source = source.replace(
                        "(#unsafe (#pin-get-payload-unchecked-mut (#pin-borrow-mut (#get target owner)) Choice.Good))",
                        "(#call select ((owner (#pin-borrow-mut (#get target owner)))))",
                    );
                }
                let declarations = fixture(&source);
                let plan = call_plan(&declarations, "driver", "resume");
                assert_eq!(plan.aliases.len(), 1, "{plan:?}");
                let result = plan.check_owner_accesses(
                    &declarations,
                    &crate::linearcheck::LinearTypes::default(),
                );
                assert_eq!(
                    result.is_err(),
                    conflicting_access.is_some(),
                    "{result:?}\n{source}"
                );
                if let Err(error) = result {
                    let span = error.span.expect("identify the conflicting owner access");
                    assert_eq!(
                        &source[span.start..span.end],
                        conflicting_access.unwrap(),
                        "{error:?}"
                    );
                }
            }
        }
    }

    fn exclusive_source() -> String {
        SOURCE
            .replace("#pin-ref #u64", "#pin-ref-mut #u64")
            .replace(
                "(#pin-borrow (#get target value))",
                "(#pin-borrow-mut (#get target value))",
            )
            .replace(
                "(#pin-set-field target view view)",
                "(#unsafe (#pin-write (#pin-borrow-mut (#get target view)) view))",
            )
            .replace(
                "(#pin-set-field running view outside)",
                "(#unsafe (#pin-write (#pin-borrow-mut (#get running view)) outside))",
            )
    }

    fn call_plan(declarations: &Declarations, caller: &str, callee: &str) -> Plan {
        let body = &declarations.bodies[caller];
        let flow = &declarations.flows[caller];
        let origins = flow.loan_origins(body);
        let id = declarations.function_id(callee).unwrap();
        let (event, value) = flow
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, event)| match event.action {
                FlowAction::Evaluate(value)
                    if matches!(body.nodes[value.0].kind,
                    NodeKind::Form { callee: Some(found), .. } if found == id) =>
                {
                    Some((FlowNodeId(index), value))
                }
                _ => None,
            })
            .unwrap();
        Plan::for_call(body, flow, event, value, &origins, declarations).unwrap()
    }

    #[test]
    fn parameter_contents_summary_preserves_the_selected_source_slot() {
        let source = "(#struct Link () ((view (#ref #u64))))
            (#fn read-link ((value (#ref Link))) #u64
              (#return (#deref (#get (#deref value) view))))
            (#fn caller ((target (#ref Link))) #u64
              (#return (#call read-link ((value target)))))";
        let declarations = fixture(source);
        let body = &declarations.bodies["caller"];
        let flow = &declarations.flows["caller"];
        let origins = flow.loan_origins(body);
        let call = declarations.function_id("read-link").unwrap();
        let (event, value) = flow
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| match node.action {
                FlowAction::Evaluate(value)
                    if matches!(body.nodes[value.0].kind,
                        NodeKind::Form { callee: Some(found), .. } if found == call) =>
                {
                    Some((FlowNodeId(index), value))
                }
                _ => None,
            })
            .unwrap();
        let view = declarations
            .field_id(&Type::Named("Link".into()), "view")
            .unwrap();
        let summary = crate::typed_body::ParameterLoanSummary {
            fresh_allocation: None,
            owned_allocation: false,
            global: None,
            parameter: 0,
            mutable: false,
            pinned: false,
            lifetime_only: false,
            maybe_absent: false,
            word_stored: false,
            word_view_address: false,
            reborrow: false,
            referent_projection: Vec::new(),
            input_storage: vec![Segment::Dereference, Segment::Field(view)],
            storage: Vec::new(),
            storage_inputs: Vec::new(),
        };
        let argument = match &body.nodes[value.0].kind {
            NodeKind::Form { children, .. } => children[1],
            _ => unreachable!(),
        };
        let slots = origins.summary_slots_before(body, flow, event, argument, &summary);
        assert_eq!(
            slots,
            vec![Place {
                root: PlaceRoot::Parameter(BindingId(0)),
                segments: vec![Segment::Dereference, Segment::Field(view)],
            }]
        );
    }

    #[test]
    fn enum_payload_owner_observation_is_not_hidden_by_a_missing_alias() {
        let source = "(#enum View () (View.NoView (View.HasView (#pin-ref-mut #u64))))
          (#struct Link () ((value #u64) (view View)))
          (#fn install ((target (#pin-ref-mut Link))) (#pin-ref-mut Link)
            (#let view (#pin-ref-mut #u64) (#pin-borrow-mut (#get target value)))
            (#unsafe (#pin-write (#pin-borrow-mut (#get target view)) (View.HasView view)))
            (#return target))
          (#fn observe ((target (#pin-ref-mut Link))) #u64 (#return (#get target value)))
          (#fn driver () #u64
            (#let-mut link Link (#struct-literal Link ((value 42u64) (view View.NoView))))
            (#let installed (#pin-ref-mut Link) (#call install ((target (#pin-borrow-mut link)))))
            (#let value #u64 (#call observe ((target installed))))
            (#unsafe (#pin-write (#pin-borrow-mut (#get installed view)) View.NoView))
            (#drop installed) (#forget link) (#return value))";
        let declarations = fixture(source);
        let plan = call_plan(&declarations, "driver", "observe");
        assert_eq!(plan.aliases.len(), 1, "{:#?}", plan.aliases);
        assert!(plan.aliases[0].mutable, "{:#?}", plan.aliases);
        assert!(plan.aliases[0]
            .storage
            .iter()
            .any(|segment| matches!(segment, Segment::Payload(..))));
        let body = &declarations.bodies["driver"];
        let flow = &declarations.flows["driver"];
        let checked = check_calls(
            body,
            flow,
            &declarations,
            &crate::linearcheck::LinearTypes::default(),
            &std::cell::OnceCell::new(),
        );
        assert!(checked.is_err(), "{source}");

        let shared = source
            .replace("#pin-ref-mut #u64", "#pin-ref #u64")
            .replace(
                "(#pin-borrow-mut (#get target value))",
                "(#pin-borrow (#get target value))",
            );
        let declarations = fixture(&shared);
        let body = &declarations.bodies["driver"];
        let flow = &declarations.flows["driver"];
        check_calls(
            body,
            flow,
            &declarations,
            &crate::linearcheck::LinearTypes::default(),
            &std::cell::OnceCell::new(),
        )
        .unwrap_or_else(|error| {
            panic!("a shared payload loan permits a shared read: {error:?}\n{shared}")
        });
    }

    #[test]
    fn ordinary_function_unknown_enum_tag_retains_possible_mutable_payload_aliases() {
        let source = "(#enum Value () (Value.Empty (Value.Full #u64)))
          (#struct Link () ((value Value) (view (#pin-ref-mut #u64))))
          (#fn install ((target (#pin-ref-mut Link))) (#pin-ref-mut Link)
            (#let view (#pin-ref-mut #u64)
              (#unsafe (#pin-get-payload-unchecked-mut (#pin-borrow-mut (#get target value)) Value.Full)))
            (#unsafe (#pin-write (#pin-borrow-mut (#get target view)) view))
            (#return target))
          (#fn observe ((target (#pin-ref-mut Link))) ()
            (#let payload (#pin-ref-mut #u64)
              (#unsafe (#pin-get-payload-unchecked-mut (#pin-borrow-mut (#get target value)) Value.Full)))
            (#drop payload) (#return ()))
          (#fn driver ((outside (#pin-ref-mut #u64)) (choose #bool)) ()
            (#let-mut link Link (#struct-literal Link
              ((value (#if choose (Value.Full 42u64) Value.Empty)) (view outside))))
            (#if choose
              (#block
                (#let installed (#pin-ref-mut Link)
                  (#call install ((target (#pin-borrow-mut link)))))
                (#drop installed) ())
              ())
            (#call observe ((target (#pin-borrow-mut link))))
            (#forget link) (#return ()))";
        let declarations = fixture(source);
        assert!(declarations.bodies.contains_key("install"));
        assert!(declarations.bodies.contains_key("observe"));
        let plan = call_plan(&declarations, "driver", "observe");
        assert!(plan.aliases.iter().any(|alias| alias
            .projection
            .iter()
            .any(|part| matches!(part, Segment::Payload(..)))));
        let body = &declarations.bodies["driver"];
        let flow = &declarations.flows["driver"];
        let origins = flow.loan_origins(body);
        let (event, call) = flow
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| match node.action {
                FlowAction::Evaluate(value)
                    if matches!(body.nodes[value.0].kind,
                    NodeKind::Form { callee: Some(found), .. }
                        if found == declarations.function_id("observe").unwrap()) =>
                {
                    Some((FlowNodeId(index), value))
                }
                _ => None,
            })
            .unwrap();
        assert_eq!(
            projection_payload_status(body, flow, event, call, &origins, &plan.aliases[0]),
            None,
            "the join must remain unknown, not be treated as inactive"
        );
        let error = check_calls(
            body,
            flow,
            &declarations,
            &crate::linearcheck::LinearTypes::default(),
            &std::cell::OnceCell::new(),
        )
        .expect_err("the active branch may retain a mutable alias into the payload");
        assert!(
            error.message.contains("stored conflicting reference"),
            "{error:?}"
        );
    }

    #[test]
    fn nested_dereference_payload_tag_proves_the_stored_reference_is_active() {
        let source = "(#enum View () (View.NoView (View.HasView (#pin-ref #u64))))
          (#struct Inner () ((value #u64) (view View)))
          (#struct Middle () ((inner (#pin-ref-mut Inner))))
          (#struct Outer () ((middle (#pin-ref-mut Middle))))
          (#struct Shell () ((outer (#pin-ref-mut Outer))))
          (#fn touch-inner ((target (#pin-ref-mut Inner))) ()
            (#let child (#pin-ref-mut #u64) (#pin-borrow-mut (#get target value)))
            (#drop child) (#return ()))
          (#fn observe ((target (#pin-ref-mut Shell))) ()
            (#let outer_ref (#pin-ref-mut Outer) (#get target outer))
            (#let middle_ref (#pin-ref-mut Middle) (#get (#deref outer_ref) middle))
            (#let inner_ref (#pin-ref-mut Inner) (#get (#deref middle_ref) inner))
            (#call touch-inner ((target inner_ref))) (#return ()))
          (#fn relay ((target (#pin-ref-mut Shell))) ()
            (#call observe ((target target))) (#return ()))
          (#fn driver () ()
            (#let-mut inner Inner (#struct-literal Inner ((value 7u64) (view View.NoView))))
            (#let inner_ref (#pin-ref-mut Inner) (#pin-borrow-mut inner))
            (#let view (#pin-ref #u64) (#pin-borrow (#get inner_ref value)))
            (#unsafe (#pin-write (#pin-borrow-mut (#get inner_ref view)) (View.HasView view)))
            (#let-mut middle Middle (#struct-literal Middle ((inner inner_ref))))
            (#let middle_ref (#pin-ref-mut Middle) (#pin-borrow-mut middle))
            (#let-mut outer Outer (#struct-literal Outer ((middle middle_ref))))
            (#let outer_ref (#pin-ref-mut Outer) (#pin-borrow-mut outer))
            (#let-mut shell Shell (#struct-literal Shell ((outer outer_ref))))
            (#let shell_ref (#pin-ref-mut Shell) (#pin-borrow-mut shell))
            (#call relay ((target shell_ref))) (#return ()))";
        let declarations = fixture(source);
        let plan = call_plan(&declarations, "driver", "relay");
        assert!(
            plan.aliases.iter().any(|alias| {
                alias
                    .storage
                    .iter()
                    .filter(|segment| **segment == Segment::Dereference)
                    .count()
                    > 2
                    && alias
                        .storage
                        .iter()
                        .any(|segment| matches!(segment, Segment::Payload(..)))
            }),
            "expected a nested payload alias: {:#?}",
            plan.aliases
        );
        let error = plan
            .check_owner_accesses(&declarations, &crate::linearcheck::LinearTypes::default())
            .expect_err("exclusive nested owner access conflicts with the stored shared loan");
        assert!(
            error.message.contains("stored conflicting reference"),
            "{error:?}"
        );

        let inactive = source.replace("(View.HasView view)", "View.NoView");
        let declarations = fixture(&inactive);
        let plan = call_plan(&declarations, "driver", "relay");
        plan.check_owner_accesses(&declarations, &crate::linearcheck::LinearTypes::default())
            .expect("an inactive payload contains no retained child loan");
    }

    #[test]
    fn numeric_backing_metadata_does_not_declare_typed_pointer_paths() {
        let declarations = fixture(
            "(#struct Packet () ((words (#array #u64 2))
          (scalar #u64) (references (#array (#ref #u64) 1)) (narrow (#array #u32 2))))",
        );
        let packet = Type::Named("Packet".into());
        let field = |name| Segment::Field(declarations.field_id(&packet, name).unwrap());
        let ghost = vec![field("words"), Segment::Index(0), Segment::Dereference];
        assert!(project(packet.clone(), &ghost, &declarations).is_err());
        assert!(crosses_numeric_word_boundary(
            &packet,
            &ghost,
            &declarations
        ));
        let mut borrowed = vec![Segment::Dereference];
        borrowed.extend_from_slice(&ghost);
        assert!(crosses_numeric_word_boundary(
            &Type::Reference {
                mutable: true,
                target: Box::new(packet.clone()),
            },
            &borrowed,
            &declarations
        ));
        for path in [
            vec![field("scalar"), Segment::Dereference],
            vec![field("words"), Segment::Index(2), Segment::Dereference],
            vec![field("words"), Segment::Index(0), field("scalar")],
            vec![field("references"), Segment::Index(0), Segment::Dereference],
            vec![field("narrow"), Segment::Index(0), Segment::Dereference],
        ] {
            assert!(
                !crosses_numeric_word_boundary(&packet, &path, &declarations),
                "{path:?}"
            );
        }
    }

    #[test]
    fn actual_stored_self_loan_has_separate_storage_and_referent_paths() {
        let declarations = fixture(SOURCE);
        let plan = call_plan(&declarations, "driver", "tick");
        let view = declarations
            .field_id(&Type::Named("Link".into()), "view")
            .unwrap();
        let value = declarations
            .field_id(&Type::Named("Link".into()), "value")
            .unwrap();
        assert_eq!(plan.callee, declarations.function_id("tick").unwrap());
        assert_eq!(
            plan.aliases,
            vec![Alias {
                parameter: BindingId(0),
                storage: vec![Segment::Dereference, Segment::Field(view)],
                owner_input: vec![],
                projection: vec![Segment::Field(value)],
                mutable: false,
                pinned: true,
                caller_slot: Some(Place {
                    root: PlaceRoot::Local(BindingId(1)),
                    segments: vec![Segment::Field(view)],
                }),
                caller_referent: Place {
                    root: PlaceRoot::Local(BindingId(1)),
                    segments: vec![Segment::Field(value)],
                },
            }]
        );
        assert!(call_plan(&declarations, "driver", "install")
            .aliases
            .is_empty());
    }

    #[test]
    fn proven_disjoint_owner_call_grants_only_its_retained_child_slot() {
        let declarations = fixture(SOURCE);
        let body = &declarations.bodies["driver"];
        let flow = &declarations.flows["driver"];
        let permissions = check_calls_cached(
            body,
            flow,
            &declarations,
            &crate::linearcheck::LinearTypes::default(),
            &std::cell::OnceCell::new(),
            &mut Cache::default(),
        )
        .unwrap();
        let view = declarations
            .field_id(&Type::Named("Link".into()), "view")
            .unwrap();
        let value = declarations
            .field_id(&Type::Named("Link".into()), "value")
            .unwrap();
        assert!(
            permissions.iter().any(|permission| {
                permission.slot
                    == Place {
                        root: PlaceRoot::Local(BindingId(1)),
                        segments: vec![Segment::Field(view)],
                    }
                    && permission.referent
                        == Place {
                            root: PlaceRoot::Local(BindingId(1)),
                            segments: vec![Segment::Field(value)],
                        }
            }),
            "the proven call should grant its own view field: {permissions:?}"
        );
    }

    #[test]
    fn loaded_internal_child_can_survive_a_proven_disjoint_owner_call() {
        let source = SOURCE.replace(
            "(#let updated (#pin-ref-mut Link) (#call tick ((target running))))\n        (#set running updated)",
            "(#let held (#pin-ref #u64) (#get running view))\n        (#let sibling #u32 (#get running state)) (#forget sibling)\n        (#let updated (#pin-ref-mut Link) (#call tick ((target running))))\n        (#set running updated)\n        (#let observed #u64 (#deref held)) (#forget observed) (#drop held)",
        );
        let declarations = fixture(&source);
        let body = &declarations.bodies["driver"];
        let flow = &declarations.flows["driver"];
        let permissions = check_calls_cached(
            body,
            flow,
            &declarations,
            &crate::linearcheck::LinearTypes::default(),
            &std::cell::OnceCell::new(),
            &mut Cache::default(),
        )
        .unwrap();
        let ordinary = crate::typed_borrow::check_live_direct_loans_cached_with_permissions(
            body,
            flow,
            &crate::linearcheck::LinearTypes::default(),
            &std::cell::OnceCell::new(),
            &[],
        );
        let permitted = crate::typed_borrow::check_live_direct_loans_cached_with_permissions(
            body,
            flow,
            &crate::linearcheck::LinearTypes::default(),
            &std::cell::OnceCell::new(),
            &permissions,
        );
        assert!(
            ordinary.is_err(),
            "the fixture must exercise the conflict: {ordinary:?}"
        );
        assert!(
            permitted.is_ok(),
            "the exact owner permission should resolve it: {permitted:?}\n{source}"
        );
        let program = crate::parse_program(&source).unwrap();
        crate::check_types(&program).unwrap();
    }

    #[test]
    fn loaded_internal_child_still_rejects_an_overlapping_owner_call() {
        let source = SOURCE
            .replace(
                "(#pin-set-field target state 2u32)",
                "(#pin-set-field target value 2u64)",
            )
            .replace(
                "(#let updated (#pin-ref-mut Link) (#call tick ((target running))))\n        (#set running updated)",
                "(#let held (#pin-ref #u64) (#get running view))\n        (#let updated (#pin-ref-mut Link) (#call tick ((target running))))\n        (#set running updated)\n        (#let observed #u64 (#deref held)) (#forget observed) (#drop held)",
            );
        let declarations = fixture(&source);
        let body = &declarations.bodies["driver"];
        let error = check_calls_cached(
            body,
            &declarations.flows["driver"],
            &declarations,
            &crate::linearcheck::LinearTypes::default(),
            &std::cell::OnceCell::new(),
            &mut Cache::default(),
        )
        .unwrap_err();
        let span = error.span.unwrap();
        assert_eq!(&source[span.start..span.end], "running");
        assert!(
            error
                .labels
                .iter()
                .any(|(_, label)| label.contains("callee accesses")),
            "expected the overlapping callee access to be labeled: {error:?}"
        );
    }

    #[test]
    fn loaded_internal_child_suspends_only_overlapping_parent_access() {
        let source = SOURCE.replace(
            "(#let updated (#pin-ref-mut Link) (#call tick ((target running))))\n        (#set running updated)",
            "(#let held (#pin-ref #u64) (#get running view))\n        (#let forbidden #u64 (#get running value)) (#forget forbidden)\n        (#let updated (#pin-ref-mut Link) (#call tick ((target running))))\n        (#set running updated)\n        (#let observed #u64 (#deref held)) (#forget observed) (#drop held)",
        );
        let program = crate::parse_program(&source).unwrap();
        let (_, _, span, _) = crate::typecheck::check_types_with_span(&program).unwrap_err();
        let span = span.unwrap();
        assert_eq!(&source[span.start..span.end], "#get");
    }

    #[test]
    fn external_pointees_and_cleared_self_loans_are_not_owner_aliases() {
        for source in [
            SOURCE.replace("(#let installed (#pin-ref-mut Link) (#call install ((target running))))\n        (#set running installed)", ""),
            SOURCE.replace("(#let updated (#pin-ref-mut Link) (#call tick ((target running))))",
                "(#pin-set-field running view outside) (#let updated (#pin-ref-mut Link) (#call tick ((target running))))"),
        ] {
            let declarations = fixture(&source);
            assert!(call_plan(&declarations, "driver", "tick").aliases.is_empty());
        }
    }

    #[test]
    fn symbolic_nested_pointer_slots_do_not_imply_physical_self_aliases() {
        let source = "(#struct Link () ((value #u64) (view (#pin-ref #u64))))
          (#fn tick ((target (#pin-ref-mut Link))) (#pin-ref-mut Link) (#return target))
          (#fn driver ((input (#pin-ref-mut Link))) (#pin-ref-mut Link)
            (#return (#call tick ((target input)))))";
        let declarations = fixture(source);
        assert!(call_plan(&declarations, "driver", "tick")
            .aliases
            .is_empty());
    }

    #[test]
    fn malformed_storage_capabilities_and_pointee_types_fail_closed() {
        let declarations = fixture(SOURCE);
        let plan = call_plan(&declarations, "driver", "tick");
        let alias = plan.aliases.first().unwrap();
        let ty = &declarations.bodies["tick"].bindings[0].ty;
        for kind in 0..6 {
            let mut bad = alias.clone();
            match kind {
                0 => {
                    if let Segment::Field(field) = &mut bad.storage[1] {
                        field.index = usize::MAX;
                    }
                }
                1 => bad.projection = vec![Segment::DynamicIndex],
                2 => bad.mutable = true,
                3 => bad.pinned = false,
                5 => {
                    bad.storage.clear();
                    bad.projection.clear();
                }
                _ => {
                    bad.projection = vec![Segment::Field(
                        declarations
                            .field_id(&Type::Named("Link".into()), "state")
                            .unwrap(),
                    )]
                }
            }
            assert!(bad.validate(ty, &declarations).is_err(), "{bad:?}");
        }
    }

    #[test]
    fn disjoint_owner_writes_and_writes_through_the_child_are_not_rejected() {
        for operation in [
            "(#pin-set-field target state 2u32)",
            "(#let observed #u64 (#deref (#get target view))) (#forget observed)",
        ] {
            let source = SOURCE.replace("(#pin-set-field target state 2u32)", operation);
            let declarations = fixture(&source);
            let plan = call_plan(&declarations, "driver", "tick");
            plan.check_owner_accesses(&declarations, &crate::linearcheck::LinearTypes::default())
                .unwrap();
        }
    }

    #[test]
    fn destructive_owner_writes_are_checked_using_actual_incoming_aliases() {
        let source = SOURCE.replace(
            "(#pin-set-field target state 2u32)",
            "(#pin-set-field target value 99u64)",
        );
        let declarations = fixture(&source);
        let plan = call_plan(&declarations, "driver", "tick");
        let error = plan
            .check_owner_accesses(&declarations, &crate::linearcheck::LinearTypes::default())
            .unwrap_err();
        let span = error.span.unwrap();
        assert_eq!(
            &source[span.start..span.end],
            "(#pin-set-field target value 99u64)"
        );
        // An external child pointer does not borrow the owner's value field.
        let external = source.replace("(#let installed (#pin-ref-mut Link) (#call install ((target running))))\n        (#set running installed)", "");
        let declarations = fixture(&external);
        call_plan(&declarations, "driver", "tick")
            .check_owner_accesses(&declarations, &crate::linearcheck::LinearTypes::default())
            .unwrap();
    }

    #[test]
    fn exclusive_internal_loans_block_owner_reads_clones_and_reborrows() {
        for (operation, expected) in [
            ("(#let observed #u64 (#get target value)) (#forget observed)", "(#get target value)"),
            ("(#let observed #u64 (#clone (#get target value))) (#forget observed)", "(#clone (#get target value))"),
            ("(#let another (#pin-ref #u64) (#pin-borrow (#get target value))) (#drop another)", "(#pin-borrow (#get target value))"),
            ("(#let another (#pin-ref-mut #u64) (#pin-borrow-mut (#get target value))) (#drop another)", "(#pin-borrow-mut (#get target value))"),
        ] {
            let source = exclusive_source().replace("(#pin-set-field target state 2u32)", operation);
            let declarations = fixture(&source);
            let plan = call_plan(&declarations, "driver", "tick");
            assert!(plan.aliases[0].mutable);
            let error = plan.check_owner_accesses(&declarations, &crate::linearcheck::LinearTypes::default())
                .err().unwrap_or_else(|| panic!("a read or reborrow through the owner cannot bypass its exclusive child: {operation}"));
            let span = error.span.unwrap();
            assert_eq!(&source[span.start..span.end], expected, "{}", error.message);
        }
    }

    #[test]
    fn shared_internal_loans_allow_shared_access_but_not_exclusive_reborrows() {
        for (operation, rejected) in [
            ("(#let observed #u64 (#get target value)) (#forget observed)", false),
            ("(#let another (#pin-ref #u64) (#pin-borrow (#get target value))) (#drop another)", false),
            ("(#let another (#pin-ref-mut #u64) (#pin-borrow-mut (#get target value))) (#drop another)", true),
        ] {
            let source = SOURCE.replace("(#pin-set-field target state 2u32)", operation);
            let declarations = fixture(&source);
            let result = call_plan(&declarations, "driver", "tick")
                .check_owner_accesses(&declarations, &crate::linearcheck::LinearTypes::default());
            assert_eq!(result.is_err(), rejected, "{result:?}\n{source}");
        }
    }

    #[test]
    fn child_access_and_disjoint_owner_reads_preserve_their_pointer_permissions() {
        for operation in [
            "(#let observed #u32 (#get target state)) (#forget observed)",
            "(#let observed #u64 (#deref (#get target view))) (#forget observed)",
            "(#let observed #u64 (#call child-read ((pointer (#get target view))))) (#forget observed)",
        ] {
            let source = format!("{} (#fn child-read ((pointer (#pin-ref-mut #u64))) #u64 (#return (#deref pointer)))",
                exclusive_source().replace("(#pin-set-field target state 2u32)", operation));
            let declarations = fixture(&source);
            call_plan(&declarations, "driver", "tick")
                .check_owner_accesses(&declarations, &crate::linearcheck::LinearTypes::default()).unwrap();
        }
    }

    #[test]
    fn nested_observers_retain_the_deepest_access_span_at_the_caller_argument() {
        let source = format!(
            "{}
          (#fn observe ((pointer (#pin-ref #u64))) #u64 (#return (#deref pointer)))
          (#fn forward ((target (#pin-ref-mut Link))) #u64
            (#return (#call observe ((pointer (#pin-borrow (#get target value)))))))",
            exclusive_source().replace(
                "(#pin-set-field target state 2u32)",
                "(#let observed #u64 (#call forward ((target target)))) (#forget observed)"
            )
        );
        let declarations = fixture(&source);
        let body = &declarations.bodies["driver"];
        let error = check_calls(
            body,
            &declarations.flows["driver"],
            &declarations,
            &crate::linearcheck::LinearTypes::default(),
            &std::cell::OnceCell::new(),
        )
        .unwrap_err();
        let span = error.span.unwrap();
        assert_eq!(&source[span.start..span.end], "running");
        let label = error
            .labels
            .iter()
            .find(|(_, label)| label.contains("callee accesses"))
            .unwrap()
            .0;
        assert_eq!(&source[label.start..label.end], "(#deref pointer)");
    }

    #[test]
    fn clearing_an_exclusive_slot_retires_its_family_but_not_a_live_loaded_child() {
        for (saved, rejected) in [(false, false), (true, true)] {
            let operation = format!(
                "{}
              (#unsafe (#pin-write (#pin-borrow-mut (#get target view)) outside))
              (#let observed #u64 (#get target value)) (#forget observed) {}",
                if saved {
                    "(#let saved (#pin-ref-mut #u64) (#get target view))"
                } else {
                    ""
                },
                if saved {
                    "(#let used #u64 (#deref saved)) (#forget used) (#drop saved)"
                } else {
                    ""
                }
            );
            let source = exclusive_source()
                .replace(
                    "(#fn tick ((target (#pin-ref-mut Link)))",
                    "(#fn tick ((target (#pin-ref-mut Link)) (outside (#pin-ref-mut #u64)))",
                )
                .replace(
                    "(#call tick ((target running)))",
                    "(#call tick ((target running) (outside outside)))",
                )
                .replace("(#pin-set-field target state 2u32)", &operation);
            let declarations = fixture(&source);
            let checked = call_plan(&declarations, "driver", "tick")
                .check_owner_accesses(&declarations, &crate::linearcheck::LinearTypes::default());
            assert_eq!(checked.is_err(), rejected, "{checked:?}\n{source}");
        }
    }

    #[test]
    fn repeated_nested_observers_deduplicate_without_erasing_the_access_slot() {
        let mut source = String::from(
            "(#fn level0 ((pointer (#pin-ref #u64))) #u64 (#return (#deref pointer)))",
        );
        for level in 1..=20 {
            source.push_str(&format!(
                "(#fn level{level} ((pointer (#pin-ref #u64))) #u64
              (#let ignored #u64 (#call level{} ((pointer pointer))))
              (#return (#call level{} ((pointer pointer)))))",
                level - 1,
                level - 1
            ));
        }
        let declarations = fixture(&source);
        let mut cache = Cache::default();
        let effects = guarded_observations(
            declarations.function_id("level20").unwrap(),
            &declarations,
            &crate::linearcheck::LinearTypes::default(),
            &mut cache,
            &mut HashSet::new(),
        )
        .unwrap();
        assert_eq!(effects.len(), 1);
        assert_eq!(cache.observations.len(), 21);
        assert!(cache
            .observations
            .values()
            .all(|effects| effects.len() == 1));
        assert_eq!(effects[0].target.input_storage, Vec::<Segment>::new());
        assert!(!effects[0].exclusive);
    }

    #[test]
    fn write_only_context_caching_does_not_authorize_observations() {
        let source = exclusive_source().replace(
            "(#pin-set-field target state 2u32)",
            "(#let observed #u64 (#get target value)) (#forget observed)",
        );
        let declarations = fixture(&source);
        let plan = call_plan(&declarations, "driver", "tick");
        let types = crate::linearcheck::LinearTypes::default();
        let mut cache = Cache::default();
        plan.check_owner_accesses_inner(&declarations, &types, &mut Vec::new(), &mut cache, false)
            .unwrap();
        let error = plan
            .check_owner_accesses_inner(&declarations, &types, &mut Vec::new(), &mut cache, true)
            .unwrap_err();
        assert!(error.1.message.contains("stored conflicting reference"));
        assert!(cache.checked.contains(&(plan.clone(), false)));
        assert!(!cache.checked.contains(&(plan, true)));
    }

    const PAYLOAD_ENTRY_SOURCE: &str = "(#enum Value () (Value.Empty (Value.Full #u64)))
          (#struct Link () ((value Value) (view (#pin-ref #u64))))
          (#fn install ((target (#pin-ref-mut Link))) (#pin-ref-mut Link)
            (#let view (#pin-ref #u64)
              (#unsafe (#pin-get-payload-unchecked (#pin-borrow (#get target value)) Value.Full)))
            (#pin-set-field target view view) (#return target))
          (#fn tick ((target (#pin-ref-mut Link))) (#pin-ref-mut Link)
            (#if (#variant-is (#pin-borrow (#get target value)) Value.Empty)
              (#block
                (#unsafe (#pin-write (#pin-borrow-mut (#get target value)) (Value.Full 40u64)))
                (#unsafe (#pin-write
                  (#unsafe (#pin-get-payload-unchecked-mut (#pin-borrow-mut (#get target value)) Value.Full)) 42u64))) ())
            (#return target))
          (#fn driver ((outside (#pin-ref #u64))) ()
            (#let-mut link Link (#struct-literal Link ((value (Value.Full 42u64)) (view outside))))
            (#let installed (#pin-ref-mut Link) (#call install ((target (#pin-borrow-mut link)))))
            (#let updated (#pin-ref-mut Link) (#call tick ((target installed))))
            (#pin-set-field updated view outside)
            (#drop updated) (#forget link) (#return ()))";

    #[test]
    fn entry_payload_constraints_survive_reinitializing_the_current_constructor() {
        let source = PAYLOAD_ENTRY_SOURCE;
        for (guard, rejected) in [("Value.Empty", false), ("Value.Full", true)] {
            let source = source.replace("value)) Value.Empty)", &format!("value)) {guard})"));
            let declarations = fixture(&source);
            let plan = call_plan(&declarations, "driver", "tick");
            assert!(plan.aliases[0]
                .projection
                .iter()
                .any(|part| matches!(part, Segment::Payload(..))));
            let checked = plan
                .check_owner_accesses(&declarations, &crate::linearcheck::LinearTypes::default());
            assert_eq!(checked.is_err(), rejected, "{checked:?}\n{source}");
        }
    }

    const STORAGE_ENTRY_SOURCE: &str = "(#enum View () (View.NoView (View.HasView (#pin-ref #u64))))
          (#struct Link () ((value #u64) (view View)))
          (#fn install ((target (#pin-ref-mut Link))) (#pin-ref-mut Link)
            (#let view (#pin-ref #u64) (#pin-borrow (#get target value)))
            (#unsafe (#pin-write (#pin-borrow-mut (#get target view)) (View.HasView view))) (#return target))
          (#fn tick ((target (#pin-ref-mut Link))) (#pin-ref-mut Link)
            (#if (#variant-is (#pin-borrow (#get target view)) View.NoView)
              (#unsafe (#pin-write (#pin-borrow-mut (#get target value)) 99u64)) ())
            (#return target))
          (#fn driver () ()
            (#let-mut link Link (#struct-literal Link ((value 42u64) (view View.NoView))))
            (#let installed (#pin-ref-mut Link) (#call install ((target (#pin-borrow-mut link)))))
            (#let updated (#pin-ref-mut Link) (#call tick ((target installed))))
            (#unsafe (#pin-write (#pin-borrow-mut (#get updated view)) View.NoView))
            (#drop updated) (#forget link) (#return ()))";

    fn with_entry_tick(source: &str, statements: &str) -> String {
        let start = source.find("(#fn tick").unwrap();
        let end = source.find("(#fn driver").unwrap();
        format!(
            "{} (#fn tick ((target (#pin-ref-mut Link))) (#pin-ref-mut Link)
            {statements} (#return target)) {}",
            &source[..start],
            &source[end..]
        )
    }

    #[test]
    fn nested_initialization_excludes_only_impossible_incoming_families() {
        for fresh in [false, true] {
            let child = if fresh {
                "(#let view (#pin-ref #u64)
                  (#unsafe (#pin-get-payload-unchecked (#pin-borrow (#get target value)) Value.Full)))
                 (#pin-set-field target view view)"
            } else {
                ""
            };
            let source = format!(
                "{}
                (#fn rewrite ((target (#pin-ref-mut Link))) ()
                  (#unsafe (#pin-write (#pin-borrow-mut (#get target value)) (Value.Full 99u64)))
                  (#return ()))",
                with_entry_tick(
                    PAYLOAD_ENTRY_SOURCE,
                    &format!(
                        "
                (#assert (#variant-is (#pin-borrow (#get target value)) Value.Empty))
                (#unsafe (#pin-write (#pin-borrow-mut (#get target value)) (Value.Full 40u64)))
                {child} (#call rewrite ((target target)))"
                    )
                )
            );
            let declarations = fixture(&source);
            let checked = call_plan(&declarations, "driver", "tick")
                .check_owner_accesses(&declarations, &crate::linearcheck::LinearTypes::default());
            assert_eq!(checked.is_err(), fresh, "{checked:?}\n{source}");
        }
    }

    #[test]
    fn a_constructor_written_into_an_owner_is_not_its_entry_constructor() {
        let source = with_entry_tick(
            PAYLOAD_ENTRY_SOURCE,
            "
          (#unsafe (#pin-write (#pin-borrow-mut (#get target value)) Value.Empty))
          (#assert (#variant-is (#pin-borrow (#get target value)) Value.Empty))",
        );
        let declarations = fixture(&source);
        let body = &declarations.bodies["tick"];
        let flow = &declarations.flows["tick"];
        let tags = entry_guards(body, flow, &flow.loan_origins(body));
        let field = declarations
            .field_id(&Type::Named("Link".into()), "value")
            .unwrap();
        let empty = declarations
            .variant_id(&Type::Named("Value".into()), "Value.Empty")
            .unwrap();
        let owner = Place {
            root: PlaceRoot::Parameter(BindingId(0)),
            segments: vec![Segment::Field(field)],
        };
        assert!(
            tags.iter().all(|facts| facts.get(&owner) != Some(&empty)),
            "a constructor assigned after entry cannot exclude a retained incoming family"
        );
    }

    #[test]
    fn joining_an_initialized_branch_does_not_guard_a_later_owner_write() {
        let source = with_entry_tick(
            PAYLOAD_ENTRY_SOURCE,
            "
          (#if (#variant-is (#pin-borrow (#get target value)) Value.Empty)
            (#unsafe (#pin-write (#pin-borrow-mut (#get target value)) (Value.Full 40u64))) ())
          (#unsafe (#pin-write (#pin-borrow-mut (#get target value)) (Value.Full 99u64)))",
        );
        let declarations = fixture(&source);
        call_plan(&declarations, "driver", "tick")
            .check_owner_accesses(&declarations, &crate::linearcheck::LinearTypes::default())
            .unwrap_err();
    }

    #[test]
    fn clearing_conditional_pointer_storage_does_not_excuse_its_live_copy() {
        let source = with_entry_tick(
            STORAGE_ENTRY_SOURCE,
            "
          (#let saved (#pin-ref #u64)
            (#deref (#unsafe (#pin-get-payload-unchecked (#pin-borrow (#get target view)) View.HasView))))
          (#unsafe (#pin-write (#pin-borrow-mut (#get target view)) View.NoView))
          (#assert (#variant-is (#pin-borrow (#get target view)) View.NoView))
          (#unsafe (#pin-write (#pin-borrow-mut (#get target value)) 99u64))
          (#let observed #u64 (#deref saved)) (#forget observed) (#drop saved)",
        );
        let declarations = fixture(&source);
        let error = call_plan(&declarations, "driver", "tick")
            .check_owner_accesses(&declarations, &crate::linearcheck::LinearTypes::default())
            .unwrap_err();
        let span = error.span.unwrap();
        assert!(
            &source[span.start..span.end].contains("(#get target value)"),
            "{error:?}"
        );
    }

    #[test]
    fn a_disjoint_same_type_tag_does_not_exclude_the_incoming_pointer() {
        let source = STORAGE_ENTRY_SOURCE
            .replace("(view View))", "(view View : other View))")
            .replace(
                "(view View.NoView)",
                "(view View.NoView : other View.NoView)",
            )
            .replace(
                "(#variant-is (#pin-borrow (#get target view)) View.NoView)",
                "(#variant-is (#pin-borrow (#get target other)) View.NoView)",
            );
        let declarations = fixture(&source);
        call_plan(&declarations, "driver", "tick")
            .check_owner_accesses(&declarations, &crate::linearcheck::LinearTypes::default())
            .unwrap_err();
    }

    #[test]
    fn entry_pointer_storage_tags_constrain_the_incoming_family_not_its_owner() {
        let source = STORAGE_ENTRY_SOURCE;
        for (guard, rejected) in [("View.NoView", false), ("View.HasView", true)] {
            let source = source.replace("view)) View.NoView)", &format!("view)) {guard})"));
            let declarations = fixture(&source);
            let plan = call_plan(&declarations, "driver", "tick");
            assert!(plan.aliases[0]
                .storage
                .iter()
                .any(|part| matches!(part, Segment::Payload(..))));
            assert!(!plan.aliases[0]
                .projection
                .iter()
                .any(|part| matches!(part, Segment::Payload(..))));
            let checked = plan
                .check_owner_accesses(&declarations, &crate::linearcheck::LinearTypes::default());
            assert_eq!(checked.is_err(), rejected, "{checked:?}\n{source}");
        }
    }

    #[test]
    fn entry_payload_aliases_are_correlated_with_checked_physical_tag_guards() {
        let source = "(#enum Value () (Value.Empty (Value.Full #u64)))
          (#struct Link () ((value Value) (view (#pin-ref #u64))))
          (#fn install ((target (#pin-ref-mut Link))) (#pin-ref-mut Link)
            (#let view (#pin-ref #u64)
              (#unsafe (#pin-get-payload-unchecked (#pin-borrow (#get target value)) Value.Full)))
            (#pin-set-field target view view) (#return target))
          (#fn tick ((target (#pin-ref-mut Link))) (#pin-ref-mut Link)
            (#if (#variant-is (#pin-borrow (#get target value)) Value.Empty)
              (#unsafe (#pin-write (#pin-borrow-mut (#get target value)) (Value.Full 99u64))) ())
            (#return target))
          (#fn driver ((outside (#pin-ref #u64))) ()
            (#let-mut link Link (#struct-literal Link ((value (Value.Full 42u64)) (view outside))))
            (#let installed (#pin-ref-mut Link) (#call install ((target (#pin-borrow-mut link)))))
            (#let updated (#pin-ref-mut Link) (#call tick ((target installed))))
            (#pin-set-field updated view outside)
            (#drop updated) (#forget link) (#return ()))";
        for (guard, rejected) in [("Value.Empty", false), ("Value.Full", true)] {
            let source = source.replace("value)) Value.Empty)", &format!("value)) {guard})"));
            let declarations = fixture(&source);
            let plan = call_plan(&declarations, "driver", "tick");
            assert_eq!(plan.aliases.len(), 1);
            let checked = plan
                .check_owner_accesses(&declarations, &crate::linearcheck::LinearTypes::default());
            assert_eq!(checked.is_err(), rejected, "{checked:?}\n{source}");
        }
        // A write invalidating the guard must be checked before it can
        // establish an incompatible tag; subsequent facts cannot excuse it.
        let bad = source.replace(
            "(#if (#variant-is",
            "(#unsafe (#pin-write (#pin-borrow-mut (#get target value)) Value.Empty)) (#if (#variant-is",
        );
        let declarations = fixture(&bad);
        call_plan(&declarations, "driver", "tick")
            .check_owner_accesses(&declarations, &crate::linearcheck::LinearTypes::default())
            .unwrap_err();
    }

    #[test]
    fn checked_empty_pointer_slots_retire_only_their_stored_entry_alias() {
        let source = "(#enum View () (View.Empty (View.Full (#pin-ref-mut #u64))))
          (#struct Link () ((value #u64) (view View)))
          (#fn install ((target (#pin-ref-mut Link))) (#pin-ref-mut Link)
            (#let view (#pin-ref-mut #u64) (#pin-borrow-mut (#get target value)))
            (#unsafe (#pin-write (#pin-borrow-mut (#get target view)) (View.Full view))) (#return target))
          (#fn tick ((target (#pin-ref-mut Link))) (#pin-ref-mut Link)
            GUARD
            (#let fresh (#pin-ref-mut #u64) (#pin-borrow-mut (#get target value)))
            (#drop fresh) (#return target))
          (#fn driver () ()
            (#let-mut link Link (#struct-literal Link ((value 42u64) (view View.Empty))))
            (#let installed (#pin-ref-mut Link) (#call install ((target (#pin-borrow-mut link)))))
            (#let updated (#pin-ref-mut Link) (#call tick ((target installed))))
            (#drop updated) (#forget link) (#return ()))";
        for (guard, rejected) in [
            (
                "(#assert (#variant-is (#pin-borrow (#get target view)) View.Empty))",
                false,
            ),
            (
                "(#assert (#variant-is (#pin-borrow (#get target view)) View.Full))",
                true,
            ),
            ("", true),
        ] {
            let declarations = fixture(&source.replace("GUARD", guard));
            let plan = call_plan(&declarations, "driver", "tick");
            assert_eq!(plan.aliases.len(), 1);
            let checked = plan
                .check_owner_accesses(&declarations, &crate::linearcheck::LinearTypes::default());
            assert_eq!(checked.is_err(), rejected, "{checked:?}\n{guard}");
        }
    }

    #[test]
    fn initializer_entry_guards_survive_destructive_reads_but_are_not_invented_after_writes() {
        for early in [true, false] {
            let assertion = "(#assert (#variant-is slot Slot.Empty))";
            let (before, after) = if early {
                (assertion, "")
            } else {
                ("", assertion)
            };
            let source = format!(
                "(#enum Slot (#linear) (Slot.Empty (Slot.Full #u64)))
              (#fn initialize ((slot (#pin-ref-mut Slot))) ()
                {before}
                (#let previous Slot (#unsafe (#pin-read slot))) (#forget previous)
                (#unsafe (#pin-write slot Slot.Empty))
                {after}
                (#unsafe (#pin-write slot (Slot.Full 42u64))) (#return ()))"
            );
            let declarations = fixture(&source);
            let function = declarations.function_id("initialize").unwrap();
            let effects = guarded_writes(
                function,
                &declarations,
                &crate::linearcheck::LinearTypes::default(),
                &mut Cache::default(),
                &mut HashSet::new(),
            )
            .unwrap();
            let empty = declarations
                .variant_id(&Type::Named("Slot".into()), "Slot.Empty")
                .unwrap();
            assert!(!effects.is_empty());
            for effect in effects {
                assert_eq!(
                    effect.guards.iter().any(|(_, variant)| *variant == empty),
                    early,
                    "a tag created by the initializer is not its entry tag"
                );
            }
        }
    }

    #[test]
    fn user_assert_calls_and_ambiguous_guard_receivers_do_not_establish_entry_tags() {
        for assertion in [
            "(#call assert ((condition (#variant-is first Slot.Empty))))",
            "(#assert (#variant-is (#if choose first second) Slot.Empty))",
        ] {
            let source = format!("(#enum Slot (#linear) (Slot.Empty (Slot.Full #u64)))
              (#fn assert ((condition #bool)) () (#return ()))
              (#fn initialize ((first (#pin-ref-mut Slot)) (second (#pin-ref-mut Slot)) (choose #bool)) ()
                {assertion}
                (#let previous Slot (#unsafe (#pin-read first))) (#forget previous)
                (#unsafe (#pin-write first (Slot.Full 42u64))) (#return ()))");
            let declarations = fixture(&source);
            let effects = guarded_writes(
                declarations.function_id("initialize").unwrap(),
                &declarations,
                &crate::linearcheck::LinearTypes::default(),
                &mut Cache::default(),
                &mut HashSet::new(),
            )
            .unwrap();
            assert!(!effects.is_empty());
            assert!(effects.iter().all(|effect| effect.guards.is_empty()));
        }
    }

    #[test]
    fn repeated_nested_calls_keep_one_distinct_write_footprint() {
        let mut source = String::from(
            "(#fn level0 ((target (#pin-ref-mut #u64))) ()
          (#unsafe (#pin-write target 42u64)) (#return ()))",
        );
        for level in 1..=20 {
            source.push_str(&format!(
                "(#fn level{level} ((target (#pin-ref-mut #u64))) ()
              (#call level{} ((target target)))
              (#call level{} ((target target))) (#return ()))",
                level - 1,
                level - 1
            ));
        }
        let declarations = fixture(&source);
        let mut cache = Cache::default();
        let effects = guarded_writes(
            declarations.function_id("level20").unwrap(),
            &declarations,
            &crate::linearcheck::LinearTypes::default(),
            &mut cache,
            &mut HashSet::new(),
        )
        .unwrap();
        assert_eq!(effects.len(), 1);
        assert_eq!(cache.writes.len(), 21);
        assert!(cache.writes.values().all(|writes| writes.len() == 1));
    }

    #[test]
    fn global_consumption_identities_do_not_substitute_an_unused_parameter() {
        let source = format!(
            "(#static count #u64 0u64)
          (#fn touch () () (#unsafe (#forget count)) (#return ())) {}",
            SOURCE.replace(
                "(#pin-set-field target state 2u32)",
                "(#call touch ()) (#pin-set-field target state 2u32)"
            )
        );
        let declarations = fixture(&source);
        let effects = guarded_writes(
            declarations.function_id("tick").unwrap(),
            &declarations,
            &crate::linearcheck::LinearTypes::default(),
            &mut Cache::default(),
            &mut HashSet::new(),
        )
        .unwrap();
        assert!(effects
            .iter()
            .any(|effect| effect.target.global == declarations.global_id("count")));
        call_plan(&declarations, "driver", "tick")
            .check_owner_accesses(&declarations, &crate::linearcheck::LinearTypes::default())
            .unwrap();
    }

    #[test]
    fn definite_clear_retires_entry_alias_but_conditional_clear_does_not() {
        for conditional in [false, true] {
            let clear = if conditional {
                "(#if (#u32::eq (#get target state) 0u32) (#pin-set-field target view outside) ())"
            } else {
                "(#pin-set-field target view outside)"
            };
            let source = SOURCE
                .replace(
                    "(#fn tick ((target (#pin-ref-mut Link)))",
                    "(#fn tick ((target (#pin-ref-mut Link)) (outside (#pin-ref #u64)))",
                )
                .replace(
                    "(#call tick ((target running)))",
                    "(#call tick ((target running) (outside outside)))",
                )
                .replace(
                    "(#pin-set-field target state 2u32)",
                    &format!("{clear} (#pin-set-field target value 99u64)"),
                );
            let declarations = fixture(&source);
            let result = call_plan(&declarations, "driver", "tick")
                .check_owner_accesses(&declarations, &crate::linearcheck::LinearTypes::default());
            assert_eq!(result.is_err(), conditional, "{result:?}\n{source}");
        }
    }

    #[test]
    fn staged_check_locates_destructive_calls_with_temporary_parent_origins() {
        let source = SOURCE.replace(
            "(#let-mut running (#pin-ref-mut Link) (#pin-borrow-mut link))\n        (#let installed (#pin-ref-mut Link) (#call install ((target running))))\n        (#set running installed)\n        (#let updated (#pin-ref-mut Link) (#call tick ((target running))))\n        (#set running updated)\n        (#pin-set-field running view outside)\n        (#drop running)",
            "(#let running (#pin-ref-mut Link) (#call install ((target (#pin-borrow-mut link)))))\n        (#let updated (#pin-ref-mut Link) (#call tick ((target running))))\n        (#pin-set-field updated view outside) (#drop updated)",
        );
        let program = crate::parse_program(&source).unwrap();
        crate::CheckedProgram::validate(&program)
            .unwrap_or_else(|error| panic!("{error}\n{source}"));
        let invalid = source.replace(
            "(#pin-set-field target state 2u32)",
            "(#pin-set-field target value 99u64)",
        );
        let declarations = fixture(&invalid);
        let body = &declarations.bodies["driver"];
        let flow = &declarations.flows["driver"];
        let error = check_calls(
            body,
            flow,
            &declarations,
            &crate::linearcheck::LinearTypes::default(),
            &std::cell::OnceCell::new(),
        )
        .unwrap_err();
        assert!(
            error.message.contains("stored internal reference"),
            "{}",
            error.message
        );
        let span = error.span.unwrap();
        assert_eq!(&invalid[span.start..span.end], "running");
        assert!(error.labels.iter().any(
            |(span, _)| &invalid[span.start..span.end] == "(#pin-set-field target value 99u64)"
        ));
    }

    #[test]
    fn aliases_are_substituted_into_nested_callee_checks() {
        let source = format!("{SOURCE}").replace(
            "(#pin-set-field target state 2u32) (#return target)",
            "(#return (#call smash ((owner target))))",
        ) + "\n(#fn smash ((owner (#pin-ref-mut Link))) (#pin-ref-mut Link)
          (#pin-set-field owner value 99u64) (#return owner))";
        let declarations = fixture(&source);
        let result = call_plan(&declarations, "driver", "tick")
            .check_owner_accesses(&declarations, &crate::linearcheck::LinearTypes::default());
        let error = result.unwrap_err();
        let span = error.span.unwrap();
        assert_eq!(
            &source[span.start..span.end],
            "(#call smash ((owner target)))"
        );
    }

    #[test]
    fn nested_tuple_projection_is_physical_not_child_pointer_storage() {
        let source = SOURCE
            .replace("(value #u64)", "(value (#tuple #u64 #u64))")
            .replace(
                "(#pin-borrow (#get target value))",
                "(#pin-borrow (#get (#get target value) 1))",
            )
            .replace(
                "(value 42u64)",
                "(value (#tuple (#tuple #u64 #u64) 1u64 42u64))",
            );
        let declarations = fixture(&source);
        let plan = call_plan(&declarations, "driver", "tick");
        assert_eq!(plan.aliases.len(), 1);
        assert_eq!(plan.aliases[0].projection.last(), Some(&Segment::Tuple(1)));
        plan.check_owner_accesses(&declarations, &crate::linearcheck::LinearTypes::default())
            .unwrap();
        let invalid = source.replace("(#pin-set-field target state 2u32)",
            "(#unsafe (#pin-write (#pin-borrow-mut (#get target value)) (#tuple (#tuple #u64 #u64) 99u64 100u64)))");
        let declarations = fixture(&invalid);
        assert!(call_plan(&declarations, "driver", "tick")
            .check_owner_accesses(&declarations, &crate::linearcheck::LinearTypes::default())
            .is_err());
    }

    #[test]
    fn retained_exclusive_child_permits_its_own_write_not_an_owner_write() {
        let source = SOURCE
            .replace("#pin-ref #u64", "#pin-ref-mut #u64")
            .replace(
                "(#pin-borrow (#get target value))",
                "(#pin-borrow-mut (#get target value))",
            )
            .replace(
                "(#pin-set-field target view view)",
                "(#unsafe (#pin-write (#pin-borrow-mut (#get target view)) view))",
            )
            .replace(
                "(#pin-set-field running view outside)",
                "(#unsafe (#pin-write (#pin-borrow-mut (#get running view)) outside))",
            )
            .replace(
                "(#pin-set-field target state 2u32)",
                "(#unsafe (#pin-write (#get target view) 9u64))",
            );
        let declarations = fixture(&source);
        let plan = call_plan(&declarations, "driver", "tick");
        assert_eq!(plan.aliases.len(), 1);
        assert!(plan.aliases[0].mutable);
        plan.check_owner_accesses(&declarations, &crate::linearcheck::LinearTypes::default())
            .unwrap();
        let invalid = source.replace(
            "(#unsafe (#pin-write (#get target view) 9u64))",
            "(#pin-set-field target value 99u64)",
        );
        let declarations = fixture(&invalid);
        assert!(call_plan(&declarations, "driver", "tick")
            .check_owner_accesses(&declarations, &crate::linearcheck::LinearTypes::default())
            .is_err());
    }

    #[test]
    fn clearing_the_field_does_not_retire_a_live_local_child_copy() {
        for read_after_write in [false, true] {
            let operation = if read_after_write {
                "(#let saved (#pin-ref #u64) (#get target view))
                 (#pin-set-field target view outside) (#pin-set-field target value 99u64)
                 (#let observed #u64 (#deref saved)) (#forget observed)"
            } else {
                "(#let saved (#pin-ref #u64) (#get target view))
                 (#let observed #u64 (#deref saved)) (#forget observed)
                 (#pin-set-field target view outside) (#pin-set-field target value 99u64)"
            };
            let source = SOURCE
                .replace(
                    "(#fn tick ((target (#pin-ref-mut Link)))",
                    "(#fn tick ((target (#pin-ref-mut Link)) (outside (#pin-ref #u64)))",
                )
                .replace(
                    "(#call tick ((target running)))",
                    "(#call tick ((target running) (outside outside)))",
                )
                .replace("(#pin-set-field target state 2u32)", operation);
            let declarations = fixture(&source);
            let result = call_plan(&declarations, "driver", "tick")
                .check_owner_accesses(&declarations, &crate::linearcheck::LinearTypes::default());
            assert_eq!(result.is_err(), read_after_write, "{result:?}\n{source}");
        }
    }

    #[test]
    fn fresh_same_address_borrows_do_not_resurrect_retired_entry_loans() {
        for keep_copy in [false, true] {
            let save = if keep_copy {
                "(#let saved (#pin-ref #u64) (#get target view))"
            } else {
                ""
            };
            let use_copy = if keep_copy {
                "(#let observed #u64 (#deref saved)) (#forget observed)"
            } else {
                ""
            };
            let operation = format!(
                "{save}
              (#pin-set-field target view outside)
              (#let fresh (#pin-ref #u64) (#pin-borrow (#get target value)))
              (#pin-set-field target view fresh)
              (#pin-set-field target state 2u32) {use_copy}"
            );
            let source = SOURCE
                .replace(
                    "(#fn tick ((target (#pin-ref-mut Link)))",
                    "(#fn tick ((target (#pin-ref-mut Link)) (outside (#pin-ref #u64)))",
                )
                .replace(
                    "(#call tick ((target running)))",
                    "(#call tick ((target running) (outside outside)))",
                )
                .replace("(#pin-set-field target state 2u32)", &operation);
            let declarations = fixture(&source);
            let plan = call_plan(&declarations, "driver", "tick");
            let body = &declarations.bodies["tick"];
            let flow = &declarations.flows["tick"];
            let origins = flow.loan_origins_with_entry_aliases(body, &plan.aliases);
            let state_field = declarations
                .field_id(&Type::Named("Link".into()), "state")
                .unwrap();
            let event = flow.nodes.iter().enumerate().find_map(|(index, node)| {
                let value = match node.action {
                    FlowAction::Evaluate(value) | FlowAction::Write { value, .. } => value,
                    _ => return None,
                };
                let NodeKind::Form { head, children, callee: None, .. } = &body.nodes[value.0].kind else { return None; };
                (head == "pin-set-field" && matches!(body.nodes[children[2].0].kind,
                    NodeKind::Declaration(crate::typed_ir::DeclarationId::Field(field)) if field == state_field))
                    .then_some(FlowNodeId(index))
            }).unwrap();
            let live = flow
                .liveness(body)
                .before(event)
                .into_iter()
                .filter(|binding| binding.0 >= body.parameter_count)
                .collect::<Vec<_>>();
            assert_eq!(
                origins.entry_alias_retained_before(event, 0, &plan.aliases[0], &live, None),
                keep_copy
            );
            let actual =
                origins.pointee_before(body, event, &origins.before(event, BindingId(0))[0]);
            assert!(actual.iter().any(|origin| origin.place.root == PlaceRoot::Parameter(BindingId(0))
                && origin.place.segments == plan.aliases[0].projection && origin.entry_loan.is_none()),
                "the fresh same-address child exists independently of the incoming family: {actual:?}");
            assert!(!actual.iter().any(|origin| origin.entry_loan == Some(0)),
                "replacing the child field retires that stored copy, even when a separate local copy remains");
        }
    }

    #[test]
    fn projected_child_reborrows_retain_the_incoming_family() {
        let source = SOURCE
            .replace("(value #u64)", "(value (#tuple #u64 #u64))")
            .replace(
                "(value 42u64)",
                "(value (#tuple (#tuple #u64 #u64) 40u64 2u64))",
            )
            .replace("#pin-ref #u64", "#pin-ref (#tuple #u64 #u64)")
            .replace(
                "(#fn tick ((target (#pin-ref-mut Link)))",
                "(#fn tick ((target (#pin-ref-mut Link)) (outside (#pin-ref (#tuple #u64 #u64))))",
            )
            .replace(
                "(#call tick ((target running)))",
                "(#call tick ((target running) (outside outside)))",
            )
            .replace(
                "(#pin-set-field target state 2u32)",
                "(#let child (#pin-ref #u64) (#pin-borrow (#get (#get target view) 1)))
                 (#pin-set-field target view outside)
                 (#unsafe (#pin-write (#pin-borrow-mut (#get target value)) (#tuple (#tuple #u64 #u64) 99u64 100u64)))
                 (#let observed #u64 (#deref child)) (#forget observed)",
            );
        let declarations = fixture(&source);
        let error = call_plan(&declarations, "driver", "tick")
            .check_owner_accesses(&declarations, &crate::linearcheck::LinearTypes::default())
            .unwrap_err();
        let span = error.span.unwrap();
        assert_eq!(&source[span.start..span.end], "(#pin-write (#pin-borrow-mut (#get target value)) (#tuple (#tuple #u64 #u64) 99u64 100u64))");
    }

    #[test]
    fn separate_incoming_families_at_one_address_retire_independently() {
        let source = SOURCE
            .replace(
                "(view (#pin-ref #u64))))",
                "(view (#pin-ref #u64) : second (#pin-ref #u64))))",
            )
            .replace("(view outside)", "(view outside : second outside)")
            .replace(
                "(#pin-set-field target view view)",
                "(#pin-set-field target view view) (#pin-set-field target second view)",
            )
            .replace(
                "(#fn tick ((target (#pin-ref-mut Link)))",
                "(#fn tick ((target (#pin-ref-mut Link)) (outside (#pin-ref #u64)))",
            )
            .replace(
                "(#call tick ((target running)))",
                "(#call tick ((target running) (outside outside)))",
            )
            .replace(
                "(#pin-set-field target state 2u32)",
                "(#pin-set-field target view outside) (#pin-set-field target state 2u32)",
            );
        let declarations = fixture(&source);
        let plan = call_plan(&declarations, "driver", "tick");
        assert_eq!(plan.aliases.len(), 2);
        assert_eq!(plan.aliases[0].projection, plan.aliases[1].projection);
        let body = &declarations.bodies["tick"];
        let flow = &declarations.flows["tick"];
        let origins = flow.loan_origins_with_entry_aliases(body, &plan.aliases);
        let field = |name| {
            declarations
                .field_id(&Type::Named("Link".into()), name)
                .unwrap()
        };
        let event = flow
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| match &node.action {
                FlowAction::Write { place, .. }
                    if place.segments.last() == Some(&Segment::Field(field("state"))) =>
                {
                    Some(FlowNodeId(index))
                }
                _ => None,
            })
            .unwrap();
        for (family, alias) in plan.aliases.iter().enumerate() {
            assert_eq!(
                origins.entry_alias_retained_before(event, family, alias, &[], None),
                alias.storage.last() == Some(&Segment::Field(field("second")))
            );
        }
    }

    #[test]
    fn projected_borrows_keep_the_receiver_evaluated_before_index_effects() {
        let source = SOURCE
            .replace("(value #u64)", "(value (#array #u64 2))")
            .replace(
                "(value 42u64)",
                "(value (#array-of (#array #u64 2) 40u64 42u64))",
            )
            .replace("#pin-ref #u64", "#pin-ref (#array #u64 2)")
            .replace(
                "(#fn tick ((target (#pin-ref-mut Link)))",
                "(#fn tick ((target (#pin-ref-mut Link)) (outside (#pin-ref (#array #u64 2))))",
            )
            .replace(
                "(#call tick ((target running)))",
                "(#call tick ((target running) (outside outside)))",
            )
            .replace(
                "(#pin-set-field target state 2u32)",
                "(#let child (#pin-ref #u64) (#pin-borrow (#index (#get target view)
                   (#block (#pin-set-field target view outside) 1usize))))
                 (#unsafe (#pin-write (#pin-borrow-mut (#get target value))
                   (#array-of (#array #u64 2) 99u64 100u64)))
                 (#let observed #u64 (#deref child)) (#forget observed)",
            );
        let declarations = fixture(&source);
        let error = call_plan(&declarations, "driver", "tick")
            .check_owner_accesses(&declarations, &crate::linearcheck::LinearTypes::default())
            .unwrap_err();
        let span = error.span.unwrap();
        assert_eq!(&source[span.start..span.end],
            "(#pin-write (#pin-borrow-mut (#get target value))\n                   (#array-of (#array #u64 2) 99u64 100u64))");
    }

    #[test]
    fn run_local_cache_keeps_distinct_alias_contexts_separate() {
        let source = SOURCE
            .replace("(state #u32)", "(state #u64)")
            .replace("(state 0u32)", "(state 0u64)")
            .replace("state 2u32", "state 2u64");
        let declarations = fixture(&source);
        let plan = call_plan(&declarations, "driver", "tick");
        let types = crate::linearcheck::LinearTypes::default();
        let mut cache = Cache::default();
        for _ in 0..2 {
            plan.check_owner_accesses_inner(
                &declarations,
                &types,
                &mut Vec::new(),
                &mut cache,
                true,
            )
            .unwrap();
        }
        assert_eq!(cache.checked.len(), 1);
        assert_eq!(cache.baseline.len(), 1);
        assert_eq!(cache.entry_tags.len(), 1);
        let entry = cache.entry_tags[&plan.callee].clone();
        guarded_writes(
            plan.callee,
            &declarations,
            &types,
            &mut cache,
            &mut HashSet::new(),
        )
        .unwrap();
        guarded_observations(
            plan.callee,
            &declarations,
            &types,
            &mut cache,
            &mut HashSet::new(),
        )
        .unwrap();
        assert!(std::rc::Rc::ptr_eq(&entry, &cache.entry_tags[&plan.callee]));
        let mut other = plan.clone();
        other.aliases[0].projection = vec![Segment::Field(
            declarations
                .field_id(&Type::Named("Link".into()), "state")
                .unwrap(),
        )];
        other.aliases[0]
            .validate(&declarations.bodies["tick"].bindings[0].ty, &declarations)
            .unwrap();
        assert!(other
            .check_owner_accesses_inner(&declarations, &types, &mut Vec::new(), &mut cache, true)
            .is_err());
        assert!(!cache.checked.contains(&(other, true)));
        // A different set of declarations never inherits a checked context.
        assert!(Cache::default().checked.is_empty());
    }

    #[test]
    fn reordered_arguments_locate_the_owner_actually_accessed_by_the_callee() {
        let source = SOURCE.replace("(#fn tick ((target (#pin-ref-mut Link)))",
            "(#fn tick ((first (#pin-ref-mut Link)) (target (#pin-ref-mut Link)))")
            .replace("(#pin-set-field target state 2u32)", "(#pin-set-field target value 99u64)")
            .replace("(#let updated (#pin-ref-mut Link) (#call tick ((target running))))",
                "(#let-mut another Link (#struct-literal Link ((value 7u64) (state 0u32) (view outside))))
                 (#let second (#pin-ref-mut Link) (#call install ((target (#pin-borrow-mut another)))))
                 (#let updated (#pin-ref-mut Link) (#call tick ((target second) (first running))))");
        let declarations = fixture(&source);
        let body = &declarations.bodies["driver"];
        let flow = &declarations.flows["driver"];
        let error = check_calls(
            body,
            flow,
            &declarations,
            &crate::linearcheck::LinearTypes::default(),
            &std::cell::OnceCell::new(),
        )
        .unwrap_err();
        let span = error.span.unwrap();
        assert_eq!(&source[span.start..span.end], "second");
    }

    #[test]
    fn conditional_fresh_borrow_does_not_hide_a_retained_sibling_alias() {
        let source = "(#struct Link () ((value #u64) (view (#pin-ref-mut #u64))))
          (#fn install ((target (#pin-ref-mut Link))) (#pin-ref-mut Link)
            (#let view (#pin-ref-mut #u64) (#pin-borrow-mut (#get target value)))
            (#unsafe (#pin-write (#pin-borrow-mut (#get target view)) view)) (#return target))
          (#fn observe ((target (#pin-ref-mut Link)) (choose #bool)) ()
            (#let sibling (#pin-ref-mut #u64) (#get target view))
            (#if choose
              (#block
                (#let fresh (#pin-ref-mut #u64) (#pin-borrow-mut (#get target value)))
                (#drop fresh) ()) ())
            (#drop sibling)
            (#return ()))
          (#fn driver ((outside (#pin-ref-mut #u64))) ()
            (#let-mut link Link (#struct-literal Link ((value 42u64) (view outside))))
            (#let installed (#pin-ref-mut Link) (#call install ((target (#pin-borrow-mut link)))))
            (#call observe ((target installed) (choose true)))
            (#unsafe (#pin-write (#pin-borrow-mut (#get installed view)) outside))
            (#drop installed) (#forget link) (#return ()))";
        let declarations = fixture(source);
        let plan = call_plan(&declarations, "driver", "observe");
        assert_eq!(plan.aliases.len(), 1, "{:#?}", plan.aliases);
        let error = plan
            .check_owner_accesses(&declarations, &crate::linearcheck::LinearTypes::default())
            .expect_err("a conditional fresh borrow must still conflict with its retained sibling");
        assert!(
            error.message.contains("stored conflicting reference"),
            "{error:?}"
        );
    }

    #[test]
    fn observation_alternatives_keep_equal_address_entry_siblings() {
        let origin = |entry_loan, parameter_storage| LoanOrigin {
            owned_allocation: false,
            place: Place {
                root: PlaceRoot::Parameter(BindingId(0)),
                segments: Vec::new(),
            },
            mutable: false,
            pinned: true,
            lifetime_only: false,
            maybe_absent: false,
            word_stored: false,
            word_view_address: false,
            span: None,
            borrowed_from: None,
            reborrow_slot: None,
            call_reborrow: false,
            entry_loan: Some(entry_loan),
            storage: Vec::new(),
            parameter_storage,
            storage_inputs: Vec::new(),
        };
        let alternatives = observation_alternatives(vec![
            origin(0, Some(Vec::new())),
            origin(1, Some(Vec::new())),
        ]);
        assert_eq!(alternatives.len(), 2);
        assert_eq!(alternatives[0].entry_loan, Some(0));
        assert_eq!(alternatives[1].entry_loan, Some(1));
    }

    #[test]
    fn observation_alternatives_drop_only_matching_fresh_provenance() {
        let origin = |entry_loan| LoanOrigin {
            owned_allocation: false,
            place: Place {
                root: PlaceRoot::Parameter(BindingId(0)),
                segments: Vec::new(),
            },
            mutable: true,
            pinned: true,
            lifetime_only: false,
            maybe_absent: false,
            word_stored: false,
            word_view_address: false,
            span: None,
            borrowed_from: None,
            reborrow_slot: None,
            call_reborrow: false,
            entry_loan,
            storage: Vec::new(),
            parameter_storage: Some(Vec::new()),
            storage_inputs: Vec::new(),
        };
        let alternatives =
            observation_alternatives(vec![origin(None), origin(Some(0)), origin(Some(1))]);
        assert_eq!(alternatives.len(), 2);
        assert_eq!(alternatives[0].entry_loan, Some(0));
        assert_eq!(alternatives[1].entry_loan, Some(1));
    }

    #[test]
    fn observation_alternatives_keep_entry_aliases_from_distinct_input_slots() {
        let origin = |entry_loan, slot| LoanOrigin {
            owned_allocation: false,
            place: Place {
                root: PlaceRoot::Parameter(BindingId(0)),
                segments: Vec::new(),
            },
            mutable: false,
            pinned: true,
            lifetime_only: false,
            maybe_absent: false,
            word_stored: false,
            word_view_address: false,
            span: None,
            borrowed_from: None,
            reborrow_slot: None,
            call_reborrow: false,
            entry_loan: Some(entry_loan),
            storage: vec![Segment::Tuple(slot)],
            parameter_storage: Some(vec![Segment::Tuple(slot)]),
            storage_inputs: vec![Some(slot)],
        };
        let alternatives = observation_alternatives(vec![origin(0, 0), origin(1, 1)]);
        assert_eq!(alternatives.len(), 2);
        assert_eq!(
            alternatives[0].parameter_storage,
            Some(vec![Segment::Tuple(0)])
        );
        assert_eq!(
            alternatives[1].parameter_storage,
            Some(vec![Segment::Tuple(1)])
        );
    }
}
