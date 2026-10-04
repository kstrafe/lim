//! Actual caller relationships for references stored inside a borrowed owner.
//!
//! A parameter's pointer-slot name is not its physical referent. Preserve the
//! storage slot and the owner-relative pointee separately before attempting a
//! context-sensitive callee check. This plan grants no borrow permission and
//! does not replace ordinary checking or initialization/retirement contracts.
//! Ordinary validation uses this as an additional rejection gate. Entry-tag
//! guards distinguish conditional initialization from overwriting a retained
//! pointee. Owner reads, clones, and reborrows are also compared with the
//! incoming child's capability, including nested ordinary calls. These checks
//! do not authorize parent reborrows; complete state-dependent permissions
//! and external child relationships remain separate obligations.

use crate::typed_body::{BindingId, Body, NodeId, NodeKind, PlaceRoot};
use crate::typed_flow::{FlowAction, FlowGraph, FlowLoanOrigins, FlowNodeId, LoanOrigin};
use crate::typed_ir::{resolve_type, Declarations, FunctionId};
use crate::typed_place::{Place, Segment};
use crate::Type;
use std::collections::{HashMap, HashSet};

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
    // Write-only staging must not cache permission for observation checks.
    checked: HashSet<(Plan, bool)>,
    writes: HashMap<FunctionId, Vec<GuardedWrite>>,
    observations: HashMap<FunctionId, Vec<GuardedObservation>>,
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
                "borrow" | "borrow-mut" | "pin-borrow" | "pin-borrow-mut"
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
    targets
        .into_iter()
        .filter(|target| {
            !target.lifetime_only && !target.owned_allocation && target.storage.is_empty()
        })
        .map(|target| (target, exclusive))
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
    let entry = entry_guards(body, flow, &origins);
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
        referent_projection: projection,
        input_storage: input.unwrap_or_default(),
        storage: vec![],
        storage_inputs: vec![],
    })
}

/// Facts about entry tags, not the tags after an initializer has overwritten
/// them. Once established before any possible mutation, an entry fact remains
/// a path constraint even after a destructive read clears current tag facts.
fn entry_guards(
    body: &Body,
    flow: &FlowGraph,
    origins: &FlowLoanOrigins,
) -> Vec<HashMap<Place, crate::typed_ir::VariantId>> {
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
    let entry = entry_guards(body, flow, &baseline);
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
    check_calls_cached(body, flow, declarations, types, cache, &mut checked)
}

pub(crate) fn check_calls_cached(
    body: &Body,
    flow: &FlowGraph,
    declarations: &Declarations,
    types: &crate::linearcheck::LinearTypes,
    cache: &std::cell::OnceCell<FlowLoanOrigins>,
    checked: &mut Cache,
) -> Result<(), crate::typed_borrow::BorrowConflict> {
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
        let plan =
            Plan::for_call(body, flow, event, value, origins, declarations).map_err(|message| {
                crate::typed_borrow::BorrowConflict {
                    message,
                    span: node.span,
                    labels: vec![],
                }
            })?;
        // The extra rejection gate does not replace the authoritative direct
        // loan checks. Exclusive pointers in conditional payload storage still
        // need path-correlated incoming/fresh families before this specialized
        // context can be used: unioning their resume and initial-entry paths
        // incorrectly treats a write through a newly installed child as an
        // access through its parent. Keep those contexts staged, without
        // granting any additional reborrow permission.
        if plan.aliases.iter().any(|alias| {
            alias.mutable
                && (alias
                    .storage
                    .iter()
                    .any(|slot| matches!(slot, Segment::Payload(..)))
                    || alias
                        .projection
                        .iter()
                        .any(|slot| matches!(slot, Segment::Payload(..))))
        }) {
            continue;
        }
        // Observation permissions for conditional shared payloads are staged
        // too: constructing an initializer's argument happens before its
        // checked Empty guard. Keep existing guarded write rejection, but do
        // not apply resume-only observation contexts to the initial path.
        let check_observations = !plan.aliases.iter().any(|alias| {
            alias
                .storage
                .iter()
                .chain(&alias.projection)
                .any(|slot| matches!(slot, Segment::Payload(..)))
        });
        if let Err((parameter, mut error)) = plan.check_owner_accesses_inner(
            declarations,
            types,
            &mut Vec::new(),
            checked,
            check_observations,
        ) {
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
    }
    Ok(())
}

fn static_path(path: &[Segment]) -> bool {
    path.iter().all(|segment| {
        matches!(
            segment,
            Segment::Field(_) | Segment::Tuple(_) | Segment::Payload(_, _) | Segment::Index(_)
        )
    })
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
                Type::Reference { target, .. } | Type::PinnedReference { target, .. },
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
            _ => return Err("incoming self-loan needs a checked static storage path".into()),
        };
    }
    resolve_type(&ty, &declarations.aliases)
}

impl Alias {
    pub fn validate(
        &self,
        parameter_type: &Type,
        declarations: &Declarations,
    ) -> Result<(), String> {
        let mut prefix = self.owner_input.clone();
        prefix.push(Segment::Dereference);
        if !static_path(&self.owner_input)
            || !self.storage.starts_with(&prefix)
            || !static_path(&self.storage[prefix.len()..])
        {
            return Err("incoming self-loan storage is not inside its owner pointee".into());
        }
        let owner = project(parameter_type.clone(), &self.owner_input, declarations)?;
        let (Type::Reference { target, .. } | Type::PinnedReference { target, .. }) = owner else {
            return Err("incoming self-loan owner is not a reference slot".into());
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
                    || !static_path(&parent.storage)
                    || !static_path(&parent.place.segments)
                {
                    continue;
                }
                let pointer = project(ty.clone(), &parent.storage, declarations)?;
                if !matches!(
                    pointer,
                    Type::Reference { .. } | Type::PinnedReference { .. }
                ) {
                    continue;
                }
                for child in origins.pointee_before(body, event, &parent) {
                    if child.lifetime_only
                        || !same_pointer_root(&parent, &child)
                        || !child.place.segments.starts_with(&parent.place.segments)
                        || !static_path(&child.storage)
                    {
                        continue;
                    }
                    let mut storage = parent.storage.clone();
                    storage.push(Segment::Dereference);
                    storage.extend_from_slice(&child.storage);
                    let alias = Alias {
                        parameter: BindingId(parameter),
                        storage,
                        owner_input: parent.storage.clone(),
                        projection: child.place.segments[parent.place.segments.len()..].to_vec(),
                        mutable: child.mutable,
                        pinned: child.pinned,
                    };
                    alias.validate(ty, declarations)?;
                    if !aliases.contains(&alias) {
                        aliases.push(alias);
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
        let consumptions = flow.consumptions(body, types);
        let live = flow.liveness(body);
        for (index, node) in flow.nodes.iter().enumerate() {
            let event = FlowNodeId(index);
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
            // Baseline pointer-slot identity identifies accesses through the
            // owner, as opposed to legitimate writes through its child handle.
            // The specialized solver supplies the child's actual lifetime.
            let mut writes = baseline
                .stores_before(body, flow, event)
                .into_iter()
                .map(|store| store.destination)
                .collect::<Vec<_>>();
            let mut guarded = Vec::new();
            let mut observations = if check_observations {
                observations_at(body, flow, &baseline, event, &consumptions)
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
                        let targets =
                            map_write_input(body, flow, &baseline, event, children, &effect.target);
                        let mut guards = Vec::new();
                        for (guard, variant) in effect.guards {
                            let mapped =
                                map_write_input(body, flow, &baseline, event, children, &guard);
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
                                map_write_input(body, flow, &baseline, event, children, &guard);
                            if mapped.len() == 1 && !mapped[0].lifetime_only {
                                guards.push((mapped[0].clone(), variant));
                            }
                        }
                        observations.extend(
                            map_write_input(body, flow, &baseline, event, children, &effect.target)
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
                        writes.extend(baseline.projected_origins(event, binding, &place.segments));
                    }
                }
                FlowAction::Release { place, .. } => {
                    if let PlaceRoot::Local(binding) = place.root {
                        writes.extend(baseline.projected_origins(event, binding, &place.segments));
                    }
                }
                FlowAction::Evaluate(value) if body.consuming_pin_reads.contains(value) => {
                    if let NodeKind::Form { children, .. } = &body.nodes[value.0].kind {
                        writes.extend(baseline.value_before(body, flow, event, children[1]));
                    }
                }
                _ => {}
            }
            for (family, alias) in self.aliases.iter().enumerate() {
                if !origins.entry_alias_retained_before(event, family, alias, &live_bindings) {
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
                if writes.iter().any(overlaps)
                    || guarded.iter().any(|(write, guards)| {
                        overlaps(write)
                            && !guards
                                .iter()
                                .any(|(guard, variant)| incompatible(guard, *variant))
                    })
                {
                    return Err((alias.parameter, BorrowConflict {
                        message: format!("cannot mutate or consume an owner while its stored internal reference is retained in '{name}'"),
                        span: node.span, labels: vec![],
                    }));
                }
                if let Some((_, _, _, span)) =
                    observations.iter().find(|(target, exclusive, guards, _)| {
                        (alias.mutable || *exclusive)
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
                    let nested = Self::for_call(body, flow, event, value, &origins, declarations)
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
      (#struct Link (: value u64 : state u32 : view (#pin-ref u64)))
      (#fn install (: target (#pin-ref-mut Link)) (#pin-ref-mut Link)
        (#let view (#pin-ref u64) (#pin-borrow (#get target value)))
        (#pin-set-field target view view) (#return target))
      (#fn tick (: target (#pin-ref-mut Link)) (#pin-ref-mut Link)
        (#pin-set-field target state 2u32) (#return target))
      (#fn driver (: outside (#pin-ref u64)) u64
        (#let-mut link Link (#struct-literal Link (: value 42u64 : state 0u32 : view outside)))
        (#let-mut running (#pin-ref-mut Link) (#pin-borrow-mut link))
        (#let installed (#pin-ref-mut Link) (#call install (: target running)))
        (#set running installed)
        (#let updated (#pin-ref-mut Link) (#call tick (: target running)))
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

    fn exclusive_source() -> String {
        SOURCE
            .replace("#pin-ref u64", "#pin-ref-mut u64")
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
            }]
        );
        assert!(call_plan(&declarations, "driver", "install")
            .aliases
            .is_empty());
    }

    #[test]
    fn external_pointees_and_cleared_self_loans_are_not_owner_aliases() {
        for source in [
            SOURCE.replace("(#let installed (#pin-ref-mut Link) (#call install (: target running)))\n        (#set running installed)", ""),
            SOURCE.replace("(#let updated (#pin-ref-mut Link) (#call tick (: target running)))",
                "(#pin-set-field running view outside) (#let updated (#pin-ref-mut Link) (#call tick (: target running)))"),
        ] {
            let declarations = fixture(&source);
            assert!(call_plan(&declarations, "driver", "tick").aliases.is_empty());
        }
    }

    #[test]
    fn symbolic_nested_pointer_slots_do_not_imply_physical_self_aliases() {
        let source = "(#struct Link (: value u64 : view (#pin-ref u64)))
          (#fn tick (: target (#pin-ref-mut Link)) (#pin-ref-mut Link) (#return target))
          (#fn driver (: input (#pin-ref-mut Link)) (#pin-ref-mut Link)
            (#return (#call tick (: target input))))";
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
            "(#let observed u64 (#deref (#get target view))) (#forget observed)",
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
        let external = source.replace("(#let installed (#pin-ref-mut Link) (#call install (: target running)))\n        (#set running installed)", "");
        let declarations = fixture(&external);
        call_plan(&declarations, "driver", "tick")
            .check_owner_accesses(&declarations, &crate::linearcheck::LinearTypes::default())
            .unwrap();
    }

    #[test]
    fn exclusive_internal_loans_block_owner_reads_clones_and_reborrows() {
        for (operation, expected) in [
            ("(#let observed u64 (#get target value)) (#forget observed)", "(#get target value)"),
            ("(#let observed u64 (#clone (#get target value))) (#forget observed)", "(#clone (#get target value))"),
            ("(#let another (#pin-ref u64) (#pin-borrow (#get target value))) (#drop another)", "(#pin-borrow (#get target value))"),
            ("(#let another (#pin-ref-mut u64) (#pin-borrow-mut (#get target value))) (#drop another)", "(#pin-borrow-mut (#get target value))"),
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
            ("(#let observed u64 (#get target value)) (#forget observed)", false),
            ("(#let another (#pin-ref u64) (#pin-borrow (#get target value))) (#drop another)", false),
            ("(#let another (#pin-ref-mut u64) (#pin-borrow-mut (#get target value))) (#drop another)", true),
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
            "(#let observed u32 (#get target state)) (#forget observed)",
            "(#let observed u64 (#deref (#get target view))) (#forget observed)",
            "(#let observed u64 (#call child-read (: pointer (#get target view)))) (#forget observed)",
        ] {
            let source = format!("{} (#fn child-read (: pointer (#pin-ref-mut u64)) u64 (#return (#deref pointer)))",
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
          (#fn observe (: pointer (#pin-ref u64)) u64 (#return (#deref pointer)))
          (#fn forward (: target (#pin-ref-mut Link)) u64
            (#return (#call observe (: pointer (#pin-borrow (#get target value))))))",
            exclusive_source().replace(
                "(#pin-set-field target state 2u32)",
                "(#let observed u64 (#call forward (: target target))) (#forget observed)"
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
              (#let observed u64 (#get target value)) (#forget observed) {}",
                if saved {
                    "(#let saved (#pin-ref-mut u64) (#get target view))"
                } else {
                    ""
                },
                if saved {
                    "(#let used u64 (#deref saved)) (#forget used) (#drop saved)"
                } else {
                    ""
                }
            );
            let source = exclusive_source()
                .replace(
                    "(#fn tick (: target (#pin-ref-mut Link))",
                    "(#fn tick (: target (#pin-ref-mut Link) : outside (#pin-ref-mut u64))",
                )
                .replace(
                    "(#call tick (: target running))",
                    "(#call tick (: target running : outside outside))",
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
        let mut source =
            String::from("(#fn level0 (: pointer (#pin-ref u64)) u64 (#return (#deref pointer)))");
        for level in 1..=20 {
            source.push_str(&format!(
                "(#fn level{level} (: pointer (#pin-ref u64)) u64
              (#let ignored u64 (#call level{} (: pointer pointer)))
              (#return (#call level{} (: pointer pointer))))",
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
            "(#let observed u64 (#get target value)) (#forget observed)",
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

    #[test]
    fn entry_payload_aliases_are_correlated_with_checked_physical_tag_guards() {
        let source = "(#enum Value (Empty (Full u64)))
          (#struct Link (: value Value : view (#pin-ref u64)))
          (#fn install (: target (#pin-ref-mut Link)) (#pin-ref-mut Link)
            (#let view (#pin-ref u64)
              (#pin-get-payload (#pin-borrow (#get target value)) Full 0))
            (#pin-set-field target view view) (#return target))
          (#fn tick (: target (#pin-ref-mut Link)) (#pin-ref-mut Link)
            (#if (#variant-is (#pin-borrow (#get target value)) Empty)
              (#unsafe (#pin-write (#pin-borrow-mut (#get target value)) (Full 99u64))) ())
            (#return target))
          (#fn driver (: outside (#pin-ref u64)) ()
            (#let-mut link Link (#struct-literal Link (: value (Full 42u64) : view outside)))
            (#let installed (#pin-ref-mut Link) (#call install (: target (#pin-borrow-mut link))))
            (#let updated (#pin-ref-mut Link) (#call tick (: target installed)))
            (#pin-set-field updated view outside)
            (#drop updated) (#forget link) (#return ()))";
        for (guard, rejected) in [("Empty", false), ("Full", true)] {
            let source = source.replace("value)) Empty)", &format!("value)) {guard})"));
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
            "(#unsafe (#pin-write (#pin-borrow-mut (#get target value)) Empty)) (#if (#variant-is",
        );
        let declarations = fixture(&bad);
        call_plan(&declarations, "driver", "tick")
            .check_owner_accesses(&declarations, &crate::linearcheck::LinearTypes::default())
            .unwrap_err();
    }

    #[test]
    fn initializer_entry_guards_survive_destructive_reads_but_are_not_invented_after_writes() {
        for early in [true, false] {
            let assertion = "(#assert (#variant-is slot Empty))";
            let (before, after) = if early {
                (assertion, "")
            } else {
                ("", assertion)
            };
            let source = format!(
                "(#enum Slot (Empty (Full u64))) (#linear Slot)
              (#fn initialize (: slot (#pin-ref-mut Slot)) ()
                {before}
                (#let previous Slot (#unsafe (#pin-read slot))) (#forget previous)
                (#unsafe (#pin-write slot Empty))
                {after}
                (#unsafe (#pin-write slot (Full 42u64))) (#return ()))"
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
                .variant_id(&Type::Named("Slot".into()), "Empty")
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
            "(#call assert (: condition (#variant-is first Empty)))",
            "(#assert (#variant-is (#if choose first second) Empty))",
        ] {
            let source = format!("(#enum Slot (Empty (Full u64))) (#linear Slot)
              (#fn assert (: condition bool) () (#return ()))
              (#fn initialize (: first (#pin-ref-mut Slot) : second (#pin-ref-mut Slot) : choose bool) ()
                {assertion}
                (#let previous Slot (#unsafe (#pin-read first))) (#forget previous)
                (#unsafe (#pin-write first (Full 42u64))) (#return ()))");
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
            "(#fn level0 (: target (#pin-ref-mut u64)) ()
          (#unsafe (#pin-write target 42u64)) (#return ()))",
        );
        for level in 1..=20 {
            source.push_str(&format!(
                "(#fn level{level} (: target (#pin-ref-mut u64)) ()
              (#call level{} (: target target))
              (#call level{} (: target target)) (#return ()))",
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
            "(#static Count u64 0u64)
          (#fn touch () () (#unsafe (#forget Count)) (#return ())) {}",
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
            .any(|effect| effect.target.global == declarations.global_id("Count")));
        call_plan(&declarations, "driver", "tick")
            .check_owner_accesses(&declarations, &crate::linearcheck::LinearTypes::default())
            .unwrap();
    }

    #[test]
    fn definite_clear_retires_entry_alias_but_conditional_clear_does_not() {
        for conditional in [false, true] {
            let clear = if conditional {
                "(#if (#u32.== (#get target state) 0u32) (#pin-set-field target view outside) ())"
            } else {
                "(#pin-set-field target view outside)"
            };
            let source = SOURCE
                .replace(
                    "(#fn tick (: target (#pin-ref-mut Link))",
                    "(#fn tick (: target (#pin-ref-mut Link) : outside (#pin-ref u64))",
                )
                .replace(
                    "(#call tick (: target running))",
                    "(#call tick (: target running : outside outside))",
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
            "(#let-mut running (#pin-ref-mut Link) (#pin-borrow-mut link))\n        (#let installed (#pin-ref-mut Link) (#call install (: target running)))\n        (#set running installed)\n        (#let updated (#pin-ref-mut Link) (#call tick (: target running)))\n        (#set running updated)\n        (#pin-set-field running view outside)\n        (#drop running)",
            "(#let running (#pin-ref-mut Link) (#call install (: target (#pin-borrow-mut link))))\n        (#let updated (#pin-ref-mut Link) (#call tick (: target running)))\n        (#pin-set-field updated view outside) (#drop updated)",
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
            "(#return (#call smash (: owner target)))",
        ) + "\n(#fn smash (: owner (#pin-ref-mut Link)) (#pin-ref-mut Link)
          (#pin-set-field owner value 99u64) (#return owner))";
        let declarations = fixture(&source);
        let result = call_plan(&declarations, "driver", "tick")
            .check_owner_accesses(&declarations, &crate::linearcheck::LinearTypes::default());
        let error = result.unwrap_err();
        let span = error.span.unwrap();
        assert_eq!(
            &source[span.start..span.end],
            "(#call smash (: owner target))"
        );
    }

    #[test]
    fn nested_tuple_projection_is_physical_not_child_pointer_storage() {
        let source = SOURCE
            .replace(": value u64", ": value (#tuple u64 u64)")
            .replace(
                "(#pin-borrow (#get target value))",
                "(#pin-borrow (#get (#get target value) 1))",
            )
            .replace(
                ": value 42u64",
                ": value (#tuple (#tuple u64 u64) 1u64 42u64)",
            );
        let declarations = fixture(&source);
        let plan = call_plan(&declarations, "driver", "tick");
        assert_eq!(plan.aliases.len(), 1);
        assert_eq!(plan.aliases[0].projection.last(), Some(&Segment::Tuple(1)));
        plan.check_owner_accesses(&declarations, &crate::linearcheck::LinearTypes::default())
            .unwrap();
        let invalid = source.replace("(#pin-set-field target state 2u32)",
            "(#unsafe (#pin-write (#pin-borrow-mut (#get target value)) (#tuple (#tuple u64 u64) 99u64 100u64)))");
        let declarations = fixture(&invalid);
        assert!(call_plan(&declarations, "driver", "tick")
            .check_owner_accesses(&declarations, &crate::linearcheck::LinearTypes::default())
            .is_err());
    }

    #[test]
    fn retained_exclusive_child_permits_its_own_write_not_an_owner_write() {
        let source = SOURCE
            .replace("#pin-ref u64", "#pin-ref-mut u64")
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
                "(#let saved (#pin-ref u64) (#get target view))
                 (#pin-set-field target view outside) (#pin-set-field target value 99u64)
                 (#let observed u64 (#deref saved)) (#forget observed)"
            } else {
                "(#let saved (#pin-ref u64) (#get target view))
                 (#let observed u64 (#deref saved)) (#forget observed)
                 (#pin-set-field target view outside) (#pin-set-field target value 99u64)"
            };
            let source = SOURCE
                .replace(
                    "(#fn tick (: target (#pin-ref-mut Link))",
                    "(#fn tick (: target (#pin-ref-mut Link) : outside (#pin-ref u64))",
                )
                .replace(
                    "(#call tick (: target running))",
                    "(#call tick (: target running : outside outside))",
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
                "(#let saved (#pin-ref u64) (#get target view))"
            } else {
                ""
            };
            let use_copy = if keep_copy {
                "(#let observed u64 (#deref saved)) (#forget observed)"
            } else {
                ""
            };
            let operation = format!(
                "{save}
              (#pin-set-field target view outside)
              (#let fresh (#pin-ref u64) (#pin-borrow (#get target value)))
              (#pin-set-field target view fresh)
              (#pin-set-field target state 2u32) {use_copy}"
            );
            let source = SOURCE
                .replace(
                    "(#fn tick (: target (#pin-ref-mut Link))",
                    "(#fn tick (: target (#pin-ref-mut Link) : outside (#pin-ref u64))",
                )
                .replace(
                    "(#call tick (: target running))",
                    "(#call tick (: target running : outside outside))",
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
                origins.entry_alias_retained_before(event, 0, &plan.aliases[0], &live),
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
            .replace(": value u64", ": value (#tuple u64 u64)")
            .replace(
                ": value 42u64",
                ": value (#tuple (#tuple u64 u64) 40u64 2u64)",
            )
            .replace("#pin-ref u64", "#pin-ref (#tuple u64 u64)")
            .replace(
                "(#fn tick (: target (#pin-ref-mut Link))",
                "(#fn tick (: target (#pin-ref-mut Link) : outside (#pin-ref (#tuple u64 u64)))",
            )
            .replace(
                "(#call tick (: target running))",
                "(#call tick (: target running : outside outside))",
            )
            .replace(
                "(#pin-set-field target state 2u32)",
                "(#let child (#pin-ref u64) (#pin-borrow (#get (#get target view) 1)))
                 (#pin-set-field target view outside)
                 (#unsafe (#pin-write (#pin-borrow-mut (#get target value)) (#tuple (#tuple u64 u64) 99u64 100u64)))
                 (#let observed u64 (#deref child)) (#forget observed)",
            );
        let declarations = fixture(&source);
        let error = call_plan(&declarations, "driver", "tick")
            .check_owner_accesses(&declarations, &crate::linearcheck::LinearTypes::default())
            .unwrap_err();
        let span = error.span.unwrap();
        assert_eq!(&source[span.start..span.end], "(#pin-write (#pin-borrow-mut (#get target value)) (#tuple (#tuple u64 u64) 99u64 100u64))");
    }

    #[test]
    fn separate_incoming_families_at_one_address_retire_independently() {
        let source = SOURCE
            .replace(
                ": view (#pin-ref u64)))",
                ": view (#pin-ref u64) : second (#pin-ref u64)))",
            )
            .replace(": view outside", ": view outside : second outside")
            .replace(
                "(#pin-set-field target view view)",
                "(#pin-set-field target view view) (#pin-set-field target second view)",
            )
            .replace(
                "(#fn tick (: target (#pin-ref-mut Link))",
                "(#fn tick (: target (#pin-ref-mut Link) : outside (#pin-ref u64))",
            )
            .replace(
                "(#call tick (: target running))",
                "(#call tick (: target running : outside outside))",
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
                origins.entry_alias_retained_before(event, family, alias, &[]),
                alias.storage.last() == Some(&Segment::Field(field("second")))
            );
        }
    }

    #[test]
    fn projected_borrows_keep_the_receiver_evaluated_before_index_effects() {
        let source = SOURCE
            .replace(": value u64", ": value (#array u64 2)")
            .replace(
                ": value 42u64",
                ": value (#array-of (#array u64 2) 40u64 42u64)",
            )
            .replace("#pin-ref u64", "#pin-ref (#array u64 2)")
            .replace(
                "(#fn tick (: target (#pin-ref-mut Link))",
                "(#fn tick (: target (#pin-ref-mut Link) : outside (#pin-ref (#array u64 2)))",
            )
            .replace(
                "(#call tick (: target running))",
                "(#call tick (: target running : outside outside))",
            )
            .replace(
                "(#pin-set-field target state 2u32)",
                "(#let child (#pin-ref u64) (#pin-borrow (#index (#get target view)
                   (#block (#pin-set-field target view outside) 1usize))))
                 (#unsafe (#pin-write (#pin-borrow-mut (#get target value))
                   (#array-of (#array u64 2) 99u64 100u64)))
                 (#let observed u64 (#deref child)) (#forget observed)",
            );
        let declarations = fixture(&source);
        let error = call_plan(&declarations, "driver", "tick")
            .check_owner_accesses(&declarations, &crate::linearcheck::LinearTypes::default())
            .unwrap_err();
        let span = error.span.unwrap();
        assert_eq!(&source[span.start..span.end],
            "(#pin-write (#pin-borrow-mut (#get target value))\n                   (#array-of (#array u64 2) 99u64 100u64))");
    }

    #[test]
    fn run_local_cache_keeps_distinct_alias_contexts_separate() {
        let source = SOURCE
            .replace(": state u32", ": state u64")
            .replace(": state 0u32", ": state 0u64")
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
        let source = SOURCE.replace("(#fn tick (: target (#pin-ref-mut Link))",
            "(#fn tick (: first (#pin-ref-mut Link) : target (#pin-ref-mut Link))")
            .replace("(#pin-set-field target state 2u32)", "(#pin-set-field target value 99u64)")
            .replace("(#let updated (#pin-ref-mut Link) (#call tick (: target running)))",
                "(#let-mut another Link (#struct-literal Link (: value 7u64 : state 0u32 : view outside)))
                 (#let second (#pin-ref-mut Link) (#call install (: target (#pin-borrow-mut another))))
                 (#let updated (#pin-ref-mut Link) (#call tick (: target second : first running)))");
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
}
