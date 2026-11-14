//! Bounded scalar facts over ordinary control flow. These facts describe
//! values, never ownership, initialized references, or permission to read.
use super::*;

mod specialize;
mod word_returns;
pub(super) use specialize::{specialize, specialize_excluding, specialize_for_calls};
pub(super) use word_returns::word_and_scalar_return_guarantees;

type Values = Vec<crate::Expr>;
type Shape = HashMap<Vec<Segment>, Values>;

pub(super) fn scalar_clone_is_pure(body: &Body, value: NodeId) -> bool {
    matches!(
        body.nodes[value.0].ty,
        Some(
            Type::Unit
                | Type::Bool
                | Type::Char
                | Type::I8
                | Type::I16
                | Type::I32
                | Type::I64
                | Type::I128
                | Type::Isize
                | Type::U8
                | Type::U16
                | Type::U32
                | Type::U64
                | Type::U128
                | Type::Usize
                | Type::F32
                | Type::F64
                | Type::RawPointer { .. }
        )
    )
}

#[derive(Clone, Default, PartialEq)]
struct Facts {
    memory: HashMap<Place, Values>,
    excluded_memory: HashMap<Place, Values>,
    excluded_values: HashMap<NodeId, Values>,
    // Evaluated values are snapshots: a later write must not change a match's
    // already evaluated scrutinee. Each evaluation replaces its own snapshot.
    values: HashMap<NodeId, Shape>,
    // A captured value constrains live memory only while its physical read
    // remains fresh on every reaching path. Snapshots survive invalidation.
    reads: HashMap<NodeId, Place>,
}

pub(super) struct Analysis {
    before: Vec<Option<Facts>>,
    active: bool,
}

impl Analysis {
    pub(super) fn unsigned_value_before(
        &self,
        event: FlowNodeId,
        body: &Body,
        value: NodeId,
        path: &[Segment],
    ) -> Option<Vec<u128>> {
        let facts = self.before.get(event.0)?.as_ref()?;
        let shape = snapshot(facts, body, value);
        let values = shape.get(path)?;
        if values.is_empty() {
            return None;
        }
        values
            .iter()
            .map(|value| match value {
                crate::Expr::UnsignedInteger(value) => Some(*value),
                _ => None,
            })
            .collect()
    }
    pub(super) fn unsigned_before(&self, event: FlowNodeId, place: &Place) -> Option<Vec<u128>> {
        let values = self.before.get(event.0)?.as_ref()?.memory.get(place)?;
        if values.is_empty() {
            return None;
        }
        values
            .iter()
            .map(|value| match value {
                crate::Expr::UnsignedInteger(value) => Some(*value),
                _ => None,
            })
            .collect()
    }
    pub(super) fn excludes(&self, event: FlowNodeId, value: NodeId, wanted: &crate::Expr) -> bool {
        if self.active && self.before[event.0].is_none() {
            return true;
        }
        self.before[event.0]
            .as_ref()
            .and_then(|facts| facts.values.get(&value))
            .and_then(|shape| shape.get(&Vec::new()))
            .is_some_and(|values| !values.is_empty() && !values.contains(wanted))
    }
}

/// Candidate entry partitions only choose an exact physical parameter field.
/// The actual proof comes from re-solving each complete context graph, not
/// from assuming the field remains unchanged at a later pattern event.
pub(super) fn entry_partition(
    flow: &FlowGraph,
    body: &Body,
    origins: &FlowLoanOrigins,
) -> Option<(Place, Vec<u128>)> {
    let mut selected: Option<(Place, Vec<u128>)> = None;
    for (index, node) in flow.nodes.iter().enumerate() {
        let FlowAction::Pattern { pattern, value } = node.action else {
            continue;
        };
        let Some(crate::Expr::UnsignedInteger(number)) = scalar_pattern_value(body, pattern) else {
            continue;
        };
        let Some(place) = read_place(body, origins, FlowNodeId(index), value)
            .and_then(|place| entry_parameter_place(flow, body, place))
        else {
            continue;
        };
        if selected.is_none() {
            selected = Some((place.clone(), Vec::new()));
        }
        let (held, values) = selected.as_mut().unwrap();
        if *held == place && !values.contains(&number) {
            values.push(number);
        }
    }
    selected
}

pub(super) fn entry_parameter_place(
    flow: &FlowGraph,
    body: &Body,
    mut place: Place,
) -> Option<Place> {
    for _ in 0..=body.bindings.len() {
        match place.root {
            PlaceRoot::Parameter(_) => return Some(place),
            PlaceRoot::Local(binding)
                if binding.0 < body.parameter_count
                    && !matches!(
                        body.bindings[binding.0].ty,
                        Type::Reference { .. } | Type::PinnedReference { .. }
                    ) =>
            {
                return Some(place);
            }
            PlaceRoot::Local(binding) => {
                if binding.0 < body.parameter_count {
                    if matches!(
                        body.bindings[binding.0].ty,
                        Type::Reference { .. } | Type::PinnedReference { .. }
                    ) {
                        if place.segments.first() == Some(&Segment::Dereference) {
                            place.segments.remove(0);
                        }
                        place.root = PlaceRoot::Parameter(binding);
                        return Some(place);
                    }
                    return None;
                }
                let mut sources = flow.nodes.iter().filter_map(|node| match node.action {
                    FlowAction::Bind {
                        binding: bound,
                        value,
                    } if bound == binding => Some(value),
                    _ => None,
                });
                let mut value = sources.next()?;
                if sources.next().is_some() {
                    return None;
                }
                // An entry selector may have been copied into a temporary
                // aggregate before a destructive operation. Follow its exact
                // constructor field, not the aggregate's unrelated fields.
                while let Some(segment) = place.segments.first() {
                    let NodeKind::Form {
                        head,
                        children,
                        callee: None,
                        ..
                    } = &body.nodes[value.0].kind
                    else {
                        break;
                    };
                    let Some(child) =
                        children
                            .iter()
                            .skip(1)
                            .enumerate()
                            .find_map(|(index, child)| {
                                (aggregate_slot(body, head, children, index).as_ref()
                                    == Some(segment))
                                .then_some(*child)
                            })
                    else {
                        break;
                    };
                    value = child;
                    place.segments.remove(0);
                }
                let mut source = Place::from_expression(body, value)?;
                source.segments.extend(place.segments);
                place = source;
            }
            _ => return None,
        }
    }
    None
}

fn join_values(held: &mut Values, incoming: &Values) -> bool {
    for value in incoming {
        if !held.contains(value) {
            held.push(value.clone());
            if held.len() > 16 {
                return false;
            }
        }
    }
    true
}

fn join_map<K: Eq + std::hash::Hash>(held: &mut HashMap<K, Values>, incoming: &HashMap<K, Values>) {
    held.retain(|key, values| {
        incoming
            .get(key)
            .is_some_and(|other| join_values(values, other))
    });
}

fn join(held: &mut Facts, incoming: &Facts) -> bool {
    let previous = held.clone();
    intersect_exclusions(&mut held.excluded_memory, &incoming.excluded_memory);
    intersect_exclusions(&mut held.excluded_values, &incoming.excluded_values);
    join_map(&mut held.memory, &incoming.memory);
    held.values.retain(|node, shape| {
        if let Some(other) = incoming.values.get(node) {
            join_map(shape, other);
            !shape.is_empty()
        } else {
            false
        }
    });
    held.reads
        .retain(|node, place| incoming.reads.get(node) == Some(place));
    *held != previous
}

fn intersect_exclusions<K: Eq + std::hash::Hash>(
    held: &mut HashMap<K, Values>,
    incoming: &HashMap<K, Values>,
) {
    held.retain(|key, values| {
        let Some(other) = incoming.get(key) else {
            return false;
        };
        values.retain(|value| other.contains(value));
        !values.is_empty()
    });
}

fn stored_shape(facts: &Facts, place: &Place) -> Shape {
    facts
        .memory
        .iter()
        .filter_map(|(source, values)| {
            (source.root == place.root && source.segments.starts_with(&place.segments)).then(|| {
                (
                    source.segments[place.segments.len()..].to_vec(),
                    values.clone(),
                )
            })
        })
        .collect()
}

fn snapshot(facts: &Facts, body: &Body, value: NodeId) -> Shape {
    if let Some(literal) = scalar_pattern_value(body, value) {
        return HashMap::from([(Vec::new(), vec![literal])]);
    }
    facts.values.get(&value).cloned().unwrap_or_default()
}

fn read_shape(facts: &Facts, places: &[Place]) -> Shape {
    let mut common = None;
    for place in places {
        let incoming = stored_shape(facts, place);
        if let Some(held) = &mut common {
            join_map(held, &incoming);
        } else {
            common = Some(incoming);
        }
    }
    common.unwrap_or_default()
}

fn evaluate(
    facts: &Facts,
    body: &Body,
    origins: &FlowLoanOrigins,
    event: FlowNodeId,
    value: NodeId,
) -> Shape {
    if let Some(literal) = scalar_pattern_value(body, value) {
        return HashMap::from([(Vec::new(), vec![literal])]);
    }
    if let NodeKind::Form {
        callee: Some(callee),
        ..
    } = &body.nodes[value.0].kind
    {
        return body
            .call_scalar_returns
            .get(callee)
            .map(|facts| {
                facts
                    .iter()
                    .map(|fact| {
                        (
                            fact.storage.clone(),
                            fact.values
                                .iter()
                                .map(|value| crate::Expr::UnsignedInteger(*value))
                                .collect(),
                        )
                    })
                    .collect()
            })
            .unwrap_or_default();
    }
    if let Some(place) = Place::from_expression(body, value) {
        if reads_through_reference(body, value) {
            if let Some(places) = physical_write_places(body, origins, event, &place) {
                let shape = read_shape(facts, &places);
                if !shape.is_empty() {
                    return shape;
                }
            }
            if let NodeKind::Form { head, children, .. } = &body.nodes[value.0].kind {
                if matches!(
                    body.nodes[children[1].0].ty,
                    Some(Type::Reference { .. } | Type::PinnedReference { .. })
                ) {
                    let mut prefix = vec![Segment::Dereference];
                    if head != "deref" {
                        let slot = match head.as_str() {
                            "get" => match body.nodes[children[2].0].kind {
                                NodeKind::Declaration(DeclarationId::Field(field)) => {
                                    Segment::Field(field)
                                }
                                _ => {
                                    let Some(index) =
                                        crate::typed_place::literal_index(body, children[2])
                                    else {
                                        return Shape::new();
                                    };
                                    Segment::Tuple(index as usize)
                                }
                            },
                            _ => return Shape::new(),
                        };
                        prefix.push(slot);
                    }
                    return snapshot(facts, body, children[1])
                        .into_iter()
                        .filter_map(|(path, values)| {
                            path.strip_prefix(prefix.as_slice())
                                .map(|path| (path.to_vec(), values))
                        })
                        .collect();
                }
            }
            return Shape::new();
        } else if matches!(place.root, PlaceRoot::Local(_)) {
            return stored_shape(facts, &place);
        }
    }
    let NodeKind::Form {
        head,
        children,
        callee: None,
        ..
    } = &body.nodes[value.0].kind
    else {
        return Shape::new();
    };
    if matches!(
        head.as_str(),
        "borrow" | "borrow-mut" | "pin-borrow" | "pin-borrow-mut"
    ) && children.len() == 2
    {
        let Some(place) = Place::from_expression(body, children[1]) else {
            return Shape::new();
        };
        let shape = if reads_through_reference(body, children[1]) {
            physical_write_places(body, origins, event, &place)
                .map(|places| read_shape(facts, &places))
                .unwrap_or_default()
        } else {
            stored_shape(facts, &place)
        };
        return shape
            .into_iter()
            .map(|(path, values)| {
                (
                    std::iter::once(Segment::Dereference).chain(path).collect(),
                    values,
                )
            })
            .collect();
    }
    let declared = matches!(
        children.first().map(|child| &body.nodes[child.0].kind),
        Some(NodeKind::Declaration(
            DeclarationId::Aggregate(_) | DeclarationId::Variant(_)
        ))
    );
    if !declared && !matches!(head.as_str(), "tuple" | "array-of") {
        return Shape::new();
    }
    let start = if declared {
        1
    } else {
        constructor_values_start(body.nodes[value.0].ty.as_ref(), children.len())
    };
    let mut shape = Shape::new();
    for (index, child) in children.iter().skip(start).enumerate() {
        let Some(slot) = aggregate_slot(body, head, children, index) else {
            continue;
        };
        for (path, values) in snapshot(facts, body, *child) {
            let mut destination = vec![slot.clone()];
            destination.extend(path);
            shape.insert(destination, values);
        }
    }
    shape
}

fn write(facts: &mut Facts, place: &Place, incoming: Shape) {
    facts.memory.retain(|source, _| !place.overlaps(source));
    facts
        .excluded_memory
        .retain(|source, _| !place.overlaps(source));
    facts.reads.retain(|_, source| !place.overlaps(source));
    if place
        .segments
        .iter()
        .any(|segment| matches!(segment, Segment::DynamicIndex | Segment::SliceDynamicIndex))
    {
        return;
    }
    for (path, values) in incoming {
        let mut destination = place.clone();
        destination.segments.extend(path);
        facts.memory.insert(destination, values);
    }
}

fn read_place(
    body: &Body,
    origins: &FlowLoanOrigins,
    event: FlowNodeId,
    value: NodeId,
) -> Option<Place> {
    let place = Place::from_expression(body, value)?;
    let places = if reads_through_reference(body, value) {
        physical_write_places(body, origins, event, &place)?
    } else {
        vec![place]
    };
    if places.len() != 1
        || !matches!(
            places[0].root,
            PlaceRoot::Local(_) | PlaceRoot::Parameter(_)
        )
        || places[0].segments.iter().any(|part| {
            matches!(
                part,
                Segment::DynamicIndex | Segment::SliceDynamicIndex | Segment::SliceRangeUnknown
            )
        })
    {
        return None;
    }
    Some(places[0].clone())
}

fn invalidate(facts: &mut Facts) {
    facts.memory.clear();
    facts.excluded_memory.clear();
    facts.reads.clear();
    invalidate_referent_snapshots(facts);
}

// A scalar copied out of a referent remains a value snapshot. A scalar
// recorded *behind* a returned reference is instead a live-memory fact and
// must not survive a later mutation through any alias.
fn invalidate_referent_snapshots(facts: &mut Facts) {
    facts
        .memory
        .retain(|place, _| !place.segments.contains(&Segment::Dereference));
    for shape in facts.values.values_mut() {
        shape.retain(|path, _| !path.contains(&Segment::Dereference));
    }
}

fn invalidate_footprint(facts: &mut Facts, targets: Option<Vec<LoanOrigin>>) {
    invalidate_referent_snapshots(facts);
    let Some(targets) = targets else {
        invalidate(facts);
        return;
    };
    if targets
        .iter()
        .any(|target| target.lifetime_only || !target.storage.is_empty())
    {
        invalidate(facts);
        return;
    }
    for target in targets {
        write(facts, &target.referent_place(), Shape::new());
    }
}

/// Narrow a copied scrutinee, not a newly evaluated read. A guard may have
/// changed the original variable; only a still-fresh singleton address can
/// receive the same refinement. Missing bounds on failure stay unknown.
fn constrain(facts: &mut Facts, value: NodeId, wanted: &crate::Expr, success: bool) -> bool {
    if success
        && facts
            .excluded_values
            .get(&value)
            .is_some_and(|values| values.contains(wanted))
    {
        return false;
    }
    if !success {
        let excluded = facts.excluded_values.entry(value).or_default();
        if !excluded.contains(wanted) && excluded.len() < 16 {
            excluded.push(wanted.clone());
        }
        if let Some(place) = facts.reads.get(&value) {
            let excluded = facts.excluded_memory.entry(place.clone()).or_default();
            if !excluded.contains(wanted) && excluded.len() < 16 {
                excluded.push(wanted.clone());
            }
        }
    }
    let known = facts
        .values
        .get(&value)
        .and_then(|shape| shape.get(&Vec::new()));
    let narrowed = if success {
        if known.is_some_and(|values| !values.contains(wanted)) {
            return false;
        }
        Some(vec![wanted.clone()])
    } else if let Some(values) = known {
        let possible = values
            .iter()
            .filter(|value| *value != wanted)
            .cloned()
            .collect::<Vec<_>>();
        if possible.is_empty() {
            return false;
        }
        Some(possible)
    } else {
        None
    };
    if let Some(values) = narrowed {
        facts
            .values
            .entry(value)
            .or_default()
            .insert(Vec::new(), values.clone());
        if let Some(place) = facts.reads.get(&value) {
            facts.memory.insert(place.clone(), values);
        }
    }
    true
}

fn edge_facts(
    flow: &FlowGraph,
    body: &Body,
    event: FlowNodeId,
    edge: usize,
    mut facts: Facts,
) -> Option<Facts> {
    if let FlowAction::Branch(pattern) = flow.nodes[event.0].action {
        if let Some(wanted) = scalar_pattern_value(body, pattern) {
            if let Some(success) = flow.nodes[event.0].successors.first() {
                if let FlowAction::Pattern {
                    pattern: selected,
                    value,
                } = flow.nodes[success.0].action
                {
                    if selected == pattern && !constrain(&mut facts, value, &wanted, edge == 0) {
                        return None;
                    }
                }
            }
        }
    }
    Some(facts)
}

/// Selected result constructors expose MUST scalar postconditions, just as
/// they expose stored-loan postconditions. They never supply a loan. Recover
/// them only from every producer and only while the destination stays fresh.
fn selected_call_scalar_stores(
    flow: &FlowGraph,
    body: &Body,
    origins: &FlowLoanOrigins,
    event: FlowNodeId,
) -> HashMap<Place, Shape> {
    let refinement = if origins
        .clear_refinements
        .get(event.0)
        .is_some_and(Option::is_some)
    {
        &origins.clear_refinements
    } else {
        origins
            .scalar_refinements
            .get_or_init(|| flow.call_result_refinements(body))
    };
    let Some(Some((calls, variant, region))) = refinement.get(event.0) else {
        return HashMap::new();
    };
    let mut common: Option<HashMap<Place, Shape>> = None;
    for (call_event, call, path) in calls {
        let Some(state) = &origins.before[call_event.0] else {
            return HashMap::new();
        };
        let NodeKind::Form {
            callee: Some(callee),
            children,
            ..
        } = &body.nodes[call.0].kind
        else {
            return HashMap::new();
        };
        let summaries = if path.is_empty() {
            body.call_store_variants
                .get(callee)
                .and_then(|groups| groups.get(variant))
        } else {
            body.call_output_store_variants
                .get(callee)
                .and_then(|groups| groups.get(&(path.clone(), *variant)))
        };
        let Some(summaries) = summaries else {
            return HashMap::new();
        };
        let mut incoming = HashMap::new();
        for summary in summaries {
            if summary.scalars.is_empty() {
                continue;
            }
            let Some(argument) = children.get(summary.destination.parameter + 1) else {
                continue;
            };
            let targets = origins
                .value_before(body, flow, *call_event, *argument)
                .into_iter()
                .flat_map(|origin| {
                    apply_parameter_loan_summary(origin, &summary.destination, state)
                })
                .collect::<Vec<_>>();
            if !one_concrete_store_destination(&targets) {
                continue;
            }
            let target = targets[0].referent_place();
            let stale = region.iter().any(|previous| match &flow.nodes[previous.0].action {
                FlowAction::Assign { place, .. } | FlowAction::Release { place, .. } => place.overlaps(&target),
                FlowAction::ScopeExit(bindings) => matches!(target.root,
                    PlaceRoot::Local(binding) | PlaceRoot::Parameter(binding) if bindings.contains(&binding)),
                FlowAction::Write { place, .. } => physical_write_places(body, origins, *previous, place)
                    .is_none_or(|places| places.iter().any(|place| place.overlaps(&target))),
                FlowAction::Clone { value, .. } => !scalar_clone_is_pure(body, *value),
                FlowAction::Evaluate(value) => match &body.nodes[value.0].kind {
                    NodeKind::Form { callee: Some(_), .. } => origins.call_scalar_mutations(body, flow, *previous, *value)
                        .is_none_or(|targets| targets.iter().any(|address| address.referent_place().overlaps(&target))),
                    NodeKind::Form { head, .. } => matches!(head.as_str(), "ptr-write" | "linux-syscall" | "asm" | "pin-read" | "word-write")
                        || head.starts_with("atomic-"),
                    _ => false,
                },
                _ => false,
            });
            if stale {
                continue;
            }
            incoming.insert(
                target,
                summary
                    .scalars
                    .iter()
                    .map(|(path, values)| {
                        (
                            path.clone(),
                            values
                                .iter()
                                .map(|value| crate::Expr::UnsignedInteger(*value))
                                .collect(),
                        )
                    })
                    .collect(),
            );
        }
        if let Some(common) = &mut common {
            common.retain(|place, shape| {
                let Some(other) = incoming.get(place) else {
                    return false;
                };
                join_map(shape, other);
                !shape.is_empty()
            });
        } else {
            common = Some(incoming);
        }
    }
    common.unwrap_or_default()
}

fn transfer(
    flow: &FlowGraph,
    body: &Body,
    origins: &FlowLoanOrigins,
    event: FlowNodeId,
    mut facts: Facts,
) -> Facts {
    match &flow.nodes[event.0].action {
        FlowAction::Evaluate(value)
        | FlowAction::Read { value, .. }
        | FlowAction::Borrow { value, .. }
        | FlowAction::Clone { value, .. } => {
            // A user clone hook can return different numeric fields. An
            // unknown hook result is not the source's pre-hook snapshot.
            let shape = if matches!(flow.nodes[event.0].action, FlowAction::Clone { .. }) {
                if scalar_clone_is_pure(body, *value) {
                    match &body.nodes[value.0].kind {
                        NodeKind::Form { children, .. } => snapshot(&facts, body, children[1]),
                        _ => Shape::new(),
                    }
                } else {
                    Shape::new()
                }
            } else {
                evaluate(&facts, body, origins, event, *value)
            };
            facts.values.remove(value);
            facts.excluded_values.remove(value);
            facts.reads.remove(value);
            if let Some(place) = read_place(body, origins, event, *value) {
                if !matches!(flow.nodes[event.0].action, FlowAction::Clone { .. }) {
                    if let Some(excluded) = facts.excluded_memory.get(&place) {
                        facts.excluded_values.insert(*value, excluded.clone());
                    }
                }
                facts.reads.insert(*value, place);
            }
            if !shape.is_empty() {
                facts.values.insert(*value, shape.clone());
            }
            let call = matches!(
                &body.nodes[value.0].kind,
                NodeKind::Form {
                    callee: Some(_),
                    ..
                }
            );
            if call {
                invalidate_footprint(
                    &mut facts,
                    origins.call_scalar_mutations(body, flow, event, *value),
                );
                let NodeKind::Form {
                    callee: Some(callee),
                    children,
                    ..
                } = &body.nodes[value.0].kind
                else {
                    unreachable!()
                };
                if let Some(state) = &origins.before[event.0] {
                    for summary in body.call_store_origins.get(callee).into_iter().flatten() {
                        if summary.scalars.is_empty() {
                            continue;
                        }
                        let Some(argument) = children.get(summary.destination.parameter + 1) else {
                            continue;
                        };
                        let mut targets = origins
                            .value_before(body, flow, event, *argument)
                            .into_iter()
                            .flat_map(|origin| {
                                apply_parameter_loan_summary(origin, &summary.destination, state)
                            })
                            .collect::<Vec<_>>();
                        targets.dedup();
                        if targets.len() != 1
                            || targets[0].lifetime_only
                            || targets[0].maybe_absent
                            || !targets[0].storage.is_empty()
                        {
                            continue;
                        }
                        let incoming = summary
                            .scalars
                            .iter()
                            .map(|(path, values)| {
                                (
                                    path.clone(),
                                    values
                                        .iter()
                                        .map(|value| crate::Expr::UnsignedInteger(*value))
                                        .collect(),
                                )
                            })
                            .collect();
                        write(&mut facts, &targets[0].referent_place(), incoming);
                    }
                }
                // The call's own postconditions are newer than its writes.
                if !shape.is_empty() {
                    facts.values.insert(*value, shape);
                }
            } else if matches!(flow.nodes[event.0].action, FlowAction::Clone { .. })
                && !scalar_clone_is_pure(body, *value)
            {
                invalidate(&mut facts);
            } else if let NodeKind::Form {
                head,
                children,
                callee: None,
                ..
            } = &body.nodes[value.0].kind
            {
                if head == "pin-own-of" && children.len() == 3 {
                    let target = Place::root(PlaceRoot::Allocation(*value, Vec::new()));
                    let incoming = snapshot(&facts, body, children[2]);
                    // Only a fresh static allocation identity can establish
                    // initializer facts. Repeated live instances at one loop
                    // site must not overwrite the older object's state.
                    invalidate_footprint(
                        &mut facts,
                        Some(vec![allocation_origin(
                            *value,
                            Vec::new(),
                            body.nodes[value.0].span,
                        )]),
                    );
                    if allocation_identity_is_fresh(origins.before[event.0].as_ref(), &target.root)
                    {
                        write(&mut facts, &target, incoming);
                    }
                }
                if matches!(
                    head.as_str(),
                    "pin-read" | "word-write" | "pin-write" | "pin-set-field" | "deref-set"
                ) {
                    let operand = if head == "word-write" { 2 } else { 1 };
                    let targets = children
                        .get(operand)
                        .map(|operand| {
                            origins
                                .value_before(body, flow, event, *operand)
                                .into_iter()
                                .collect::<Vec<_>>()
                        })
                        .filter(|targets| !targets.is_empty())
                        .map(|mut targets| {
                            if head == "pin-set-field" {
                                if let NodeKind::Declaration(DeclarationId::Field(field)) =
                                    body.nodes[children[2].0].kind
                                {
                                    for target in &mut targets {
                                        target.place.segments.push(Segment::Field(field));
                                    }
                                }
                            }
                            targets
                        });
                    invalidate_footprint(&mut facts, targets);
                } else if matches!(head.as_str(), "ptr-write" | "linux-syscall" | "asm")
                    || head.starts_with("atomic-")
                {
                    invalidate(&mut facts);
                }
            }
            // word-take/word-forget retire loan metadata, not bytes.
            // This analysis never tracks their typed restored contents.
        }
        FlowAction::Pattern { pattern, value } => {
            for (place, shape) in selected_call_scalar_stores(flow, body, origins, event) {
                write(&mut facts, &place, shape);
            }
            let source = snapshot(&facts, body, *value);
            let mut bindings = HashSet::new();
            collect_pattern_bindings(body, *pattern, &mut bindings);
            for binding in bindings {
                let Some(prefix) = pattern_binding_path(body, *pattern, binding) else {
                    continue;
                };
                let incoming = source
                    .iter()
                    .filter_map(|(path, values)| {
                        path.strip_prefix(prefix.as_slice())
                            .map(|path| (path.to_vec(), values.clone()))
                    })
                    .collect();
                write(
                    &mut facts,
                    &Place::root(PlaceRoot::Local(binding)),
                    incoming,
                );
            }
        }
        FlowAction::Bind { binding, value } => {
            let incoming = snapshot(&facts, body, *value);
            write(
                &mut facts,
                &Place::root(PlaceRoot::Local(*binding)),
                incoming,
            );
        }
        FlowAction::Assign { place, value } => {
            let incoming = snapshot(&facts, body, *value);
            if matches!(place.root, PlaceRoot::Local(binding)
                    if matches!(body.bindings[binding.0].ty, Type::Reference { .. } | Type::PinnedReference { .. }))
                || place.segments.contains(&Segment::Dereference)
            {
                invalidate(&mut facts);
                write(&mut facts, place, incoming);
            } else {
                write(&mut facts, place, incoming);
            }
        }
        FlowAction::Write { place, value } => {
            let source = match &body.nodes[value.0].kind {
                NodeKind::Form { head, children, .. } if head == "pin-set-field" => children.get(3),
                NodeKind::Form { children, .. } => children.get(2),
                _ => None,
            };
            let targets = physical_write_places(body, origins, event, place);
            if let (Some(source), Some(targets)) = (source, targets) {
                if targets.len() == 1
                    && matches!(
                        targets[0].root,
                        PlaceRoot::Local(_) | PlaceRoot::Parameter(_)
                    )
                {
                    let incoming = snapshot(&facts, body, *source);
                    write(&mut facts, &targets[0], incoming);
                } else {
                    invalidate(&mut facts);
                }
            } else {
                invalidate(&mut facts);
            }
        }
        FlowAction::Release { place, .. } => {
            facts.memory.retain(|source, _| !place.overlaps(source));
            facts
                .excluded_memory
                .retain(|source, _| !place.overlaps(source));
            facts.reads.retain(|_, source| !place.overlaps(source));
        }
        FlowAction::ScopeExit(bindings) => {
            facts.memory.retain(|place, _| !matches!(place.root, PlaceRoot::Local(binding) if bindings.contains(&binding)));
            facts.excluded_memory.retain(|place, _| !matches!(place.root, PlaceRoot::Local(binding) if bindings.contains(&binding)));
            facts.reads.retain(|_, place| !matches!(place.root, PlaceRoot::Local(binding) if bindings.contains(&binding)));
        }
        _ => {}
    }
    facts
}

pub(super) fn analyze(flow: &FlowGraph, body: &Body, origins: &FlowLoanOrigins) -> Analysis {
    analyze_with_entry(flow, body, origins, HashMap::new())
}

pub(super) fn returned_memory(
    flow: &FlowGraph,
    body: &Body,
    origins: &FlowLoanOrigins,
) -> HashMap<Place, Vec<u128>> {
    let analysis = analyze_for_contract(flow, body, origins);
    let reachable = flow.reachable();
    let mut result: Option<HashMap<Place, Vec<u128>>> = None;
    for (index, node) in flow.nodes.iter().enumerate() {
        if !matches!(node.action, FlowAction::Return(_))
            || origins.before[index].is_none()
            || !reachable.contains(&FlowNodeId(index))
        {
            continue;
        }
        let Some(facts) = &analysis.before[index] else {
            return HashMap::new();
        };
        let incoming = facts
            .memory
            .iter()
            .filter_map(|(place, values)| {
                if has_dynamic_projection(place)
                    || place.segments.contains(&Segment::Dereference)
                    || values.is_empty()
                {
                    return None;
                }
                let values = values
                    .iter()
                    .map(|value| match value {
                        crate::Expr::UnsignedInteger(value) => Some(*value),
                        _ => None,
                    })
                    .collect::<Option<Vec<_>>>()?;
                Some((place.clone(), values))
            })
            .collect::<HashMap<_, _>>();
        if let Some(held) = &mut result {
            held.retain(|place, values| {
                let Some(other) = incoming.get(place) else {
                    return false;
                };
                for value in other {
                    if !values.contains(value) {
                        values.push(*value);
                    }
                }
                values.len() <= 16
            });
        } else {
            result = Some(incoming);
        }
    }
    result.unwrap_or_default()
}

pub(super) fn analyze_for_contract(
    flow: &FlowGraph,
    body: &Body,
    origins: &FlowLoanOrigins,
) -> Analysis {
    analyze_impl(flow, body, origins, HashMap::new(), true)
}

fn analyze_for_contract_at_entry(
    flow: &FlowGraph,
    body: &Body,
    origins: &FlowLoanOrigins,
    entry: &[(Place, crate::Expr)],
) -> Analysis {
    analyze_impl(
        flow,
        body,
        origins,
        entry
            .iter()
            .map(|(place, value)| (place.clone(), vec![value.clone()]))
            .collect(),
        true,
    )
}

/// Intersect fields across all reaching returns, and union finite values for
/// fields present on every return. Missing/opaque values remove a guarantee.
pub(super) fn returned(
    flow: &FlowGraph,
    body: &Body,
    origins: &FlowLoanOrigins,
) -> Vec<crate::typed_body::ScalarReturnFact> {
    let analysis = origins
        .scalars
        .get_or_init(|| analyze_for_contract(flow, body, origins));
    let mut common: Option<Shape> = None;
    for (index, node) in flow.nodes.iter().enumerate() {
        let FlowAction::Return(value) = node.action else {
            continue;
        };
        let Some(facts) = &analysis.before[index] else {
            continue;
        };
        let shape = value
            .map(|value| snapshot(facts, body, value))
            .unwrap_or_default();
        if let Some(held) = &mut common {
            join_map(held, &shape);
        } else {
            common = Some(shape);
        }
    }
    let mut result = common
        .unwrap_or_default()
        .into_iter()
        .filter_map(|(storage, values)| {
            if values.is_empty() {
                return None;
            }
            let mut values: Vec<u128> = values
                .into_iter()
                .map(|value| match value {
                    crate::Expr::UnsignedInteger(value) => Some(value),
                    _ => None,
                })
                .collect::<Option<_>>()?;
            values.sort_unstable();
            Some(crate::typed_body::ScalarReturnFact { storage, values })
        })
        .collect::<Vec<_>>();
    result.sort_by(|a, b| a.storage.cmp(&b.storage));
    result
}

fn analyze_with_entry(
    flow: &FlowGraph,
    body: &Body,
    origins: &FlowLoanOrigins,
    memory: HashMap<Place, Values>,
) -> Analysis {
    analyze_impl(flow, body, origins, memory, false)
}

fn analyze_impl(
    flow: &FlowGraph,
    body: &Body,
    origins: &FlowLoanOrigins,
    memory: HashMap<Place, Values>,
    force: bool,
) -> Analysis {
    let mut before = vec![None; flow.nodes.len()];
    if !force
        && !flow.nodes.iter().any(|node| {
            matches!(node.action,
        FlowAction::Pattern { pattern, .. } if scalar_pattern_value(body, pattern).is_some())
        })
    {
        return Analysis {
            before,
            active: false,
        };
    }
    before[flow.entry.0] = Some(Facts {
        memory,
        ..Facts::default()
    });
    let mut pending = VecDeque::from([flow.entry]);
    let mut queued = vec![false; flow.nodes.len()];
    queued[flow.entry.0] = true;
    while let Some(event) = pending.pop_front() {
        queued[event.0] = false;
        let facts = transfer(flow, body, origins, event, before[event.0].clone().unwrap());
        // Solve the restored graph before pruning. A loop can widen an early
        // constant to unknown; early observations must not erase its backedge.
        for (edge, next) in flow.nodes[event.0].successors.iter().enumerate() {
            let Some(incoming) = edge_facts(flow, body, event, edge, facts.clone()) else {
                continue;
            };
            let changed = if let Some(held) = &mut before[next.0] {
                join(held, &incoming)
            } else {
                before[next.0] = Some(incoming);
                true
            };
            if changed && !queued[next.0] {
                queued[next.0] = true;
                pending.push_back(*next);
            }
        }
    }
    Analysis {
        before,
        active: true,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn excluded_entry_facts_do_not_survive_writes_or_path_joins() {
        let place = Place::root(PlaceRoot::Local(BindingId(0)));
        let value = NodeId(0);
        let wanted = crate::Expr::UnsignedInteger(1);
        let mut facts = Facts::default();
        facts
            .excluded_memory
            .insert(place.clone(), vec![wanted.clone()]);
        facts.excluded_values.insert(value, vec![wanted.clone()]);
        facts.reads.insert(value, place.clone());
        write(&mut facts, &place, Shape::new());
        assert!(facts.excluded_memory.is_empty());
        assert!(
            !constrain(&mut facts.clone(), value, &wanted, true),
            "a captured old scrutinee is unchanged by a write"
        );
        let mut joined = facts.clone();
        join(&mut joined, &Facts::default());
        assert!(
            joined.excluded_values.is_empty(),
            "every incoming path must justify an exclusion"
        );
        invalidate(&mut facts);
        assert!(facts.excluded_memory.is_empty());
    }

    fn pruned(source: &str) -> Vec<u128> {
        let program = crate::parse_program(source).unwrap();
        let declarations = crate::typecheck::resolve_program_for_analysis(&program, false).unwrap();
        let body = &declarations.bodies["work"];
        let mut flow = FlowGraph::lower(body).unwrap();
        flow.prune_impossible_variant_patterns(body);
        let mut result = flow
            .variant_pruned_edges
            .keys()
            .filter_map(|event| {
                let FlowAction::Pattern { pattern, .. } = flow.nodes[event.0].action else {
                    return None;
                };
                match scalar_pattern_value(body, pattern) {
                    Some(crate::Expr::UnsignedInteger(value)) => Some(value),
                    _ => None,
                }
            })
            .collect::<Vec<_>>();
        result.sort_unstable();
        result
    }

    #[test]
    fn selected_patterns_refine_fresh_parameter_reads_only() {
        let source = "(#struct State () ((pc #u64)))
          (#fn work ((view (#ref-mut State))) #u64
            (#return (#match (#get view pc)
              (#case 1 (#match (#get view pc) (#case 0 0u64) (#case _ 42u64)))
              (#case _ 0u64))))";
        assert_eq!(pruned(source), vec![0]);
        let mutated = "(#struct State () ((pc #u64)))
          (#fn work ((view (#ref-mut State))) #u64
            (#return (#match (#get view pc)
              (#case 1 (#when (#block
                (#deref-set view (#struct-literal State ((pc 0u64)))) true))
                (#match (#get view pc) (#case 0 42u64) (#case 1 0u64) (#case _ 0u64)))
              (#case _ 0u64))))";
        assert_eq!(
            pruned(mutated),
            vec![1],
            "a guard write invalidates the old physical-read refinement"
        );
    }

    #[test]
    fn a_selected_alias_does_not_refine_every_possible_referent() {
        let source = "(#struct State () ((pc #u64)))
          (#fn work ((condition #bool)) #u64
            (#let left State (#struct-literal State ((pc 0u64))))
            (#let right State (#struct-literal State ((pc 1u64))))
            (#let view (#ref State) (#if condition (#borrow left) (#borrow right)))
            (#return (#match (#get view pc)
              (#case 1 (#match (#get left pc) (#case 0 42u64) (#case 1 0u64) (#case _ 0u64)))
              (#case _ 0u64))))";
        assert_eq!(pruned(source), vec![1]);
    }

    #[test]
    fn loop_widening_activates_later_pattern_edges_before_pruning() {
        let source = "(#fn work ((condition #bool)) #u64
          (#let-mut selector #u64 0u64)
          (#while condition (#match selector
            (#case 0 (#block (#set selector 1u64) ()))
            (#case 1 (#block (#set selector 2u64) ()))
            (#case _ ())))
          (#return (#match selector (#case 0 40u64) (#case 1 41u64)
            (#case 2 42u64) (#case 99 0u64) (#case _ 0u64))))";
        assert_eq!(pruned(source), vec![99]);
    }

    #[test]
    fn forward_owned_fields_and_loop_writes_join_every_reaching_value() {
        let source = "(#struct State () ((pc #u64)))
          (#fn work ((condition #bool)) #u64
            (#let-mut state State (#struct-literal State ((pc 0u64))))
            (#while condition (#set state (#struct-literal State ((pc 1u64)))))
            (#return (#match (#get state pc)
              (#case 0 40u64) (#case 1 42u64) (#case 2 41u64) (#case _ 0u64))))";
        assert_eq!(pruned(source), vec![2]);
        assert_eq!(
            pruned(&source.replace("((pc 1u64))", "((pc (#if condition 1u64 2u64)))")),
            vec![]
        );
    }

    #[test]
    fn guard_writes_do_not_change_the_captured_scrutinee() {
        let source = "(#fn work () #u64
          (#let-mut selector #u64 1u64)
          (#return (#match selector
            (#case 1 (#when (#block (#set selector 0u64) false)) 0u64)
            (#case 0 0u64) (#case _ 42u64))))";
        assert_eq!(pruned(source), vec![0]);
    }

    #[test]
    fn checked_call_postconditions_replace_facts_but_assembly_invalidates_them() {
        let prefix = "(#struct State () ((pc #u64)))
          (#fn change ((target (#ref-mut State))) ()
            (#deref-set target (#struct-literal State ((pc 0u64)))) (#return ()))";
        for (write, expected) in [
            ("(#call change ((target (#borrow-mut state))))", vec![1]),
            ("(#unsafe (#asm () ((rdi (#ref-ptr (#borrow-mut state)))) \"mov QWORD PTR [rdi], 0\"))", vec![]),
        ] {
            let source = format!(
                "{prefix} (#fn work () #u64
              (#let-mut state State (#struct-literal State ((pc 1u64)))) {write}
              (#return (#match (#get state pc) (#case 0 0u64) (#case 1 42u64) (#case _ 0u64))))"
            );
            assert_eq!(pruned(&source), expected, "{source}");
        }
    }

    #[test]
    fn complete_scalar_mutation_footprints_preserve_only_disjoint_fields() {
        let prefix = "(#struct State () ((pc #u64) (other #u64) (words (#array #u64 1))))
          (#fn erase ((target (#ref-mut #u64))) () (#deref-set target 0u64) (#return ()))
          (#fn forward ((target (#ref-mut #u64))) ()
            (#call erase ((target target))) (#return ()))";
        let source = |effect: &str| {
            format!(
                "{prefix}
          (#fn work ((condition #bool)) #u64
            (#let-mut state State (#struct-literal State
              ((pc 1u64) (other 9u64) (words (#array-repeat 0u64)))))
            {effect}
            (#return (#match (#get state pc) (#case 0 0u64) (#case 1 42u64) (#case _ 0u64))))"
            )
        };
        for effect in [
            "(#call forward ((target (#borrow-mut (#get state other)))))",
            "(#unsafe (#word-write #u64 (#borrow-slice-mut (#get state words)) 9u64))",
        ] {
            assert_eq!(pruned(&source(effect)), vec![0], "{effect}");
        }
        for (effect, expected) in [
            (
                "(#call forward ((target (#borrow-mut (#get state pc)))))",
                vec![1],
            ),
            (
                "(#call forward ((target (#if condition
              (#borrow-mut (#get state pc)) (#borrow-mut (#get state other))))))",
                vec![],
            ),
        ] {
            assert_eq!(pruned(&source(effect)), expected, "{effect}");
        }
    }

    #[test]
    fn resolved_reference_writes_update_only_the_actual_owned_place() {
        for setup in [
            "(#let view (#ref-mut State) (#borrow-mut state))
             (#deref-set view (#struct-literal State ((pc 1u64))))",
            "(#let view (#pin-ref-mut State) (#pin state)) (#pin-set-field view pc 1u64)",
        ] {
            let source = format!(
                "(#struct State () ((pc #u64)))
              (#fn work () #u64
                (#let-mut state State (#struct-literal State ((pc 0u64)))) {setup}
                (#return (#match (#get view pc)
                  (#case 0 0u64) (#case 1 42u64) (#case 2 2u64) (#case _ 3u64))))"
            );
            assert_eq!(pruned(&source), vec![0, 2], "{source}");
        }
        let ambiguous = "(#struct State () ((pc #u64)))
          (#fn work ((condition #bool)) #u64
            (#let-mut left State (#struct-literal State ((pc 0u64))))
            (#let-mut right State (#struct-literal State ((pc 0u64))))
            (#let view (#ref-mut State) (#if condition (#borrow-mut left) (#borrow-mut right)))
            (#deref-set view (#struct-literal State ((pc 1u64))))
            (#return (#match (#get view pc) (#case 0 0u64) (#case 1 42u64) (#case _ 2u64))))";
        assert!(
            pruned(ambiguous).is_empty(),
            "an abstract alias cannot strongly update both owners"
        );
    }

    #[test]
    fn entry_scalar_assumptions_are_distinct_from_later_parameter_writes() {
        for reference in ["#ref-mut", "#pin-ref-mut"] {
            let source = format!(
                "(#struct State () ((pc #u64)))
              (#fn work ((view ({reference} State))) #u64
                (#return (#match (#get view pc) (#case 0 0u64)
                  (#case 1 42u64) (#case _ 2u64))))"
            );
            let program = crate::parse_program(&source).unwrap();
            let declarations =
                crate::typecheck::resolve_program_for_analysis(&program, false).unwrap();
            let body = &declarations.bodies["work"];
            let flow = FlowGraph::lower(body).unwrap();
            let origins = flow.loan_origins(body);
            let pc = body
                .nodes
                .iter()
                .find_map(|node| match node.kind {
                    NodeKind::Declaration(DeclarationId::Field(field)) => Some(field),
                    _ => None,
                })
                .unwrap();
            let place = Place {
                root: PlaceRoot::Parameter(BindingId(0)),
                segments: vec![Segment::Field(pc)],
            };
            let seeded = analyze_with_entry(
                &flow,
                body,
                &origins,
                HashMap::from([(place, vec![crate::Expr::UnsignedInteger(1)])]),
            );
            let unknown = analyze(&flow, body, &origins);
            let mut count = 0;
            for (index, node) in flow.nodes.iter().enumerate() {
                if let FlowAction::Pattern { pattern, value } = node.action {
                    if let Some(wanted) = scalar_pattern_value(body, pattern) {
                        assert!(!unknown.excludes(FlowNodeId(index), value, &wanted));
                        if wanted == crate::Expr::UnsignedInteger(0) {
                            assert!(
                                seeded.excludes(FlowNodeId(index), value, &wanted),
                                "{reference}"
                            );
                            count += 1;
                        }
                    }
                }
            }
            assert_eq!(count, 1);

            let write = if reference == "#pin-ref-mut" {
                "(#pin-set-field view pc 2u64)"
            } else {
                "(#deref-set view (#struct-literal State ((pc 2u64))))"
            };
            let written = source.replace("(#return", &format!("{write} (#return"));
            let program = crate::parse_program(&written).unwrap();
            let declarations =
                crate::typecheck::resolve_program_for_analysis(&program, false).unwrap();
            let body = &declarations.bodies["work"];
            let flow = FlowGraph::lower(body).unwrap();
            let origins = flow.loan_origins(body);
            let entry = Place {
                root: PlaceRoot::Parameter(BindingId(0)),
                segments: vec![Segment::Field(pc)],
            };
            let facts = analyze_with_entry(
                &flow,
                body,
                &origins,
                HashMap::from([(entry, vec![crate::Expr::UnsignedInteger(1)])]),
            );
            for (index, node) in flow.nodes.iter().enumerate() {
                if let FlowAction::Pattern { pattern, value } = node.action {
                    if let Some(wanted) = scalar_pattern_value(body, pattern) {
                        assert!(
                            facts.excludes(FlowNodeId(index), value, &wanted),
                            "an entry value cannot override a subsequent store: {reference}"
                        );
                    }
                }
            }
        }
    }
}
