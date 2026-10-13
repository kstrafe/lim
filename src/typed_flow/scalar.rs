//! Bounded scalar facts over ordinary control flow. These facts describe
//! values, never ownership, initialized references, or permission to read.
use super::*;

type Values = Vec<crate::Expr>;
type Shape = HashMap<Vec<Segment>, Values>;

#[derive(Clone, Default, PartialEq)]
struct Facts {
    memory: HashMap<Place, Values>,
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
    if let Some(place) = Place::from_expression(body, value) {
        if reads_through_reference(body, value) {
            if let Some(places) = physical_write_places(body, origins, event, &place) {
                return read_shape(facts, &places);
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
    facts.reads.clear();
}

/// Narrow a copied scrutinee, not a newly evaluated read. A guard may have
/// changed the original variable; only a still-fresh singleton address can
/// receive the same refinement. Missing bounds on failure stay unknown.
fn constrain(facts: &mut Facts, value: NodeId, wanted: &crate::Expr, success: bool) -> bool {
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

pub(super) fn analyze(flow: &FlowGraph, body: &Body, origins: &FlowLoanOrigins) -> Analysis {
    analyze_with_entry(flow, body, origins, HashMap::new())
}

fn analyze_with_entry(
    flow: &FlowGraph,
    body: &Body,
    origins: &FlowLoanOrigins,
    memory: HashMap<Place, Values>,
) -> Analysis {
    let mut before = vec![None; flow.nodes.len()];
    if !flow.nodes.iter().any(|node| {
        matches!(node.action,
        FlowAction::Pattern { pattern, .. } if scalar_pattern_value(body, pattern).is_some())
    }) {
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
        let mut facts = before[event.0].clone().unwrap();
        match &flow.nodes[event.0].action {
            FlowAction::Evaluate(value)
            | FlowAction::Read { value, .. }
            | FlowAction::Clone { value, .. } => {
                let shape = evaluate(&facts, body, origins, event, *value);
                facts.values.remove(value);
                facts.reads.remove(value);
                if let Some(place) = read_place(body, origins, event, *value) {
                    facts.reads.insert(*value, place);
                }
                if !shape.is_empty() {
                    facts.values.insert(*value, shape);
                }
                if matches!(
                    &body.nodes[value.0].kind,
                    NodeKind::Form {
                        callee: Some(_),
                        ..
                    }
                ) || matches!(flow.nodes[event.0].action, FlowAction::Clone { .. })
                    || matches!(&body.nodes[value.0].kind, NodeKind::Form { head, .. }
                        if matches!(head.as_str(), "ptr-write" | "linux-syscall" | "asm" | "pin-read" | "word-write" | "pin-write" | "pin-set-field" | "deref-set")
                            || head.starts_with("atomic-"))
                {
                    invalidate(&mut facts);
                }
                // word-take/word-forget retire loan metadata, not bytes.
                // This analysis never tracks their typed restored contents.
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
                } else {
                    write(&mut facts, place, incoming);
                }
            }
            FlowAction::Write { place, value } => {
                let source = match &body.nodes[value.0].kind {
                    NodeKind::Form { head, children, .. } if head == "pin-set-field" => {
                        children.get(3)
                    }
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
                facts.reads.retain(|_, source| !place.overlaps(source));
            }
            FlowAction::ScopeExit(bindings) => {
                facts.memory.retain(|place, _| !matches!(place.root, PlaceRoot::Local(binding) if bindings.contains(&binding)));
                facts.reads.retain(|_, place| !matches!(place.root, PlaceRoot::Local(binding) if bindings.contains(&binding)));
            }
            _ => {}
        }
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
        let source = "(#struct State (: pc #u64))
          (#fn work (: view (#ref-mut State)) #u64
            (#return (#match (#get view pc)
              (#case 1 (#match (#get view pc) (#case 0 0u64) (#case _ 42u64)))
              (#case _ 0u64))))";
        assert_eq!(pruned(source), vec![0]);
        let mutated = "(#struct State (: pc #u64))
          (#fn work (: view (#ref-mut State)) #u64
            (#return (#match (#get view pc)
              (#case 1 (#when (#block
                (#deref-set view (#struct-literal State (: pc 0u64))) true))
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
        let source = "(#struct State (: pc #u64))
          (#fn work (: condition #bool) #u64
            (#let left State (#struct-literal State (: pc 0u64)))
            (#let right State (#struct-literal State (: pc 1u64)))
            (#let view (#ref State) (#if condition (#borrow left) (#borrow right)))
            (#return (#match (#get view pc)
              (#case 1 (#match (#get left pc) (#case 0 42u64) (#case 1 0u64) (#case _ 0u64)))
              (#case _ 0u64))))";
        assert_eq!(pruned(source), vec![1]);
    }

    #[test]
    fn loop_widening_activates_later_pattern_edges_before_pruning() {
        let source = "(#fn work (: condition #bool) #u64
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
        let source = "(#struct State (: pc #u64))
          (#fn work (: condition #bool) #u64
            (#let-mut state State (#struct-literal State (: pc 0u64)))
            (#while condition (#set state (#struct-literal State (: pc 1u64))))
            (#return (#match (#get state pc)
              (#case 0 40u64) (#case 1 42u64) (#case 2 41u64) (#case _ 0u64))))";
        assert_eq!(pruned(source), vec![2]);
        assert_eq!(
            pruned(&source.replace("(: pc 1u64)", "(: pc (#if condition 1u64 2u64))")),
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
    fn unknown_calls_and_assembly_do_not_preserve_live_field_facts() {
        let prefix = "(#struct State (: pc #u64))
          (#fn change (: target (#ref-mut State)) ()
            (#deref-set target (#struct-literal State (: pc 0u64))) (#return ()))";
        for write in [
            "(#call change (: target (#borrow-mut state)))",
            "(#unsafe (#asm () ((rdi (#ref-ptr (#borrow-mut state)))) \"mov QWORD PTR [rdi], 0\"))",
        ] {
            let source = format!(
                "{prefix} (#fn work () #u64
              (#let-mut state State (#struct-literal State (: pc 1u64))) {write}
              (#return (#match (#get state pc) (#case 0 0u64) (#case 1 42u64) (#case _ 0u64))))"
            );
            assert!(pruned(&source).is_empty(), "{source}");
        }
    }

    #[test]
    fn resolved_reference_writes_update_only_the_actual_owned_place() {
        for setup in [
            "(#let view (#ref-mut State) (#borrow-mut state))
             (#deref-set view (#struct-literal State (: pc 1u64)))",
            "(#let view (#pin-ref-mut State) (#pin state)) (#pin-set-field view pc 1u64)",
        ] {
            let source = format!(
                "(#struct State (: pc #u64))
              (#fn work () #u64
                (#let-mut state State (#struct-literal State (: pc 0u64))) {setup}
                (#return (#match (#get view pc)
                  (#case 0 0u64) (#case 1 42u64) (#case 2 2u64) (#case _ 3u64))))"
            );
            assert_eq!(pruned(&source), vec![0, 2], "{source}");
        }
        let ambiguous = "(#struct State (: pc #u64))
          (#fn work (: condition #bool) #u64
            (#let-mut left State (#struct-literal State (: pc 0u64)))
            (#let-mut right State (#struct-literal State (: pc 0u64)))
            (#let view (#ref-mut State) (#if condition (#borrow-mut left) (#borrow-mut right)))
            (#deref-set view (#struct-literal State (: pc 1u64)))
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
                "(#struct State (: pc #u64))
              (#fn work (: view ({reference} State)) #u64
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
                "(#deref-set view (#struct-literal State (: pc 2u64)))"
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
