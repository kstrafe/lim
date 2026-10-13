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
}

pub(super) struct Analysis {
    before: Vec<Option<Facts>>,
}

impl Analysis {
    pub(super) fn excludes(&self, event: FlowNodeId, value: NodeId, wanted: &crate::Expr) -> bool {
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

fn evaluate(facts: &Facts, body: &Body, value: NodeId) -> Shape {
    if let Some(literal) = scalar_pattern_value(body, value) {
        return HashMap::from([(Vec::new(), vec![literal])]);
    }
    // Only owned places are read here. Reference/atomic/heap projections stay
    // unknown until their physical identity and mutation rules are modeled.
    if !reads_through_reference(body, value) {
        if let Some(place) = Place::from_expression(body, value) {
            if matches!(place.root, PlaceRoot::Local(_)) {
                return stored_shape(facts, &place);
            }
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

pub(super) fn analyze(flow: &FlowGraph, body: &Body) -> Analysis {
    let mut before = vec![None; flow.nodes.len()];
    if !flow.nodes.iter().any(|node| {
        matches!(node.action,
        FlowAction::Pattern { pattern, .. } if scalar_pattern_value(body, pattern).is_some())
    }) {
        return Analysis { before };
    }
    before[flow.entry.0] = Some(Facts::default());
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
                let shape = evaluate(&facts, body, *value);
                facts.values.remove(value);
                if !shape.is_empty() {
                    facts.values.insert(*value, shape);
                }
                if matches!(
                    &body.nodes[value.0].kind,
                    NodeKind::Form {
                        callee: Some(_),
                        ..
                    }
                ) || matches!(&body.nodes[value.0].kind, NodeKind::Form { head, .. }
                        if matches!(head.as_str(), "ptr-write" | "linux-syscall" | "asm" | "pin-read" | "word-write" | "pin-write" | "pin-set-field" | "deref-set")
                            || head.starts_with("atomic-"))
                {
                    facts.memory.clear();
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
                    facts.memory.clear();
                } else {
                    write(&mut facts, place, incoming);
                }
            }
            FlowAction::Write { .. } => facts.memory.clear(),
            FlowAction::Release { place, .. } => {
                facts.memory.retain(|source, _| !place.overlaps(source));
            }
            FlowAction::ScopeExit(bindings) => {
                facts.memory.retain(|place, _| !matches!(place.root, PlaceRoot::Local(binding) if bindings.contains(&binding)));
            }
            _ => {}
        }
        // Solve the restored graph before pruning. A loop can widen an early
        // constant to unknown; early observations must not erase its backedge.
        for next in &flow.nodes[event.0].successors {
            let changed = if let Some(held) = &mut before[next.0] {
                join(held, &facts)
            } else {
                before[next.0] = Some(facts.clone());
                true
            };
            if changed && !queued[next.0] {
                queued[next.0] = true;
                pending.push_back(*next);
            }
        }
    }
    Analysis { before }
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
    fn unknown_calls_and_aliased_writes_do_not_preserve_live_field_facts() {
        let prefix = "(#struct State (: pc #u64))
          (#fn change (: target (#ref-mut State)) ()
            (#deref-set target (#struct-literal State (: pc 0u64))) (#return ()))";
        for write in [
            "(#call change (: target (#borrow-mut state)))",
            "(#deref-set (#borrow-mut state) (#struct-literal State (: pc 0u64)))",
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
}
