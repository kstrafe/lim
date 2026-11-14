//! Bounded context graphs for scalar entry assumptions. The ordinary loan
//! solver runs on the resulting paths; scalar facts never supply a loan.
use super::*;

// Bound history alternatives within each proven scalar dispatch state. Unknown
// and multi-valued selectors share one bucket; no feasible path is discarded.
const STATES_PER_DISPATCH: usize = 16;

#[derive(Clone, PartialEq)]
struct Context {
    scalar: Facts,
    // Last strong storage effect at each exact backing cell. Equal numeric
    // state alone must not merge an entry cell with a written/retired cell.
    words: HashMap<Place, FlowNodeId>,
    // A weak effect may initialize or retire a cell. May-origin unions do
    // not prove it remains initialized; relevant readers require a later
    // definite replacement or abandon this entire specialization.
    uncertain: HashSet<Place>,
    // Separate histories across opaque effects. Neither this discriminator
    // nor a storage epoch supplies initialized contents or a loan capability.
    opaque: Option<FlowNodeId>,
}

/// Snapshots are needed until their next use, not for the entire invocation.
/// Ordinary backwards liveness removes only snapshots overwritten before any
/// possible use. Physical memory and word epochs remain separate and intact.
fn snapshot_liveness(flow: &FlowGraph, body: &Body) -> Vec<HashSet<NodeId>> {
    let mut used = vec![HashSet::new(); flow.nodes.len()];
    let mut defined = vec![None; flow.nodes.len()];
    for (index, node) in flow.nodes.iter().enumerate() {
        match &node.action {
            FlowAction::Evaluate(value)
            | FlowAction::Read { value, .. }
            | FlowAction::Borrow { value, .. }
            | FlowAction::Clone { value, .. } => {
                defined[index] = Some(*value);
                if let NodeKind::Form { children, .. } = &body.nodes[value.0].kind {
                    used[index].extend(children.iter().copied());
                }
            }
            FlowAction::Bind { value, .. }
            | FlowAction::Assign { value, .. }
            | FlowAction::Pattern { value, .. } => {
                used[index].insert(*value);
            }
            FlowAction::Write { value, .. } => {
                if let NodeKind::Form { children, .. } = &body.nodes[value.0].kind {
                    used[index].extend(children.iter().copied());
                }
            }
            FlowAction::Branch(pattern) => {
                used[index].insert(*pattern);
                if let Some(success) = node.successors.first() {
                    if let FlowAction::Pattern { value, .. } = flow.nodes[success.0].action {
                        used[index].insert(value);
                    }
                }
            }
            FlowAction::Return(Some(value))
            | FlowAction::Break {
                value: Some(value), ..
            } => {
                // Return summaries can recursively inspect stable aggregate
                // constructors and unsafe wrappers, not only the outer value.
                let mut pending = vec![*value];
                while let Some(value) = pending.pop() {
                    if used[index].insert(value) {
                        if let NodeKind::Form { children, .. } = &body.nodes[value.0].kind {
                            pending.extend(children.iter().copied());
                        }
                    }
                }
            }
            _ => {}
        }
    }
    let candidates = defined
        .iter()
        .flatten()
        .copied()
        .filter(|value| scalar_pattern_value(body, *value).is_none())
        .collect::<HashSet<_>>();
    for values in &mut used {
        values.retain(|value| candidates.contains(value));
    }
    let mut predecessors = vec![Vec::new(); flow.nodes.len()];
    for (index, node) in flow.nodes.iter().enumerate() {
        for next in &node.successors {
            predecessors[next.0].push(index);
        }
    }
    let mut live = used;
    let mut pending = (0..flow.nodes.len()).collect::<VecDeque<_>>();
    let mut queued = vec![true; flow.nodes.len()];
    while let Some(index) = pending.pop_front() {
        queued[index] = false;
        for &previous in &predecessors[index] {
            let additions = live[index]
                .iter()
                .filter(|value| Some(**value) != defined[previous])
                .copied()
                .collect::<Vec<_>>();
            let count = live[previous].len();
            live[previous].extend(additions);
            if live[previous].len() != count && !queued[previous] {
                queued[previous] = true;
                pending.push_back(previous);
            }
        }
    }
    live
}

fn word_effects(
    flow: &FlowGraph,
    body: &Body,
    origins: &FlowLoanOrigins,
    event: FlowNodeId,
    words: &mut HashMap<Place, FlowNodeId>,
    uncertain: &mut HashSet<Place>,
) -> Option<()> {
    if let FlowAction::Assign { place, .. } | FlowAction::Write { place, .. } =
        &flow.nodes[event.0].action
    {
        let indirect_assignment = matches!(flow.nodes[event.0].action, FlowAction::Assign { .. })
            && (!place.segments.is_empty()
                && matches!(place.root, PlaceRoot::Local(binding)
                    if matches!(body.bindings[binding.0].ty,
                        Type::Reference { .. } | Type::PinnedReference { .. }))
                || place.segments.contains(&Segment::Dereference));
        let targets = if matches!(flow.nodes[event.0].action, FlowAction::Assign { .. })
            && !indirect_assignment
        {
            vec![place.clone()]
        } else {
            physical_write_places(body, origins, event, place)?
        };
        if targets.len() != 1 {
            return None;
        }
        let target = &targets[0];
        if !matches!(target.root, PlaceRoot::Local(_) | PlaceRoot::Parameter(_))
            || target.segments.iter().any(|part| {
                matches!(
                    part,
                    Segment::DynamicIndex | Segment::SliceDynamicIndex | Segment::SliceRangeUnknown
                )
            })
        {
            return None;
        }
        words.retain(|held, _| !held.overlaps(target));
        words.insert(target.clone(), event);
        uncertain.retain(|held| !place_covers(target, held));
    }
    let value = match flow.nodes[event.0].action {
        FlowAction::Evaluate(value) | FlowAction::Write { value, .. } => value,
        _ => return Some(()),
    };
    let NodeKind::Form { head, .. } = &body.nodes[value.0].kind else {
        return Some(());
    };
    let word_op = matches!(head.as_str(), "word-write" | "word-take" | "word-forget");
    let call = matches!(
        body.nodes[value.0].kind,
        NodeKind::Form {
            callee: Some(_),
            ..
        }
    );
    if !word_op && !call {
        return Some(());
    }
    let stores = origins.stores_before(body, flow, event);
    if word_op
        && stores.is_empty()
        && body
            .word_layouts
            .get(&value)
            .is_some_and(|layout| layout.words != 0)
    {
        return None;
    }
    for store in stores {
        let place = store.destination.referent_place();
        if store.destination.lifetime_only
            || !matches!(place.root, PlaceRoot::Local(_) | PlaceRoot::Parameter(_))
            || place.segments.iter().any(|part| {
                matches!(
                    part,
                    Segment::DynamicIndex | Segment::SliceDynamicIndex | Segment::SliceRangeUnknown
                )
            })
        {
            return None;
        }
        words.retain(|held, _| !held.overlaps(&place));
        // A definite metadata retirement leaves no initialized word loan to
        // distinguish. The ordinary solver still executes the retirement;
        // byte writes and weak effects retain their separate histories.
        if !store.definitely_written || !store.preserves_bytes {
            words.insert(place.clone(), event);
        }
        if store.definitely_written {
            uncertain.retain(|held| !place_covers(&place, held));
        } else {
            uncertain.insert(place);
        }
    }
    Some(())
}

fn reads_uncertain_words(
    flow: &FlowGraph,
    body: &Body,
    origins: &FlowLoanOrigins,
    event: FlowNodeId,
    uncertain: &HashSet<Place>,
) -> Option<bool> {
    if uncertain.is_empty() {
        return Some(false);
    }
    let FlowAction::Evaluate(value) = flow.nodes[event.0].action else {
        return Some(false);
    };
    let NodeKind::Form {
        head,
        children,
        callee,
        ..
    } = &body.nodes[value.0].kind
    else {
        return Some(false);
    };
    let affected = |place: &Place| uncertain.iter().any(|held| held.overlaps(place));
    if callee.is_none()
        && !matches!(head.as_str(), "word-write" | "word-forget")
        && body
            .word_layouts
            .get(&value)
            .is_some_and(|layout| !layout.slots.is_empty())
    {
        let address = *children.get(2)?;
        let addresses = origins
            .value_before(body, flow, event, address)
            .into_iter()
            .filter(|origin| origin.storage.is_empty())
            .collect::<Vec<_>>();
        if addresses.is_empty() || addresses.iter().any(|origin| origin.lifetime_only) {
            return None;
        }
        if addresses
            .iter()
            .any(|origin| affected(&origin.referent_place()))
        {
            return Some(true);
        }
    }
    if let Some(callee) = callee {
        for requirement in body
            .call_word_input_requirements
            .get(callee)
            .into_iter()
            .flatten()
        {
            if requirement.unresolved {
                return None;
            }
            let argument = *children.get(requirement.parameter + 1)?;
            let dereferences = requirement
                .input_storage
                .iter()
                .filter(|part| **part == Segment::Dereference)
                .count();
            let mut places = Vec::new();
            if dereferences == 0 {
                let base = Place::from_expression(body, argument)?;
                let bases = if reads_through_reference(body, argument) {
                    physical_write_places(body, origins, event, &base)?
                } else {
                    vec![base]
                };
                for mut base in bases {
                    base.segments
                        .extend(requirement.input_storage.iter().cloned());
                    places.push(base);
                }
            } else if dereferences == 1 {
                let boundary = requirement
                    .input_storage
                    .iter()
                    .position(|part| *part == Segment::Dereference)?;
                for origin in origins
                    .value_before(body, flow, event, argument)
                    .into_iter()
                    .filter(|origin| origin.storage == requirement.input_storage[..boundary])
                {
                    if origin.lifetime_only {
                        return None;
                    }
                    let mut place = origin.referent_place();
                    place
                        .segments
                        .extend(requirement.input_storage[boundary + 1..].iter().cloned());
                    places.push(place);
                }
            } else {
                return None;
            }
            if places.is_empty() {
                return None;
            }
            if places.iter().any(affected) {
                return Some(true);
            }
        }
    }
    Some(false)
}

/// Build a separate analysis graph without changing runtime code or the base
/// graph. The caller must retain and prove the entry assumptions at each use.
/// If state separation exceeds the bound, discard the entire result: a partial
/// graph could omit a feasible reader and must never be used as a contract.
pub(in super::super) fn specialize(
    flow: &FlowGraph,
    body: &Body,
    origins: &FlowLoanOrigins,
    entry: &[(Place, crate::Expr)],
) -> Option<FlowGraph> {
    specialize_impl(flow, body, origins, entry, &[], false)
}

pub(in super::super) fn specialize_for_calls(
    flow: &FlowGraph,
    body: &Body,
    origins: &FlowLoanOrigins,
) -> Option<FlowGraph> {
    specialize_impl(flow, body, origins, &[], &[], true)
}

pub(in super::super) fn specialize_excluding(
    flow: &FlowGraph,
    body: &Body,
    origins: &FlowLoanOrigins,
    excluding: &[(Place, Values)],
) -> Option<FlowGraph> {
    specialize_impl(flow, body, origins, &[], excluding, false)
}

fn specialize_impl(
    flow: &FlowGraph,
    body: &Body,
    origins: &FlowLoanOrigins,
    entry: &[(Place, crate::Expr)],
    excluding: &[(Place, Values)],
    checking_calls: bool,
) -> Option<FlowGraph> {
    let mut memory = HashMap::new();
    if excluding.iter().any(|(place, values)| {
        !matches!(place.root, PlaceRoot::Local(_) | PlaceRoot::Parameter(_))
            || place.segments.iter().any(|part| {
                matches!(
                    part,
                    Segment::DynamicIndex | Segment::SliceDynamicIndex | Segment::SliceRangeUnknown
                )
            })
            || values.is_empty()
            || values.len() > 16
            || values
                .iter()
                .any(|value| !matches!(value, crate::Expr::UnsignedInteger(_)))
    }) {
        return None;
    }
    for (place, value) in entry {
        if !matches!(place.root, PlaceRoot::Local(_) | PlaceRoot::Parameter(_))
            || place.segments.iter().any(|part| {
                matches!(
                    part,
                    Segment::DynamicIndex | Segment::SliceDynamicIndex | Segment::SliceRangeUnknown
                )
            })
        {
            return None;
        }
        let value = match value {
            crate::Expr::Integer(value) if *value >= 0 => {
                crate::Expr::UnsignedInteger(*value as u128)
            }
            crate::Expr::Integer(_) | crate::Expr::UnsignedInteger(_) | crate::Expr::Char(_) => {
                value.clone()
            }
            crate::Expr::Symbol(name) if matches!(name.as_str(), "true" | "false") => value.clone(),
            _ => return None,
        };
        if memory.insert(place.clone(), vec![value]).is_some() {
            return None;
        }
    }
    let initial = Context {
        scalar: Facts {
            memory,
            excluded_memory: excluding.iter().cloned().collect(),
            ..Facts::default()
        },
        words: HashMap::new(),
        uncertain: HashSet::new(),
        opaque: None,
    };
    // Keep one common normal exit for every state. Must-store guarantees are
    // intersected there by the ordinary solver, not chosen from one outcome.
    let mut result = FlowGraph {
        nodes: vec![
            flow.nodes[flow.exit.0].clone(),
            FlowNode {
                action: FlowAction::Diverge,
                successors: Vec::new(),
                span: None,
            },
        ],
        entry: FlowNodeId(2),
        exit: FlowNodeId(0),
        variant_pruned_edges: HashMap::new(),
    };
    result.nodes[0].successors.clear();
    let dead = FlowNodeId(1);
    let mut states: Vec<Vec<(Context, FlowNodeId)>> = vec![Vec::new(); flow.nodes.len()];
    let live_snapshots = snapshot_liveness(flow, body);
    let partition = entry_partition(flow, body, origins);
    let dispatch = |facts: &Context| {
        let (place, choices) = partition.as_ref()?;
        let values = facts.scalar.memory.get(place)?;
        let [crate::Expr::UnsignedInteger(value)] = values.as_slice() else {
            return None;
        };
        choices.contains(value).then_some(*value)
    };
    let mut pending = VecDeque::new();
    let mut intern =
        |event: FlowNodeId,
         mut facts: Context,
         result: &mut FlowGraph,
         pending: &mut VecDeque<(FlowNodeId, Context, FlowNodeId)>| {
            if event == flow.exit {
                return Some(result.exit);
            }
            facts
                .scalar
                .values
                .retain(|value, _| live_snapshots[event.0].contains(value));
            facts
                .scalar
                .reads
                .retain(|value, _| live_snapshots[event.0].contains(value));
            facts
                .scalar
                .excluded_values
                .retain(|value, _| live_snapshots[event.0].contains(value));
            if let Some((_, id)) = states[event.0].iter().find(|(held, _)| held == &facts) {
                return Some(*id);
            }
            let key = dispatch(&facts);
            if states[event.0]
                .iter()
                .filter(|(held, _)| dispatch(held) == key)
                .count()
                == STATES_PER_DISPATCH
            {
                return None;
            }
            let id = FlowNodeId(result.nodes.len());
            let mut node = flow.nodes[event.0].clone();
            node.successors.clear();
            result.nodes.push(node);
            states[event.0].push((facts.clone(), id));
            pending.push_back((event, facts, id));
            Some(id)
        };
    result.entry = intern(flow.entry, initial, &mut result, &mut pending)?;
    while let Some((event, before, copied)) = pending.pop_front() {
        let call = matches!(flow.nodes[event.0].action, FlowAction::Evaluate(value)
            if matches!(body.nodes[value.0].kind, NodeKind::Form { callee: Some(_), .. }));
        // Call checking consumes this graph only after checking every call's
        // actual inputs. Do not abandon separation merely because the base
        // may-store summary could not prove a call input before separation.
        if !(checking_calls && call)
            && reads_uncertain_words(flow, body, origins, event, &before.uncertain)?
        {
            return None;
        }
        let mut words = before.words;
        let mut uncertain = before.uncertain;
        let mut opaque = before.opaque;
        if matches!(flow.nodes[event.0].action, FlowAction::Clone { value, .. } if !scalar_clone_is_pure(body, value))
            || matches!(flow.nodes[event.0].action, FlowAction::Evaluate(value)
                if matches!(&body.nodes[value.0].kind, NodeKind::Form { callee: Some(_), .. })
                    || matches!(&body.nodes[value.0].kind, NodeKind::Form { head, .. }
                        if matches!(head.as_str(), "ptr-write" | "linux-syscall" | "asm" | "pin-read") || head.starts_with("atomic-")))
        {
            opaque = Some(event);
        }
        word_effects(flow, body, origins, event, &mut words, &mut uncertain)?;
        let after = transfer(flow, body, origins, event, before.scalar);
        for (edge, next) in flow.nodes[event.0].successors.iter().enumerate() {
            let destination =
                if let Some(facts) = edge_facts(flow, body, event, edge, after.clone()) {
                    intern(
                        *next,
                        Context {
                            scalar: facts,
                            words: words.clone(),
                            uncertain: uncertain.clone(),
                            opaque,
                        },
                        &mut result,
                        &mut pending,
                    )?
                } else {
                    dead
                };
            // Preserve edge positions. Other ownership passes interpret edge
            // zero as success/true; removing it would relabel a failure edge.
            result.nodes[copied.0].successors.push(destination);
        }
    }
    Some(result)
}

#[cfg(test)]
mod tests {
    use super::*;

    const PHASE_SOURCE: &str = "(#struct Holder () ((value (#ref #u64))))
          (#struct Frame () ((pc #u64) (source (#ref #u64)) (words (#array #u64 1))))
          (#fn work ((frame (#ref-mut Frame))) #u64
            (#loop (#match (#get frame pc)
              (#case 0 (#block
                (#unsafe (#word-write Holder (#borrow-slice-mut (#get frame words))
                  (#struct-literal Holder ((value (#get frame source))))))
                (#deref-set (#borrow-mut (#get frame pc)) 1u64) (#continue) (#unreachable)))
              (#case 1 (#block
                (#let holder Holder (#unsafe (#word-take Holder (#borrow-slice-mut (#get frame words)))))
                (#let answer #u64 (#deref (#get holder value)))
                (#forget holder) (#return answer) (#unreachable)))
              (#case _ (#block (#return 0u64) (#unreachable)))))
            (#return 0u64))";

    #[test]
    fn projected_assignment_epochs_follow_the_physical_referent() {
        let program = crate::parse_program(
            "(#struct Frame () ((pc #u64)))
            (#fn work ((frame (#ref-mut Frame))) ()
              (#let-mut alias (#ref-mut #u64) (#borrow-mut (#get frame pc)))
              (#deref-set alias 1u64) (#return ()))",
        )
        .unwrap();
        let declarations = crate::typecheck::resolve_program_for_analysis(&program, false).unwrap();
        let body = &declarations.bodies["work"];
        let mut flow = FlowGraph::lower(body).unwrap();
        let origins = flow.loan_origins(body);
        let (event, place, value) = flow
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| match &node.action {
                FlowAction::Write { place, value } => {
                    Some((FlowNodeId(index), place.clone(), *value))
                }
                _ => None,
            })
            .unwrap();
        let physical = physical_write_places(body, &origins, event, &place).unwrap();
        assert_eq!(physical.len(), 1);
        assert!(matches!(physical[0].root, PlaceRoot::Parameter(_)));
        flow.nodes[event.0].action = FlowAction::Assign {
            place: place.clone(),
            value,
        };
        let mut epochs = HashMap::new();
        word_effects(
            &flow,
            body,
            &origins,
            event,
            &mut epochs,
            &mut HashSet::new(),
        )
        .unwrap();
        assert_eq!(epochs, HashMap::from([(physical[0].clone(), event)]));

        // Rebinding a reference variable itself is not a pointee write.
        let rebound = Place::root(place.root);
        flow.nodes[event.0].action = FlowAction::Assign {
            place: rebound.clone(),
            value,
        };
        let mut epochs = HashMap::new();
        word_effects(
            &flow,
            body,
            &origins,
            event,
            &mut epochs,
            &mut HashSet::new(),
        )
        .unwrap();
        assert_eq!(epochs, HashMap::from([(rebound, event)]));
    }

    #[test]
    fn phase_context_keeps_real_word_stores_before_a_later_loop_reader() {
        let source = PHASE_SOURCE;
        let program = crate::parse_program(source).unwrap();
        let declarations = crate::typecheck::resolve_program_for_analysis(&program, false).unwrap();
        let body = &declarations.bodies["work"];
        let flow = FlowGraph::lower(body).unwrap();
        let field = body
            .nodes
            .iter()
            .find_map(|node| match node.kind {
                NodeKind::Declaration(DeclarationId::Field(field)) if field.index == 0 => {
                    Some(field)
                }
                _ => None,
            })
            .unwrap();
        let pc = Place {
            root: PlaceRoot::Parameter(BindingId(0)),
            segments: vec![Segment::Field(field)],
        };
        let at_start = flow
            .parameter_summary_at_scalar_entry(
                body,
                &[(pc.clone(), crate::Expr::UnsignedInteger(0))],
            )
            .unwrap();
        assert!(
            at_start.word_inputs.is_empty(),
            "entry PC0 writes before reaching PC1: {:?}",
            at_start.word_inputs
        );
        let at_resume = flow
            .parameter_summary_at_scalar_entry(body, &[(pc, crate::Expr::UnsignedInteger(1))])
            .unwrap();
        assert!(
            !at_resume.word_inputs.is_empty(),
            "entry PC1 must already hold its reference"
        );
        assert!(
            !flow
                .parameter_summary_at_scalar_entry(body, &[])
                .unwrap()
                .word_inputs
                .is_empty(),
            "an unknown entry cannot waive the stored-loan requirement"
        );
    }

    #[test]
    fn overwritten_scalar_snapshots_do_not_spend_the_storage_history_budget() {
        let arguments = (0..5)
            .map(|index| format!(" (flag{index} #bool)"))
            .collect::<String>();
        let choices = (0..5)
            .map(|index| {
                format!(
                    "(#if flag{index} (#block (#set selector {}u64) ()) (#block (#set selector {}u64) ()))",
                    2 * index + 1,
                    2 * index + 2,
                )
            })
            .collect::<String>();
        let source = PHASE_SOURCE
            .replace(
                "((frame (#ref-mut Frame)))",
                &format!("((frame (#ref-mut Frame){arguments}))"),
            )
            .replace(
                "(#loop",
                &format!("(#let-mut selector #u64 0u64) {choices} (#loop"),
            );
        let program = crate::parse_program(&source).unwrap();
        let declarations = crate::typecheck::resolve_program_for_analysis(&program, false).unwrap();
        let body = &declarations.bodies["work"];
        let flow = FlowGraph::lower(body).unwrap();
        assert!(specialize(&flow, body, &flow.loan_origins(body), &[]).is_some());
    }

    #[test]
    fn definite_retirements_do_not_retain_dead_word_epochs() {
        let arguments = (0..5)
            .map(|index| format!(" (flag{index} #bool)"))
            .collect::<String>();
        let choices = (0..5).map(|index| format!(
            "(#if flag{index}
              (#block
                (#unsafe (#word-write Holder (#borrow-slice-mut (#get frame words) {}usize {}usize)
                  (#struct-literal Holder ((value (#get frame source))))))
                (#unsafe (#word-forget Holder (#borrow-slice-mut (#get frame words) {}usize {}usize))))
              (#unsafe (#word-forget Holder (#borrow-slice-mut (#get frame words) {}usize {}usize))))",
            index+1, index+2, index+1, index+2, index+1, index+2)).collect::<String>();
        let source = PHASE_SOURCE
            .replace(
                "((frame (#ref-mut Frame)))",
                &format!("((frame (#ref-mut Frame){arguments}))"),
            )
            .replace("(#array #u64 1)", "(#array #u64 6)")
            .replace("(#loop", &format!("{choices} (#loop"));
        let program = crate::parse_program(&source).unwrap();
        let declarations = crate::typecheck::resolve_program_for_analysis(&program, false).unwrap();
        let body = &declarations.bodies["work"];
        let flow = FlowGraph::lower(body).unwrap();
        let origins = flow.loan_origins(body);
        assert!(specialize(&flow, body, &origins, &[]).is_some());
        assert!(flow
            .parameter_summary(body, false)
            .word_inputs
            .iter()
            .all(|input| !input.unresolved));
    }

    #[test]
    fn specialization_budget_loss_never_discharges_wildcard_entry_slots() {
        let arguments = (0..5)
            .map(|index| format!(" (flag{index} #bool)"))
            .collect::<String>();
        let choices = (0..5)
            .map(|index| {
                format!(
            "(#if flag{index}
              (#unsafe (#word-write #u64 (#borrow-slice-mut (#get frame words) {}usize {}usize) 1u64))
              (#unsafe (#word-forget #u64 (#borrow-slice-mut (#get frame words) {}usize {}usize))))",
            index + 1, index + 2, index + 1, index + 2)
            })
            .collect::<String>();
        let source = PHASE_SOURCE
            .replace(
                "((frame (#ref-mut Frame)))",
                &format!("((frame (#ref-mut Frame){arguments}))"),
            )
            .replace("(#array #u64 1)", "(#array #u64 6)")
            .replace("(#loop", &format!("{choices} (#loop"));
        let program = crate::parse_program(&source).unwrap();
        let declarations = crate::typecheck::resolve_program_for_analysis(&program, false).unwrap();
        let body = &declarations.bodies["work"];
        let flow = FlowGraph::lower(body).unwrap();
        let origins = flow.loan_origins(body);
        let count = flow.nodes.len();
        assert!(
            specialize(&flow, body, &origins, &[]).is_none(),
            "too many contexts must discard the entire product"
        );
        assert_eq!(flow.nodes.len(), count, "the base graph is not mutated");
        let summary = flow.parameter_summary(body, false);
        let unresolved = summary
            .word_inputs
            .iter()
            .filter(|input| input.unresolved)
            .collect::<Vec<_>>();
        assert!(!unresolved.is_empty());
        assert!(
            unresolved
                .iter()
                .all(|input| input.input_storage.is_empty()),
            "proof loss is not represented by a wildcard loan witness"
        );
        for input in unresolved {
            // No set of matching origins can discharge an unproved contract.
            assert!(!word_input_available(
                Vec::new(),
                input,
                &empty_loan_state(body.bindings.len())
            ));
            assert!(!word_requirement_inactive(
                body,
                &flow,
                &origins,
                flow.entry,
                NodeId(0),
                input
            ));
        }
        // A function with no parameters must not silently drop the marker
        // because its unused placeholder parameter has no actual argument.
        let main_program = crate::parse_program("(#fn main () #u64 (#return 0u64))").unwrap();
        let mut main_declarations =
            crate::typecheck::resolve_program_for_analysis(&main_program, false).unwrap();
        let mut main = main_declarations.bodies.remove("main").unwrap();
        main.word_input_requirements = summary.word_inputs;
        let main_flow = FlowGraph::lower(&main).unwrap();
        let main_origins = main_flow.loan_origins(&main);
        let main_moves = main_flow.consumptions_with_origins(
            &main,
            &LinearTypes::from_program(&main_program),
            Some(&main_origins),
        );
        let error = main_flow
            .check_stored_reference_provenance(
                &main,
                &main_declarations,
                &main_origins,
                &main_moves,
            )
            .expect_err("no-argument bodies must reject an unproved entry contract");
        assert!(error.message.contains("context bound"));
    }
}
