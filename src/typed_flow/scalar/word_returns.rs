//! Conditional initialization of returned numeric-backed reference cells.
//! Scalar selectors partition proof obligations; real loan stores, rather
//! than selector values, establish the initialized slots on each path.
use super::*;
use crate::typed_body::{ScalarReturnFact, WordReturnGuarantee};

/// Reading a stable value at the return event must not re-evaluate an earlier
/// call or borrow. Unsupported evaluated expressions yield no guarantees.
fn stable_result(body: &Body, value: NodeId) -> bool {
    if scalar_pattern_value(body, value).is_some() {
        return true;
    }
    match &body.nodes[value.0].kind {
        NodeKind::Symbol {
            binding: Some(_), ..
        }
        | NodeKind::Literal(_) => true,
        NodeKind::Declaration(DeclarationId::Variant(_)) => true,
        NodeKind::Form {
            head,
            children,
            callee: None,
            ..
        } if head == "unsafe" && children.len() == 2 => stable_result(body, children[1]),
        NodeKind::Form {
            head,
            children,
            callee: None,
            ..
        } if head == "pin-read" && children.len() == 2 => {
            owned_pin_read_place(body, children[1]).is_some()
        }
        NodeKind::Form {
            head,
            children,
            callee: None,
            ..
        } if matches!(
            head.as_str(),
            "borrow" | "borrow-mut" | "pin-borrow" | "pin-borrow-mut"
        ) && children.len() == 2 =>
        {
            Place::from_expression(body, children[1])
                .is_some_and(|place| !has_dynamic_projection(&place))
        }
        NodeKind::Form {
            head,
            children,
            callee: None,
            ..
        } if matches!(
            head.as_str(),
            "struct-literal" | "tuple" | "array" | "array-of"
        ) || matches!(
            children.first().map(|id| &body.nodes[id.0].kind),
            Some(NodeKind::Declaration(
                DeclarationId::Aggregate(_) | DeclarationId::Variant(_)
            ))
        ) =>
        {
            let start = if matches!(head.as_str(), "tuple" | "array" | "array-of") {
                constructor_values_start(body.nodes[value.0].ty.as_ref(), children.len())
            } else {
                1
            };
            children
                .iter()
                .skip(start)
                .all(|child| stable_result(body, *child))
        }
        _ => false,
    }
}

fn owned_pin_read_place(body: &Body, pointer: NodeId) -> Option<Place> {
    let NodeKind::Form {
        head,
        children,
        callee: None,
        ..
    } = &body.nodes[pointer.0].kind
    else {
        return None;
    };
    if head != "pin-borrow-mut" || children.len() != 2 || reads_through_reference(body, children[1])
    {
        return None;
    }
    let place = Place::from_expression(body, children[1])?;
    let PlaceRoot::Local(binding) = place.root else {
        return None;
    };
    if matches!(
        body.bindings[binding.0].ty,
        Type::Reference { .. }
            | Type::PinnedReference { .. }
            | Type::RawPointer { .. }
            | Type::Slice(_)
            | Type::MutableSlice(_)
            | Type::PinOwned(_)
            | Type::PinShared(_)
    ) {
        return None;
    }
    Some(place)
}

fn return_snapshot(
    graph: &FlowGraph,
    body: &Body,
    loans: &FlowLoanOrigins,
    scalars: &Analysis,
    event: FlowNodeId,
    value: NodeId,
) -> Option<(Shape, Vec<LoanOrigin>)> {
    if let Some(literal) = scalar_pattern_value(body, value) {
        return Some((HashMap::from([(Vec::new(), vec![literal])]), Vec::new()));
    }
    if !stable_result(body, value) {
        return None;
    }
    if matches!(
        body.nodes[value.0].ty,
        Some(Type::Reference { .. } | Type::PinnedReference { .. })
    ) {
        let state = loans.before[event.0].as_ref()?;
        let facts = scalars.before[event.0].as_ref()?;
        let mut held = value_loan_origins(body, value, state);
        let addresses = held
            .iter()
            .filter(|loan| loan.storage.is_empty() && !loan.lifetime_only)
            .cloned()
            .collect::<Vec<_>>();
        if addresses.len() != 1 || has_dynamic_projection(&addresses[0].referent_place()) {
            return None;
        }
        let address = &addresses[0];
        let shape = stored_shape(facts, &address.referent_place())
            .into_iter()
            .map(|(path, values)| {
                (
                    std::iter::once(Segment::Dereference).chain(path).collect(),
                    values,
                )
            })
            .collect();
        let loaded = select_summary_inputs(address.clone(), &[Segment::Dereference], state);
        for mut loan in loaded {
            loan.prepend_storage(&[Segment::Dereference]);
            merge_loan_origins(&mut held, &[loan]);
        }
        return Some((shape, held));
    }
    if let NodeKind::Form {
        head,
        children,
        callee: None,
        ..
    } = &body.nodes[value.0].kind
    {
        if head == "unsafe" {
            return return_snapshot(graph, body, loans, scalars, event, children[1]);
        }
        if head == "pin-read" {
            let place = owned_pin_read_place(body, children[1])?;
            let mut predecessors = vec![Vec::new(); graph.nodes.len()];
            for (index, node) in graph.nodes.iter().enumerate() {
                for successor in &node.successors {
                    predecessors[successor.0].push(FlowNodeId(index));
                }
            }
            let mut pending = predecessors[event.0].clone();
            let mut visited = HashSet::new();
            let mut captures = Vec::new();
            while let Some(candidate) = pending.pop() {
                if !visited.insert(candidate) {
                    continue;
                }
                if matches!(graph.nodes[candidate.0].action, FlowAction::Evaluate(found) if found == value)
                {
                    captures.push(candidate);
                } else if matches!(graph.nodes[candidate.0].action, FlowAction::Entry) {
                    return None;
                } else {
                    pending.extend_from_slice(&predecessors[candidate.0]);
                }
            }
            let mut shape: Option<Shape> = None;
            let mut held = None;
            for capture in captures {
                let facts = scalars.before[capture.0].as_ref()?;
                let current = stored_shape(facts, &place);
                if let Some(shape) = &mut shape {
                    join_map(shape, &current);
                } else {
                    shape = Some(current);
                }
                let state = loans.before[capture.0].as_ref()?;
                join_value_alternative(&mut held, value_loan_origins(body, value, state));
            }
            return Some((shape?, held?));
        }
        let mut shape = Shape::new();
        let mut held = Vec::new();
        let start = if matches!(head.as_str(), "tuple" | "array" | "array-of") {
            constructor_values_start(body.nodes[value.0].ty.as_ref(), children.len())
        } else {
            1
        };
        for (index, child) in children.iter().skip(start).enumerate() {
            let slot = aggregate_slot(body, head, children, index)?;
            let (nested, mut incoming) =
                return_snapshot(graph, body, loans, scalars, event, *child)?;
            for (path, values) in nested {
                let mut storage = vec![slot.clone()];
                storage.extend(path);
                shape.insert(storage, values);
            }
            for loan in &mut incoming {
                loan.prepend_storage(&[slot.clone()]);
            }
            merge_loan_origins(&mut held, &incoming);
        }
        return Some((shape, held));
    }
    Some((
        snapshot(scalars.before[event.0].as_ref()?, body, value),
        value_loan_origins(body, value, loans.before[event.0].as_ref()?),
    ))
}

fn inactive_output(body: &Body, value: NodeId, path: &[Segment]) -> bool {
    path.iter().enumerate().any(|(index, segment)| {
        let Segment::Payload(wanted, _) = segment else {
            return false;
        };
        constructor_variant_at_storage(body, value, &path[..index])
            .is_some_and(|actual| actual.owner == wanted.owner && actual != *wanted)
    })
}

#[cfg(test)]
fn word_return_guarantees(
    flow: &FlowGraph,
    body: &Body,
    origins: &FlowLoanOrigins,
    contents: bool,
) -> Vec<WordReturnGuarantee> {
    word_and_scalar_return_guarantees(flow, body, origins, contents).0
}

pub(in crate::typed_flow) fn word_and_scalar_return_guarantees(
    flow: &FlowGraph,
    body: &Body,
    origins: &FlowLoanOrigins,
    contents: bool,
) -> (Vec<WordReturnGuarantee>, Vec<ScalarReturnFact>) {
    if !body
        .word_layouts
        .values()
        .any(|layout| !layout.slots.is_empty())
    {
        return (Vec::new(), Vec::new());
    }
    let ordinary = contents.then(|| flow.loan_origins(body));
    let context_origins = ordinary.as_ref().unwrap_or(origins);
    let mut entries = vec![(Vec::new(), Vec::new())];
    if let Some((place, values)) = entry_partition(flow, body, context_origins) {
        if values.len() > 16 {
            return (Vec::new(), Vec::new());
        }
        entries = values
            .iter()
            .map(|value| {
                (
                    vec![(place.clone(), crate::Expr::UnsignedInteger(*value))],
                    Vec::new(),
                )
            })
            .collect();
        entries.push((
            Vec::new(),
            vec![(
                place,
                values
                    .into_iter()
                    .map(crate::Expr::UnsignedInteger)
                    .collect(),
            )],
        ));
    }
    let mut returns = Vec::new();
    let mut selectors = HashSet::new();
    let mut slots = HashSet::new();
    for (entry, excluded) in entries {
        let graph = if excluded.is_empty() {
            specialize(flow, body, context_origins, &entry)
        } else {
            specialize_excluding(flow, body, context_origins, &excluded)
        };
        let Some(graph) = graph else {
            return (Vec::new(), Vec::new());
        };
        let loans = graph.return_guarantee_loan_origins(body, contents, &entry, &excluded);
        let scalars = analyze_for_contract_at_entry(&graph, body, &loans, &entry);
        for (index, node) in graph.nodes.iter().enumerate() {
            let FlowAction::Return(Some(value)) = node.action else {
                continue;
            };
            let Some(_) = &loans.before[index] else {
                continue;
            };
            let Some(_) = &scalars.before[index] else {
                return (Vec::new(), Vec::new());
            };
            // Context nodes can share expression IDs. Query this return's actual
            // binding state, not the union of every evaluation of the same ID.
            let snapshot =
                return_snapshot(&graph, body, &loans, &scalars, FlowNodeId(index), value);
            let (shape, held) = snapshot.unwrap_or_default();
            for loan in &held {
                if loan.word_stored {
                    slots.insert(loan.storage.clone());
                }
            }
            for (path, values) in &shape {
                for value in values {
                    if let crate::Expr::UnsignedInteger(value) = value {
                        selectors.insert((path.clone(), *value));
                    }
                }
            }
            returns.push((value, shape, held));
        }
    }
    // Bound only precision, never correctness. Failure produces no guarantee.
    if selectors.len() > 32 || slots.len() > 64 {
        return (Vec::new(), Vec::new());
    }
    let mut scalar_returns = Vec::new();
    let paths = selectors
        .iter()
        .map(|(path, _)| path.clone())
        .collect::<HashSet<_>>();
    for path in paths {
        let mut values = Vec::new();
        let valid = returns.iter().all(|(value, shape, _)| {
            if inactive_output(body, *value, &path) {
                return true;
            }
            let Some(known) = shape.get(&path) else {
                return false;
            };
            for value in known {
                let crate::Expr::UnsignedInteger(value) = value else {
                    return false;
                };
                if !values.contains(value) {
                    values.push(*value);
                }
            }
            !known.is_empty() && values.len() <= 16
        });
        if valid && !values.is_empty() {
            values.sort_unstable();
            scalar_returns.push(ScalarReturnFact {
                storage: path,
                values,
            });
        }
    }
    scalar_returns.sort_by(|a, b| a.storage.cmp(&b.storage));
    let mut result = Vec::new();
    for (selector, wanted) in selectors {
        for slot in &slots {
            let mut witnessed = false;
            let valid = returns.iter().all(|(value, shape, held)| {
                if inactive_output(body, *value, &selector) {
                    return true;
                }
                if let Some(values) = shape.get(&selector) {
                    if values
                        .iter()
                        .all(|value| matches!(value, crate::Expr::UnsignedInteger(_)))
                        && !values.contains(&crate::Expr::UnsignedInteger(wanted))
                    {
                        return true;
                    }
                    witnessed = true;
                }
                // An unknown selector could equal wanted, so it participates
                // in the must intersection rather than being silently skipped.
                let matching = held
                    .iter()
                    .filter(|loan| loan.storage == *slot)
                    .collect::<Vec<_>>();
                !matching.is_empty()
                    && matching
                        .iter()
                        .all(|loan| !loan.maybe_absent && loan.has_concrete_address())
            });
            if valid && witnessed {
                result.push(WordReturnGuarantee {
                    condition: ScalarReturnFact {
                        storage: selector.clone(),
                        values: vec![wanted],
                    },
                    storage: slot.clone(),
                });
            }
        }
    }
    result.sort_by(|a, b| {
        (&a.condition.storage, &a.condition.values, &a.storage).cmp(&(
            &b.condition.storage,
            &b.condition.values,
            &b.storage,
        ))
    });
    (result, scalar_returns)
}

#[cfg(test)]
mod tests {
    use super::*;

    const SOURCE: &str = "#struct Holder () ((value (#ref #u64)))
#struct Frame () ((state #u64) (words (#array #u64 1)))
#fn make ((value (#ref #u64)) (flag #bool) (unknown #u64)) Frame
          (#let-mut frame Frame (#struct-literal Frame ((state 0u64) (words (#array-repeat 0u64)))))
          (#if flag (#block
            (#unsafe (#word-write Holder (#borrow-slice-mut (#get frame words))
              (#struct-literal Holder ((value value)))))
            (#set-field frame state 1u64)) ())
          (#return frame)\n";

    fn guarantees(source: &str) -> Vec<WordReturnGuarantee> {
        let program = crate::parse_program(source).unwrap();
        let declarations = crate::typecheck::resolve_program_for_analysis(&program, false).unwrap();
        let body = &declarations.bodies["make"];
        let flow = &declarations.flows["make"];
        word_return_guarantees(flow, body, &flow.loan_origins(body), false)
    }

    #[test]
    fn returned_scalar_states_partition_real_cell_initialization() {
        let facts = guarantees(SOURCE);
        assert!(
            facts.iter().any(|fact| fact.condition.values == [1]
                && fact.storage.last() == Some(&Segment::Index(0))),
            "{facts:?}"
        );
        assert!(!facts.iter().any(|fact| fact.condition.values == [0]));
    }

    #[test]
    fn borrowed_return_guarantees_describe_the_referent_not_the_handle() {
        let source = SOURCE
            .replace("#fn make ((value (#ref #u64)", "#fn make ((frame (#ref-mut Frame)) (value (#ref #u64)")
            .replace(") Frame\n", ") (#ref-mut Frame)\n")
            .replace("(#let-mut frame Frame (#struct-literal Frame ((state 0u64) (words (#array-repeat 0u64)))))", "(#deref-set (#borrow-mut (#get frame state)) 0u64)")
            .replace("(#set-field frame state 1u64)", "(#deref-set (#borrow-mut (#get frame state)) 1u64)");
        let facts = guarantees(&source);
        assert!(
            facts.iter().any(|fact| fact.condition.values == [1]
                && fact.condition.storage.first() == Some(&Segment::Dereference)
                && fact.storage.first() == Some(&Segment::Dereference)),
            "{facts:?}"
        );
        for alternative in ["1u64", "unknown"] {
            let bad = source.replace(
                "1u64)) ())",
                &format!("1u64)) (#deref-set (#borrow-mut (#get frame state)) {alternative}))"),
            );
            assert_ne!(source, bad);
            assert!(!guarantees(&bad)
                .iter()
                .any(|fact| fact.condition.values == [1]));
        }
        let retired = source.replace("(#return frame)", "(#unsafe (#word-forget Holder (#borrow-slice-mut (#get frame words)))) (#return frame)");
        assert!(guarantees(&retired).is_empty());
    }

    #[test]
    fn another_compatible_or_unknown_return_revokes_the_guarantee() {
        for alternative in [
            "(#set-field frame state 1u64)",
            "(#set-field frame state unknown)",
        ] {
            let source = SOURCE.replace("1u64)) ())", &format!("1u64)) (#block {alternative}))"));
            assert_ne!(source, SOURCE);
            assert!(!guarantees(&source)
                .iter()
                .any(|fact| fact.condition.values == [1]));
        }
    }

    #[test]
    fn a_later_selector_write_does_not_keep_an_old_condition() {
        let source = SOURCE.replace(
            "(#return frame)",
            "(#set-field frame state 2u64) (#return frame)",
        );
        // Both paths now report 2, but only one initialized the cell.
        assert!(!guarantees(&source)
            .iter()
            .any(|fact| fact.condition.values == [1] || fact.condition.values == [2]));
    }

    #[test]
    fn owned_pin_reads_preserve_the_evaluated_frame_return_snapshot() {
        let source = SOURCE.replace(
            "(#return frame)",
            "(#return (#unsafe (#pin-read (#pin-borrow-mut frame))))",
        );
        assert!(guarantees(&source)
            .iter()
            .any(|fact| fact.condition.values == [1]
                && fact.storage.last() == Some(&Segment::Index(0))));
        let source = source
            .replace(
                "#struct Frame ()",
                "#enum Outcome () ((Outcome.Pending Frame) (Outcome.Ready #u64))\n#struct Frame ()",
            )
            .replace(") Frame\n", ") Outcome\n")
            .replace(
                "(#let-mut frame",
                "(#if flag () (#block (#return (Outcome.Ready 0u64)))) (#let-mut frame",
            )
            .replace("(#return (#unsafe", "(#return (Outcome.Pending (#unsafe")
            .replace("(#pin-borrow-mut frame))))", "(#pin-borrow-mut frame)))))");
        let program = crate::parse_program(&source).unwrap();
        let d = crate::typecheck::resolve_program_for_analysis(&program, false).unwrap();
        let body = &d.bodies["make"];
        let (words, scalars) = word_and_scalar_return_guarantees(
            &d.flows["make"],
            body,
            &d.flows["make"].loan_origins(body),
            false,
        );
        assert!(words.iter().any(|fact| fact.condition.values == [1]));
        assert!(
            scalars.iter().any(
                |fact| matches!(fact.storage.first(), Some(Segment::Payload(..)))
                    && fact.values.contains(&1)
            ),
            "{scalars:?}"
        );
    }

    #[test]
    fn owned_pin_read_with_unknown_alternative_does_not_invent_return_facts() {
        let source = SOURCE
            .replace(
                "1u64)) ())",
                "1u64)) (#block (#set-field frame state unknown)))",
            )
            .replace(
                "(#return frame)",
                "(#return (#unsafe (#pin-read (#pin-borrow-mut frame))))",
            );
        let program = crate::parse_program(&source).unwrap();
        let d = crate::typecheck::resolve_program_for_analysis(&program, false).unwrap();
        let body = &d.bodies["make"];
        let (words, scalars) = word_and_scalar_return_guarantees(
            &d.flows["make"],
            body,
            &d.flows["make"].loan_origins(body),
            false,
        );
        assert!(words.is_empty(), "{words:?}");
        assert!(scalars.is_empty(), "{scalars:?}");
    }
}
