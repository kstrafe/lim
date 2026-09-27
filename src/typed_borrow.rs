//! Checks simultaneous call-argument loans using resolved places. Pure
//! constructors preserve direct borrows through aggregates and conditional
//! results. Bindings inside value blocks retain their origins; general
//! flow-sensitive bindings and call results remain for IR-04.

use std::collections::{HashMap, HashSet};

use crate::typed_body::{BindingId, Body, Control, NodeId, NodeKind, PlaceRoot};
use crate::typed_flow::{FlowAction, FlowGraph, FlowNodeId, LoanOrigin};
use crate::typed_ir::DeclarationId;
use crate::typed_place::Place;
use crate::{Span, Type};

const MAX_BORROW_ALTERNATIVES: usize = 1024;

#[derive(Debug)]
pub(crate) struct BorrowConflict {
    pub message: String,
    pub span: Option<Span>,
    pub labels: Vec<(Span, String)>,
}

#[derive(Clone)]
struct DirectBorrow {
    place: Place,
    mutable: bool,
    span: Option<Span>,
}

pub(crate) fn check_call_arguments(body: &Body, flow: &FlowGraph) -> Result<(), BorrowConflict> {
    let calls = body
        .nodes
        .iter()
        .enumerate()
        .filter(|(_, node)| {
            matches!(
                node.kind,
                NodeKind::Form {
                    callee: Some(_),
                    ..
                }
            )
        })
        .collect::<Vec<_>>();
    if calls.is_empty() {
        return Ok(());
    }
    let has_reference_bindings = body
        .bindings
        .iter()
        .any(|binding| matches!(binding.ty, Type::Reference { .. }));
    let call_events = flow
        .nodes
        .iter()
        .enumerate()
        .filter_map(|(index, node)| match node.action {
            FlowAction::Evaluate(id) => Some((id, FlowNodeId(index))),
            _ => None,
        })
        .collect::<HashMap<_, _>>();
    let origins = has_reference_bindings.then(|| flow.loan_origins(body));
    for (index, node) in calls {
        let NodeKind::Form {
            head,
            children,
            callee: Some(_),
            ..
        } = &node.kind
        else {
            continue;
        };
        let mut bindings = BoundBorrows::new();
        if let (Some(event), Some(origins)) = (call_events.get(&NodeId(index)), &origins) {
            for (index, binding) in body.bindings.iter().enumerate() {
                if !matches!(binding.ty, Type::Reference { .. }) {
                    continue;
                }
                let held = origins.before(*event, BindingId(index));
                if let Some(alternatives) = origin_alternatives(held, node.span)? {
                    bindings.insert(BindingId(index), alternatives);
                }
            }
        }
        let mut prior = vec![Vec::<DirectBorrow>::new()];
        for argument in children.iter().skip(1) {
            let alternatives = returned_borrows_with_bindings(body, *argument, head, &bindings)?;
            prior = combine(prior, alternatives, head, node.span)?;
        }
    }
    Ok(())
}

type BoundBorrows = HashMap<BindingId, Vec<Vec<DirectBorrow>>>;

fn origin_alternatives(
    held: &[LoanOrigin],
    span: Option<Span>,
) -> Result<Option<Vec<Vec<DirectBorrow>>>, BorrowConflict> {
    if held.is_empty() || held.iter().any(|origin| !origin.storage.is_empty()) {
        return Ok(None);
    }
    let alternatives = held
        .iter()
        .map(|origin| {
            vec![DirectBorrow {
                place: origin.place.clone(),
                mutable: origin.mutable,
                span: origin.span,
            }]
        })
        .collect();
    bounded(alternatives, span).map(Some)
}

/// Each alternative is one execution path through the value expression.
/// Borrows within one alternative coexist; different alternatives do not.
fn returned_borrows_with_bindings(
    body: &Body,
    id: NodeId,
    callee: &str,
    bindings: &BoundBorrows,
) -> Result<Vec<Vec<DirectBorrow>>, BorrowConflict> {
    if let Some(borrow) = direct_borrow(body, id) {
        if let Some(resolved) = resolve_projected_borrow(body, &borrow, bindings) {
            return bounded(resolved, body.nodes[id.0].span);
        }
        return Ok(vec![vec![borrow]]);
    }
    let node = &body.nodes[id.0];
    match &node.kind {
        NodeKind::Symbol {
            binding: Some(binding),
            ..
        } => Ok(bindings
            .get(binding)
            .cloned()
            .unwrap_or_else(|| vec![Vec::new()])),
        NodeKind::If {
            then_value,
            else_value,
            ..
        } => {
            let mut alternatives =
                returned_borrows_with_bindings(body, *then_value, callee, bindings)?;
            if let Some(otherwise) = else_value {
                alternatives.extend(returned_borrows_with_bindings(
                    body, *otherwise, callee, bindings,
                )?);
            } else {
                alternatives.push(Vec::new());
            }
            bounded(alternatives, node.span)
        }
        NodeKind::Match { arms, .. } => {
            let mut alternatives = Vec::new();
            for arm in arms {
                let NodeKind::MatchArm { values, .. } = &body.nodes[arm.0].kind else {
                    continue;
                };
                if let Some(value) = values.last() {
                    alternatives.extend(returned_borrows_with_bindings(
                        body, *value, callee, bindings,
                    )?);
                }
            }
            bounded(alternatives, node.span)
        }
        NodeKind::Block(instructions) => {
            let mut local = bindings.clone();
            for instruction in instructions {
                match &instruction.control {
                    Control::Bind(binding, value, _) => {
                        let loans = returned_borrows_with_bindings(body, *value, callee, &local)?;
                        local.insert(*binding, loans);
                    }
                    Control::Assign(PlaceRoot::Local(binding), _, _) => {
                        local.remove(binding);
                    }
                    _ => {}
                }
            }
            match instructions.last().map(|item| &item.control) {
                Some(Control::Evaluate(value)) => {
                    returned_borrows_with_bindings(body, *value, callee, &local)
                }
                _ => Ok(vec![Vec::new()]),
            }
        }
        NodeKind::Labeled(_, inner) => {
            returned_borrows_with_bindings(body, *inner, callee, bindings)
        }
        NodeKind::Form { head, children, .. } if head == "unsafe" && children.len() == 2 => {
            returned_borrows_with_bindings(body, children[1], callee, bindings)
        }
        NodeKind::Form { head, children, .. } if head == "clone" && children.len() == 2 => {
            returned_borrows_with_bindings(body, children[1], callee, bindings)
        }
        NodeKind::Form { head, children, .. }
            if matches!(head.as_str(), "tuple" | "array" | "struct-literal")
                || matches!(
                    children.first().map(|child| &body.nodes[child.0].kind),
                    Some(NodeKind::Declaration(
                        DeclarationId::Variant(_) | DeclarationId::Aggregate(_)
                    ))
                ) =>
        {
            combine_children(
                body,
                children.iter().skip(1).copied(),
                callee,
                node.span,
                bindings,
            )
        }
        NodeKind::Syntax(children) => {
            combine_children(body, children.iter().copied(), callee, node.span, bindings)
        }
        _ => Ok(vec![Vec::new()]),
    }
}

fn resolve_projected_borrow(
    body: &Body,
    borrow: &DirectBorrow,
    bindings: &BoundBorrows,
) -> Option<Vec<Vec<DirectBorrow>>> {
    let PlaceRoot::Local(binding) = borrow.place.root else {
        return None;
    };
    if borrow.place.segments.is_empty()
        || !matches!(body.bindings[binding.0].ty, Type::Reference { .. })
    {
        return None;
    }
    let origins = bindings.get(&binding)?;
    origins
        .iter()
        .map(|alternative| {
            let [origin] = alternative.as_slice() else {
                return None;
            };
            let mut place = origin.place.clone();
            place.segments.extend(borrow.place.segments.iter().cloned());
            Some(vec![DirectBorrow {
                place,
                mutable: borrow.mutable,
                span: borrow.span,
            }])
        })
        .collect()
}

fn combine_children(
    body: &Body,
    children: impl Iterator<Item = NodeId>,
    callee: &str,
    span: Option<Span>,
    bindings: &BoundBorrows,
) -> Result<Vec<Vec<DirectBorrow>>, BorrowConflict> {
    let mut alternatives = vec![Vec::new()];
    for child in children {
        alternatives = combine(
            alternatives,
            returned_borrows_with_bindings(body, child, callee, bindings)?,
            callee,
            span,
        )?;
    }
    Ok(alternatives)
}

fn combine(
    left: Vec<Vec<DirectBorrow>>,
    right: Vec<Vec<DirectBorrow>>,
    callee: &str,
    span: Option<Span>,
) -> Result<Vec<Vec<DirectBorrow>>, BorrowConflict> {
    let mut result = Vec::new();
    let mut seen = HashSet::new();
    for existing in &left {
        for incoming in &right {
            let mut combined = existing.clone();
            for borrow in incoming {
                if let Some(first) = combined.iter().find(|first| {
                    (first.mutable || borrow.mutable) && first.place.overlaps(&borrow.place)
                }) {
                    return Err(BorrowConflict {
                        message: format!(
                            "call to '{callee}' passes overlapping borrows; at most one may be mutable"
                        ),
                        span: borrow.span.or(span),
                        labels: first
                            .span
                            .map(|span| (span, "first borrow is passed here".into()))
                            .into_iter()
                            .collect(),
                    });
                }
                combined.push(borrow.clone());
            }
            let key = borrow_key(&combined);
            if seen.insert(key) {
                result.push(combined);
                if result.len() > MAX_BORROW_ALTERNATIVES {
                    return Err(complexity_error(span));
                }
            }
        }
    }
    Ok(result)
}

fn bounded(
    alternatives: Vec<Vec<DirectBorrow>>,
    span: Option<Span>,
) -> Result<Vec<Vec<DirectBorrow>>, BorrowConflict> {
    let mut unique = Vec::new();
    let mut seen = HashSet::new();
    for alternative in alternatives {
        if seen.insert(borrow_key(&alternative)) {
            unique.push(alternative);
            if unique.len() > MAX_BORROW_ALTERNATIVES {
                return Err(complexity_error(span));
            }
        }
    }
    Ok(unique)
}

fn borrow_key(borrows: &[DirectBorrow]) -> Vec<(Place, bool)> {
    borrows
        .iter()
        .map(|borrow| (borrow.place.clone(), borrow.mutable))
        .collect()
}

fn complexity_error(span: Option<Span>) -> BorrowConflict {
    BorrowConflict {
        message: format!(
            "call argument has more than {MAX_BORROW_ALTERNATIVES} borrow paths; split the expression"
        ),
        span,
        labels: Vec::new(),
    }
}

fn direct_borrow(body: &Body, id: NodeId) -> Option<DirectBorrow> {
    let node = body.nodes.get(id.0)?;
    let NodeKind::Form { head, children, .. } = &node.kind else {
        return None;
    };
    if head == "unsafe" && children.len() == 2 {
        return direct_borrow(body, children[1]);
    }
    if !matches!(head.as_str(), "borrow" | "borrow-mut") || children.len() != 2 {
        return None;
    }
    Some(DirectBorrow {
        place: Place::from_expression(body, children[1])?,
        mutable: head == "borrow-mut",
        span: node.span,
    })
}

#[cfg(test)]
mod tests {
    use super::{
        bounded, combine, origin_alternatives, returned_borrows_with_bindings, BoundBorrows,
        DirectBorrow, MAX_BORROW_ALTERNATIVES,
    };
    use crate::typed_body::{BindingId, NodeId, NodeKind, PlaceRoot};
    use crate::typed_flow::{FlowAction, FlowNodeId, LoanOrigin};
    use crate::typed_place::Place;

    fn source(args: &str) -> String {
        format!(
            "(#fn inspect ((left (#ref-mut u64)) (right (#ref u64))) u64
               (#forget left) (#forget right) (#return 0u64))
             (#fn main () u64
               (#let-mut value u64 1u64)
               (#return (#call inspect (#fn-args {args}))))"
        )
    }

    #[test]
    fn overlapping_direct_borrows_have_two_exact_source_sites() {
        let source = source("(left (#borrow-mut value)) (right (#borrow value))");
        let program = crate::parse_program(&source).unwrap();
        let error = crate::CheckedProgram::validate_with_span(&program)
            .err()
            .unwrap();
        assert!(error.0.contains("overlapping borrows"), "{}", error.0);
        assert_eq!(error.1, crate::DiagnosticCode::Borrow);
        let second = error.2.unwrap();
        assert_eq!(&source[second.start..second.end], "(#borrow value)");
        let first = error.3[0].0;
        assert_eq!(&source[first.start..first.end], "(#borrow-mut value)");
    }

    #[test]
    fn two_shared_direct_borrows_are_allowed() {
        let source = "(#fn inspect ((left (#ref u64)) (right (#ref u64))) u64
            (#return (#u64.+.wrap (#deref left) (#deref right))))
          (#fn main () u64
            (#let value u64 1u64)
            (#return (#call inspect (#fn-args
              (left (#borrow value)) (right (#borrow value))))))";
        let program = crate::parse_program(source).unwrap();
        crate::CheckedProgram::validate(&program).unwrap_or_else(|error| panic!("{error}"));
    }

    #[test]
    fn disjoint_struct_fields_can_be_borrowed_together() {
        let source = "(#struct Pair ((left u64) (right u64)))
          (#fn inspect ((left (#ref-mut u64)) (right (#ref u64))) u64
            (#forget left) (#forget right) (#return 0u64))
          (#fn main () u64
            (#let-mut pair Pair (#struct-literal Pair ((left 1u64) (right 2u64))))
            (#let pair-ref (#ref-mut Pair) (#borrow-mut pair))
            (#return (#call inspect (#fn-args
              (left (#borrow-mut (#get pair-ref left)))
              (right (#borrow (#get pair-ref right)))))))";
        let program = crate::parse_program(source).unwrap();
        crate::CheckedProgram::validate(&program).unwrap_or_else(|error| panic!("{error}"));

        let overlapping = source.replace(
            "(right (#borrow (#get pair-ref right)))",
            "(right (#borrow (#get pair-ref left)))",
        );
        let program = crate::parse_program(&overlapping).unwrap();
        let error = crate::CheckedProgram::validate(&program).err().unwrap();
        assert!(error.contains("overlapping borrows"), "{error}");
    }

    #[test]
    fn borrow_inside_struct_argument_conflicts_with_another_argument() {
        let source = "(#struct Holder ((item (#ref u64))))
          (#fn inspect ((holder Holder) (right (#ref-mut u64))) u64
            (#let (Holder item) Holder holder)
            (#drop item) (#drop right) (#return 0u64))
          (#fn main () u64
            (#let-mut value u64 1u64)
            (#return (#call inspect (#fn-args
              (holder (#struct-literal Holder ((item (#borrow value)))))
              (right (#borrow-mut value))))))";
        let program = crate::parse_program(source).unwrap();
        let error = crate::CheckedProgram::validate_with_span(&program)
            .err()
            .unwrap();
        assert!(error.0.contains("overlapping borrows"), "{}", error.0);
        let second = error.2.unwrap();
        assert_eq!(&source[second.start..second.end], "(#borrow-mut value)");
    }

    #[test]
    fn conditional_alternatives_do_not_conflict_with_each_other() {
        let source = "(#fn inspect ((left (#ref-mut u64)) (right (#ref u64))) u64
            (#forget left) (#forget right) (#return 0u64))
          (#fn main () u64
            (#let-mut first u64 1u64)
            (#let-mut second u64 2u64)
            (#return (#call inspect (#fn-args
              (left (#if true (#borrow-mut first) (#borrow-mut second)))
              (right (#borrow second))))))";
        let program = crate::parse_program(source).unwrap();
        let error = crate::CheckedProgram::validate(&program).err().unwrap();
        assert!(error.contains("overlapping borrows"), "{error}");

        let disjoint = source
            .replace(
                "(#let-mut second u64 2u64)",
                "(#let-mut second u64 2u64) (#let-mut third u64 3u64)",
            )
            .replace("(right (#borrow second))", "(right (#borrow third))");
        let program = crate::parse_program(&disjoint).unwrap();
        crate::CheckedProgram::validate(&program).unwrap_or_else(|error| panic!("{error}"));
    }

    #[test]
    fn borrow_inside_tuple_argument_conflicts_with_another_argument() {
        let source = "(#fn inspect ((left (#tuple (#ref u64))) (right (#ref-mut u64))) u64
            (#let (#tuple item) (#tuple (#ref u64)) left)
            (#drop item) (#drop right) (#return 0u64))
          (#fn main () u64
            (#let-mut value u64 1u64)
            (#return (#call inspect (#fn-args
              (left (#tuple (#borrow value)))
              (right (#borrow-mut value))))))";
        let program = crate::parse_program(source).unwrap();
        let error = crate::CheckedProgram::validate(&program).err().unwrap();
        assert!(error.contains("overlapping borrows"), "{error}");
    }

    #[test]
    fn borrow_inside_array_argument_conflicts_with_another_argument() {
        let source = "(#fn inspect ((left (#array (#ref u64) 1)) (right (#ref-mut u64))) u64
            (#let (#array item) (#array (#ref u64) 1) left)
            (#drop item) (#drop right) (#return 0u64))
          (#fn main () u64
            (#let-mut value u64 1u64)
            (#return (#call inspect (#fn-args
              (left (#array (#array (#ref u64) 1) (#borrow value)))
              (right (#borrow-mut value))))))";
        let program = crate::parse_program(source).unwrap();
        let error = crate::CheckedProgram::validate(&program).err().unwrap();
        assert!(error.contains("overlapping borrows"), "{error}");
    }

    #[test]
    fn borrow_inside_enum_argument_conflicts_with_another_argument() {
        let source = "(#enum Holder ((Has (#ref u64))))
          (#fn inspect ((left Holder) (right (#ref-mut u64))) u64
            (#let-else (Has item) Holder left (#return 0u64))
            (#drop item) (#drop right) (#return 0u64))
          (#fn main () u64
            (#let-mut value u64 1u64)
            (#return (#call inspect (#fn-args
              (left (Has (#borrow value)))
              (right (#borrow-mut value))))))";
        let program = crate::parse_program(source).unwrap();
        let error = crate::CheckedProgram::validate(&program).err().unwrap();
        assert!(error.contains("overlapping borrows"), "{error}");
    }

    #[test]
    fn match_result_borrows_are_checked_per_arm() {
        let source = "(#fn inspect ((left (#ref u64)) (right (#ref-mut u64))) u64
            (#drop left) (#drop right) (#return 0u64))
          (#fn main () u64
            (#let-mut first u64 1u64)
            (#let-mut second u64 2u64)
            (#return (#call inspect (#fn-args
              (left (#match true
                (#case true (#borrow first))
                (#case false (#borrow second))))
              (right (#borrow-mut first))))))";
        let program = crate::parse_program(source).unwrap();
        let error = crate::CheckedProgram::validate(&program).err().unwrap();
        assert!(error.contains("overlapping borrows"), "{error}");
    }

    #[test]
    fn immutable_block_binding_retains_borrow_origin() {
        let source = "(#fn inspect ((left (#ref u64)) (right (#ref-mut u64))) u64
            (#drop left) (#drop right) (#return 0u64))
          (#fn main () u64
            (#let-mut value u64 1u64)
            (#return (#call inspect (#fn-args
              (left (#block (#let view (#ref u64) (#borrow value)) view))
              (right (#borrow-mut value))))))";
        let program = crate::parse_program(source).unwrap();
        let error = crate::CheckedProgram::validate_with_span(&program)
            .err()
            .unwrap();
        assert!(error.0.contains("overlapping borrows"), "{}", error.0);
        let second = error.2.unwrap();
        assert_eq!(&source[second.start..second.end], "(#borrow-mut value)");
        let first = error.3[0].0;
        assert_eq!(&source[first.start..first.end], "(#borrow value)");
    }

    #[test]
    fn mutable_block_binding_retains_initial_borrow_origin() {
        let source = "(#fn inspect ((left (#ref u64)) (right (#ref-mut u64))) u64
            (#drop left) (#drop right) (#return 0u64))
          (#fn main () u64
            (#let-mut value u64 1u64)
            (#return (#call inspect (#fn-args
              (left (#block
                (#let-mut view (#ref u64) (#borrow value))
                view))
              (right (#borrow-mut value))))))";
        let program = crate::parse_program(source).unwrap();
        let error = crate::CheckedProgram::validate_with_span(&program)
            .err()
            .unwrap();
        assert!(error.0.contains("overlapping borrows"), "{}", error.0);
        let first = error.3[0].0;
        assert_eq!(&source[first.start..first.end], "(#borrow value)");

        let disjoint = source
            .replace(
                "(#let-mut value u64 1u64)",
                "(#let-mut value u64 1u64) (#let-mut other u64 2u64)",
            )
            .replace("(right (#borrow-mut value))", "(right (#borrow-mut other))");
        let program = crate::parse_program(&disjoint).unwrap();
        crate::CheckedProgram::validate(&program).unwrap_or_else(|error| panic!("{error}"));
    }

    #[test]
    fn equivalent_borrow_paths_do_not_exhaust_the_path_budget() {
        let shared = DirectBorrow {
            place: Place::root(PlaceRoot::Local(BindingId(0))),
            mutable: false,
            span: None,
        };
        let repeated = vec![vec![shared.clone()]; MAX_BORROW_ALTERNATIVES + 1];
        assert_eq!(bounded(repeated, None).unwrap().len(), 1);

        // The Cartesian product has 33 * 33 paths, but only 65 distinct
        // loan sequences after equivalent alternatives are folded together.
        let alternatives = (0..33).map(|count| vec![shared.clone(); count]).collect();
        assert_eq!(
            combine(
                alternatives,
                (0..33).map(|count| vec![shared.clone(); count]).collect(),
                "inspect",
                None
            )
            .unwrap()
            .len(),
            65
        );

        let distinct = (0..=MAX_BORROW_ALTERNATIVES)
            .map(|index| {
                vec![DirectBorrow {
                    place: Place::root(PlaceRoot::Local(BindingId(index))),
                    mutable: false,
                    span: None,
                }]
            })
            .collect();
        assert!(bounded(distinct, None).is_err());
    }

    #[test]
    fn reference_binding_as_call_argument_retains_its_direct_origin() {
        let source = "(#fn inspect ((left (#ref u64)) (right (#ref-mut u64))) u64
            (#drop left) (#drop right) (#return 0u64))
          (#fn main () u64
            (#let-mut value u64 1u64)
            (#let view (#ref u64) (#borrow value))
            (#return (#call inspect (#fn-args
              (left view) (right (#borrow-mut value))))))";
        let program = crate::parse_program(source).unwrap();
        let error = crate::CheckedProgram::validate_with_span(&program)
            .err()
            .unwrap();
        assert!(error.0.contains("overlapping borrows"), "{}", error.0);
        let second = error.2.unwrap();
        assert_eq!(&source[second.start..second.end], "(#borrow-mut value)");
        let first = error.3[0].0;
        assert_eq!(&source[first.start..first.end], "(#borrow value)");

        let disjoint = source
            .replace(
                "(#let-mut value u64 1u64)",
                "(#let-mut value u64 1u64) (#let-mut other u64 2u64)",
            )
            .replace("(right (#borrow-mut value))", "(right (#borrow-mut other))");
        let program = crate::parse_program(&disjoint).unwrap();
        crate::CheckedProgram::validate(&program).unwrap_or_else(|error| panic!("{error}"));
    }

    #[test]
    fn joined_reference_origins_are_checked_as_alternatives() {
        let held = [
            LoanOrigin {
                place: Place::root(PlaceRoot::Local(BindingId(0))),
                mutable: true,
                span: None,
                storage: Vec::new(),
            },
            LoanOrigin {
                place: Place::root(PlaceRoot::Local(BindingId(1))),
                mutable: true,
                span: None,
                storage: Vec::new(),
            },
        ];
        let alternatives = origin_alternatives(&held, None).unwrap().unwrap();
        assert_eq!(alternatives.len(), 2);
        let shared = |binding| {
            vec![vec![DirectBorrow {
                place: Place::root(PlaceRoot::Local(BindingId(binding))),
                mutable: false,
                span: None,
            }]]
        };
        assert!(combine(alternatives.clone(), shared(0), "inspect", None).is_err());
        assert!(combine(alternatives, shared(2), "inspect", None).is_ok());

        let source = "(#fn inspect ((first (#ref-mut u64)) (second (#ref u64))) u64
            (#drop first) (#drop second) (#return 0u64))
          (#fn main () u64
            (#let-mut left u64 1u64)
            (#let-mut right u64 2u64)
            (#let flag bool true)
            (#let view (#ref-mut u64)
              (#if flag (#borrow-mut left) (#borrow-mut right)))
            (#let-mut third u64 3u64)
            (#return (#call inspect (#fn-args
              (first view) (second (#borrow third))))))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let graph = &checked.declarations().flows["main"];
        let view = BindingId(body.bindings.iter().position(|b| b.name == "view").unwrap());
        let call = body
            .nodes
            .iter()
            .position(|node| {
                matches!(&node.kind, NodeKind::Form { head, callee: Some(_), .. } if head == "inspect")
            })
            .map(NodeId)
            .unwrap();
        let event = graph
            .nodes
            .iter()
            .position(|node| matches!(node.action, FlowAction::Evaluate(id) if id == call))
            .map(FlowNodeId)
            .unwrap();
        assert_eq!(graph.loan_origins(body).before(event, view).len(), 2);
    }

    #[test]
    fn projected_borrow_uses_reference_bindings_referent_place() {
        let source = "(#struct Pair ((left u64) (right u64)))
          (#fn main () u64
            (#let-mut pair Pair (#struct-literal Pair ((left 1u64) (right 2u64))))
            (#let pair-ref (#ref-mut Pair) (#borrow-mut pair))
            (#let field-ref (#ref u64) (#borrow (#get pair-ref left)))
            (#drop field-ref)
            (#drop pair-ref)
            (#forget pair)
            (#return 0u64))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let body = &checked.declarations().bodies["main"];
        let pair = BindingId(body.bindings.iter().position(|b| b.name == "pair").unwrap());
        let pair_ref = BindingId(
            body.bindings
                .iter()
                .position(|b| b.name == "pair-ref")
                .unwrap(),
        );
        let borrow = body
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| match &node.kind {
                NodeKind::Form { head, children, .. } if head == "borrow" => {
                    matches!(&body.nodes[children[1].0].kind, NodeKind::Form { head, .. } if head == "get")
                        .then_some(NodeId(index))
                }
                _ => None,
            })
            .unwrap();
        let mut bindings = BoundBorrows::new();
        bindings.insert(
            pair_ref,
            vec![vec![DirectBorrow {
                place: Place::root(PlaceRoot::Local(pair)),
                mutable: true,
                span: None,
            }]],
        );
        let projected = returned_borrows_with_bindings(body, borrow, "inspect", &bindings)
            .unwrap()
            .pop()
            .unwrap()
            .pop()
            .unwrap();
        assert_eq!(projected.place.root, PlaceRoot::Local(pair));
        assert_eq!(projected.place.segments.len(), 1);
        let overlapping = DirectBorrow {
            place: projected.place.clone(),
            mutable: true,
            span: None,
        };
        assert!(combine(
            vec![vec![projected]],
            vec![vec![overlapping]],
            "inspect",
            None,
        )
        .is_err());
    }
}
