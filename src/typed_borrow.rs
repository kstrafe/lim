//! Checks simultaneous call-argument loans using resolved places. Pure
//! constructors preserve direct borrows through aggregates and conditional
//! results. Bindings inside value blocks retain their origins; general
//! flow-sensitive bindings and call results remain for IR-04.

use std::collections::{HashMap, HashSet};

use crate::typed_body::{BindingId, Body, Control, NodeId, NodeKind, PlaceRoot};
use crate::typed_ir::DeclarationId;
use crate::typed_place::Place;
use crate::Span;

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

pub(crate) fn check_call_arguments(body: &Body) -> Result<(), BorrowConflict> {
    for node in &body.nodes {
        let NodeKind::Form {
            head,
            children,
            callee: Some(_),
            ..
        } = &node.kind
        else {
            continue;
        };
        let mut prior = vec![Vec::<DirectBorrow>::new()];
        for argument in children.iter().skip(1) {
            let alternatives = returned_borrows(body, *argument, head)?;
            prior = combine(prior, alternatives, head, node.span)?;
        }
    }
    Ok(())
}

/// Each alternative is one execution path through the value expression.
/// Borrows within one alternative coexist; different alternatives do not.
fn returned_borrows(
    body: &Body,
    id: NodeId,
    callee: &str,
) -> Result<Vec<Vec<DirectBorrow>>, BorrowConflict> {
    returned_borrows_with_bindings(body, id, callee, &HashMap::new())
}

type BoundBorrows = HashMap<BindingId, Vec<Vec<DirectBorrow>>>;

fn returned_borrows_with_bindings(
    body: &Body,
    id: NodeId,
    callee: &str,
    bindings: &BoundBorrows,
) -> Result<Vec<Vec<DirectBorrow>>, BorrowConflict> {
    if let Some(borrow) = direct_borrow(body, id) {
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
    use super::{bounded, combine, DirectBorrow, MAX_BORROW_ALTERNATIVES};
    use crate::typed_body::{BindingId, PlaceRoot};
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
}
