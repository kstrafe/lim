//! Checks simultaneous direct call-argument loans using resolved places.
//! Longer-lived references and aggregate provenance still use the lexical
//! borrow pass until the full CFG loan migration is complete.

use crate::typed_body::{Body, NodeId, NodeKind};
use crate::typed_place::Place;
use crate::Span;

pub(crate) struct BorrowConflict {
    pub message: String,
    pub span: Option<Span>,
    pub labels: Vec<(Span, String)>,
}

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
        let mut prior = Vec::<DirectBorrow>::new();
        for argument in children.iter().skip(1) {
            let Some(borrow) = direct_borrow(body, *argument) else {
                continue;
            };
            if let Some(first) = prior.iter().find(|first| {
                (first.mutable || borrow.mutable) && first.place.overlaps(&borrow.place)
            }) {
                return Err(BorrowConflict {
                    message: format!(
                        "call to '{head}' passes overlapping borrows; at most one may be mutable"
                    ),
                    span: borrow.span.or(node.span),
                    labels: first
                        .span
                        .map(|span| (span, "first borrow is passed here".into()))
                        .into_iter()
                        .collect(),
                });
            }
            prior.push(borrow);
        }
    }
    Ok(())
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
}
