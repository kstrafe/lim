//! Regression tests for induction; usable as a crate test module or via rustc.
use crate::{parse_program, CheckedProgram};

fn validate(source: &str) -> std::result::Result<(), String> {
    let program = parse_program(source).unwrap_or_else(|error| panic!("{error}\n{source}"));
    CheckedProgram::validate(&program).map(|_| ())
}
fn rejected(source: &str, expected: &str) {
    let error = validate(source).expect_err("unsound or unsupported induction was accepted");
    assert!(
        error.starts_with("theorem '"),
        "ordinary validation failed: {error}"
    );
    assert!(error.contains(expected), "expected {expected:?}: {error}");
}
fn claim(body: &str, predicate: &str, rank: &str, condition: &str, post: &str) -> String {
    format!(
        r#"
      (#fn countdown ((count #u8)) #u8
        (#let-mut remaining #u8 count)
        (#let-mut changed #u8 0u8)
        (#label again (#while {condition} {body}))
        (#return {post}))
      (#theorem induction
        (#proof-with-invariants ((countdown again {predicate} {rank}))
          (#proof-loop-limit 1
            (#proof-for-all ((count #u8))
              (#proof-eq (#call countdown (: count count)) 0u8)))))"#
    )
}

#[test]
fn proves_unsigned_countdown_by_induction() {
    let source = claim(
        "(#set remaining (#u8::sub-wrap remaining 1u8))",
        "true",
        "remaining",
        "(#u8::gt remaining 0u8)",
        "remaining",
    );
    validate(&source).unwrap();
}

#[test]
fn rejects_nondecreasing_rank() {
    let source = claim(
        "(#continue)",
        "true",
        "remaining",
        "(#u8::gt remaining 0u8)",
        "remaining",
    );
    rejected(&source, "loop rank does not strictly decrease");
}

#[test]
fn rejects_writes_in_invariant_and_rank_blocks() {
    for (predicate, rank) in [
        ("(#block (#set remaining 0u8) true)", "remaining"),
        ("true", "(#block (#set remaining 0u8) remaining)"),
    ] {
        let source = claim(
            "(#continue)",
            predicate,
            rank,
            "(#u8::gt remaining 0u8)",
            "remaining",
        );
        rejected(&source, "pure");
    }
}

#[test]
fn rejects_effectful_condition() {
    let source = claim(
        "(#continue)",
        "true",
        "remaining",
        "(#block (#set remaining 0u8) false)",
        "remaining",
    );
    rejected(&source, "pure");
}

#[test]
fn havocs_writes_nested_in_expression_blocks() {
    let source = claim(
        r#"
      (#u8::add-wrap (#block (#set changed 1u8) changed) 0u8)
      (#set remaining (#u8::sub-wrap remaining 1u8))"#,
        "true",
        "remaining",
        "(#u8::gt remaining 0u8)",
        "changed",
    );
    rejected(&source, "inductive obligation");
}

#[test]
fn rejects_user_calls_without_an_effect_summary() {
    let source = format!(
        "(#fn helper () #u8 (#return 0u8)) {}",
        claim(
            "(#call helper (:)) (#set remaining (#u8::sub-wrap remaining 1u8))",
            "true",
            "remaining",
            "(#u8::gt remaining 0u8)",
            "remaining"
        )
    );
    rejected(&source, "induction cannot summarize");
}

#[test]
fn havocs_writes_in_array_index_expressions() {
    rejected(
        r#"
      (#fn countdown ((count #u8) (initial (#array #u8 1))) #u8
        (#let-mut remaining #u8 count)
        (#let-mut changed #u8 0u8)
        (#let-mut storage (#array #u8 1) initial)
        (#label again (#while (#u8::gt remaining 0u8)
          (#set-index storage (#block (#set changed 1u8) 0usize) 0u8)
          (#set remaining (#u8::sub-wrap remaining 1u8))))
        (#return changed))
      (#theorem induction
        (#proof-with-invariants ((countdown again true remaining))
          (#proof-contract countdown true (#proof-eq (#proof-result) 0u8))))
    "#,
        "inductive obligation",
    );
}

#[test]
fn qualified_user_calls_cannot_masquerade_as_numeric_builtins() {
    let declarations = "(#struct Helper () (: value #u8))
      (#fn Helper::identity () #u8 (#return 0u8))
      (#fn Helper::predicate () #bool (#return true))";
    let body_call = format!(
        "{declarations} {}",
        claim(
            "(#call Helper::identity (:)) (#set remaining (#u8::sub-wrap remaining 1u8))",
            "true",
            "remaining",
            "(#u8::gt remaining 0u8)",
            "remaining"
        )
    );
    rejected(&body_call, "induction cannot summarize user-call effects");
    let predicate_call = format!(
        "{declarations} {}",
        claim(
            "(#set remaining (#u8::sub-wrap remaining 1u8))",
            "(#call Helper::predicate (:))",
            "remaining",
            "(#u8::gt remaining 0u8)",
            "remaining"
        )
    );
    rejected(&predicate_call, "pure induction expression");
}
