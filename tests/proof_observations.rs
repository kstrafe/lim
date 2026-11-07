use lim::{CompileConfig, Diagnostic, ProofOutcome};

fn check(source: &str) -> Result<lim::CheckedTheorem, Diagnostic> {
    lim::check_theorem_details_from_path_with_config(
        source,
        std::path::Path::new("observations.lim"),
        &CompileConfig::default(),
        "claim",
    )
}

#[test]
fn many_read_only_implications_do_not_multiply_execution_states() {
    let clauses = (1..=20)
        .map(|index| {
            format!(
                "(#proof-implies (#u8::lt input {}u8) (#proof-eq input input))",
                index * 7
            )
        })
        .collect::<Vec<_>>()
        .join(" ");
    check(&format!(
        "(#theorem claim (#proof-for-all (: input #u8) (#proof-and {clauses})))"
    ))
    .unwrap();
}

#[test]
fn compact_implications_keep_partial_reads_under_their_guard() {
    check(
        r#"
      (#theorem claim (#proof-for-all (: values (#array #u8 2) : position #usize)
        (#proof-implies (#usize::lt position 2usize)
          (#proof-eq (#index values position) (#index values position)))))"#,
    )
    .unwrap();
}

#[test]
fn a_real_false_consequence_keeps_its_quantified_counterexample() {
    let error = check(
        r#"
      (#theorem claim (#proof-for-all (: input #u8)
        (#proof-implies (#u8::eq input 7u8) false)))"#,
    )
    .unwrap_err();
    assert_eq!(error.proof_outcome(), Some(ProofOutcome::Counterexample));
    assert!(error.message.contains("input = 7u8"), "{}", error.message);
}

#[test]
fn pure_guarding_cannot_hide_an_actual_invalid_index() {
    let error = check(
        r#"
      (#theorem claim (#proof-for-all (: values (#array #u8 2) : position #usize)
        (#proof-implies true (#proof-eq (#index values position) 0u8))))"#,
    )
    .unwrap_err();
    assert_eq!(error.proof_outcome(), Some(ProofOutcome::Counterexample));
    assert!(error.message.contains("out of bounds"), "{}", error.message);
}

#[test]
fn false_premises_do_not_accept_unknown_forms_or_mismatched_value_types() {
    for (body, expected) in [
        ("(#proof-missing)", ProofOutcome::Invalid),
        ("(#proof-eq 0u8 false)", ProofOutcome::Invalid),
        ("(#proof-eq (u8.+.wrap 1u8 2u8) 3u8)", ProofOutcome::Invalid),
    ] {
        let source = format!("(#theorem claim (#proof-implies false {body}))");
        let error =
            check(&source).expect_err("unmodeled or malformed observations cannot be accepted");
        assert_eq!(error.proof_outcome(), Some(expected), "{error:?}");
    }
}

#[test]
fn implication_compaction_cannot_accept_effectful_specifications() {
    for implication in [
        "(#proof-implies true (#block (#set value 1u8) true))",
        "(#proof-implies false (#block (#set value 1u8) true))",
        "(#proof-implies (#block (#set value 1u8) false) true)",
    ] {
        let source = format!("(#theorem claim (#proof-for-all (: value #u8) {implication}))");
        let error = check(&source).expect_err("specifications cannot mutate storage");
        assert_eq!(
            error.proof_outcome(),
            Some(ProofOutcome::Invalid),
            "{error:?}"
        );
        assert!(
            error.message.contains("statement blocks"),
            "{}",
            error.message
        );
    }
}
