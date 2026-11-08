//! Fresh symbolic referents cannot prove that safe shared inputs are disjoint.
use lim::{CompileConfig, ProofOutcome};

const PROGRAM: &str = r#"
  (#fn validate (: user (#ref #u8) : accepted #bool) #bool (#return accepted))
  (#fn perform (: user (#ref #u8)) () (#return ()))
  (#fn entry (: first (#ref #u8) : second (#ref #u8)) ()
    (#let valid #bool (#call validate (: user second : accepted true)))
    (#let failed #bool (#call validate (: user first : accepted false)))
    (#call perform (: user second))
    (#return ()))
  (#fn aliased () ()
    (#let user #u8 0u8)
    (#call entry (: first (#borrow user) : second (#borrow user)))
    (#return ()))
"#;

fn check(source: &str, outcome: ProofOutcome) {
    let error = lim::check_theorem_details_from_path_with_config(
        source,
        std::path::Path::new("input-aliases.lim"),
        &CompileConfig::default(),
        "claim",
    )
    .expect_err("symbolic input roots were treated as necessarily disjoint");
    assert_eq!(
        error.proof_outcome(),
        Some(outcome),
        "{}\n{source}",
        error.message
    );
}

#[test]
fn shared_inputs_cover_the_same_object_as_well_as_distinct_objects() {
    lim::check_types(&lim::parse_program(PROGRAM).unwrap()).unwrap();
    let body = "(#proof-requires-validation ENTRY (#parameter-of validate user) (#parameter-of perform user))";
    check(
        &format!(
            "{PROGRAM} (#theorem claim {})",
            body.replace("ENTRY", "aliased")
        ),
        ProofOutcome::Counterexample,
    );
    check(
        &format!(
            "{PROGRAM} (#theorem claim {})",
            body.replace("ENTRY", "entry")
        ),
        ProofOutcome::Counterexample,
    );
    let negated = format!(
        "{PROGRAM} (#theorem claim (#proof-not {}))",
        body.replace("ENTRY", "entry")
    );
    lim::check_theorem_details_from_path_with_config(
        &negated,
        std::path::Path::new("input-aliases.lim"),
        &CompileConfig::default(),
        "claim",
    )
    .unwrap();
}

#[test]
fn successful_revalidation_preserves_prior_evidence_for_possible_aliases() {
    let source = PROGRAM.replace(": accepted false", ": accepted true");
    let source = format!("{source} (#theorem claim (#proof-requires-validation entry (#parameter-of validate user) (#parameter-of perform user)))");
    lim::check_theorem_details_from_path_with_config(
        &source,
        std::path::Path::new("input-aliases.lim"),
        &CompileConfig::default(),
        "claim",
    )
    .unwrap();
}

#[test]
fn loop_evidence_cannot_hide_failed_revalidation_through_another_input() {
    let source = r#"
      (#fn validate (: user (#ref #u8) : accepted #bool) #bool (#return accepted))
      (#fn perform (: user (#ref #u8)) () (#return ()))
      (#fn entry (: first (#ref #u8) : second (#ref #u8) : count #u8) ()
        (#let checked #bool (#call validate (: user second : accepted true)))
        (#let-mut remaining #u8 count)
        (#label again (#while (#u8::gt remaining 0u8)
          (#let failed #bool (#call validate (: user first : accepted false)))
          (#if checked (#call perform (: user second)))
          (#set remaining (#u8::sub-wrap remaining 1u8))))
        (#return ()))
    "#;
    lim::check_types(&lim::parse_program(source).unwrap()).unwrap();
    let claim = "(#proof-requires-validation entry (#parameter-of validate user) (#parameter-of perform user))";
    for claim in [claim.to_owned(), format!("(#proof-not {claim})")] {
        let theorem = format!("{source} (#theorem claim (#proof-loop-limit 1 (#proof-with-invariants ((entry again (#proof-implies checked (#proof-validated (#parameter-of validate user) second)) remaining)) {claim})))");
        check(&theorem, ProofOutcome::InductionFailure);
    }
    let valid = format!("{source} (#theorem claim (#proof-loop-limit 1 (#proof-with-invariants ((entry again (#proof-implies checked (#proof-validated (#parameter-of validate user) second)) remaining)) (#proof-requires-validation entry (#parameter-of validate user) (#parameter-of perform user)))))").replace(": accepted false", ": accepted true");
    lim::check_theorem_details_from_path_with_config(
        &valid,
        std::path::Path::new("input-aliases.lim"),
        &CompileConfig::default(),
        "claim",
    )
    .unwrap();
}

#[test]
fn shared_parents_can_alias_including_their_stored_mutable_references() {
    let source = r#"
      (#struct Holder () (: loan (#ref-mut #u8)))
      (#fn validate (: user (#ref #u8) : accepted #bool) #bool (#return accepted))
      (#fn perform (: user (#ref #u8)) () (#return ()))
      (#fn entry (: first (#ref Holder) : second (#ref Holder)) ()
        (#let valid #bool (#call validate (: user (#borrow (#deref (#get (#deref second) loan))) : accepted true)))
        (#let failed #bool (#call validate (: user (#borrow (#deref (#get (#deref first) loan))) : accepted false)))
        (#call perform (: user (#borrow (#deref (#get (#deref second) loan)))))
        (#return ()))
    "#;
    lim::check_types(&lim::parse_program(source).unwrap()).unwrap();
    let claim = "(#proof-requires-validation entry (#parameter-of validate user) (#parameter-of perform user))";
    check(
        &format!("{source} (#theorem claim {claim})"),
        ProofOutcome::Unsupported,
    );
    check(
        &format!("{source} (#theorem claim (#proof-not {claim}))"),
        ProofOutcome::Unsupported,
    );
}

#[test]
fn a_shared_parameter_can_reference_a_subobject_of_another_parameter() {
    let source = r#"
      (#struct Pair () (: value #u8 : other #u8))
      (#fn validate (: user (#ref #u8) : accepted #bool) #bool (#return accepted))
      (#fn perform (: user (#ref #u8)) () (#return ()))
      (#fn entry (: first (#ref #u8) : second (#ref Pair)) ()
        (#let valid #bool (#call validate (: user (#borrow (#get (#deref second) value)) : accepted true)))
        (#let failed #bool (#call validate (: user first : accepted false)))
        (#call perform (: user (#borrow (#get (#deref second) value))))
        (#return ()))
      (#fn aliased () ()
        (#let pair Pair (#struct-literal Pair (: value 0u8 : other 1u8)))
        (#call entry (: first (#borrow (#get pair value)) : second (#borrow pair)))
        (#forget pair)
        (#return ()))
    "#;
    lim::check_types(&lim::parse_program(source).unwrap()).unwrap();
    let claim = "(#proof-requires-validation ENTRY (#parameter-of validate user) (#parameter-of perform user))";
    check(
        &format!(
            "{source} (#theorem claim {})",
            claim.replace("ENTRY", "entry")
        ),
        ProofOutcome::Unsupported,
    );
    check(
        &format!(
            "{source} (#theorem claim {})",
            claim.replace("ENTRY", "aliased")
        ),
        ProofOutcome::Counterexample,
    );
}
