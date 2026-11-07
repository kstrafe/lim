//! Program proofs remain executable obligations after removing proof terms.
fn check(source: &str) -> Result<(), String> {
    lim::check_types(&lim::parse_program(source)?)
}

const CHOOSE: &str = "
    (#fn choose ((flag #bool) (value #u8)) #u8
      (#if flag (#block (#return value)))
      (#return 0u8))";

#[test]
fn contracts_quantify_function_inputs_and_follow_both_branches() {
    check(&format!(
        "{CHOOSE}
        (#theorem choose-contract
          (#proof-contract choose true
            (#proof-eq (#proof-result) (#if flag value 0u8))))"
    ))
    .unwrap();
}

#[test]
fn a_false_branch_claim_produces_a_program_counterexample() {
    let error = check(&format!(
        "{CHOOSE}
        (#theorem choose-is-zero
          (#proof-contract choose true (#proof-eq (#proof-result) 0u8)))"
    ))
    .unwrap_err();
    assert!(error.starts_with("theorem '"), "{error}");
    assert!(error.contains("disproved"), "{error}");
    assert!(error.contains("flag"), "{error}");
    assert!(error.contains("value"), "{error}");
}

#[test]
fn mathematical_declarations_are_no_longer_language_forms() {
    for source in [
        "(#math-definition identity () (#pt-type 0) (#pt-type 0))",
        "(#math-opaque identity () #pt-prop #pt-false)",
        "(#math-inductive Natural () () (#pt-type 0) ())",
        "(#theorem old (#universes) (#parameters) (#statement #pt-false) (#proof #pt-false))",
    ] {
        assert!(lim::parse_program(source).is_err(), "{source}");
    }
}

#[test]
fn mathematical_term_wrappers_cannot_bypass_program_checking() {
    for proposition in [
        "(#proof-theorem () #pt-false #pt-false)",
        "(#pt-program missing)",
        "(#pt-certificate missing)",
    ] {
        let error = check(&format!("(#theorem invalid {proposition})")).unwrap_err();
        assert!(error.starts_with("theorem '"), "{error}");
    }
}
