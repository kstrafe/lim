//! Regression coverage for helper contracts used by invariant proofs of loops.

use lim::{CompileConfig, Diagnostic, ProofOutcome};
mod support;

fn check(source: &str, theorem: &str) -> Result<lim::CheckedTheorem, Diagnostic> {
    lim::check_theorem_details_from_path_with_config(
        source,
        std::path::Path::new("main.lim"),
        &CompileConfig::default(),
        theorem,
    )
}

fn proved(source: &str, theorem: &str) {
    check(source, theorem).unwrap_or_else(|error| panic!("{}\n{source}", error.message));
}

fn rejected(source: &str, theorem: &str, outcome: ProofOutcome) {
    let error = check(source, theorem).expect_err("must fail closed");
    assert_eq!(
        error.proof_outcome(),
        Some(outcome),
        "{}\n{source}",
        error.message
    );
}

const STEP: &str = r#"
  (#fn step (: value #u8) #u8
    (#return (#u8::sub-wrap value 1u8)))
  (#theorem step-contract
    (#proof-contract step (#u8::gt value 0u8)
      (#proof-eq (#proof-result) (#u8::sub-wrap (#proof-old value) 1u8))))
"#;

fn loop_source(invariant: &str, postcondition: &str, selected: &str) -> String {
    format!(
        r#"
      (#fn owner (: input #u8) #u8
        (#let-mut remaining #u8 input)
        (#label again
          (#while (#u8::gt remaining 0u8)
            (#set remaining (#call step (: value remaining)))))
        (#return remaining))
      (#theorem owner-contract
        (#proof-using {selected}
          (#proof-loop-limit 1
            (#proof-with-invariants
              ((owner again {invariant} remaining))
              (#proof-contract owner true {postcondition})))) )"#
    )
}

#[test]
fn selected_exact_decrement_contract_proves_countdown_loop() {
    let source = format!(
        "{STEP} {}",
        loop_source("true", "(#proof-eq (#proof-result) 0u8)", "(step-contract)")
    );
    proved(&source, "owner-contract");
}

#[test]
fn loop_helper_without_selected_contract_is_unsupported() {
    let source = format!(
        "{STEP} {}",
        loop_source("true", "(#proof-eq (#proof-result) 0u8)", "()")
    );
    rejected(&source, "owner-contract", ProofOutcome::Unsupported);
}

#[test]
fn helper_precondition_failure_survives_negation() {
    let source = format!(
        r#"{STEP}
      (#fn owner (: input #u8) #u8
        (#let-mut remaining #u8 input)
        (#label again
          (#while (#u8::gt remaining 0u8)
            (#set remaining (#call step (: value remaining)))))
        (#return remaining))
      (#theorem owner-contract
        (#proof-using (step-contract)
          (#proof-with-invariants ((owner again true remaining))
            (#proof-loop-limit 1
              (#proof-not
                (#proof-contract owner true
                  (#proof-eq (#proof-result) 0u8)))))))"#
    );
    let source = source.replace("(#u8::gt value 0u8)", "(#u8::gt value 1u8)");
    rejected(&source, "owner-contract", ProofOutcome::ContractFailure);
}

#[test]
fn weak_helper_summary_cannot_prove_loop_rank_or_result_under_negation() {
    let source = r#"
      (#fn step (: value #u8) #u8
        (#return (#u8::sub-wrap value 1u8)))
      (#theorem weak-step-contract (#proof-contract step (#u8::gt value 0u8) true))
      (#fn owner (: input #u8) #u8
        (#let-mut remaining #u8 input)
        (#label again
          (#while (#u8::gt remaining 0u8)
            (#set remaining (#call step (: value remaining)))))
        (#return remaining))
      (#theorem owner-contract
        (#proof-using (weak-step-contract)
          (#proof-loop-limit 1
            (#proof-with-invariants ((owner again true remaining))
              (#proof-not
                (#proof-contract owner true
                  (#proof-eq (#proof-result) 0u8)))))))"#;
    rejected(source, "owner-contract", ProofOutcome::ContractFailure);
}

#[test]
fn a_selected_contract_can_update_the_for_step() {
    let source = format!(
        r#"{STEP}
      (#fn owner (: input #u8) #u8
        (#let-mut result #u8 input)
        (#label again
          (#for (#let-mut remaining #u8 input)
            (#u8::gt remaining 0u8)
            (#set remaining (#call step (: value remaining)))
            (#set result (#u8::sub-wrap remaining 1u8))))
        (#return result))
      (#theorem owner-contract
        (#proof-using (step-contract)
          (#proof-with-invariants ((owner again (#u8::eq result remaining) remaining))
            (#proof-loop-limit 1
              (#proof-contract owner true (#proof-eq (#proof-result) 0u8))))))"#
    );
    proved(&source, "owner-contract");
}

#[test]
fn selected_contracts_compose_transitively_inside_a_loop() {
    let source = format!(
        r#"{STEP}
      (#fn forward (: value #u8) #u8
        (#return (#call step (: value value))))
      (#theorem forward-contract
        (#proof-using (step-contract)
          (#proof-contract forward (#u8::gt value 0u8)
            (#proof-eq (#proof-result) (#u8::sub-wrap value 1u8)))))
      {}"#,
        loop_source(
            "true",
            "(#proof-eq (#proof-result) 0u8)",
            "(forward-contract)"
        )
        .replace("(#call step", "(#call forward")
    );
    proved(&source, "owner-contract");
}

#[test]
fn reference_free_helpers_can_mutate_their_owned_local_records() {
    let source = format!(
        r#"
      (#struct Counter () (: value #u8))
      (#fn step (: value #u8) #u8
        (#let-mut counter Counter (#struct-literal Counter (: value value)))
        (#set-field counter value (#u8::sub-wrap (#get counter value) 1u8))
        (#return (#get counter value)))
      (#theorem step-contract
        (#proof-contract step (#u8::gt value 0u8)
          (#proof-eq (#proof-result) (#u8::sub-wrap value 1u8))))
      {}"#,
        loop_source("true", "(#proof-eq (#proof-result) 0u8)", "(step-contract)")
    );
    proved(&source, "owner-contract");
}

#[test]
fn selecting_a_reference_contract_does_not_enable_aliased_induction() {
    for claim in [
        "(#proof-contract owner true true)",
        "(#proof-not (#proof-contract owner true true))",
    ] {
        let source = format!(
            r#"
          (#fn read (: value (#ref #u8)) #u8 (#return (#deref value)))
          (#theorem read-contract (#proof-contract read true true))
          (#fn owner (: input #u8) #u8
            (#let-mut remaining #u8 input)
            (#label again (#while (#u8::gt remaining 0u8)
              (#call read (: value (#borrow input)))
              (#set remaining (#u8::sub-wrap remaining 1u8))))
            (#return remaining))
          (#theorem owner-contract (#proof-using (read-contract)
            (#proof-with-invariants ((owner again true remaining)) {claim})))"#
        );
        rejected(&source, "owner-contract", ProofOutcome::Unsupported);
    }
}

#[test]
fn selected_helpers_remain_forbidden_in_invariants_ranks_and_conditions() {
    let base = format!(
        "{STEP} {}",
        loop_source("true", "(#proof-eq (#proof-result) 0u8)", "(step-contract)")
    );
    for source in [
        base.replace(
            "owner again true remaining",
            "owner again (#u8::eq (#call step (: value 1u8)) 0u8) remaining",
        ),
        base.replace(
            "owner again true remaining",
            "owner again true (#call step (: value remaining))",
        ),
        base.replace(
            "(#while (#u8::gt remaining 0u8)",
            "(#while (#u8::gt (#call step (: value remaining)) 0u8)",
        ),
    ] {
        rejected(&source, "owner-contract", ProofOutcome::Unsupported);
    }
}

#[test]
fn argument_writes_are_not_lost_from_the_loop_exit_state() {
    let source = r#"
      (#fn identity (: value #u8) #u8 (#return value))
      (#theorem identity-contract
        (#proof-contract identity true (#proof-eq (#proof-result) value)))
      (#fn owner (: input #u8) #u8
        (#let-mut remaining #u8 input)
        (#let-mut touched #u8 0u8)
        (#label again (#while (#u8::gt remaining 0u8)
          (#call identity (: value (#block (#set touched 1u8) remaining)))
          (#set remaining (#u8::sub-wrap remaining 1u8))))
        (#return touched))"#;
    for claim in [
        "(#proof-contract owner true (#proof-eq (#proof-result) 0u8))",
        "(#proof-not (#proof-contract owner true (#proof-eq (#proof-result) 0u8)))",
    ] {
        let source = format!(
            "{source} (#theorem owner-contract (#proof-using (identity-contract) (#proof-with-invariants ((owner again true remaining)) {claim})))"
        );
        rejected(&source, "owner-contract", ProofOutcome::ContractFailure);
    }
}

#[test]
fn loop_contract_example_matches_native_for_every_byte_input() {
    use std::{fs, process::Command, time::Duration};
    let scratch = support::Scratch::new("proof-loop-contract-native");
    let mut source = include_str!("../examples/proof_loop_contracts.lim").to_owned();
    source.truncate(source.find("(#fn main ").unwrap());
    source.push_str(
        r#"
      (#fn main () #u64
        (#let-mut index #u16 0u16)
        (#while (#u16::lt index 256u16)
          (#let actual #u8 (#call countdown (: count (#as index #u8))))
          (#if (#u8::ne actual 0u8) (#block (#return 1u64)))
          (#set index (#u16::add-wrap index 1u16)))
        (#return 42u64))"#,
    );
    let path = scratch.path().join("main.lim");
    let binary = scratch.path().join("main");
    fs::write(&path, source).unwrap();
    let (status, _, stderr) = support::run(
        Command::new(env!("CARGO_BIN_EXE_lim"))
            .arg(&path)
            .arg("-o")
            .arg(&binary)
            .env("PATH", ""),
        Duration::from_secs(20),
        1024 * 1024,
    )
    .unwrap();
    assert!(status.success(), "{}", String::from_utf8_lossy(&stderr));
    let (status, _, stderr) = support::run(
        Command::new(&binary).env("PATH", ""),
        Duration::from_secs(5),
        1024 * 1024,
    )
    .unwrap();
    assert_eq!(
        status.code(),
        Some(42),
        "{}",
        String::from_utf8_lossy(&stderr)
    );
}
