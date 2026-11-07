//! Regression coverage for inconclusive induction obligations.

use std::{fs, process::Command, time::Duration};

mod support;

const IDENTITY_COUNTDOWN: &str = r#"
  (#fn identity-countdown (: count #u8) #u8
    (#let-mut remaining #u8 count)
    (#let-mut answer #u8 0u8)
    (#label again
      (#while (#u8::gt remaining 0u8)
        (#set answer (#u8::add-wrap answer 1u8))
        (#set remaining (#u8::sub-wrap remaining 1u8))))
    (#return answer))
"#;

fn check(source: &str) -> Result<(), String> {
    let program = lim::parse_program(source)?;
    lim::check_types(&program)
}

fn rejected_as_unproved(source: &str) {
    let error = check(source).expect_err("inconclusive inductive claim must fail closed");
    assert!(
        error.starts_with("theorem '"),
        "not a theorem failure: {error}"
    );
    assert!(
        error.contains("unproved"),
        "expected unproved diagnostic: {error}"
    );
    assert!(
        error.contains("inductive obligation"),
        "expected inductive obligation diagnostic: {error}"
    );
    assert!(
        !error.contains("disproved"),
        "claim was reported disproved: {error}"
    );
}

#[test]
fn weak_invariant_contract_and_negations_are_unproved() {
    let contract = "(#proof-contract identity-countdown true
      (#proof-eq (#proof-result) count))";
    let weak = format!(
        "{IDENTITY_COUNTDOWN}
         (#theorem weak
           (#proof-with-invariants ((identity-countdown again true remaining))
             {contract}))"
    );
    rejected_as_unproved(&weak);

    let negated_contract = format!(
        "{IDENTITY_COUNTDOWN}
         (#theorem weak-negation
           (#proof-with-invariants ((identity-countdown again true remaining))
             (#proof-not {contract})))"
    );
    rejected_as_unproved(&negated_contract);

    let negated_forall_call = format!(
        "{IDENTITY_COUNTDOWN}
         (#theorem weak-forall-negation
           (#proof-with-invariants ((identity-countdown again true remaining))
             (#proof-not
               (#proof-for-all ((count #u8))
                 (#proof-eq (#call identity-countdown (: count count)) count)))))"
    );
    rejected_as_unproved(&negated_forall_call);
}

#[test]
fn strong_sum_invariant_proves_identity_contract() {
    let source = format!(
        "{IDENTITY_COUNTDOWN}
         (#theorem strong
           (#proof-with-invariants
             ((identity-countdown again
               (#u8::eq (#u8::add-wrap answer remaining) count)
               remaining))
             (#proof-contract identity-countdown true
               (#proof-eq (#proof-result) count))))"
    );
    check(&source).unwrap_or_else(|error| panic!("{error}\n{source}"));
}

#[test]
fn concrete_loop_limit_counterexample_to_false_contract_is_proved() {
    let source = format!(
        "{IDENTITY_COUNTDOWN}
         (#theorem bounded-counterexample
           (#proof-loop-limit 4
             (#proof-not
               (#proof-contract identity-countdown
                 (#u8::le count 2u8)
                 (#proof-eq (#proof-result) 42u8)))))"
    );
    check(&source).unwrap_or_else(|error| panic!("{error}\n{source}"));
}

#[test]
fn native_replay_checks_identity_contract_for_all_u8_values() {
    let source_text = format!(
        "{IDENTITY_COUNTDOWN}
         (#fn main () #u64
           (#let-mut index #u16 0u16)
           (#while (#u16::lt index 256u16)
             (#let value #u8 (#as index #u8))
             (#let actual #u8 (#call identity-countdown (: count value)))
             (#if (#u8::ne actual value) (#block (#return 1u64)))
             (#set index (#u16::add-wrap index 1u16)))
           (#return 42u64))"
    );
    let scratch = support::Scratch::new("proof-induction-replay");
    let source = scratch.path().join("main.lim");
    let binary = scratch.path().join("main");
    fs::write(&source, source_text).unwrap();

    let (status, _, stderr) = support::run(
        Command::new(env!("CARGO_BIN_EXE_lim"))
            .arg(&source)
            .arg("-o")
            .arg(&binary)
            .env("PATH", ""),
        Duration::from_secs(20),
        1024 * 1024,
    )
    .unwrap();
    assert!(
        status.success(),
        "compile failed: {}",
        String::from_utf8_lossy(&stderr)
    );
    let (status, stdout, stderr) = support::run(
        Command::new(&binary).env("PATH", ""),
        Duration::from_secs(5),
        1024 * 1024,
    )
    .unwrap();
    assert_eq!(status.code(), Some(42));
    assert!(stdout.is_empty() && stderr.is_empty());
}
