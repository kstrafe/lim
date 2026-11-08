//! Bounded trace claims over invariant countdown loops.

use lim::{CompileConfig, Diagnostic, ProofOutcome};
mod support;

fn check(source: &str) -> Result<lim::CheckedTheorem, Diagnostic> {
    lim::check_theorem_details_from_path_with_config(
        source,
        std::path::Path::new("trace-induction.lim"),
        &CompileConfig::default(),
        "claim",
    )
}

fn proved(source: &str) {
    check(source).unwrap_or_else(|error| panic!("{}\n{source}", error.message));
}

fn induction_failure(source: &str) {
    let error = check(source).expect_err("abstract trace claim must fail closed");
    assert_eq!(
        error.proof_outcome(),
        Some(ProofOutcome::InductionFailure),
        "{}\n{source}",
        error.message
    );
}

const DECLS: &str = r#"
  (#struct User () (: ready #bool : data #u8))
  (#fn validate (: user (#ref User)) #bool (#return (#get user ready)))
  (#fn observe (: user (#ref User) : result #bool) #bool (#return result))
  (#fn action (: user (#ref User)) () (#return ()))
"#;

fn loop_body(body: &str) -> String {
    format!(
        r#"
      {DECLS}
      (#fn entry (: user (#ref User) : alternate (#ref User) : count #u8 : guard #bool) ()
        (#let-mut remaining #u8 count)
        (#label again
          (#while (#u8::gt remaining 0u8)
            {body}
            (#set remaining (#u8::sub-wrap remaining 1u8))))
        (#return ()))
    "#
    )
}

fn claim(body: &str, proposition: &str) -> String {
    format!(
        "{} (#theorem claim (#proof-loop-limit 1 (#proof-with-invariants ((entry again true remaining)) {})))",
        body, proposition
    )
}

#[test]
fn repeated_read_only_validation_authorizes_each_iteration_action() {
    let source = loop_body("(#if (#call validate (: user user)) (#call action (: user user)))");
    proved(&claim(
        &source,
        "(#proof-requires-validation entry (#parameter-of validate user) (#parameter-of action user))",
    ));
}

#[test]
fn each_iteration_validation_precedes_action() {
    let source = loop_body("(#call validate (: user user)) (#call action (: user user))");
    proved(&claim(
        &source,
        "(#proof-calls-before entry validate action)",
    ));
}

#[test]
fn immutable_boolean_guard_preserves_calls_when() {
    let source = loop_body(
        "(#if (#call observe (: user user : result guard)) (#call action (: user user)))",
    );
    proved(&claim(
        &source,
        "(#proof-calls-when entry observe false action)",
    ));
}

#[test]
fn prefix_validation_survives_read_only_loop() {
    let source = format!(
        r#"{DECLS}
      (#fn entry (: user (#ref User) : count #u8) ()
        (#let valid #bool (#call validate (: user user)))
        (#let-mut remaining #u8 count)
        (#label again
          (#while (#u8::gt remaining 0u8)
            (#if valid (#call action (: user user)))
            (#set remaining (#u8::sub-wrap remaining 1u8))))
        (#return ()))"#
    );
    proved(&claim(
        &source,
        "(#proof-requires-validation entry (#parameter-of validate user) (#parameter-of action user))",
    ));
}

#[test]
fn action_before_validation_and_wrong_object_fail_inductively() {
    for body in [
        loop_body("(#call action (: user user)) (#call validate (: user user))"),
        loop_body("(#if (#call validate (: user user)) (#call action (: user alternate)))"),
    ] {
        induction_failure(&claim(
            &body,
            "(#proof-requires-validation entry (#parameter-of validate user) (#parameter-of action user))",
        ));
    }
}

#[test]
fn later_only_required_call_and_bad_observation_are_not_proved_or_negated() {
    let late = loop_body("(#call action (: user user)) (#call validate (: user user))");
    induction_failure(&claim(&late, "(#proof-calls-before entry validate action)"));

    // A false result from observe must rule out the later action in every
    // iteration, including under the abstract loop fixed point.
    let observation = loop_body(
        "(#if (#bool::not (#call observe (: user user : result guard))) (#call action (: user user)))",
    );
    for proposition in [
        "(#proof-calls-when entry observe false action)",
        "(#proof-not (#proof-calls-when entry observe false action))",
    ] {
        induction_failure(&claim(&observation, proposition));
    }
}

#[test]
fn validation_obtained_in_one_iteration_does_not_authorize_a_later_action() {
    let source = format!(
        r#"{DECLS}
      (#fn entry (: user (#ref User) : count #u8) ()
        (#let-mut remaining #u8 count)
        (#label again
          (#while (#u8::gt remaining 0u8)
            (#if (#u8::eq remaining 2u8)
              (#block (#let ignored #bool (#call validate (: user user))) ()))
            (#if (#u8::eq remaining 1u8) (#call action (: user user)))
            (#set remaining (#u8::sub-wrap remaining 1u8))))
        (#return ()))"#
    );
    induction_failure(&claim(
        &source,
        "(#proof-requires-validation entry (#parameter-of validate user) (#parameter-of action user))",
    ));
}

#[test]
fn observation_and_action_in_different_iterations_remain_unproved() {
    let observe_then_act = loop_body(
        "(#if (#u8::eq remaining 2u8) (#block (#let ignored #bool (#call observe (: user user : result false))) ()))\n            (#if (#u8::eq remaining 1u8) (#call action (: user user)))",
    );
    let act_then_observe = loop_body(
        "(#if (#u8::eq remaining 2u8) (#call action (: user user)))\n            (#if (#u8::eq remaining 1u8) (#block (#let ignored #bool (#call observe (: user user : result false))) ()))",
    );
    let proposition = "(#proof-calls-when entry observe false action)";
    for source in [observe_then_act, act_then_observe] {
        induction_failure(&claim(&source, proposition));
        induction_failure(&claim(
            &source,
            "(#proof-not (#proof-calls-when entry observe false action))",
        ));
    }
}

#[test]
fn failed_validation_in_an_earlier_iteration_does_not_authorize_later_action() {
    let source = format!(
        r#"{DECLS}
      (#fn validate-result (: user (#ref User) : result #bool) #bool
        (#return result))
      (#fn prepare (: user (#ref User) : count #u8) ()
        (#let-mut remaining #u8 count)
        (#label again
          (#while (#u8::gt remaining 0u8)
            (#if (#u8::eq remaining 2u8)
              (#block (#let ignored #bool (#call validate-result (: user user : result false))) ()))
            (#if (#u8::eq remaining 1u8) (#call action (: user user)))
            (#set remaining (#u8::sub-wrap remaining 1u8))))
        (#return ()))
      (#fn entry (: user (#ref User) : count #u8) ()
        (#call prepare (: user user : count count))
        (#return ()))"#
    );
    let theorem = format!(
        r#"{source}
      (#theorem claim
        (#proof-loop-limit 1
          (#proof-with-invariants ((prepare again true remaining))
            (#proof-requires-validation prepare
              (#parameter-of validate-result user) (#parameter-of action user)))))"#
    );
    induction_failure(&theorem);
}

#[test]
fn selected_weak_helper_contract_does_not_hide_actual_trace_calls() {
    let source = r#"
      (#struct User () (: ready #bool : data #u8))
      (#fn validate (: user (#ref User)) #bool (#return (#get user ready)))
      (#fn action (: user (#ref User)) () (#return ()))
      (#fn prepare (: user (#ref User)) ()
        (#let ignored #bool (#call validate (: user user)))
        (#return ()))
      (#fn entry (: user (#ref User) : count #u8) ()
        (#let-mut remaining #u8 count)
        (#label again
          (#while (#u8::gt remaining 0u8)
            (#call prepare (: user user))
            (#call action (: user user))
            (#set remaining (#u8::sub-wrap remaining 1u8))))
        (#return ()))
      (#theorem prepare-contract (#proof-contract prepare true true))
      (#theorem claim
        (#proof-using (prepare-contract)
          (#proof-loop-limit 1
            (#proof-with-invariants ((entry again true remaining))
              (#proof-calls-before entry validate action)))))
    "#;
    proved(source);
}

#[test]
fn trace_example_replays_all_byte_counts_for_both_ready_values() {
    use std::{fs, process::Command, time::Duration};

    let mut source = include_str!("../examples/proof_trace_induction.lim").to_owned();
    source.truncate(source.find("(#fn main ").expect("example main function"));
    source.push_str(
        r#"
      (#fn main () #u64
        (#let-mut phase #u8 0u8)
        (#while (#u8::lt phase 2u8)
          (#let ready #bool (#u8::eq phase 1u8))
          (#let user User (#struct-literal User (: ready ready : data 42u8)))
          (#let-mut index #u16 0u16)
          (#while (#u16::lt index 256u16)
            (#let count #u8 (#as index #u8))
            (#let answer #u8 (#call process (: user (#borrow user) : count count)))
            (#let expected #u8 (#if ready count 0u8))
            (#if (#u8::ne answer expected) (#block (#forget user) (#return 1u64)))
            (#set index (#u16::add-wrap index 1u16)))
          (#forget user)
          (#set phase (#u8::add-wrap phase 1u8)))
        (#return 42u64))
    "#,
    );

    let scratch = support::Scratch::new("proof-trace-induction-native");
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
