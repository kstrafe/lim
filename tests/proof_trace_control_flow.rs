//! Loop exits, helper bodies and memory changes must preserve trace safety.
use lim::{CompileConfig, ProofOutcome};

fn check(source: &str, proposition: &str, invariants: &str, expected: Option<ProofOutcome>) {
    // Never confuse a malformed or ordinarily unsafe fixture with rejection by
    // the proof checker.
    let program = lim::parse_program(source).unwrap();
    lim::check_types(&program).unwrap();
    let source = format!("{source}\n(#theorem claim (#proof-loop-limit 1 (#proof-with-invariants ({invariants}) {proposition})))");
    let result = lim::check_theorem_details_from_path_with_config(
        &source,
        std::path::Path::new("trace-control.lim"),
        &CompileConfig::default(),
        "claim",
    );
    match expected {
        None => {
            result.unwrap_or_else(|error| panic!("{}\n{source}", error.message));
        }
        Some(outcome) => assert_eq!(
            result.expect_err("must remain unproved").proof_outcome(),
            Some(outcome),
            "{source}"
        ),
    }
}

const EVENTS: &str = r#"
  (#fn required () () (#return ()))
  (#fn action () () (#return ()))
"#;
const BEFORE: &str = "(#proof-calls-before entry required action)";

#[test]
fn call_history_survives_break_continue_and_early_return() {
    let source = format!(
        r#"{EVENTS}
      (#fn entry (: count #u8 : stop #bool : early #bool) ()
        (#let-mut remaining #u8 count)
        (#label again (#while (#u8::gt remaining 0u8)
          (#call required (:))
          (#if stop (#block (#break)))
          (#if early (#block (#return ())))
          (#call action (:))
          (#set remaining (#u8::sub-wrap remaining 1u8))
          (#continue)))
        (#if (#u8::gt count 0u8) (#call action (:)))
        (#return ()))"#
    );
    check(&source, BEFORE, "(entry again true remaining)", None);
}

#[test]
fn actual_for_step_calls_are_observed_before_forwarding_an_exit() {
    let source = format!(
        r#"{EVENTS}
      (#fn step (: value #u8) #u8
        (#call required (:))
        (#return (#u8::sub-wrap value 1u8)))
      (#fn entry (: count #u8) ()
        (#label again (#for (#let-mut remaining #u8 count)
          (#u8::gt remaining 0u8)
          (#set remaining (#call step (: value remaining)))
          (#continue)))
        (#if (#u8::gt count 0u8) (#call action (:)))
        (#return ()))"#
    );
    check(&source, BEFORE, "(entry again true remaining)", None);
}

#[test]
fn nested_invariant_loops_keep_monitor_history() {
    let source = format!(
        r#"{EVENTS}
      (#fn entry (: count #u8) ()
        (#let-mut outer-left #u8 count)
        (#label outer (#while (#u8::gt outer-left 0u8)
          (#let-mut inner-left #u8 count)
          (#label inner (#while (#u8::gt inner-left 0u8)
            (#call required (:))
            (#call action (:))
            (#set inner-left (#u8::sub-wrap inner-left 1u8))))
          (#set outer-left (#u8::sub-wrap outer-left 1u8))))
        (#return ()))"#
    );
    check(
        &source,
        BEFORE,
        "(entry outer true outer-left) (entry inner true inner-left)",
        None,
    );
}

const USER: &str = r#"
  (#struct User () (: ready #bool : data #u8))
  (#fn validate (: user (#ref User)) #bool (#return (#get user ready)))
  (#fn perform (: user (#ref User)) () (#return ()))
"#;
const VALIDATION: &str =
    "(#proof-requires-validation entry (#parameter-of validate user) (#parameter-of perform user))";

#[test]
fn nonzero_loop_exit_keeps_the_final_iterations_validation() {
    let source = format!(
        r#"{USER}
      (#fn entry (: user (#ref User) : count #u8) ()
        (#let-mut remaining #u8 count)
        (#label again (#while (#u8::gt remaining 0u8)
          (#let succeeded #bool (#call validate (: user user)))
          (#set remaining (#u8::sub-wrap remaining 1u8))))
        (#if (#u8::gt count 0u8)
          (#if (#get user ready) (#call perform (: user user))))
        (#return ()))"#
    );
    check(&source, VALIDATION, "(entry again true remaining)", None);
}

#[test]
fn writes_after_validation_fail_closed_under_negation_too() {
    let source = format!(
        r#"{USER}
      (#fn entry (: user (#ref-mut User) : count #u8) ()
        (#let-mut remaining #u8 count)
        (#label again (#while (#u8::gt remaining 0u8)
          (#if (#call validate (: user (#borrow (#deref user))))
            (#block
              (#deref-set (#borrow-mut (#get (#deref user) data)) 1u8)
              (#call perform (: user (#borrow (#deref user))))))
          (#set remaining (#u8::sub-wrap remaining 1u8))))
        (#return ()))"#
    );
    for proposition in [VALIDATION.to_owned(), format!("(#proof-not {VALIDATION})")] {
        check(
            &source,
            &proposition,
            "(entry again true remaining)",
            Some(ProofOutcome::InductionFailure),
        );
    }
}

#[test]
fn changing_reference_graphs_require_revalidating_the_new_target() {
    let source = format!(
        r#"{USER}
      (#struct Holder () (: target (#ref User)))
      (#fn entry (: holder (#ref-mut Holder) : alternate (#ref User) : count #u8) ()
        (#let-mut remaining #u8 count)
        (#label again (#while (#u8::gt remaining 0u8)
          (#deref-set (#borrow-mut (#get (#deref holder) target)) alternate)
          (#if (#call validate (: user (#get (#deref holder) target)))
            (#call perform (: user (#get (#deref holder) target))))
          (#set remaining (#u8::sub-wrap remaining 1u8))))
        (#return ()))"#
    );
    check(&source, VALIDATION, "(entry again true remaining)", None);
    let wrong = source.replace(
        "(#deref-set (#borrow-mut (#get (#deref holder) target)) alternate)",
        "",
    );
    let wrong = wrong.replace(
        "(#call perform (: user (#get (#deref holder) target)))",
        "(#block (#deref-set (#borrow-mut (#get (#deref holder) target)) alternate) (#call perform (: user (#get (#deref holder) target))))");
    check(
        &wrong,
        VALIDATION,
        "(entry again true remaining)",
        Some(ProofOutcome::InductionFailure),
    );
}

#[test]
fn invalid_ranks_cannot_prove_a_property_or_its_negation() {
    let source = format!(
        r#"{EVENTS}
      (#fn entry (: count #u8) ()
        (#let-mut remaining #u8 count)
        (#label again (#while (#u8::gt remaining 0u8)
          (#call required (:)) (#call action (:))))
        (#return ()))"#
    );
    for proposition in [BEFORE.to_owned(), format!("(#proof-not {BEFORE})")] {
        check(
            &source,
            &proposition,
            "(entry again true remaining)",
            Some(ProofOutcome::InductionFailure),
        );
    }
}

#[test]
fn prefix_success_is_not_restored_after_transitive_failed_revalidation() {
    let source = format!(
        r#"{USER}
      (#fn validate-result (: user (#ref User) : result #bool) #bool
        (#return result))
      (#fn reject (: user (#ref User)) ()
        (#let ignored #bool (#call validate-result (: user user : result false)))
        (#return ()))
      (#fn entry (: user (#ref User) : count #u8) ()
        (#let valid #bool (#call validate-result (: user user : result true)))
        (#let-mut remaining #u8 count)
        (#label again (#while (#u8::gt remaining 0u8)
          (#if (#u8::eq remaining 2u8) (#call reject (: user user)))
          (#if (#u8::eq remaining 1u8) (#call perform (: user user)))
          (#set remaining (#u8::sub-wrap remaining 1u8))))
        (#return ()))"#
    );
    let validation = "(#proof-requires-validation entry (#parameter-of validate-result user) (#parameter-of perform user))";
    for proposition in [validation.to_owned(), format!("(#proof-not {validation})")] {
        check(
            &source,
            &proposition,
            "(entry again true remaining)",
            Some(ProofOutcome::InductionFailure),
        );
    }
}
