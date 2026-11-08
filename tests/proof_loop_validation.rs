//! Validation evidence is an inductive resource, never a negative history fact.
use lim::{CompileConfig, ProofOutcome};
mod support;

const DECLS: &str = r#"
  (#struct User () (: ready #bool : data #u8))
  (#fn validate (: user (#ref User)) #bool (#return (#get user ready)))
  (#fn perform (: user (#ref User)) () (#return ()))
"#;
const VALID: &str = "(#proof-validated (#parameter-of validate user) user)";
const CLAIM: &str =
    "(#proof-requires-validation entry (#parameter-of validate user) (#parameter-of perform user))";

fn verify(source: &str, predicate: &str, expected: Option<ProofOutcome>) {
    let ordinary = lim::parse_program(source).unwrap();
    lim::check_types(&ordinary).unwrap();
    let source = format!("{source}\n(#theorem claim (#proof-loop-limit 1 (#proof-with-invariants ((entry again {predicate} remaining)) {CLAIM})))");
    verify_theorem(&source, expected);
}

fn verify_theorem(source: &str, expected: Option<ProofOutcome>) {
    let result = lim::check_theorem_details_from_path_with_config(
        source,
        std::path::Path::new("loop-validation.lim"),
        &CompileConfig::default(),
        "claim",
    );
    match expected {
        None => {
            result.unwrap_or_else(|error| panic!("{}\n{source}", error.message));
        }
        Some(outcome) => {
            let error = result.expect_err("must remain unproved");
            assert_eq!(
                error.proof_outcome(),
                Some(outcome),
                "{}\n{source}",
                error.message
            );
        }
    }
}

fn cached(body: &str, initial: &str) -> String {
    format!(
        r#"{DECLS}
      (#fn entry (: user (#ref User) : alternate (#ref User) : count #u8) ()
        (#let-mut checked #bool {initial})
        (#let-mut remaining #u8 count)
        (#label again (#while (#u8::gt remaining 0u8)
          {body}
          (#set remaining (#u8::sub-wrap remaining 1u8))))
        (#return ()))"#
    )
}

#[test]
fn validation_once_then_repeated_actions_proves_with_an_explicit_invariant() {
    let source = cached(
        r#"
      (#if (#bool::not checked)
        (#block (#set checked (#call validate (: user user)))))
      (#if checked (#call perform (: user user)))
    "#,
        "false",
    );
    verify(&source, &format!("(#proof-implies checked {VALID})"), None);
    verify(&source, "true", Some(ProofOutcome::InductionFailure));
}

#[test]
fn an_unestablished_initial_requirement_is_not_an_assumption() {
    let source = cached("(#if checked (#call perform (: user user)))", "true");
    verify(
        &source,
        &format!("(#proof-implies checked {VALID})"),
        Some(ProofOutcome::InductionFailure),
    );
}

#[test]
fn wrong_object_evidence_does_not_authorize_actions() {
    let source = cached(
        r#"
      (#if (#bool::not checked)
        (#block (#set checked (#call validate (: user alternate)))))
      (#if checked (#call perform (: user user)))
    "#,
        "false",
    );
    let alternate = VALID.replace(") user)", ") alternate)");
    verify(
        &source,
        &format!("(#proof-implies checked {alternate})"),
        Some(ProofOutcome::InductionFailure),
    );
}

#[test]
fn writes_require_revoking_the_corresponding_cached_flag() {
    let source = format!(
        r#"{DECLS}
      (#fn entry (: user (#ref-mut User) : count #u8) ()
        (#let-mut checked #bool false)
        (#let-mut remaining #u8 count)
        (#label again (#while (#u8::gt remaining 0u8)
          (#if (#bool::not checked)
            (#block (#set checked (#call validate (: user (#borrow (#deref user)))))))
          (#if checked (#call perform (: user (#borrow (#deref user)))))
          (#deref-set (#borrow-mut (#get (#deref user) data)) remaining)
          (#set checked false)
          (#set remaining (#u8::sub-wrap remaining 1u8))))
        (#return ()))"#
    );
    let predicate = "(#proof-implies checked (#proof-validated (#parameter-of validate user) (#borrow (#deref user))))";
    verify(&source, predicate, None);
    let stale = source.replace("(#set checked false)", "");
    verify(&stale, predicate, Some(ProofOutcome::InductionFailure));
}

#[test]
fn failed_revalidation_must_update_the_cached_flag() {
    let source = format!(
        r#"{DECLS}
      (#fn decide (: user (#ref User) : result #bool) #bool (#return result))
      (#fn entry (: user (#ref User) : count #u8) ()
        (#let-mut checked #bool false)
        (#let-mut remaining #u8 count)
        (#label again (#while (#u8::gt remaining 0u8)
          (#if checked (#call perform (: user user)))
          (#set checked (#call decide (: user user : result (#u8::gt remaining 2u8))))
          (#set remaining (#u8::sub-wrap remaining 1u8))))
        (#return ()))"#
    );
    let claim = CLAIM.replace("#parameter-of validate user", "#parameter-of decide user");
    let predicate = "(#proof-implies checked (#proof-validated (#parameter-of decide user) user))";
    let theorem = format!("{source} (#theorem claim (#proof-loop-limit 1 (#proof-with-invariants ((entry again {predicate} remaining)) {claim})))");
    verify_theorem(&theorem, None);
    let stale = theorem.replace(
        "(#set checked (#call decide (: user user : result (#u8::gt remaining 2u8))))",
        "(#let ignored #bool (#call decide (: user user : result false))) (#set checked true)",
    );
    verify_theorem(&stale, Some(ProofOutcome::InductionFailure));
}

#[test]
fn negative_evidence_queries_and_negated_failures_are_rejected() {
    let source = cached("", "false");
    for predicate in [
        format!("(#proof-not {VALID})"),
        format!("(#proof-eq {VALID} false)"),
        format!("(#proof-implies {VALID} false)"),
        format!("(#if {VALID} true false)"),
        format!("(#bool::eq {VALID} false)"),
    ] {
        for claim in [CLAIM.to_owned(), format!("(#proof-not {CLAIM})")] {
            let theorem = format!("{source} (#theorem claim (#proof-with-invariants ((entry again {predicate} remaining)) {claim}))");
            verify_theorem(&theorem, Some(ProofOutcome::Unsupported));
        }
    }
}

#[test]
fn descriptors_and_operand_types_are_checked_before_assuming_facts() {
    let source = cached("", "false");
    for predicate in [
        "(#proof-validated (#parameter-of validate missing) user)",
        "(#proof-validated (#parameter-of perform user) user)",
        "(#proof-validated (#parameter-of validate user) count)",
        "(#proof-validated (#parameter-of validate user))",
        "(#proof-validated (validate user) user)",
    ] {
        verify(&source, predicate, Some(ProofOutcome::Invalid));
    }
}

#[test]
fn validation_requirements_are_not_runtime_values_or_general_history_queries() {
    verify_theorem(
        &format!("{DECLS} (#theorem claim (#proof-not {VALID}))"),
        Some(ProofOutcome::Invalid),
    );
    let source = cached("", "false");
    let theorem = format!("{source} (#theorem claim (#proof-with-invariants ((entry again {VALID} remaining)) (#proof-calls-before entry validate perform)))");
    verify_theorem(&theorem, Some(ProofOutcome::Unsupported));
    let theorem = format!(
        "{source} (#theorem claim (#proof-with-invariants ((entry again true {VALID})) {CLAIM}))"
    );
    verify_theorem(&theorem, Some(ProofOutcome::Unsupported));
}

#[test]
fn installing_a_reference_enum_payload_requires_establishing_its_evidence() {
    let source = format!(
        r#"{DECLS}
      (#enum Maybe () (: Maybe.None : Maybe.Some (#ref User)))
      (#fn entry (: selected (#ref-mut Maybe) : user (#ref User) : count #u8) ()
        (#deref-set selected (#enum-literal Maybe.None))
        (#let-mut remaining #u8 count)
        (#label again (#while (#u8::gt remaining 0u8)
          (#match (#deref selected)
            (#case Maybe.None (#block
              (#let valid #bool (#call validate (: user user)))
              (#if valid (#block (#deref-set selected (#enum-literal Maybe.Some user))))))
            (#case (Maybe.Some saved) (#call perform (: user saved))))
          (#set remaining (#u8::sub-wrap remaining 1u8))))
        (#return ()))"#
    );
    let predicate = "(#match (#deref selected) (#case Maybe.None true) (#case (Maybe.Some subject) (#proof-validated (#parameter-of validate user) subject)))";
    verify(&source, predicate, None);
    let invalid = source.replace("(#call validate (: user user))", "true");
    for claim in [CLAIM.to_owned(), format!("(#proof-not {CLAIM})")] {
        let theorem = format!("{invalid} (#theorem claim (#proof-with-invariants ((entry again {predicate} remaining)) {claim}))");
        verify_theorem(&theorem, Some(ProofOutcome::InductionFailure));
    }
}

#[test]
fn symbolic_aliases_revoke_both_flags_in_either_invariant_query_order() {
    let source = format!(
        r#"{DECLS}
      (#fn decide (: user (#ref User) : result #bool) #bool (#return result))
      (#fn entry (: users (#ref (#array User 2)) : i #usize : j #usize : count #u8) ()
        (#if (#usize::ge i 2usize) (#block (#return ())))
        (#if (#usize::ge j 2usize) (#block (#return ())))
        (#let first (#ref User) (#borrow (#index (#deref users) i)))
        (#let second (#ref User) (#borrow (#index (#deref users) j)))
        (#let-mut checked-first #bool false)
        (#let-mut checked-second #bool false)
        (#let-mut remaining #u8 count)
        (#label again (#while (#u8::gt remaining 0u8)
          (#if (#bool::not checked-first)
            (#block (#set checked-first (#call decide (: user first : result true)))))
          (#if (#bool::not checked-second)
            (#block (#set checked-second (#call decide (: user second : result true)))))
          (#let ignored #bool (#call decide (: user first : result false)))
          (#set checked-first false)
          (#if (#usize::eq i j) (#block (#set checked-second false)))
          (#if checked-second (#call perform (: user second)))
          (#set remaining (#u8::sub-wrap remaining 1u8))))
        (#return ()))"#
    );
    lim::check_types(&lim::parse_program(&source).unwrap()).unwrap();
    let first =
        "(#proof-implies checked-first (#proof-validated (#parameter-of decide user) first))";
    let second =
        "(#proof-implies checked-second (#proof-validated (#parameter-of decide user) second))";
    let claim = CLAIM.replace("#parameter-of validate user", "#parameter-of decide user");
    for (a, b) in [(first, second), (second, first)] {
        let theorem = format!("{source} (#theorem claim (#proof-loop-limit 1 (#proof-with-invariants ((entry again (#proof-and {a} {b}) remaining)) {claim})))");
        verify_theorem(&theorem, None);
        let stale = theorem.replace(
            "(#if (#usize::eq i j) (#block (#set checked-second false)))",
            "",
        );
        verify_theorem(&stale, Some(ProofOutcome::InductionFailure));
    }
}

#[test]
fn referenced_dependency_writes_revoke_reconstructed_evidence() {
    let source = r#"
      (#struct Holder () (: value (#ref-mut #u8)))
      (#fn validate-holder (: holder (#ref Holder)) #bool (#return true))
      (#fn perform-holder (: holder (#ref Holder)) () (#return ()))
      (#fn entry (: holder (#ref-mut Holder) : count #u8) ()
        (#let-mut checked #bool false)
        (#let-mut remaining #u8 count)
        (#label again (#while (#u8::gt remaining 0u8)
          (#if (#bool::not checked) (#block
            (#set checked (#call validate-holder (: holder (#borrow (#deref holder)))))))
          (#if checked (#call perform-holder (: holder (#borrow (#deref holder)))))
          (#deref-set (#get (#deref holder) value) remaining)
          (#set checked false)
          (#set remaining (#u8::sub-wrap remaining 1u8))))
        (#return ()))
    "#;
    lim::check_types(&lim::parse_program(source).unwrap()).unwrap();
    let predicate = "(#proof-implies checked (#proof-validated (#parameter-of validate-holder holder) (#borrow (#deref holder))))";
    let claim = "(#proof-requires-validation entry (#parameter-of validate-holder holder) (#parameter-of perform-holder holder))";
    let theorem = format!("{source} (#theorem claim (#proof-loop-limit 1 (#proof-with-invariants ((entry again {predicate} remaining)) {claim})))");
    verify_theorem(&theorem, None);
    verify_theorem(
        &theorem.replace("(#set checked false)", ""),
        Some(ProofOutcome::InductionFailure),
    );
}

#[test]
fn cached_validation_example_replays_every_byte_count_and_ready_value() {
    use std::{fs, process::Command, time::Duration};
    let mut source = include_str!("../examples/proof_cached_validation.lim").to_owned();
    source.truncate(source.find("(#fn main ").unwrap());
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
    let scratch = support::Scratch::new("cached-validation-native");
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

#[test]
fn abstract_fact_budgets_fail_closed_and_repeated_queries_share_one_fact() {
    let mut source = String::from(
        r#"
      (#fn validate (: item (#ref #u8)) #bool (#return true))
      (#fn perform (: item (#ref #u8)) () (#return ()))
      (#fn entry (: count #u8) ()
    "#,
    );
    for index in 0..65 {
        source.push_str(&format!("(#let object{index} #u8 0u8)\n"));
    }
    source.push_str(
        r#"
      (#let-mut remaining #u8 count)
      (#label again (#while (#u8::gt remaining 0u8)
        (#set remaining (#u8::sub-wrap remaining 1u8))))
      (#return ()))
    "#,
    );
    let claim = "(#proof-requires-validation entry (#parameter-of validate item) (#parameter-of perform item))";
    for repeated in [false, true] {
        let mut predicate = String::from("(#proof-or true ");
        for index in 0..65 {
            let object = if repeated { 0 } else { index };
            predicate.push_str(&format!(
                "(#proof-validated (#parameter-of validate item) (#borrow object{object})) "
            ));
        }
        predicate.push(')');
        let theorem = format!("{source} (#theorem claim (#proof-loop-limit 1 (#proof-with-invariants ((entry again {predicate} remaining)) {claim})))");
        verify_theorem(
            &theorem,
            if repeated {
                None
            } else {
                Some(ProofOutcome::ResourceLimit)
            },
        );
        if !repeated {
            let negated = theorem.replace(claim, &format!("(#proof-not {claim})"));
            verify_theorem(&negated, Some(ProofOutcome::ResourceLimit));
        }
    }
}

#[test]
fn imported_validator_labels_resolve_without_adding_runtime_code() {
    use std::fs;
    let scratch = support::Scratch::new("loop-evidence-resolution");
    fs::create_dir(scratch.path().join("library")).unwrap();
    fs::write(
        scratch.path().join("library/lib.lim"),
        r#"
      (#export validate perform)
      (#fn validate (: user (#ref #u8)) #bool (#return true))
      (#fn perform (: target (#ref #u8)) () (#return ()))
    "#,
    )
    .unwrap();
    let source = r#"
      (#alias check = ./library/lib.lim::validate)
      (#alias action = ./library/lib.lim::perform)
      (#fn user () #u8 (#return 0u8))
      (#fn entry (: input (#ref #u8) : count #u8) ()
        (#let-mut checked #bool false)
        (#let-mut remaining #u8 count)
        (#label again (#while (#u8::gt remaining 0u8)
          (#if (#bool::not checked) (#block (#set checked (#call check (: user input)))))
          (#if checked (#call action (: target input)))
          (#set remaining (#u8::sub-wrap remaining 1u8))))
        (#return ()))
      (#fn main () #u64
        (#let value #u8 42u8)
        (#call entry (: input (#borrow value) : count 42u8))
        (#return 42u64))
    "#;
    let theorem = r#"
      (#theorem claim (#proof-loop-limit 1
        (#proof-with-invariants ((entry again
          (#proof-implies checked (#proof-validated (#parameter-of check user) input)) remaining))
          (#proof-requires-validation entry (#parameter-of check user) (#parameter-of action target)))))
    "#;
    let path = scratch.path().join("main.lim");
    let compile = |text: &str| {
        lim::compile_source_to_assembly(
            text,
            &path,
            &CompileConfig::default(),
            &scratch.path().join("cache"),
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap()
    };
    assert_eq!(compile(source), compile(&format!("{source}\n{theorem}")));
}
