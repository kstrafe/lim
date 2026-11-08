//! Different immutable contents exclude identity; equal contents never grant it.
use lim::{CompileConfig, ProofOutcome};
mod support;

const CLAIM: &str =
    "(#proof-requires-validation entry (#parameter-of validate user) (#parameter-of perform user))";
fn check(source: &str, claim: &str, expected: Option<ProofOutcome>) {
    lim::check_types(&lim::parse_program(source).expect("ordinary fixture must parse"))
        .expect("ordinary fixture must be safe");
    let source = format!("{source}\n(#theorem claim {claim})");
    let result = lim::check_theorem_details_from_path_with_config(
        &source,
        std::path::Path::new("alias-contents.lim"),
        &CompileConfig::default(),
        "claim",
    );
    match expected {
        None => {
            result.unwrap_or_else(|error| panic!("{}\n{source}", error.message));
        }
        Some(outcome) => {
            let error = result.expect_err("ambiguous identity must not be certified");
            assert_eq!(
                error.proof_outcome(),
                Some(outcome),
                "{}\n{source}",
                error.message
            );
        }
    }
}
fn declarations(ty: &str) -> String {
    format!("(#fn validate (: user (#ref {ty}) : accepted #bool) #bool (#return accepted))\n(#fn perform (: user (#ref {ty})) () (#return ()))")
}
fn inputs(ty: &str, prefix: &str) -> String {
    format!("{}\n(#fn entry (: first (#ref {ty}) : second (#ref {ty})) ()\n{prefix}\n(#let valid #bool (#call validate (: user second : accepted true)))\n(#let failed #bool (#call validate (: user first : accepted false)))\n(#call perform (: user second))\n(#return ()))", declarations(ty))
}
#[test]
fn different_scalar_contents_preserve_the_other_inputs_evidence() {
    for (ty, equality) in [("#u8", "#u8::eq"), ("#bool", "#bool::eq")] {
        let source = inputs(
            ty,
            &format!("(#if ({equality} (#deref first) (#deref second)) (#block (#return ())))"),
        );
        check(&source, CLAIM, None);
    }
}
#[test]
fn equal_scalar_contents_remain_ambiguous_under_negation() {
    let source = inputs(
        "#u8",
        "(#if (#u8::ne (#deref first) (#deref second)) (#block (#return ())))",
    );
    check(&source, CLAIM, Some(ProofOutcome::Unsupported));
    check(
        &source,
        &format!("(#proof-not {CLAIM})"),
        Some(ProofOutcome::Unsupported),
    );
}
#[test]
fn whole_record_array_and_tuple_values_can_exclude_identity() {
    for (ty, left, right) in [
        ("Record", "(#get first id)", "(#get second id)"),
        (
            "(#array #u8 2)",
            "(#index first 0usize)",
            "(#index second 0usize)",
        ),
        ("(#tuple #u8 #bool)", "(#get first 0)", "(#get second 0)"),
    ] {
        let source = format!(
            "(#struct Record () (: id #u8 : other #bool))\n{}",
            inputs(
                ty,
                &format!("(#if (#u8::eq {left} {right}) (#block (#return ())))")
            )
        );
        check(&source, CLAIM, None);
    }
}
#[test]
fn enum_tags_and_active_payloads_can_exclude_identity() {
    let decl = "(#enum Choice () (: Choice.Empty : Choice.Value #u8))";
    let tags = inputs(
        "Choice",
        r#"
      (#if (#variant-is first Choice.Value) (#block (#return ())))
      (#if (#variant-is second Choice.Empty) (#block (#return ())))
    "#,
    );
    check(&format!("{decl}\n{tags}"), CLAIM, None);
    let payloads = inputs(
        "Choice",
        r#"
      (#if (#variant-is first Choice.Empty) (#block (#return ())))
      (#if (#variant-is second Choice.Empty) (#block (#return ())))
      (#let first-value #u8 (#match (#deref first)
        (#case Choice.Empty 0u8) (#case (Choice.Value first-item) first-item)))
      (#let second-value #u8 (#match (#deref second)
        (#case Choice.Empty 0u8) (#case (Choice.Value second-item) second-item)))
      (#if (#u8::eq first-value second-value) (#block (#return ())))
    "#,
    );
    check(&format!("{decl}\n{payloads}"), CLAIM, None);
}
#[test]
fn reference_fields_do_not_make_fresh_records_definitely_distinct() {
    let decl = "(#struct Holder () (: id #u8 : link (#ref #u8)))";
    let ambiguous = format!(
        "{decl}\n{}",
        inputs(
            "Holder",
            "(#if (#u8::ne (#get first id) (#get second id)) (#block (#return ())))"
        )
    );
    check(&ambiguous, CLAIM, Some(ProofOutcome::Unsupported));
    check(
        &ambiguous,
        &format!("(#proof-not {CLAIM})"),
        Some(ProofOutcome::Unsupported),
    );
    let distinct = format!(
        "{decl}\n{}",
        inputs(
            "Holder",
            "(#if (#u8::eq (#get first id) (#get second id)) (#block (#return ())))"
        )
    );
    check(&distinct, CLAIM, None);
}
#[test]
fn equal_contents_cannot_authorize_an_unvalidated_different_object() {
    let source = format!(
        r#"{}
      (#fn entry (: first (#ref #u8) : second (#ref #u8)) ()
        (#if (#u8::ne (#deref first) (#deref second)) (#block (#return ())))
        (#let valid #bool (#call validate (: user first : accepted true)))
        (#call perform (: user second)) (#return ()))
    "#,
        declarations("#u8")
    );
    check(&source, CLAIM, Some(ProofOutcome::Counterexample));
}
#[test]
fn cached_evidence_survives_loop_revalidation_of_a_distinct_input() {
    let source = format!(
        r#"{}
      (#fn entry (: first (#ref #u8) : second (#ref #u8) : count #u8) ()
        (#if (#u8::eq (#deref first) (#deref second)) (#block (#return ())))
        (#let checked #bool (#call validate (: user second : accepted true)))
        (#let-mut remaining #u8 count)
        (#label again (#while (#u8::gt remaining 0u8)
          (#let ignored #bool (#call validate (: user first : accepted false)))
          (#if checked (#call perform (: user second)))
          (#set remaining (#u8::sub-wrap remaining 1u8))))
        (#return ()))
    "#,
        declarations("#u8")
    );
    let claim = format!("(#proof-loop-limit 1 (#proof-with-invariants ((entry again (#proof-implies checked (#proof-validated (#parameter-of validate user) second)) remaining)) {CLAIM}))");
    check(&source, &claim, None);
    let ambiguous = source.replace(
        "(#if (#u8::eq (#deref first) (#deref second)) (#block (#return ())))",
        "",
    );
    check(&ambiguous, &claim, Some(ProofOutcome::InductionFailure));
    check(
        &ambiguous,
        &format!("(#proof-not {claim})"),
        Some(ProofOutcome::InductionFailure),
    );
}

#[test]
fn immutable_aliases_receive_consistent_results_from_a_pure_validator() {
    let source = r#"
      (#fn validate (: user (#ref #bool)) #bool (#return (#deref user)))
      (#fn perform (: user (#ref #bool)) () (#return ()))
      (#fn entry (: first (#ref #bool) : second (#ref #bool)) ()
        (#let checked #bool (#call validate (: user second)))
        (#let ignored #bool (#call validate (: user first)))
        (#if checked (#call perform (: user second)))
        (#return ()))
    "#;
    check(source, CLAIM, None);
}

#[test]
fn example_replays_every_byte_count_with_both_validation_results() {
    use std::{fs, process::Command, time::Duration};
    let mut source = include_str!("../examples/proof_distinct_validation.lim").to_owned();
    source.truncate(source.find("(#fn main ").unwrap());
    source.push_str(r#"
      (#fn main () #u64
        (#let-mut phase #u8 0u8)
        (#while (#u8::lt phase 2u8)
          (#let second-id #u8 (#if (#u8::eq phase 0u8) 41u8 42u8))
          (#let second User (#struct-literal User (: id second-id)))
          (#let-mut index #u16 0u16)
          (#while (#u16::lt index 256u16)
            (#let count #u8 (#as index #u8))
            (#let first User (#struct-literal User (: id (#u8::add-wrap count 17u8))))
            (#let expected #u8 (#if (#u8::eq phase 0u8) 0u8 count))
            (#let answer #u8 (#call process (: first (#borrow first) : second (#borrow second) : count count)))
            (#if (#u8::ne answer expected) (#block (#forget first) (#forget second) (#return 1u64)))
            (#let alias-answer #u8 (#call process (: first (#borrow second) : second (#borrow second) : count count)))
            (#if (#u8::ne alias-answer expected) (#block (#forget first) (#forget second) (#return 2u64)))
            (#forget first)
            (#set index (#u16::add-wrap index 1u16)))
          (#forget second)
          (#set phase (#u8::add-wrap phase 1u8)))
        (#return 42u64))
    "#);
    let scratch = support::Scratch::new("alias-contents-native");
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
