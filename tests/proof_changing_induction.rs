//! Regression coverage for bounded induction over changing reference graphs.

use lim::{CompileConfig, Diagnostic, ProofOutcome};
mod support;

fn check(source: &str, theorem: &str) -> Result<lim::CheckedTheorem, Diagnostic> {
    lim::check_theorem_details_from_path_with_config(
        source,
        std::path::Path::new("changing-induction.lim"),
        &CompileConfig::default(),
        theorem,
    )
}

fn proved(source: &str, theorem: &str) {
    check(source, theorem).unwrap_or_else(|error| panic!("{}\n{source}", error.message));
}

fn induction_failure(source: &str, theorem: &str) {
    let error = check(source, theorem).expect_err("must fail closed");
    assert_eq!(
        error.proof_outcome(),
        Some(ProofOutcome::InductionFailure),
        "{}\n{source}",
        error.message
    );
}

#[test]
fn retargeted_stored_shared_reference_proves_contents_by_countdown_invariant() {
    proved(
        r#"
      (#struct Holder () (: target (#ref #u8)))
      (#fn retarget (: holder (#ref-mut Holder) : alternate (#ref #u8) : count #u8) #u8
        (#let-mut remaining #u8 count)
        (#let original #u8 (#deref (#get (#deref holder) target)))
        (#label again
          (#while (#u8::gt remaining 0u8)
            (#deref-set (#borrow-mut (#get (#deref holder) target)) alternate)
            (#set remaining (#u8::sub-wrap remaining 1u8))))
        (#return (#deref (#get (#deref holder) target))))
      (#theorem retarget-contract
        (#proof-with-invariants
          ((retarget again
            (#proof-and
              (#u8::le remaining count)
              (#proof-implies (#u8::eq remaining count)
                (#u8::eq (#deref (#get (#deref holder) target)) original))
              (#proof-implies (#u8::lt remaining count)
                (#u8::eq (#deref (#get (#deref holder) target)) (#deref alternate))))
            remaining))
          (#proof-contract retarget true
            (#proof-and
              (#proof-implies (#u8::eq count 0u8)
                (#proof-eq (#proof-result) (#proof-old (#deref (#get holder target)))))
              (#proof-implies (#u8::gt count 0u8)
                (#proof-eq (#proof-result) (#deref alternate)))))))
    "#,
        "retarget-contract",
    );
}

#[test]
fn clearing_reference_enum_is_proved_from_variant_invariant() {
    proved(
        r#"
      (#enum Maybe () (: Maybe.None : Maybe.Some (#ref #u8)))
      (#fn clear (: target (#ref-mut Maybe) : count #u8) ()
        (#let-mut remaining #u8 count)
        (#label again
          (#while (#u8::gt remaining 0u8)
            (#deref-set target (#enum-literal Maybe.None))
            (#set remaining (#u8::sub-wrap remaining 1u8))))
        (#return ()))
      (#theorem clear-contract
        (#proof-with-invariants
          ((clear again
            (#proof-and
              (#u8::le remaining count)
              (#proof-implies (#u8::lt remaining count)
                (#variant-is (#deref target) Maybe.None)))
            remaining))
          (#proof-contract clear true
            (#proof-implies (#u8::gt count 0u8)
              (#variant-is (#deref target) Maybe.None)))))
    "#,
        "clear-contract",
    );
}

#[test]
fn populating_reference_enum_proves_contents_after_nonzero_countdown() {
    proved(
        r#"
      (#enum Maybe () (: Maybe.None : Maybe.Some (#ref #u8)))
      (#fn populate (: target (#ref-mut Maybe) : alternate (#ref #u8) : count #u8) ()
        (#let-mut remaining #u8 count)
        (#label again
          (#while (#u8::gt remaining 0u8)
            (#deref-set target (#enum-literal Maybe.Some alternate))
            (#set remaining (#u8::sub-wrap remaining 1u8))))
        (#return ()))
      (#theorem populate-contract
        (#proof-with-invariants
          ((populate again
            (#proof-and
              (#u8::le remaining count)
              (#proof-implies (#u8::lt remaining count)
                (#proof-and
                  (#variant-is (#deref target) Maybe.Some)
                  (#match (#deref target) (#case (Maybe.Some value) (#u8::eq (#deref value) (#deref alternate))) (#case Maybe.None false)))))
            remaining))
          (#proof-contract populate true
            (#proof-implies (#u8::gt count 0u8)
              (#proof-and
                (#variant-is (#deref target) Maybe.Some)
                (#match (#deref target) (#case (Maybe.Some value) (#u8::eq (#deref value) (#deref alternate))) (#case Maybe.None false)))))))
    "#,
        "populate-contract",
    );
}

#[test]
fn wrong_retargeted_contents_and_negation_fail_induction() {
    let body = r#"
      (#struct Holder () (: target (#ref #u8)))
      (#fn retarget (: holder (#ref-mut Holder) : alternate (#ref #u8) : count #u8) #u8
        (#let-mut remaining #u8 count)
        (#let original #u8 (#deref (#get (#deref holder) target)))
        (#label again
          (#while (#u8::gt remaining 0u8)
            (#deref-set (#borrow-mut (#get (#deref holder) target)) alternate)
            (#set remaining (#u8::sub-wrap remaining 1u8))))
        (#return (#deref (#get (#deref holder) target))))
    "#;
    for claim in [
        "(#proof-contract retarget true (#proof-eq (#proof-result) (#proof-old (#deref (#get holder target)))))",
        "(#proof-not (#proof-contract retarget true (#proof-eq (#proof-result) (#proof-old (#deref (#get holder target))))))",
    ] {
        let source = format!(
            "{body} (#theorem claim (#proof-with-invariants ((retarget again (#u8::le remaining count) remaining)) {claim}))"
        );
        induction_failure(&source, "claim");
    }
}

#[test]
fn enum_tag_claim_without_variant_invariant_and_negation_fail_induction() {
    let body = r#"
      (#enum Maybe () (: Maybe.None : Maybe.Some (#ref #u8)))
      (#fn clear (: target (#ref-mut Maybe) : count #u8) ()
        (#let-mut remaining #u8 count)
        (#label again
          (#while (#u8::gt remaining 0u8)
            (#deref-set target (#enum-literal Maybe.None))
            (#set remaining (#u8::sub-wrap remaining 1u8))))
        (#return ()))
    "#;
    for claim in [
        "(#proof-contract clear (#u8::gt count 0u8) (#variant-is (#deref target) Maybe.None))",
        "(#proof-not (#proof-contract clear (#u8::gt count 0u8) (#variant-is (#deref target) Maybe.None)))",
    ] {
        let source = format!(
            "{body} (#theorem claim (#proof-with-invariants ((clear again (#u8::le remaining count) remaining)) {claim}))"
        );
        induction_failure(&source, "claim");
    }
}

#[test]
fn shrinking_slice_geometry_proves_termination_and_empty_result() {
    proved(
        r#"
      (#struct View () (: view (#slice #u8)))
      (#fn shrink-view (: holder (#ref-mut View)) #usize
        (#label again (#while (#usize::gt (#slice-len (#get holder view)) 0usize)
          (#let next (#slice #u8) (#slice-range (#get holder view) 1usize (#slice-len (#get holder view))))
          (#deref-set (#borrow-mut (#get (#deref holder) view)) next)))
        (#return (#slice-len (#get holder view))))
      (#fn shrink (: source (#ref (#array #u8 3))) #usize
        (#let-mut holder View (#struct-literal View (: view (#slice-of source))))
        (#let result #usize (#call shrink-view (: holder (#borrow-mut holder))))
        (#forget holder) (#return result))
      (#theorem claim (#proof-with-invariants ((shrink-view again true (#slice-len (#get holder view))))
        (#proof-contract shrink true (#proof-eq (#proof-result) 0usize))))
    "#,
        "claim",
    );
}

#[test]
fn enum_invariant_patterns_cannot_shadow_locals_or_run_effectful_blocks() {
    let prefix = r#"
      (#enum Maybe () (: Maybe.None : Maybe.Some (#ref #u8)))
      (#fn clear (: target (#ref-mut Maybe) : count #u8) ()
        (#let-mut remaining #u8 count)
        (#label again (#while (#u8::gt remaining 0u8)
          (#deref-set target (#enum-literal Maybe.None))
          (#set remaining (#u8::sub-wrap remaining 1u8))))
        (#return ()))"#;
    for (predicate, expected) in [
        ("(#match (#deref target) (#case (Maybe.Some remaining) true) (#case Maybe.None true))", ProofOutcome::Invalid),
        ("(#match (#deref target) (#case (Maybe.Some value) (#block (#let ignored #u8 0u8) true)) (#case Maybe.None true))", ProofOutcome::Unsupported),
    ] {
        let source = format!("{prefix} (#theorem claim (#proof-with-invariants ((clear again {predicate} remaining)) (#proof-contract clear true true)))");
        let error = check(&source, "claim").unwrap_err();
        assert_eq!(error.proof_outcome(), Some(expected), "{}", error.message);
    }
}

#[test]
fn reference_retargeting_example_matches_native_for_all_byte_counts_and_seeds() {
    use std::{fs, process::Command, time::Duration};
    let scratch = support::Scratch::new("proof-changing-reference-native");
    let mut source = include_str!("../examples/proof_reference_induction.lim").to_owned();
    source.truncate(source.find("(#fn main ").unwrap());
    source.push_str(r#"
      (#fn main () #u64
        (#let-mut seed #u16 0u16)
        (#while (#u16::lt seed 256u16)
          (#let left #u8 (#as seed #u8))
          (#let right #u8 (#u8::add-wrap left 17u8))
          (#let-mut count-index #u16 0u16)
          (#while (#u16::lt count-index 256u16)
            (#let count #u8 (#as count-index #u8))
            (#let-mut holder Holder (#struct-literal Holder (: target (#borrow left))))
            (#let answer #u8 (#call retarget (: holder (#borrow-mut holder) : alternate (#borrow right) : count count)))
            (#let expected #u8 (#if (#u8::eq count 0u8) left right))
            (#if (#u8::ne answer expected) (#block (#forget holder) (#return 1u64)))
            (#if (#u8::ne (#deref (#get holder target)) expected) (#block (#forget holder) (#return 2u64)))
            (#forget holder)
            (#set count-index (#u16::add-wrap count-index 1u16)))
          (#set seed (#u16::add-wrap seed 1u16)))
        (#return 42u64))
    "#);
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
