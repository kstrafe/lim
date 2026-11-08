//! Regression coverage for memory-aware induction over borrowed state.

use lim::{CompileConfig, Diagnostic, ProofOutcome};
mod support;

fn check(source: &str, theorem: &str) -> Result<lim::CheckedTheorem, Diagnostic> {
    lim::check_theorem_details_from_path_with_config(
        source,
        std::path::Path::new("borrowed-induction.lim"),
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

#[test]
fn borrowed_scalar_countdown_proves_zero() {
    proved(
        r#"
      (#fn countdown (: remaining (#ref-mut #u8)) ()
        (#label again
          (#while (#u8::gt (#deref remaining) 0u8)
            (#deref-set remaining (#u8::sub-wrap (#deref remaining) 1u8))))
        (#return ()))
      (#theorem countdown-contract
        (#proof-with-invariants ((countdown again true (#deref remaining)))
          (#proof-contract countdown true (#proof-eq (#deref remaining) 0u8))))
    "#,
        "countdown-contract",
    );
}

#[test]
fn borrowed_struct_field_countdown_preserves_sibling() {
    proved(
        r#"
      (#struct Counter () (: count #u8 : sibling #u8))
      (#fn countdown (: state (#ref-mut Counter)) ()
        (#let initial-sibling #u8 (#get state sibling))
        (#label again
          (#while (#u8::gt (#get (#deref state) count) 0u8)
            (#deref-set (#borrow-mut (#get (#deref state) count))
              (#u8::sub-wrap (#get (#deref state) count) 1u8))))
        (#return ()))
      (#theorem countdown-contract
        (#proof-with-invariants
          ((countdown again (#u8::eq (#get (#deref state) sibling) initial-sibling) (#get (#deref state) count)))
          (#proof-contract countdown true
            (#proof-and
              (#proof-eq (#get (#deref state) count) 0u8)
              (#proof-eq (#get (#deref state) sibling) (#proof-old (#get (#deref state) sibling)))))))
    "#,
        "countdown-contract",
    );
}

#[test]
fn iteration_local_mutable_borrow_can_update_owned_scalar() {
    proved(
        r#"
      (#fn countdown (: input #u8) #u8
        (#let-mut remaining #u8 input)
        (#label again
          (#while (#u8::gt remaining 0u8)
            (#let target (#ref-mut #u8) (#borrow-mut remaining))
            (#deref-set target (#u8::sub-wrap (#deref target) 1u8))))
        (#return remaining))
      (#theorem countdown-contract
        (#proof-with-invariants ((countdown again true remaining))
          (#proof-contract countdown true (#proof-eq (#proof-result) 0u8)))
      )
    "#,
        "countdown-contract",
    );
}

#[test]
fn shared_reference_loop_can_read_borrowed_value() {
    proved(
        r#"
      (#fn count-up (: source (#ref #u8)) #u8
        (#let-mut index #u8 0u8)
        (#label again
          (#while (#u8::lt index (#deref source))
            (#set index (#u8::add-wrap index 1u8))))
        (#return index))
      (#theorem count-up-contract
        (#proof-with-invariants ((count-up again (#u8::le index (#deref source)) (#u8::sub-wrap (#deref source) index)))
          (#proof-contract count-up true (#proof-eq (#proof-result) (#deref source)))))
    "#,
        "count-up-contract",
    );
}

#[test]
fn selected_decrement_contract_works_on_borrowed_loop_state() {
    proved(
        r#"
      (#fn decrement (: target (#ref-mut #u8)) ()
        (#deref-set target (#u8::sub-wrap (#deref target) 1u8))
        (#return ()))
      (#theorem decrement-contract
        (#proof-contract decrement (#u8::gt (#deref target) 0u8)
          (#proof-eq (#deref target) (#u8::sub-wrap (#proof-old (#deref target)) 1u8))))
      (#fn countdown (: remaining (#ref-mut #u8)) ()
        (#label again
          (#while (#u8::gt (#deref remaining) 0u8)
            (#call decrement (: target remaining))))
        (#return ()))
      (#theorem countdown-contract
        (#proof-using (decrement-contract)
          (#proof-with-invariants ((countdown again true (#deref remaining)))
            (#proof-contract countdown true (#proof-eq (#deref remaining) 0u8)))))
    "#,
        "countdown-contract",
    );
}

#[test]
fn weak_borrowed_summary_and_its_negation_are_unproved() {
    let source = r#"
      (#fn touch (: target (#ref-mut #u8)) ()
        (#deref-set target 9u8) (#return ()))
      (#theorem touch-contract (#proof-contract touch true true))
      (#fn caller (: input #u8) #u8
        (#let-mut value #u8 input)
        (#label again
          (#while (#u8::gt value 0u8)
            (#call touch (: target (#borrow-mut value)))
            (#set value (#u8::sub-wrap value 1u8))))
        (#return value))
    "#;
    for claim in [
        "(#proof-contract caller true (#proof-eq (#proof-result) input))",
        "(#proof-not (#proof-contract caller true (#proof-eq (#proof-result) input)))",
    ] {
        let theorem = format!(
            "{source} (#theorem caller-contract (#proof-using (touch-contract) (#proof-with-invariants ((caller again true value)) {claim})))"
        );
        rejected(&theorem, "caller-contract", ProofOutcome::ContractFailure);
    }
}

#[test]
fn reference_retargeting_still_requires_a_strictly_decreasing_rank_under_negation() {
    let source = r#"
      (#struct Holder () (: target (#ref #u8)))
      (#fn retarget (: holder (#ref-mut Holder) : alternate (#ref #u8)) ()
        (#label again
          (#while (#u8::gt (#deref (#get (#deref holder) target)) 0u8)
            (#deref-set (#borrow-mut (#get (#deref holder) target)) alternate)))
        (#return ()))
    "#;
    for claim in [
        "(#proof-contract retarget true true)",
        "(#proof-not (#proof-contract retarget true true))",
        "(#proof-contract retarget (#u8::eq (#deref (#get holder target)) (#deref alternate)) true)",
    ] {
        let theorem = format!(
            "{source} (#theorem retarget-contract (#proof-with-invariants ((retarget again true (#deref (#get (#deref holder) target)))) {claim}))"
        );
        rejected(&theorem, "retarget-contract", ProofOutcome::InductionFailure);
    }
}

#[test]
fn weak_borrowed_frame_and_its_negation_remain_induction_failures() {
    let body = r#"
      (#fn countdown (: target (#ref-mut #u8) : count #u8) ()
        (#let-mut remaining #u8 count)
        (#label again (#while (#u8::gt remaining 0u8)
          (#deref-set target 9u8)
          (#set remaining (#u8::sub-wrap remaining 1u8))))
        (#return ()))"#;
    for claim in [
        "(#proof-contract countdown true (#proof-eq (#deref target) (#proof-old (#deref target))))",
        "(#proof-not (#proof-contract countdown true (#proof-eq (#deref target) (#proof-old (#deref target)))))",
    ] {
        let source = format!("{body} (#theorem claim (#proof-with-invariants ((countdown again true remaining)) {claim}))");
        rejected(&source, "claim", ProofOutcome::InductionFailure);
    }
}

#[test]
fn a_temporary_borrow_cannot_hide_a_loop_carried_write() {
    let body = r#"
      (#fn countdown (: count #u8) #u8
        (#let-mut remaining #u8 count)
        (#let-mut changed #u8 0u8)
        (#label again (#while (#u8::gt remaining 0u8)
          (#let alias (#ref-mut #u8) (#borrow-mut changed))
          (#deref-set alias 9u8)
          (#set remaining (#u8::sub-wrap remaining 1u8))))
        (#return changed))"#;
    for claim in [
        "(#proof-contract countdown true (#proof-eq (#proof-result) 0u8))",
        "(#proof-not (#proof-contract countdown true (#proof-eq (#proof-result) 0u8)))",
    ] {
        let source = format!("{body} (#theorem claim (#proof-with-invariants ((countdown again true remaining)) {claim}))");
        rejected(&source, "claim", ProofOutcome::InductionFailure);
    }
}

#[test]
fn reference_bearing_enum_tags_can_change_with_a_proved_countdown() {
    let body = r#"
      (#enum Maybe () (: Maybe.None : Maybe.Some (#ref #u8)))
      (#fn clear (: target (#ref-mut Maybe) : count #u8) ()
        (#let-mut remaining #u8 count)
        (#label again (#while (#u8::gt remaining 0u8)
          (#deref-set target (#enum-literal Maybe.None))
          (#set remaining (#u8::sub-wrap remaining 1u8))))
        (#return ()))"#;
    for (claim, expected) in [
        ("(#proof-contract clear true true)", None),
        (
            "(#proof-not (#proof-contract clear true true))",
            Some(ProofOutcome::Counterexample),
        ),
    ] {
        let source = format!("{body} (#theorem claim (#proof-with-invariants ((clear again true remaining)) {claim}))");
        if let Some(expected) = expected {
            rejected(&source, "claim", expected);
        } else {
            proved(&source, "claim");
        }
    }
}

#[test]
fn borrowed_loop_frame_limits_survive_negation() {
    let parameters = (0..257)
        .map(|index| format!(": value-{index} (#ref-mut #u8)"))
        .collect::<Vec<_>>()
        .join(" ");
    for claim in [
        "(#proof-contract countdown true true)",
        "(#proof-not (#proof-contract countdown true true))",
    ] {
        let source = format!(
            r#"
          (#fn countdown ({parameters}) ()
            (#label again (#while (#u8::gt (#deref value-0) 0u8)
              (#deref-set value-0 (#u8::sub-wrap (#deref value-0) 1u8))))
            (#return ()))
          (#theorem claim (#proof-with-invariants ((countdown again true (#deref value-0))) {claim}))"#
        );
        rejected(&source, "claim", ProofOutcome::ResourceLimit);
    }
}

#[test]
fn ordinary_validation_rejects_mutable_aliases_of_immutable_statics() {
    let source = r#"
      (#static global-value #u8 9u8)
      (#fn countdown () ()
        (#let target (#ref-mut #u8) (#unsafe (#borrow-mut global-value)))
        (#label again (#while (#u8::gt (#deref target) 0u8)
          (#deref-set target (#u8::sub-wrap (#deref target) 1u8))))
        (#return ()))
      (#theorem claim (#proof-with-invariants ((countdown again true (#deref target)))
        (#proof-contract countdown true true)))"#;
    let error = check(source, "claim").expect_err("ordinary safety checks must still run");
    assert_eq!(error.code, lim::DiagnosticCode::Borrow);
    assert_eq!(error.proof_outcome(), None);
}

#[test]
fn a_stored_mutable_reference_keeps_its_pointee_through_induction() {
    proved(
        r#"
      (#struct Holder () (: target (#ref-mut #u8)))
      (#fn countdown (: holder (#ref-mut Holder)) ()
        (#label again (#while (#u8::gt (#deref (#get holder target)) 0u8)
          (#deref-set (#get holder target) (#u8::sub-wrap (#deref (#get holder target)) 1u8))))
        (#return ()))
      (#theorem claim (#proof-with-invariants ((countdown again true (#deref (#get holder target))))
        (#proof-contract countdown true (#proof-eq (#deref (#get holder target)) 0u8))))"#,
        "claim",
    );
}

#[test]
fn a_selected_reference_result_can_be_an_iteration_local_alias() {
    proved(
        r#"
      (#fn identity (: source (#ref-mut #u8)) (#ref-mut #u8) (#return source))
      (#theorem identity-contract (#proof-contract identity true true))
      (#fn countdown (: source (#ref-mut #u8)) ()
        (#label again (#while (#u8::gt (#deref source) 0u8)
          (#let alias (#ref-mut #u8) (#call identity (: source source)))
          (#deref-set alias (#u8::sub-wrap (#deref alias) 1u8))))
        (#return ()))
      (#theorem claim (#proof-using (identity-contract)
        (#proof-with-invariants ((countdown again true (#deref source)))
          (#proof-contract countdown true (#proof-eq (#deref source) 0u8)))))"#,
        "claim",
    );
}

#[test]
fn borrowed_induction_example_matches_native_for_every_byte_input() {
    use std::{fs, process::Command, time::Duration};
    let scratch = support::Scratch::new("proof-borrowed-induction-native");
    let mut source = include_str!("../examples/proof_borrowed_induction.lim").to_owned();
    source.truncate(source.find("(#fn main ").unwrap());
    source.push_str(
        r#"
      (#fn main () #u64
        (#let-mut index #u16 0u16)
        (#while (#u16::lt index 256u16)
          (#let initial #u8 (#as index #u8))
          (#let sibling #u8 (#u8::add-wrap initial 77u8))
          (#let-mut state Counter (#struct-literal Counter (: remaining initial : sibling sibling)))
          (#call countdown (: state (#borrow-mut state)))
          (#if (#u8::ne (#get state remaining) 0u8) (#block (#return 1u64)))
          (#if (#u8::ne (#get state sibling) sibling) (#block (#return 2u64)))
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
