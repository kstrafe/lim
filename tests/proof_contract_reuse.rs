//! Contract reuse must preserve verification and cannot create assumptions or
//! turn an abstract summary result into a concrete counterexample.
use lim::{CompileConfig, Diagnostic, ProofOutcome};
mod support;

const COUNTDOWN: &str = r#"
(#fn countdown (: count #u8) #u8
  (#let-mut remaining #u8 count)
  (#let-mut answer #u8 0u8)
  (#label again
    (#while (#u8::gt remaining 0u8)
      (#set answer (#u8::add-wrap answer 1u8))
      (#set remaining (#u8::sub-wrap remaining 1u8))))
  (#return answer))
(#theorem countdown-contract
  (#proof-with-invariants
    ((countdown again (#u8::eq (#u8::add-wrap answer remaining) count) remaining))
    (#proof-contract countdown true (#proof-eq (#proof-result) count))))
"#;
const INCREMENT: &str = r#"
(#fn increment (: value #u8) #u8 (#return (#u8::add-wrap value 1u8)))
(#theorem increment-contract
  (#proof-contract increment (#u8::lt value 255u8)
    (#proof-eq (#proof-result) (#u8::add-wrap (#proof-old value) 1u8))))
"#;

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
fn rejected(source: &str, theorem: &str, outcome: ProofOutcome, message: &str) {
    let error = check(source, theorem).expect_err("must fail closed");
    assert_eq!(
        error.proof_outcome(),
        Some(outcome),
        "{}\n{source}",
        error.message
    );
    assert!(
        error.message.contains(message),
        "{}\n{source}",
        error.message
    );
}

#[test]
fn verified_invariant_contract_replaces_callee_execution() {
    let source = format!(
        r#"{COUNTDOWN}
      (#fn caller (: input #u8) #u8 (#return (#call countdown (: count input))))
      (#theorem caller-contract
        (#proof-using (countdown-contract)
          (#proof-loop-limit 1
            (#proof-contract caller true (#proof-eq (#proof-result) input)))))"#
    );
    proved(&source, "caller-contract");
    let without_reuse = source.replace("(#proof-using (countdown-contract)", "(#proof-using ()");
    rejected(
        &without_reuse,
        "caller-contract",
        ProofOutcome::ResourceLimit,
        "symbolic iterations",
    );
}

#[test]
fn forward_and_transitive_dependencies_are_verified_before_consumers() {
    let source = format!(
        r#"
      (#fn caller (: input #u8) #u8 (#return (#call countdown (: count input))))
      (#fn outer (: seed #u8) #u8 (#return (#call caller (: input seed))))
      (#theorem outer-contract
        (#proof-using (caller-contract)
          (#proof-loop-limit 1 (#proof-contract outer true (#proof-eq (#proof-result) seed)))))
      (#theorem caller-contract
        (#proof-using (countdown-contract)
          (#proof-loop-limit 1 (#proof-contract caller true (#proof-eq (#proof-result) input)))))
      {COUNTDOWN}"#
    );
    proved(&source, "outer-contract");
}

#[test]
fn spec_calls_use_summaries_and_bind_actuals_under_callee_parameter_names() {
    proved(
        &format!(
            r#"{COUNTDOWN}
      (#theorem universal
        (#proof-using (countdown-contract)
          (#proof-loop-limit 1
            (#proof-for-all (: input #u8)
              (#proof-eq (#call countdown (: count input)) input)))))"#
        ),
        "universal",
    );
}

#[test]
fn precondition_must_hold_for_every_feasible_call_and_negation_cannot_hide_it() {
    for assertion in [
        "(#proof-contract increment true true)",
        "(#proof-not (#proof-contract increment true true))",
    ] {
        rejected(
            &format!(
                r#"{INCREMENT}
          (#theorem selected (#proof-using (increment-contract) {assertion}))"#
            ),
            "selected",
            ProofOutcome::ContractFailure,
            "precondition",
        );
    }
    proved(
        &format!(
            r#"{INCREMENT}
      (#theorem selected (#proof-using (increment-contract)
        (#proof-contract increment (#u8::lt value 255u8)
          (#u8::gt (#proof-result) value))))"#
        ),
        "selected",
    );
}

#[test]
fn weak_summary_does_not_refute_true_program_or_prove_its_negation() {
    let prefix = r#"
      (#fn identity (: value #u8) #u8 (#return value))
      (#theorem weak (#proof-contract identity true true))"#;
    for assertion in [
        "(#proof-contract identity true (#proof-eq (#proof-result) value))",
        "(#proof-not (#proof-contract identity true (#proof-eq (#proof-result) value)))",
    ] {
        rejected(
            &format!("{prefix} (#theorem selected (#proof-using (weak) {assertion}))"),
            "selected",
            ProofOutcome::ContractFailure,
            "not a concrete execution counterexample",
        );
    }
}

#[test]
fn dependency_cycles_and_duplicate_selections_are_invalid() {
    for source in [
        "(#theorem selected (#proof-using (selected) true))",
        "(#theorem selected (#proof-using (other) true)) (#theorem other (#proof-using (selected) true))",
    ] {
        rejected(source, "selected", ProofOutcome::Invalid, "cyclic");
    }
    rejected(&format!("{INCREMENT} (#theorem selected (#proof-using (increment-contract increment-contract) true))"),
      "selected", ProofOutcome::Invalid, "duplicate");
    rejected(&format!("{INCREMENT} (#theorem other (#proof-contract increment true true)) (#theorem selected (#proof-using (increment-contract other) true))"),
      "selected", ProofOutcome::Invalid, "multiple selected contracts");
}

#[test]
fn negated_and_conditional_contracts_cannot_be_registered_as_contracts() {
    for proposition in [
        "(#proof-not (#proof-contract identity true false))",
        "(#proof-implies false (#proof-contract identity true false))",
        "(#proof-or true (#proof-contract identity true false))",
    ] {
        rejected(
            &format!(
                r#"
          (#fn identity (: value #u8) #u8 (#return value))
          (#theorem not-a-contract {proposition})
          (#theorem selected (#proof-using (not-a-contract) true))"#
            ),
            "selected",
            ProofOutcome::Invalid,
            "not a verified direct",
        );
    }
}

#[test]
fn false_providers_and_unrelated_type_errors_are_never_skipped() {
    rejected(
        r#"
      (#fn identity (: value #u8) #u8 (#return value))
      (#theorem selected (#proof-using (false-provider) true))
      (#theorem false-provider (#proof-contract identity true false))"#,
        "selected",
        ProofOutcome::Counterexample,
        "false-provider",
    );
    let error = check(
        &format!(
            r#"{INCREMENT}
      (#fn invalid () #u8 (#return true))
      (#theorem selected (#proof-using (increment-contract) true))"#
        ),
        "selected",
    )
    .unwrap_err();
    assert_eq!(error.code, lim::DiagnosticCode::Type);
}

#[test]
fn contract_selection_is_scoped() {
    rejected(
        &format!(
            r#"{COUNTDOWN}
      (#theorem selected
        (#proof-loop-limit 1
          (#proof-and
            (#proof-using (countdown-contract)
              (#proof-contract countdown true (#proof-eq (#proof-result) count)))
            (#proof-contract countdown true (#proof-eq (#proof-result) count)))))"#
        ),
        "selected",
        ProofOutcome::ResourceLimit,
        "symbolic iterations",
    );
}

#[test]
fn raw_pointer_results_and_effects_are_not_given_an_unmodeled_frame() {
    rejected(
        r#"
      (#fn read (: value (#ptr #u8)) (#ptr #u8) (#return value))
      (#theorem read-contract (#proof-contract read true true))
      (#theorem selected (#proof-using (read-contract) true))"#,
        "selected",
        ProofOutcome::Unsupported,
        "reference-free",
    );
    rejected(
        r#"
      (#fn identity (: value #u8) #u8
        (#if false (#panic) ()) (#return value))
      (#theorem identity-contract (#proof-contract identity true true))
      (#theorem selected (#proof-using (identity-contract) true))"#,
        "selected",
        ProofOutcome::Unsupported,
        "effects",
    );
}

#[test]
fn self_referential_spec_calls_execute_instead_of_assuming_the_summary() {
    proved(
        r#"
      (#fn identity (: value #u8) #u8 (#return value))
      (#theorem identity-contract (#proof-contract identity true
        (#proof-eq (#proof-result) (#call identity (: value value)))))
      (#theorem selected (#proof-using (identity-contract)
        (#proof-contract identity true (#proof-eq (#proof-result) value))))"#,
        "selected",
    );
}

#[test]
fn result_contracts_cannot_suppress_execution_trace_obligations() {
    rejected(
        r#"
      (#fn identity (: value #u8) #u8 (#return value))
      (#fn caller (: input #u8) #u8 (#return (#call identity (: value input))))
      (#theorem identity-contract (#proof-contract identity true true))
      (#theorem selected (#proof-using (identity-contract)
        (#proof-calls-before caller identity identity)))"#,
        "selected",
        ProofOutcome::Unsupported,
        "execution traces",
    );
}

#[test]
fn reference_free_aggregate_results_and_local_mutations_preserve_the_caller_frame() {
    proved(
        r#"
      (#struct Pair () (: first #u8 : second #u8))
      (#fn pair (: input #u8) Pair
        (#let-mut local #u8 input)
        (#set local (#u8::add-wrap local 1u8))
        (#return (#struct-literal Pair (: first input : second local))))
      (#theorem pair-contract (#proof-contract pair true
        (#proof-and (#proof-eq (#get (#proof-result) first) input)
          (#proof-eq (#get (#proof-result) second) (#u8::add-wrap input 1u8)))))
      (#fn caller (: seed #u8) #u8
        (#let stored Pair (#call pair (: input seed)))
        (#return (#get stored second)))
      (#theorem selected (#proof-using (pair-contract)
        (#proof-contract caller true
          (#proof-eq (#proof-result) (#u8::add-wrap seed 1u8)))))"#,
        "selected",
    );
}

#[test]
fn template_visibility_uses_its_definition_without_granting_caller_field_access() {
    let scratch = support::Scratch::new("contract-private-definition");
    std::fs::create_dir(scratch.path().join("library")).unwrap();
    std::fs::write(
        scratch.path().join("library/lib.lim"),
        r#"
      (#export Secret read read-contract)
      (#struct Secret (#linear) (: hidden #u8))
      (#fn read (: item Secret) #u8
        (#let answer #u8 (#get item hidden)) (#forget item) (#return answer))
      (#theorem read-contract (#proof-contract read true
        (#proof-eq (#proof-result) (#get item hidden))))"#,
    )
    .unwrap();
    let imports = r#"
      (#alias Secret = ./library/lib.lim::Secret)
      (#alias read = ./library/lib.lim::read)
      (#alias read-contract = ./library/lib.lim::read-contract)"#;
    let source = format!(
        r#"{imports}
      (#theorem selected (#proof-using (read-contract)
        (#proof-for-all (: input Secret)
          (#proof-eq (#call read (: item input)) (#call read (: item input))))))"#
    );
    let path = scratch.path().join("main.lim");
    lim::check_theorem_details_from_path_with_config(
        &source,
        &path,
        &CompileConfig::default(),
        "selected",
    )
    .unwrap_or_else(|error| panic!("{}", error.message));
    let injected = format!(
        r#"{imports}
      (#theorem selected (#proof-using (read-contract)
        (#proof-contract read true (#proof-eq (#proof-result) (#get item hidden)))))"#
    );
    let error = lim::check_theorem_details_from_path_with_config(
        &injected,
        &path,
        &CompileConfig::default(),
        "selected",
    )
    .unwrap_err();
    assert!(
        error.message.contains("private representation"),
        "{}",
        error.message
    );
}

#[test]
fn global_reads_do_not_get_an_implicit_environment_summary() {
    rejected(
        r#"
      (#let source #bool true)
      (#fn read () #bool (#return source))
      (#theorem read-contract (#proof-contract read true true))
      (#theorem selected (#proof-using (read-contract) true))"#,
        "selected",
        ProofOutcome::Unsupported,
        "global storage reads",
    );
}

#[test]
fn enum_result_summaries_keep_discriminants_and_payload_constraints() {
    proved(
        r#"
      (#enum Choice () (: Choice.Empty : Choice.Value #u8))
      (#fn wrap (: input #u8) Choice (#return (#enum-literal Choice.Value input)))
      (#theorem wrap-contract (#proof-contract wrap true
        (#proof-eq (#proof-result) (#enum-literal Choice.Value input))))
      (#theorem selected (#proof-using (wrap-contract)
        (#proof-for-all (: input #u8)
          (#proof-eq (#call wrap (: input input)) (#enum-literal Choice.Value input)))))"#,
        "selected",
    );
}
