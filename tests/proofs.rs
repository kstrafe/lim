mod support;

use lim::{CheckedProgram, DiagnosticCode};
use std::{collections::HashMap, fs};

fn accepts(source: &str) {
    let program = lim::parse_program(source).unwrap_or_else(|error| panic!("{error}\n{source}"));
    CheckedProgram::validate(&program).unwrap_or_else(|error| panic!("{error}\n{source}"));
}

fn rejects(source: &str, expected: &str) -> String {
    let program = lim::parse_program(source).unwrap_or_else(|error| panic!("{error}\n{source}"));
    let error = CheckedProgram::validate(&program)
        .err()
        .expect("theorem must fail");
    assert!(
        error.starts_with("theorem '"),
        "ordinary validation failed: {error}"
    );
    assert!(error.contains(expected), "expected {expected:?}: {error}");
    error
}

const GRAPH: &str = "
    (#fn leaf () #u8 (#return 1u8))
    (#fn middle () #u8 (#return (#call leaf (:))))
    (#fn entry () #u8 (#return (#call middle (:))))
    (#fn unrelated () #u8 (#return 2u8))";

const VALIDATION: &str = "
    (#fn validator ((input #bool)) #bool (#return input))
    (#fn action () () (#return ()))";

const COUNTDOWN: &str = "
    (#fn countdown ((count #u8)) #u8
      (#let-mut remaining #u8 count)
      (#while (#u8::gt remaining 0u8)
        (#set remaining (#u8::sub-wrap remaining 1u8)))
      (#return remaining))";

#[test]
fn direct_call_graph_edge_is_proved() {
    accepts(&format!(
        "{GRAPH} (#theorem direct (#proof-calls-directly entry middle))"
    ));
}

#[test]
fn transitive_call_graph_path_is_proved() {
    accepts(&format!(
        "{GRAPH} (#theorem transitive (#proof-calls-transitively entry leaf))"
    ));
}

#[test]
fn transitive_path_is_not_a_direct_edge() {
    rejects(
        &format!("{GRAPH} (#theorem direct (#proof-calls-directly entry leaf))"),
        "disproved",
    );
}

#[test]
fn unrelated_function_has_no_call_path() {
    accepts(&format!(
        "{GRAPH} (#theorem absent
      (#proof-not (#proof-calls-transitively entry unrelated)))"
    ));
}

#[test]
fn false_validation_prevents_a_guarded_action() {
    accepts(&format!(
        "{VALIDATION}
      (#fn guarded ((input #bool)) ()
        (#if (#call validator (: input input)) (#call action (:)))
        (#return ()))
      (#theorem guarded-action (#proof-calls-when guarded validator false action))"
    ));
}

#[test]
fn inverted_validation_guard_is_disproved() {
    rejects(
        &format!(
            "{VALIDATION}
      (#fn inverted ((input #bool)) ()
        (#if (#bool::not (#call validator (: input input))) (#call action (:)))
        (#return ()))
      (#theorem guarded-action (#proof-calls-when inverted validator false action))"
        ),
        "disproved",
    );
}

#[test]
fn action_before_failed_validation_is_disproved() {
    rejects(
        &format!(
            "{VALIDATION}
      (#fn early ((input #bool)) ()
        (#call action (:))
        (#let valid #bool (#call validator (: input input)))
        (#return ()))
      (#theorem guarded-action (#proof-calls-when early validator false action))"
        ),
        "disproved",
    );
}

#[test]
fn required_call_before_action_is_proved() {
    accepts(
        "(#fn prepare () () (#return ()))
      (#fn action () () (#return ()))
      (#fn entry () () (#call prepare (:)) (#call action (:)) (#return ()))
      (#theorem order (#proof-calls-before entry prepare action))",
    );
}

#[test]
fn reversed_call_order_is_disproved() {
    rejects(
        "(#fn prepare () () (#return ()))
      (#fn action () () (#return ()))
      (#fn entry () () (#call action (:)) (#call prepare (:)) (#return ()))
      (#theorem order (#proof-calls-before entry prepare action))",
        "disproved",
    );
}

#[test]
fn wrapping_addition_is_universally_commutative() {
    accepts(
        "(#theorem commutative
      (#proof-for-all ((left #u8) (right #u8))
        (#proof-eq (#u8::add-wrap left right) (#u8::add-wrap right left))))",
    );
}

#[test]
fn false_universal_math_reports_a_counterexample() {
    let error = rejects(
        "(#theorem wrong
      (#proof-for-all ((input #u8))
        (#proof-eq (#u8::add-wrap input 1u8) input)))",
        "counterexample",
    );
    assert!(error.contains("input ="), "{error}");
}

#[test]
fn contract_result_uses_its_declared_parameters() {
    accepts(
        "(#fn identity ((input #u8)) #u8 (#return input))
      (#theorem identity-contract
        (#proof-contract identity true (#proof-eq (#proof-result) input)))",
    );
}

#[test]
fn contract_old_observes_storage_before_mutation() {
    accepts(
        "(#fn increment ((value (#ref-mut #u8))) #u8
        (#deref-set value (#u8::add-wrap (#deref value) 1u8))
        (#return (#deref value)))
      (#theorem increment-contract
        (#proof-contract increment true
          (#proof-and
            (#proof-eq (#deref value)
              (#u8::add-wrap (#proof-old (#deref value)) 1u8))
            (#proof-eq (#proof-result) (#deref value)))))",
    );
}

#[test]
fn false_contract_postcondition_is_disproved() {
    rejects(
        "(#fn identity ((input #u8)) #u8 (#return input))
      (#theorem wrong-contract
        (#proof-contract identity true
          (#proof-eq (#proof-result) (#u8::add-wrap input 1u8))))",
        "disproved",
    );
}

#[test]
fn contract_precondition_bounds_checked_arithmetic() {
    accepts(
        "(#fn increment ((input #u8)) #u8 (#return (#u8::add-wrap input 1u8)))
      (#theorem bounded-contract
        (#proof-contract increment (#u8::lt input 255u8)
          (#proof-and
            (#proof-no-overflow #u8::add-wrap input 1u8)
            (#proof-eq (#proof-result) (#u8::add-wrap input 1u8)))))",
    );
}

#[test]
fn bounded_universal_addition_cannot_overflow() {
    accepts(
        "(#theorem bounded-add
      (#proof-for-all ((input #u8))
        (#proof-implies (#u8::le input 254u8)
          (#proof-no-overflow #u8::add-wrap input 1u8))))",
    );
}

#[test]
fn unbounded_universal_addition_can_overflow() {
    rejects(
        "(#theorem overflowing-add
      (#proof-for-all ((input #u8))
        (#proof-no-overflow #u8::add-wrap input 1u8)))",
        "counterexample",
    );
}

#[test]
fn literal_overflow_is_disproved_without_executing_it() {
    rejects(
        "(#theorem overflow (#proof-no-overflow #u8::add-wrap 255u8 1u8))",
        "disproved",
    );
}

#[test]
fn a_finite_loop_with_enough_budget_is_proved() {
    accepts(&format!(
        "{COUNTDOWN}
      (#theorem finite (#proof-loop-limit 8
        (#proof-eq (#call countdown (: count 3u8)) 0u8)))"
    ));
}

#[test]
fn exhausting_loop_budget_fails_closed() {
    rejects(
        &format!(
            "{COUNTDOWN}
      (#theorem insufficient (#proof-loop-limit 2
        (#proof-eq (#call countdown (: count 3u8)) 0u8)))"
        ),
        "unproved: loop exceeds",
    );
}

#[test]
fn nonterminating_loop_fails_closed() {
    rejects(
        "(#fn forever () #u8 (#loop (#continue)) (#return 0u8))
      (#theorem terminating (#proof-loop-limit 2
        (#proof-eq (#call forever (:)) 0u8)))",
        "unproved: loop exceeds",
    );
}

#[test]
fn malformed_proposition_and_unknown_names_are_rejected() {
    for (source, expected) in [
        (
            "(#theorem malformed (#proof-not true false))",
            "expects 1 operand",
        ),
        (
            "(#theorem malformed (#proof-for-all ((input #u8 extra)) true))",
            "(name Type) pairs",
        ),
        (
            "(#theorem unknown (#proof-calls-directly missing absent))",
            "unknown",
        ),
        (
            "(#theorem unknown (#proof-unrecognized true))",
            "unknown or misplaced",
        ),
        (
            "(#theorem misplaced (#proof-eq (#proof-result) 0u8))",
            "only valid in a contract",
        ),
        (
            "(#theorem invalid-limit (#proof-loop-limit 0 true))",
            "1..=1024",
        ),
    ] {
        rejects(source, expected);
    }
}

#[test]
fn theorem_declaration_arity_and_value_naming_are_checked() {
    for source in [
        "(#theorem missing)",
        "(#theorem extra true false)",
        "(#theorem Uppercase true)",
    ] {
        assert!(lim::parse_program(source).is_err(), "accepted {source}");
    }
}

#[test]
fn all_public_validation_and_emission_paths_reject_false_proofs() {
    let program =
        lim::parse_program("(#fn main () #u64 (#return 42u64)) (#theorem false-claim false)")
            .unwrap();
    assert!(lim::check_types(&program)
        .unwrap_err()
        .contains("disproved"));
    assert!(CheckedProgram::validate(&program)
        .err()
        .unwrap()
        .contains("disproved"));
    assert!(lim::generate_assembly(&program)
        .unwrap_err()
        .contains("disproved"));
}

#[test]
fn failed_proof_has_e4401_and_a_proposition_span() {
    let scratch = support::Scratch::new("proof-diagnostic");
    let source = "(#fn main () #u64 (#return 42u64))\n(#theorem false-claim (#proof-eq 1u8 2u8))";
    let path = scratch.path().join("main.lim");
    let error = lim::check_source_for_editor(
        source,
        &path,
        &lim::CompileConfig::default(),
        &HashMap::new(),
    )
    .unwrap_err();
    assert_eq!(error.code, DiagnosticCode::ProofCounterexample);
    assert_eq!(error.code_string(), "E4401");
    let span = error.span.expect("proof diagnostic span");
    assert_eq!(&source[span.start..span.end], "(#proof-eq 1u8 2u8)");
    assert!(lim::render_diagnostic_json(&error, "main.lim").contains("\"category\":\"proof\""));
}

#[test]
fn compile_time_proofs_have_no_assembly_effects() {
    let source = "(#fn main () #u64 (#return 42u64))";
    let plain = lim::parse_program(source).unwrap();
    let proved =
        lim::parse_program(&format!("{source}\n(#theorem compile-time-only true)")).unwrap();
    assert_eq!(
        lim::generate_assembly(&plain).unwrap(),
        lim::generate_assembly(&proved).unwrap()
    );
}

#[test]
fn proof_example_compiles_and_returns_42() {
    let scratch = support::Scratch::new("proof-example");
    let source = include_str!("../examples/proofs.lim");
    let program = lim::parse_program(source).unwrap();
    let assembly = lim::generate_assembly(&program).unwrap();
    let binary = scratch.path().join("proofs");
    lim::link_native_binary(
        &assembly,
        &binary,
        &[],
        &[],
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    let (status, stdout, stderr) = support::run(
        &mut std::process::Command::new(&binary),
        std::time::Duration::from_secs(5),
        4096,
    )
    .unwrap();
    assert_eq!(status.code(), Some(42), "{stderr:?}");
    assert!(stdout.is_empty(), "{stdout:?}");
    assert!(stderr.is_empty(), "{stderr:?}");
    // Also exercise source compilation and a warm semantic cache.
    let path = scratch.path().join("main.lim");
    fs::write(&path, source).unwrap();
    let cache = scratch.path().join("cache");
    for _ in 0..2 {
        lim::compile_source_to_assembly(
            source,
            &path,
            &lim::CompileConfig::default(),
            &cache,
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap();
    }
}

#[test]
fn warm_cache_does_not_accept_a_false_proof() {
    let scratch = support::Scratch::new("proof-cache");
    let path = scratch.path().join("main.lim");
    let cache = scratch.path().join("cache");
    let valid = "(#fn main () #u64 (#return 42u64)) (#theorem claim true)";
    let invalid = "(#fn main () #u64 (#return 42u64)) (#theorem claim false)";
    let config = lim::CompileConfig::default();
    let target = lim::TargetDescription::X86_64_SYSTEM_V;
    fs::write(&path, valid).unwrap();
    lim::compile_source_to_assembly(valid, &path, &config, &cache, target).unwrap();
    fs::write(&path, invalid).unwrap();
    for _ in 0..2 {
        let error =
            lim::compile_source_to_assembly(invalid, &path, &config, &cache, target).unwrap_err();
        assert_eq!(error.code, DiagnosticCode::ProofCounterexample);
        assert!(error.message.contains("disproved"), "{}", error.message);
    }
}

#[test]
fn negating_a_vacuously_true_contract_is_disproved() {
    rejects(
        "(#fn identity ((input #u8)) #u8 (#return input))
      (#theorem negated-vacuous-contract
        (#proof-not (#proof-contract identity false false)))",
        "disproved",
    );
}

#[test]
fn independent_contracts_under_conjunction_have_separate_bindings() {
    accepts(
        "(#fn identity-byte ((input #u8)) #u8 (#return input))
      (#fn identity-flag ((input #bool)) #bool (#return input))
      (#theorem independent-contracts
        (#proof-and
          (#proof-contract identity-byte true
            (#proof-eq (#proof-result) (#proof-old input)))
          (#proof-contract identity-flag true
            (#proof-eq (#proof-result) (#proof-old input)))))",
    );
}

#[test]
fn a_vacuous_contract_does_not_hide_a_false_sibling_contract() {
    rejects(
        "(#fn identity ((input #u8)) #u8 (#return input))
      (#theorem independent-contracts
        (#proof-and
          (#proof-contract identity false false)
          (#proof-contract identity true false)))",
        "disproved",
    );
}

#[test]
fn negating_a_true_universal_claim_is_disproved() {
    rejects(
        "(#theorem negated-tautology
        (#proof-not
          (#proof-for-all ((input #u8)) (#proof-eq input input))))",
        "disproved",
    );
}

#[test]
fn negating_a_false_universal_claim_is_proved() {
    // The negation applies to the completed universal claim. It must not
    // turn into a universal claim that every input differs from zero.
    accepts(
        "(#theorem not-every-input-is-zero
        (#proof-not
          (#proof-for-all ((input #u8)) (#proof-eq input 0u8))))",
    );
}

#[test]
fn nested_quantified_claims_fail_closed() {
    rejects(
        "(#theorem nested
        (#proof-for-all ((left #u8))
          (#proof-for-all ((right #u8))
            (#proof-eq (#u8::add-wrap left right) (#u8::add-wrap right left)))))",
        "nested quantified claims are unsupported",
    );
}

#[test]
fn trace_query_uses_the_actual_successful_validator_result() {
    accepts(
        "(#fn validator () #bool (#return true))
      (#fn action () () (#return ()))
      (#fn entry () ()
        (#let valid #bool (#call validator (:)))
        (#call action (:))
        (#return ()))
      (#theorem actual-result (#proof-calls-when entry validator false action))",
    );
}

#[test]
fn trace_query_rejects_action_after_actual_validation_failure() {
    rejects(
        "(#fn validator () #bool (#return false))
      (#fn action () () (#return ()))
      (#fn entry () ()
        (#let valid #bool (#call validator (:)))
        (#call action (:))
        (#return ()))
      (#theorem actual-result (#proof-calls-when entry validator false action))",
        "disproved",
    );
}

#[test]
fn fixed_array_sortedness_uses_the_named_comparator() {
    accepts(
        "(#fn less ((left #u8) (right #u8)) #bool (#return (#u8::lt left right)))
      (#theorem ordered
        (#proof-sorted (#array-of (#array #u8 3) 1u8 1u8 2u8) less))",
    );
}

#[test]
fn fixed_array_inversion_is_disproved() {
    rejects(
        "(#fn less ((left #u8) (right #u8)) #bool (#return (#u8::lt left right)))
      (#theorem ordered
        (#proof-sorted (#array-of (#array #u8 3) 1u8 3u8 2u8) less))",
        "disproved",
    );
}

#[test]
fn permutation_preserves_duplicate_element_counts() {
    accepts(
        "(#theorem rearranged
        (#proof-permutation
          (#array-of (#array #u8 3) 1u8 2u8 1u8)
          (#array-of (#array #u8 3) 2u8 1u8 1u8)))",
    );
}

#[test]
fn permutation_rejects_changed_duplicate_element_counts() {
    rejects(
        "(#theorem rearranged
        (#proof-permutation
          (#array-of (#array #u8 3) 1u8 2u8 1u8)
          (#array-of (#array #u8 3) 2u8 1u8 2u8)))",
        "disproved",
    );
}

#[test]
fn failed_operation_preserves_old_mutable_storage() {
    accepts(
        "(#fn try-increment ((value (#ref-mut #u8)) (succeed #bool)) #bool
        (#if succeed (#deref-set value (#u8::add-wrap (#deref value) 1u8)))
        (#return succeed))
      (#theorem failure-atomicity
        (#proof-contract try-increment true
          (#proof-implies (#bool::not (#proof-result))
            (#proof-eq (#deref value) (#proof-old (#deref value))))))",
    );
}

#[test]
fn mutation_on_a_failure_path_is_disproved() {
    rejects(
        "(#fn try-increment ((value (#ref-mut #u8)) (succeed #bool)) #bool
        (#deref-set value (#u8::add-wrap (#deref value) 1u8))
        (#return succeed))
      (#theorem failure-atomicity
        (#proof-contract try-increment true
          (#proof-implies (#bool::not (#proof-result))
            (#proof-eq (#deref value) (#proof-old (#deref value))))))",
        "disproved",
    );
}

#[test]
fn encode_decode_round_trip_holds_for_every_byte() {
    accepts(
        "(#fn encode ((value #u8)) #u8 (#return (#u8::bit-xor value 90u8)))
      (#fn decode ((value #u8)) #u8 (#return (#u8::bit-xor value 90u8)))
      (#theorem round-trip
        (#proof-for-all ((input #u8))
          (#proof-eq
            (#call decode (: value (#call encode (: value input)))) input)))",
    );
}

#[test]
fn an_incorrect_decoder_breaks_the_round_trip() {
    rejects(
        "(#fn encode ((value #u8)) #u8 (#return (#u8::bit-xor value 90u8)))
      (#fn decode ((value #u8)) #u8 (#return (#u8::bit-xor value 91u8)))
      (#theorem round-trip
        (#proof-for-all ((input #u8))
          (#proof-eq
            (#call decode (: value (#call encode (: value input)))) input)))",
        "disproved",
    );
}

const GATE: &str = "
    (#enum Gate () (Gate.Closed Gate.Open))
    (#fn toggle ((state Gate)) Gate
      (#return (#match state
        (#case Gate.Closed Gate.Open)
        (#case Gate.Open Gate.Closed))))";

#[test]
fn enum_state_transitions_satisfy_both_directional_contracts() {
    accepts(&format!(
        "{GATE}
      (#theorem transitions
        (#proof-and
          (#proof-contract toggle (#proof-eq state Gate.Closed)
            (#proof-eq (#proof-result) Gate.Open))
          (#proof-contract toggle (#proof-eq state Gate.Open)
            (#proof-eq (#proof-result) Gate.Closed))))"
    ));
}

#[test]
fn an_incorrect_state_transition_contract_is_disproved() {
    rejects(
        &format!(
            "{GATE}
      (#theorem wrong-transition
        (#proof-contract toggle (#proof-eq state Gate.Closed)
          (#proof-eq (#proof-result) Gate.Closed)))"
        ),
        "disproved",
    );
}

#[test]
fn unsafe_allowlist_resolves_imported_function_aliases() {
    let scratch = support::Scratch::new("proof-unsafe-allowlist");
    fs::write(
        scratch.path().join("boundary.lim"),
        "(#fn trusted () #u64
          (#return (#unsafe (#asm #u64 () \"mov rax, 42\"))))",
    )
    .unwrap();
    let source = "(#alias allowed = ./boundary.lim::trusted)
      (#fn entry () #u64 (#return (#call allowed (:))))
      (#theorem confined (#proof-only-unsafe entry (allowed)))";
    let program = lim::parse_program_from_path(source, &scratch.path().join("main.lim")).unwrap();
    CheckedProgram::validate(&program).unwrap_or_else(|error| panic!("{error}"));
}

const ASM_BOUNDARY: &str = "
    (#fn boundary () #u64 (#return (#unsafe (#asm #u64 () \"mov rax, 42\"))))
    (#fn main () #u64 (#return (#call boundary (:))))";

#[test]
fn concrete_native_stack_bound_is_proved_without_reentering_validation() {
    accepts(
        "(#fn leaf () #u64 (#return 42u64))
      (#fn main () #u64 (#return (#call leaf (:))))
      (#theorem bounded-stack (#proof-stack-at-most main \"x86_64-sysv\" 4096usize))",
    );
}

#[test]
fn zero_stack_bound_rejects_a_real_call_chain() {
    rejects(
        "(#fn leaf () #u64 (#return 42u64))
      (#fn main () #u64 (#return (#call leaf (:))))
      (#theorem no-stack (#proof-stack-at-most main \"x86_64-sysv\" 0usize))",
        "disproved",
    );
}

#[test]
fn pure_local_scalar_updates_have_no_observable_effects() {
    accepts(
        "(#fn pure () #u8
        (#let-mut local #u8 0u8)
        (#set local 1u8)
        (#return local))
      (#theorem pure-effects (#proof-no-effects pure
        (#proof-allocation #proof-io #proof-global-write #proof-unsafe
         #proof-external #proof-asm #proof-mutation)))",
    );
}

#[test]
fn writing_through_a_reference_has_an_observable_mutation_effect() {
    rejects(
        "(#fn write ((value (#ref-mut #u8))) ()
        (#deref-set value 1u8)
        (#return ()))
      (#theorem immutable (#proof-no-effects write (#proof-mutation)))",
        "disproved",
    );
}

#[test]
fn transitive_inline_assembly_blocks_a_no_asm_claim() {
    rejects(
        &format!(
            "{ASM_BOUNDARY}
      (#theorem no-assembly (#proof-no-effects main (#proof-asm)))"
        ),
        "disproved",
    );
}

#[test]
fn unsafe_builtin_allowlist_permits_exactly_the_declared_assembly_operation() {
    accepts(&format!(
        "{ASM_BOUNDARY}
      (#theorem allowed-assembly (#proof-only-unsafe main (#asm)))"
    ));
}

#[test]
fn empty_unsafe_allowlist_rejects_inline_assembly() {
    rejects(
        &format!(
            "{ASM_BOUNDARY}
      (#theorem forbidden-assembly (#proof-only-unsafe main ()))"
        ),
        "disproved",
    );
}

#[test]
fn unsafe_function_allowlist_trusts_the_named_boundary() {
    accepts(&format!(
        "{ASM_BOUNDARY}
      (#theorem trusted-boundary (#proof-only-unsafe main (boundary)))"
    ));
}

#[test]
fn unrelated_allowed_function_cannot_hide_inline_assembly() {
    rejects(
        &format!(
            "{ASM_BOUNDARY}
      (#fn unrelated () #u64 (#return 0u64))
      (#theorem wrong-boundary (#proof-only-unsafe main (unrelated)))"
        ),
        "disproved",
    );
}

#[test]
fn unknown_unsafe_allowlist_function_is_rejected() {
    rejects(
        "(#fn pure () #u64 (#return 42u64))
      (#theorem unknown-boundary (#proof-only-unsafe pure (missing)))",
        "unknown proof function",
    );
}

fn compile_fixture(source: &str, scratch: &support::Scratch) -> Result<String, lim::Diagnostic> {
    lim::compile_source_to_assembly(
        source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
}

#[test]
fn imported_proofs_are_checked_on_cold_and_warm_compilation() {
    let scratch = support::Scratch::new("proof-import-cache");
    let module = scratch.path().join("checked.lim");
    let checked = "(#fn identity ((input #u64)) #u64 (#return input))
      (#theorem imported-contract
        (#proof-contract identity true (#proof-eq (#proof-result) input)))";
    fs::write(&module, checked).unwrap();
    let source = "(#alias imported = ./checked.lim::identity)
      (#fn main () #u64 (#return (#call imported (: input 42u64))))
      (#theorem imported-call (#proof-calls-directly main imported))";
    fs::write(scratch.path().join("main.lim"), source).unwrap();
    let cold = compile_fixture(source, &scratch).unwrap();
    assert_eq!(cold, compile_fixture(source, &scratch).unwrap());

    fs::write(
        &module,
        checked.replace("(#proof-eq (#proof-result) input)", "false"),
    )
    .unwrap();
    for _ in 0..2 {
        let error = compile_fixture(source, &scratch).unwrap_err();
        assert_eq!(error.code, DiagnosticCode::ProofCounterexample);
        assert_eq!(error.source_name.as_deref(), module.to_str());
        assert!(
            error.message.contains("imported-contract"),
            "{}",
            error.message
        );
    }
}

#[test]
fn generated_proofs_are_checked_on_cold_and_warm_compilation() {
    let scratch = support::Scratch::new("proof-generated-cache");
    let source = "(#gn emit ()
        `((#fn generated ((value #u64)) #u64 (#return value))
          (#theorem generated-contract
            (#proof-contract generated true (#proof-eq (#proof-result) value)))))
      (#generate emit)
      (#fn main () #u64 (#return (#call generated (: value 42u64))))";
    let path = scratch.path().join("main.lim");
    fs::write(&path, source).unwrap();
    let cold = compile_fixture(source, &scratch).unwrap();
    assert_eq!(cold, compile_fixture(source, &scratch).unwrap());

    let invalid = source.replace("(#proof-eq (#proof-result) value)", "false");
    fs::write(&path, &invalid).unwrap();
    for _ in 0..2 {
        let error = compile_fixture(&invalid, &scratch).unwrap_err();
        assert_eq!(error.code, DiagnosticCode::ProofCounterexample);
        assert!(
            error.message.contains("generated-contract"),
            "{}",
            error.message
        );
    }
}
