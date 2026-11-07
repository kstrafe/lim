fn counterexample(source: &str) -> String {
    let program = lim::parse_program(source).unwrap_or_else(|error| panic!("{error}\n{source}"));
    let error = lim::check_types(&program).expect_err("false theorem must be disproved");
    assert!(error.starts_with("theorem '"), "{error}");
    assert!(error.contains("disproved"), "{error}");
    error
}

#[test]
fn scalar_counterexample_shows_canonical_typed_literal() {
    let error = counterexample(
        "(#theorem wrong
           (#proof-for-all ((input #u8))
             (#proof-implies (#u8::eq input 1u8) false)))",
    );
    assert!(error.contains("input = 1u8"), "{error}");
}

#[test]
fn claims_without_parameters_do_not_emit_an_empty_witness() {
    let error = counterexample(
        "(#fn constant () #u8 (#return 1u8))
      (#theorem wrong (#proof-contract constant true (#proof-eq (#proof-result) 0u8)))",
    );
    assert!(error.contains("no named input bindings"), "{error}");
    let empty = counterexample("(#theorem empty (#proof-for-all () false))");
    assert!(empty.contains("no named input bindings"), "{empty}");
}

#[test]
fn record_counterexample_renders_fields() {
    let error = counterexample(
        "(#struct User () (: id #u8))
         (#theorem wrong
           (#proof-for-all ((user User))
             (#proof-implies (#u8::eq (#get user id) 7u8) false)))",
    );
    assert!(error.contains("User { id = 7u8 }"), "{error}");
}

#[test]
fn guarded_enum_counterexample_shows_active_variant() {
    let error = counterexample(
        "(#enum Choice () ((Choice.Left #u8) (Choice.Right #u8)))
         (#theorem wrong
           (#proof-for-all ((choice Choice))
             (#proof-implies (#variant-is choice Choice.Right) false)))",
    );
    assert!(error.contains("Choice.Right("), "{error}");
}

#[test]
fn array_counterexample_renders_elements() {
    let error = counterexample(
        "(#theorem wrong
           (#proof-for-all ((values (#array #u8 3)))
             (#proof-eq (#index values 0usize) 0u8)))",
    );
    assert!(error.contains("values = ["), "{error}");
    assert!(error.contains("u8"), "{error}");
}

#[test]
fn reference_counterexample_shows_initial_referent() {
    let error = counterexample(
        "(#theorem wrong
           (#proof-for-all ((value (#ref #u8)))
             (#proof-eq (#deref value) 0u8)))",
    );
    assert!(error.contains("ref#0("), "{error}");
}

#[test]
fn mutable_reference_witness_is_the_initial_value_after_write() {
    let error = counterexample(
        "(#fn overwrite (: source (#ref-mut #u8)) ()
           (#deref-set source 7u8)
           (#return ()))
         (#theorem unchanged
           (#proof-contract overwrite
             (#u8::eq (#deref source) 1u8)
             (#proof-eq (#deref source) (#proof-old (#deref source)))))",
    );
    assert!(error.contains("source = mut-ref#0(1u8)"), "{error}");
    assert!(!error.contains("source = mut-ref#0(7u8)"), "{error}");
}

#[test]
fn large_array_counterexample_is_explicitly_truncated() {
    let error = counterexample(
        "(#theorem wrong
           (#proof-for-all ((values (#array #u8 64)))
             (#proof-eq (#index values 0usize) 0u8)))",
    );
    assert!(error.contains("..."), "{error}");
}

#[test]
fn discarded_negated_forall_does_not_leak_stale_witness() {
    let error = counterexample(
        "(#theorem stale
           (#proof-and
             (#proof-not (#proof-for-all ((stale #u8)) false))
             false))",
    );
    assert!(!error.contains("stale ="), "{error}");
}

#[test]
fn surviving_branch_reports_actual_witness_without_stale_one() {
    let error = counterexample(
        "(#theorem stale
           (#proof-and
             (#proof-or
               (#proof-for-all ((stale #u8)) false)
               true)
             (#proof-for-all ((actual #u8)) false)))",
    );
    assert!(error.contains("actual ="), "{error}");
    assert!(!error.contains("stale ="), "{error}");
}

#[test]
fn disjunction_counterexample_preserves_both_witnesses() {
    let error = counterexample(
        "(#theorem both
           (#proof-or
             (#proof-for-all ((left #u8)) false)
             (#proof-for-all ((right #u8)) false)))",
    );
    assert!(error.contains("left ="), "{error}");
    assert!(error.contains("right ="), "{error}");
}

#[test]
fn independent_witnesses_have_separate_storage_identity_scopes() {
    let error = counterexample(
        "(#theorem independent
        (#proof-or
          (#proof-for-all (: left (#ref #u8))
            (#proof-implies (#u8::eq (#deref left) 1u8) false))
          (#proof-for-all (: right (#ref #u8))
            (#proof-implies (#u8::eq (#deref right) 2u8) false))))",
    );
    assert!(error.contains("witness 1: left = ref#0(1u8)"), "{error}");
    assert!(error.contains("witness 2: right = ref#0(2u8)"), "{error}");
}

#[test]
fn logical_witnesses_preserve_boolean_truth_tables() {
    for first in [false, true] {
        for second in [false, true] {
            for operator in ["and", "or"] {
                let source = format!(
                    "(#theorem combinations
                    (#proof-{operator}
                      (#proof-for-all (: first #u8) {first})
                      (#proof-for-all (: second #u8) {second})))"
                );
                let expected = if operator == "and" {
                    first && second
                } else {
                    first || second
                };
                let result = lim::check_types(&lim::parse_program(&source).unwrap());
                assert_eq!(result.is_ok(), expected, "{source}: {result:?}");
                if let Err(error) = result {
                    assert!(error.contains("disproved"), "{error}");
                }
            }
        }
    }
}

#[test]
fn claim_values_keep_ordinary_boolean_call_match_and_equality_semantics() {
    let source = "(#fn invert (: value #bool) #bool
        (#return (#match value (#case true false) (#case false true))))
      (#theorem boolean-call
        (#proof-eq
          (#call invert (: value (#proof-for-all (: value #u8) false))) true))
      (#theorem boolean-aggregate
        (#proof-eq (#index (#array-of (#array #bool 2)
          (#proof-for-all (: value #u8) false) true) 0usize) false))";
    lim::check_types(&lim::parse_program(source).unwrap()).unwrap();
}

#[test]
fn compound_witness_lists_have_an_explicit_bound() {
    let claims = (0..20)
        .map(|index| format!("(#proof-for-all (: input{index} #u8) false)"))
        .collect::<Vec<_>>()
        .join(" ");
    let error = counterexample(&format!("(#theorem bounded (#proof-or {claims}))"));
    assert!(
        error.contains("additional counterexamples omitted"),
        "{error}"
    );
    assert!(
        error.len() < 10_000,
        "oversized witness: {} bytes",
        error.len()
    );
}

#[test]
fn signed_and_character_inputs_keep_their_literal_spelling() {
    let signed = counterexample(
        "(#theorem signed
        (#proof-for-all (: value #i128)
          (#proof-implies (#i128::eq value -170141183460469231731687303715884105728i128) false)))",
    );
    assert!(
        signed.contains("value = -170141183460469231731687303715884105728i128"),
        "{signed}"
    );
    let character = counterexample(
        "(#theorem character
        (#proof-for-all (: value #char)
          (#proof-implies (#char::eq value #\\λ) false)))",
    );
    assert!(character.contains("value = #\\λ"), "{character}");
}

#[test]
fn an_inductive_witness_is_not_advertised_as_a_concrete_execution() {
    let source = "(#fn countdown (: count #u8) #u8
        (#let-mut remaining #u8 count)
        (#label again (#while (#u8::gt remaining 0u8)
          (#set remaining (#u8::sub-wrap remaining 1u8))))
        (#return remaining))
      (#theorem bad-rank
        (#proof-with-invariants ((countdown again true 0u8))
          (#proof-contract countdown true true)))";
    let error = lim::check_types(&lim::parse_program(source).unwrap()).unwrap_err();
    assert!(error.starts_with("theorem '"), "{error}");
    assert!(error.contains("unproved"), "{error}");
    assert!(error.contains("inductive obligation witness"), "{error}");
    assert!(error.contains("not a concrete execution replay"), "{error}");
}
mod support;

#[test]
fn opaque_record_fields_are_not_exposed_by_counterexample_rendering() {
    let scratch = support::Scratch::new("proof-private-witness");
    std::fs::write(
        scratch.path().join("opaque.lim"),
        "(#struct Secret () (: hidden-token #u8)) (#opaque Secret)",
    )
    .unwrap();
    let source = "(#alias Secret = ./opaque.lim::Secret)
      (#theorem bounded-private-witness (#proof-for-all (: secret Secret) false))";
    let path = scratch.path().join("main.lim");
    std::fs::write(&path, source).unwrap();
    let program = lim::parse_program_from_path(source, &path).unwrap();
    let error = lim::check_types(&program).unwrap_err();
    assert!(error.contains("disproved"), "{error}");
    assert!(error.contains("<private representation>"), "{error}");
    assert!(!error.contains("hidden-token"), "{error}");
}

#[test]
fn a_reported_mutation_input_reproduces_the_violation_in_native_code() {
    use std::{process::Command, time::Duration};
    let scratch = support::Scratch::new("proof-witness-replay");
    let function = "(#fn overwrite (: source (#ref-mut #u8)) ()
        (#deref-set source 7u8) (#return ()))";
    let error = counterexample(&format!(
        "{function}
      (#theorem unchanged (#proof-contract overwrite
        (#u8::eq (#deref source) 1u8)
        (#proof-eq (#deref source) (#proof-old (#deref source)))))"
    ));
    assert!(error.contains("source = mut-ref#0(1u8)"), "{error}");
    let source = format!(
        "{function}
      (#fn main () #u64
        (#let-mut source #u8 1u8)
        (#call overwrite (: source (#borrow-mut source)))
        (#return (#if (#u8::ne source 1u8) 42u64 1u64)))"
    );
    std::fs::write(scratch.path().join("replay.lim"), source).unwrap();
    let (status, _, errors) = support::run(
        Command::new(env!("CARGO_BIN_EXE_lim"))
            .current_dir(scratch.path())
            .env("PATH", "")
            .args(["replay.lim", "-o", "program"]),
        Duration::from_secs(20),
        1024 * 1024,
    )
    .unwrap();
    assert!(status.success(), "{}", String::from_utf8_lossy(&errors));
    let (status, stdout, stderr) = support::run(
        &mut Command::new(scratch.path().join("program")),
        Duration::from_secs(5),
        1024 * 1024,
    )
    .unwrap();
    assert_eq!(status.code(), Some(42));
    assert!(stdout.is_empty() && stderr.is_empty());
}
