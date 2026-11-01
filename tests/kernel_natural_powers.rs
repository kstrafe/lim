//! Affine iteration must preserve unbounded natural and binding semantics.
const EXAMPLE: &str = include_str!("../examples/proof_natural_powers.lim");
fn checks(source: &str) {
    let program = lim::parse_program(source).unwrap_or_else(|why| panic!("{why}\n{source}"));
    lim::check_types(&program).unwrap_or_else(|why| panic!("{why}\n{source}"));
}
fn rejects(source: &str, expected: &str) {
    let why = lim::check_types(&lim::parse_program(source).unwrap()).unwrap_err();
    assert!(why.contains(expected), "expected {expected}: {why}");
}
fn literal(value: &str) -> String {
    format!("(#pt-nat-literal #pt-nat \"{value}\")")
}
fn assertion(value: &str, expected: &str) -> String {
    format!(
        "(#theorem computes (#universes) (#parameters)
      (#statement (#pt-eq #pt-nat {value} {expected})) (#proof (#pt-refl #pt-nat {expected})))"
    )
}
fn definitions() -> &'static str {
    EXAMPLE.split("(#theorem").next().unwrap()
}

#[test]
fn native_large_powers_and_affine_offsets_need_no_logical_assumptions() {
    checks(EXAMPLE);
    for target in ["two-to-128", "affine-growth"] {
        let checked = lim::check_theorem_details_from_path_with_config(
            EXAMPLE,
            &std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("examples/proof_natural_powers.lim"),
            &lim::CompileConfig::default(),
            target,
        )
        .unwrap();
        assert!(checked.foundations.is_empty());
    }
}

#[test]
fn small_powers_and_affine_iterations_match_an_independent_integer_reference() {
    for base in 0..=6u128 {
        for exponent in 0..=8u32 {
            let value = format!(
                "(#pt-app (#pt-use power ()) {} {})",
                literal(&base.to_string()),
                literal(&exponent.to_string())
            );
            let expected = literal(&base.pow(exponent).to_string());
            checks(&format!(
                "{}\n{}",
                definitions(),
                assertion(&value, &expected)
            ));
        }
    }
}

#[test]
fn false_large_values_and_changed_affine_steps_are_rejected() {
    rejects(
        &EXAMPLE.replace(
            "340282366920938463463374607431768211456",
            "340282366920938463463374607431768211457",
        ),
        "type mismatch",
    );
    rejects(
        &EXAMPLE.replace(
            "340282366920938463463374607431768211455",
            "340282366920938463463374607431768211454",
        ),
        "type mismatch",
    );
    rejects(
        &EXAMPLE.replace("value (#pt-numeral 2)", "value (#pt-numeral 3)"),
        "type mismatch",
    );
}

#[test]
fn zero_and_one_bases_do_not_iterate_through_huge_counts() {
    let huge = literal(&"9".repeat(4096));
    for (base, exponent, answer) in [
        ("0", literal("0"), "1"),
        ("0", huge.clone(), "0"),
        ("1", huge, "1"),
    ] {
        let value = format!("(#pt-app (#pt-use power ()) {} {exponent})", literal(base));
        checks(&format!(
            "{}\n{}",
            definitions(),
            assertion(&value, &literal(answer))
        ));
    }
}

#[test]
fn exponent_one_does_not_construct_an_unused_oversized_square() {
    let huge = literal(&"9".repeat(4096));
    let value = format!("(#pt-app (#pt-use power ()) {huge} {})", literal("1"));
    checks(&format!("{}\n{}", definitions(), assertion(&value, &huge)));
}

#[test]
fn an_unbounded_symbolic_exponent_is_not_silently_treated_as_zero() {
    rejects(&format!("{}\n(#theorem not-all-ones (#universes) (#parameters (#parameter exponent #pt-nat))
      (#statement (#pt-eq #pt-nat (#pt-app (#pt-use power ()) (#pt-numeral 2) exponent) (#pt-numeral 1)))
      (#proof (#pt-refl #pt-nat (#pt-numeral 1))))", definitions()), "type mismatch");
}

#[test]
fn nonlinear_accumulators_and_variable_iteration_counts_keep_their_meaning() {
    for (step, answer) in [
        ("(#pt-app (#pt-use multiply ()) value value)", "4"),
        ("(#pt-app (#pt-use power ()) (#pt-numeral 2) value)", "4"),
    ] {
        let fold = format!(
            "(#pt-nat-induct (#pt-lambda ((index #pt-nat)) #pt-nat) (#pt-numeral 2)
          (#pt-lambda ((previous #pt-nat) (value #pt-nat)) {step}) (#pt-numeral 1))"
        );
        checks(&format!(
            "{}\n{}",
            definitions(),
            assertion(&fold, &literal(answer))
        ));
        rejects(
            &format!("{}\n{}", definitions(), assertion(&fold, &literal("1"))),
            "type mismatch",
        );
    }
}

#[test]
fn large_general_powers_fail_closed_at_the_unchanged_budget() {
    let power = format!(
        "(#pt-app (#pt-use power ()) (#pt-numeral 2) {})",
        literal(&"9".repeat(100))
    );
    rejects(
        &format!("{}\n{}", definitions(), assertion(&power, &literal("0"))),
        "resource limit",
    );
}

#[test]
fn iteration_counts_are_not_truncated_to_machine_widths() {
    for count in [
        "18446744073709551616",
        "340282366920938463463374607431768211456",
    ] {
        let power = format!(
            "(#pt-app (#pt-use power ()) (#pt-numeral 2) {})",
            literal(count)
        );
        rejects(
            &format!("{}\n{}", definitions(), assertion(&power, &literal("1"))),
            "resource limit",
        );
    }
}

#[test]
fn a_reset_with_an_unknown_nested_count_still_distinguishes_zero() {
    let step = "(#pt-nat-induct (#pt-lambda ((inner-index #pt-nat)) #pt-nat) (#pt-numeral 7)
      (#pt-lambda ((inner-previous #pt-nat) (inner-value #pt-nat)) (#pt-numeral 3)) value)";
    for (initial, answer, wrong) in [("0", "7", "3"), ("1", "3", "7")] {
        let fold = format!(
            "(#pt-nat-induct (#pt-lambda ((index #pt-nat)) #pt-nat) {}
          (#pt-lambda ((previous #pt-nat) (value #pt-nat)) {step}) (#pt-numeral 1))",
            literal(initial)
        );
        checks(&format!(
            "{}\n{}",
            definitions(),
            assertion(&fold, &literal(answer))
        ));
        rejects(
            &format!("{}\n{}", definitions(), assertion(&fold, &literal(wrong))),
            "type mismatch",
        );
    }
}
