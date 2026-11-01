//! Repeated predecessor is truncated mathematical subtraction, not word arithmetic.
const EXAMPLE: &str = include_str!("../examples/proof_natural_subtraction.lim");
fn checks(source: &str) {
    let program = lim::parse_program(source).unwrap_or_else(|why| panic!("{why}\n{source}"));
    lim::check_types(&program).unwrap_or_else(|why| panic!("{why}\n{source}"));
}
fn rejects(source: &str, expected: &str) {
    let why = lim::check_types(&lim::parse_program(source).unwrap()).unwrap_err();
    assert!(why.contains(expected), "expected {expected}: {why}");
    assert!(!why.contains("resource limit"), "{why}");
}
fn definitions() -> &'static str {
    EXAMPLE.split("(#theorem").next().unwrap()
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
fn subtraction(left: &str, right: &str) -> String {
    format!("(#pt-app (#pt-use subtract ()) {left} {right})")
}

#[test]
fn native_large_subtraction_and_saturation_need_no_logical_assumptions() {
    checks(EXAMPLE);
    for target in ["large-subtraction", "truncated-at-zero"] {
        let checked = lim::check_theorem_details_from_path_with_config(
            EXAMPLE,
            &std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("examples/proof_natural_subtraction.lim"),
            &lim::CompileConfig::default(),
            target,
        )
        .unwrap();
        assert!(checked.foundations.is_empty());
    }
}

#[test]
fn subtraction_matches_independent_integer_reference_for_small_pairs() {
    for left in 0..=12u128 {
        for right in 0..=12u128 {
            checks(&format!(
                "{}\n{}",
                definitions(),
                assertion(
                    &subtraction(&literal(&left.to_string()), &literal(&right.to_string())),
                    &literal(&left.saturating_sub(right).to_string())
                )
            ));
        }
    }
}

#[test]
fn wrong_results_and_changed_well_typed_bodies_are_rejected() {
    rejects(
        &EXAMPLE.replace(
            "340282366920938463444927863358058659840",
            "340282366920938463444927863358058659841",
        ),
        "type mismatch",
    );
    let small = format!(
        "{}\n{}",
        definitions(),
        assertion(&subtraction(&literal("7"), &literal("2")), &literal("5"))
    );
    let changed = small.replace(
        "(#pt-lambda ((previous #pt-nat) (ignored #pt-nat)) previous)",
        "(#pt-lambda ((previous #pt-nat) (ignored #pt-nat)) (#pt-succ previous))",
    );
    checks(changed.split("(#theorem").next().unwrap());
    rejects(&changed, "type mismatch");
}

#[test]
fn maximum_decimal_values_and_machine_width_boundaries_do_not_truncate() {
    let huge = "9".repeat(4096);
    let before = format!("{}8", "9".repeat(4095));
    for (left, right, result) in [
        (huge.as_str(), "1", before.as_str()),
        (huge.as_str(), huge.as_str(), "0"),
        ("7", huge.as_str(), "0"),
        ("18446744073709551617", "18446744073709551616", "1"),
        (
            "340282366920938463463374607431768211457",
            "340282366920938463463374607431768211456",
            "1",
        ),
    ] {
        checks(&format!(
            "{}\n{}",
            definitions(),
            assertion(
                &subtraction(&literal(left), &literal(right)),
                &literal(result)
            )
        ));
    }
}

#[test]
fn unknown_counts_and_outer_locals_are_never_replaced_by_zero() {
    let source = format!(
        "{}\n(#theorem unsound (#universes) (#parameters (#parameter value #pt-nat))
        (#statement (#pt-eq #pt-nat {} #pt-zero)) (#proof (#pt-refl #pt-nat #pt-zero)))",
        definitions(),
        subtraction(&literal("1"), "value")
    );
    rejects(&source, "type mismatch");
    let source = format!(
        "{}\n(#theorem unsound (#universes) (#parameters (#parameter value #pt-nat))
        (#statement (#pt-eq #pt-nat {} #pt-zero)) (#proof (#pt-refl #pt-nat #pt-zero)))",
        definitions(),
        subtraction("value", &literal("1"))
    );
    rejects(&source, "type mismatch");
}

#[test]
fn opaque_predecessors_and_invalid_erased_values_do_not_acquire_reduction_rules() {
    let small = format!(
        "{}\n{}",
        definitions(),
        assertion(&subtraction(&literal("7"), &literal("2")), &literal("5"))
    );
    rejects(
        &small.replacen(
            "#math-definition predecessor",
            "#math-opaque predecessor",
            1,
        ),
        "type mismatch",
    );
    rejects(&small.replace("(#pt-app (#pt-use predecessor ()) value)",
        "(#pt-let (#parameter ignored #pt-nat) #pt-false (#pt-app (#pt-use predecessor ()) value))"), "type mismatch");
    rejects(
        &small.replace(
            "(ignored #pt-nat)) previous",
            "(ignored #pt-nat)) #pt-false",
        ),
        "type mismatch",
    );
}

#[test]
fn nested_subtraction_and_other_natural_operations_keep_exact_meaning() {
    let nested = subtraction(
        &subtraction(
            &literal("100000000000000000000"),
            &literal("18446744073709551616"),
        ),
        &literal("81553255926290448380"),
    );
    checks(&format!(
        "{}\n{}",
        definitions(),
        assertion(&nested, &literal("4"))
    ));
    checks(
        &EXAMPLE
            .replace("predecessor", "unrelated-operation")
            .replace("subtract", "different-name"),
    );
}

#[test]
fn zero_count_does_not_evaluate_an_unused_step_but_still_checks_its_type() {
    let source = format!(
        "{}\n{}",
        definitions(),
        assertion(&subtraction(&literal("7"), &literal("0")), &literal("7"))
    );
    checks(&source);
    rejects(
        &source.replace("(#pt-app (#pt-use predecessor ()) value)", "#pt-false"),
        "type mismatch",
    );
}

#[test]
fn changed_zero_branches_and_wrong_binder_subjects_keep_their_actual_meaning() {
    let small = format!(
        "{}\n{}",
        definitions(),
        assertion(&subtraction(&literal("7"), &literal("8")), &literal("0"))
    );
    let original = "(#pt-nat-induct (#pt-lambda ((index #pt-nat)) #pt-nat) #pt-zero";
    assert!(small.contains(original));
    let changed = small.replacen(
        original,
        "(#pt-nat-induct (#pt-lambda ((index #pt-nat)) #pt-nat) (#pt-numeral 1)",
        1,
    );
    checks(changed.split("(#theorem").next().unwrap());
    rejects(&changed, "type mismatch");
    let small = format!(
        "{}\n{}",
        definitions(),
        assertion(&subtraction(&literal("7"), &literal("2")), &literal("5"))
    );
    for other in ["previous", "left"] {
        let changed = small.replace(
            "(#pt-app (#pt-use predecessor ()) value)",
            &format!("(#pt-app (#pt-use predecessor ()) {other})"),
        );
        checks(changed.split("(#theorem").next().unwrap());
        rejects(&changed, "type mismatch");
    }
}
