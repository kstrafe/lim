//! Natural comparison reduces through both induction arguments without losing scope.
const EXAMPLE: &str = include_str!("../examples/proof_natural_comparison.lim");

fn checks(source: &str) {
    let program = lim::parse_program(source).unwrap_or_else(|why| panic!("{why}\n{source}"));
    lim::check_types(&program).unwrap_or_else(|why| panic!("{why}\n{source}"));
}
fn rejects(source: &str) {
    let why = lim::check_types(&lim::parse_program(source).unwrap()).unwrap_err();
    assert!(why.contains("type mismatch"), "{why}");
    assert!(!why.contains("resource limit"), "{why}");
}
fn definitions() -> &'static str {
    EXAMPLE.split("(#theorem").next().unwrap()
}
fn literal(value: &str) -> String {
    format!("(#pt-nat-literal #pt-nat \"{value}\")")
}
fn flag(which: &str) -> String {
    format!("(#pt-construct comparison-flag () () {which} ())")
}
fn compare(left: &str, right: &str) -> String {
    format!("(#pt-app (#pt-use less-or-equal ()) {left} {right})")
}
fn assertion(left: &str, right: &str, answer: &str) -> String {
    let expected = flag(answer);
    format!(
        "(#theorem computes (#universes) (#parameters)
      (#statement (#pt-eq (#pt-use comparison-flag ()) {} {expected}))
      (#proof (#pt-refl (#pt-use comparison-flag ()) {expected})))",
        compare(left, right)
    )
}

#[test]
fn large_comparison_theorems_have_no_assumptions() {
    checks(EXAMPLE);
    for target in ["two-to-128-le-next", "next-not-le-two-to-128"] {
        let checked = lim::check_theorem_details_from_path_with_config(
            EXAMPLE,
            &std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("examples/proof_natural_comparison.lim"),
            &lim::CompileConfig::default(),
            target,
        )
        .unwrap();
        assert!(checked.foundations.is_empty());
    }
}

#[test]
fn small_pairs_match_an_independent_reference() {
    for left in 0..=12u128 {
        for right in 0..=12u128 {
            checks(&format!(
                "{}\n{}",
                definitions(),
                assertion(
                    &literal(&left.to_string()),
                    &literal(&right.to_string()),
                    if left <= right { "yes" } else { "no" }
                )
            ));
        }
    }
}

#[test]
fn arbitrary_precision_equal_and_adjacent_values_are_compared_exactly() {
    let huge = "9".repeat(4096);
    let previous = format!("{}8", "9".repeat(4095));
    for (left, right, answer) in [
        (huge.as_str(), huge.as_str(), "yes"),
        (previous.as_str(), huge.as_str(), "yes"),
        (huge.as_str(), previous.as_str(), "no"),
        (
            "340282366920938463463374607431768211457",
            "340282366920938463463374607431768211456",
            "no",
        ),
    ] {
        checks(&format!(
            "{}\n{}",
            definitions(),
            assertion(&literal(left), &literal(right), answer)
        ));
    }
}

#[test]
fn false_results_and_changed_terminal_cases_are_rejected() {
    rejects(&format!(
        "{}\n{}",
        definitions(),
        assertion(&literal("2"), &literal("1"), "yes")
    ));
    let small = format!(
        "{}\n{}",
        definitions(),
        assertion(&literal("2"), &literal("1"), "no")
    );
    let changed = small.replacen(
        "(#pt-construct comparison-flag () () no ())",
        "(#pt-construct comparison-flag () () yes ())",
        1,
    );
    rejects(&changed);
}

#[test]
fn unknown_operands_do_not_reduce_as_zero_and_capture_is_preserved() {
    for (left, right, answer) in [
        ("value", &literal("1")[..], "no"),
        (&literal("1")[..], "value", "yes"),
    ] {
        rejects(&format!(
            "{}\n(#theorem symbolic (#universes) (#parameters (#parameter value #pt-nat))
          (#statement (#pt-eq (#pt-use comparison-flag ()) {} {}))
          (#proof (#pt-refl (#pt-use comparison-flag ()) {})))",
            definitions(),
            compare(left, right),
            flag(answer),
            flag(answer)
        ));
    }
    let source = format!(
        "{}\n{}",
        definitions(),
        assertion(&literal("2"), &literal("1"), "no")
    );
    // Renaming distinct binders must leave both operand scopes intact.
    checks(
        &source
            .replace("right-index", "remaining-right")
            .replace("right-previous", "preceding-right"),
    );
    rejects(&source.replace(
        "(#pt-app older right-previous)",
        "(#pt-app older right-index)",
    ));
}

#[test]
fn opacity_and_invalid_erased_or_unused_terms_are_checked() {
    let small = format!(
        "{}\n{}",
        definitions(),
        assertion(&literal("3"), &literal("2"), "no")
    );
    rejects(&small.replacen(
        "#math-definition less-or-equal",
        "#math-opaque less-or-equal",
        1,
    ));
    rejects(&small.replace("(#pt-app older right-previous)",
      "(#pt-let (#parameter ignored (#pt-use comparison-flag ())) #pt-false (#pt-app older right-previous))"));
    rejects(&small.replace("(#pt-app older right-previous)", "#pt-false"));
}

#[test]
fn the_inner_case_cannot_use_the_outer_predecessor_as_its_operand() {
    let source = format!(
        "{}\n{}",
        definitions(),
        assertion(&literal("1"), &literal("2"), "yes")
    );
    let original = "            right-index)))";
    assert!(source.contains(original));
    let changed = source.replace(original, "            previous)))");
    checks(changed.split("(#theorem").next().unwrap());
    rejects(&changed);
}
