//! Batching a structurally checked fold must not trust names or bypass typing.
const EXAMPLE: &str = include_str!("../examples/proof_natural_arithmetic.lim");

fn checks(source: &str) {
    let program = lim::parse_program(source).unwrap_or_else(|why| panic!("{why}\n{source}"));
    lim::check_types(&program).unwrap_or_else(|why| panic!("{why}\n{source}"));
}

fn rejects(source: &str, expected: &str) {
    let program = lim::parse_program(source).unwrap();
    let why = lim::check_types(&program).unwrap_err();
    assert!(why.contains(expected), "expected {expected}: {why}");
}

fn assertion(left: &str, right: &str) -> String {
    format!(
        "(#theorem computes (#universes) (#parameters)
      (#statement (#pt-eq #pt-nat {left} {right}))
      (#proof (#pt-refl #pt-nat {right})))"
    )
}

fn literal(decimal: &str) -> String {
    format!("(#pt-nat-literal #pt-nat \"{decimal}\")")
}

#[test]
fn large_native_addition_and_multiplication_check_without_any_assumptions() {
    checks(EXAMPLE);
    for target in ["large-addition", "large-multiplication"] {
        let details = lim::check_theorem_details_from_path_with_config(
            EXAMPLE,
            &std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("examples/proof_natural_arithmetic.lim"),
            &lim::CompileConfig::default(),
            target,
        )
        .unwrap();
        assert!(details.foundations.is_empty());
    }
}

#[test]
fn false_large_results_are_rejected_in_both_directions() {
    for (correct, incorrect) in [
        (
            "340282366920938463647842048168863727616",
            "340282366920938463647842048168863727617",
        ),
        (
            "18446744073709551616000000000000000000000",
            "18446744073709551616000000000000000000001",
        ),
    ] {
        rejects(&EXAMPLE.replace(correct, incorrect), "type mismatch");
    }
}

#[test]
fn recognition_is_independent_of_the_definition_names() {
    checks(
        &EXAMPLE
            .replace("add", "unrelated-name")
            .replace("multiply", "another-name"),
    );
}

#[test]
fn native_small_arithmetic_agrees_with_independent_machine_computation() {
    // Each independently checked theorem has its own work budget.
    let definitions = EXAMPLE.split("(#theorem").next().unwrap();
    for a in 0..=8u64 {
        for b in 0..=8u64 {
            for (function, answer) in [("add", a + b), ("multiply", a * b)] {
                let value = format!(
                    "(#pt-app (#pt-use {function} ()) {} {})",
                    literal(&a.to_string()),
                    literal(&b.to_string())
                );
                checks(&format!(
                    "{definitions}\n{}",
                    assertion(&value, &literal(&answer.to_string()))
                ));
            }
        }
    }
}

#[test]
fn maximum_digits_work_without_magnitude_sized_loops_and_carry_overflow_fails() {
    let definitions = EXAMPLE.split("(#theorem").next().unwrap();
    let huge = "9".repeat(4096);
    let almost = format!("{}8", "9".repeat(4095));
    let addition = format!(
        "(#pt-app (#pt-use add ()) {} {})",
        literal(&almost),
        literal("1")
    );
    checks(&format!(
        "{definitions}\n{}",
        assertion(&addition, &literal(&huge))
    ));
    let overflow = format!(
        "(#pt-app (#pt-use add ()) {} {})",
        literal(&huge),
        literal("1")
    );
    rejects(
        &format!("{definitions}\n{}", assertion(&overflow, &literal("0"))),
        "natural arithmetic digit limit",
    );
    let zero_product = format!(
        "(#pt-app (#pt-use multiply ()) {} {})",
        literal("0"),
        literal(&huge)
    );
    checks(&format!(
        "{definitions}\n{}",
        assertion(&zero_product, &literal("0"))
    ));
}

#[test]
fn product_work_budget_is_checked_before_the_digit_multiplication() {
    let definitions = EXAMPLE.split("(#theorem").next().unwrap();
    let big = literal(&"9".repeat(512));
    let product = format!("(#pt-app (#pt-use multiply ()) {big} {big})");
    rejects(
        &format!("{definitions}\n{}", assertion(&product, &literal("0"))),
        "kernel resource limit",
    );
}

#[test]
fn invalid_erased_let_values_and_annotations_do_not_become_valid_arithmetic() {
    let definitions = EXAMPLE.split("(#theorem").next().unwrap();
    for (annotation, value) in [("#pt-nat", "#pt-false"), ("#pt-false", "#pt-zero")] {
        let bad = definitions.replace(
            "(#pt-succ sum)",
            &format!("(#pt-let (#parameter ignored {annotation}) {value} (#pt-succ sum))"),
        );
        rejects(&bad, "type mismatch");
    }
}

#[test]
fn a_function_named_add_with_a_different_step_keeps_its_actual_meaning() {
    let definitions = EXAMPLE.split("(#theorem").next().unwrap();
    let bad_model = definitions.replace("(#pt-succ sum)", "previous");
    let value = "(#pt-app (#pt-use add ()) (#pt-numeral 3) (#pt-numeral 4))";
    checks(&format!(
        "{bad_model}\n{}",
        assertion(value, "(#pt-numeral 3)")
    ));
    rejects(
        &format!("{bad_model}\n{}", assertion(value, "(#pt-numeral 7)")),
        "type mismatch",
    );
}

#[test]
fn nontranslation_affine_steps_preserve_their_actual_meaning() {
    let definitions = EXAMPLE.split("(#theorem").next().unwrap();
    let doubling = definitions.replace("(#pt-succ sum)", "(#pt-app (#pt-use twice ()) sum)");
    let twice = "(#math-definition twice () (#pt-pi ((x #pt-nat)) #pt-nat)
      (#pt-lambda ((x #pt-nat))
        (#pt-nat-induct (#pt-lambda ((index #pt-nat)) #pt-nat) x
          (#pt-lambda ((previous #pt-nat) (sum #pt-nat)) (#pt-succ sum)) x)))";
    let value = "(#pt-app (#pt-use add ()) (#pt-numeral 3) (#pt-numeral 2))";
    checks(&format!(
        "{twice}\n{doubling}\n{}",
        assertion(value, "(#pt-numeral 12)")
    ));
    rejects(
        &format!(
            "{twice}\n{doubling}\n{}",
            assertion(value, "(#pt-numeral 5)")
        ),
        "type mismatch",
    );
}

#[test]
fn checked_nominal_natural_families_preserve_their_identity() {
    checks(
        r#"(#math-inductive tally () () (#pt-type 0)
        ((zero ()) (next ((previous #pt-self)))))
      (#math-definition add-tallies ()
        (#pt-pi ((left (#pt-use tally ())) (right (#pt-use tally ()))) (#pt-use tally ()))
        (#pt-lambda ((left (#pt-use tally ())) (right (#pt-use tally ())))
          (#pt-induct tally () ()
            (#pt-lambda ((index (#pt-use tally ()))) (#pt-use tally ()))
            (left (#pt-lambda ((previous (#pt-use tally ())) (sum (#pt-use tally ())))
              (#pt-construct tally () () next (sum)))) right)))
      (#theorem tallies-compute (#universes) (#parameters)
        (#statement (#pt-eq (#pt-use tally ())
          (#pt-app (#pt-use add-tallies ())
            (#pt-nat-literal tally "2") (#pt-nat-literal tally "184467440737095516160"))
          (#pt-nat-literal tally "184467440737095516162")))
        (#proof (#pt-refl (#pt-use tally ()) (#pt-nat-literal tally "184467440737095516162"))))"#,
    );
}

#[test]
fn opaque_step_functions_are_not_unfolded_or_assumed_to_be_addition() {
    let definitions = EXAMPLE.split("(#theorem").next().unwrap();
    let successor = "(#math-opaque hidden () (#pt-pi ((x #pt-nat)) #pt-nat)
      (#pt-lambda ((x #pt-nat)) (#pt-succ x)))";
    let opaque = definitions.replace("(#pt-succ sum)", "(#pt-app (#pt-use hidden ()) sum)");
    let value = "(#pt-app (#pt-use add ()) (#pt-numeral 3) (#pt-numeral 2))";
    rejects(
        &format!(
            "{successor}\n{opaque}\n{}",
            assertion(value, "(#pt-numeral 5)")
        ),
        "type mismatch",
    );
}

#[test]
fn outer_locals_and_the_predecessor_cannot_masquerade_as_the_accumulator() {
    let definitions = EXAMPLE.split("(#theorem").next().unwrap();
    for step in ["previous", "left", "(#pt-succ previous)"] {
        let altered = definitions.replace("(#pt-succ sum)", step);
        let value = "(#pt-app (#pt-use add ()) (#pt-numeral 3) (#pt-numeral 4))";
        let expected = if step == "(#pt-succ previous)" {
            "4"
        } else {
            "3"
        };
        checks(&format!(
            "{altered}\n{}",
            assertion(value, &literal(expected))
        ));
        rejects(
            &format!("{altered}\n{}", assertion(value, &literal("7"))),
            "type mismatch",
        );
    }
}

#[test]
fn constructor_projections_and_typed_lets_keep_exact_digit_values() {
    let definitions = EXAMPLE.split("(#theorem").next().unwrap();
    let huge = literal("184467440737095516160");
    let pair = format!("(#pt-pair (#pt-sigma ((field #pt-nat)) #pt-nat) {huge} (#pt-numeral 2))");
    let projected = format!("(#pt-app (#pt-use add ()) (#pt-first {pair}) (#pt-second {pair}))");
    checks(&format!(
        "{definitions}\n{}",
        assertion(&projected, &literal("184467440737095516162"))
    ));
    let record = "(#math-inductive holder () () (#pt-type 0) ((make ((field #pt-nat)))))";
    let projected = format!("(#pt-project holder 0 (#pt-construct holder () () make ({huge})))");
    let through_let = format!(
        "(#pt-let (#parameter saved #pt-nat) {projected}
      (#pt-app (#pt-use add ()) (#pt-numeral 2) saved))"
    );
    checks(&format!(
        "{definitions}\n{record}\n{}",
        assertion(&through_let, &literal("184467440737095516162"))
    ));
}

#[test]
fn zero_folds_typecheck_the_step_without_executing_its_unused_arithmetic() {
    let definitions = EXAMPLE.split("(#theorem").next().unwrap();
    let huge = literal(&"9".repeat(512));
    let product = format!("(#pt-app (#pt-use multiply ()) {huge} {huge})");
    let fold = format!(
        "(#pt-nat-induct (#pt-lambda ((index #pt-nat)) #pt-nat)
      (#pt-numeral 7) (#pt-lambda ((previous #pt-nat) (accumulator #pt-nat)) {product})
      (#pt-nat-literal #pt-nat \"0\"))"
    );
    checks(&format!(
        "{definitions}\n{}",
        assertion(&fold, &literal("7"))
    ));
    let invalid = fold.replace(
        &product,
        "(#pt-let (#parameter ignored #pt-nat) #pt-false accumulator)",
    );
    rejects(
        &format!("{definitions}\n{}", assertion(&invalid, &literal("7"))),
        "type mismatch",
    );
}

#[test]
fn a_nontranslation_step_can_discard_an_expensive_checked_base() {
    let definitions = EXAMPLE.split("(#theorem").next().unwrap();
    let huge = literal(&"9".repeat(512));
    let base = format!("(#pt-app (#pt-use multiply ()) {huge} {huge})");
    let fold = format!(
        "(#pt-nat-induct (#pt-lambda ((index #pt-nat)) #pt-nat)
      {base} (#pt-lambda ((previous #pt-nat) (accumulator #pt-nat)) (#pt-numeral 1))
      (#pt-nat-literal #pt-nat \"1\"))"
    );
    checks(&format!(
        "{definitions}\n{}",
        assertion(&fold, &literal("1"))
    ));
    let invalid = fold.replace(
        &base,
        "(#pt-let (#parameter ignored #pt-nat) #pt-false #pt-zero)",
    );
    rejects(
        &format!("{definitions}\n{}", assertion(&invalid, &literal("1"))),
        "type mismatch",
    );
}
