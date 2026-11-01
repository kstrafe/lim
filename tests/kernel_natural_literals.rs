//! Compact mathematical naturals remain checked nominal constructor values.
const EXAMPLE: &str = include_str!("../examples/proof_natural_literals.lim");
fn checks(source: &str) {
    let program = lim::parse_program(source).unwrap_or_else(|why| panic!("{why}\n{source}"));
    lim::check_types(&program).unwrap_or_else(|why| panic!("{why}\n{source}"));
}
fn rejects(source: &str, expected: &str) {
    let program = lim::parse_program(source).unwrap();
    let why = lim::check_types(&program).unwrap_err();
    assert!(why.contains(expected), "expected {expected}: {why}");
    assert!(!why.contains("resource limit"), "{why}");
}
const TALLY: &str =
    r#"(#math-inductive tally () () (#pt-type 0) ((zero ()) (next ((previous #pt-self)))))"#;

#[test]
fn huge_successor_and_predecessor_compute_with_ordinary_nat_induction() {
    checks(EXAMPLE);
    for name in ["huge-successor", "huge-predecessor"] {
        lim::check_theorem_from_path_with_config(
            EXAMPLE,
            &std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("examples/proof_natural_literals.lim"),
            &lim::CompileConfig::default(),
            name,
        )
        .unwrap();
    }
}

#[test]
fn compact_literals_convert_both_ways_with_small_constructor_values() {
    for (decimal, constructor) in [
        ("0", "#pt-zero"),
        ("1", "(#pt-succ #pt-zero)"),
        ("3", "(#pt-numeral 3)"),
    ] {
        for (left, right) in [
            (
                format!("(#pt-nat-literal #pt-nat \"{decimal}\")"),
                constructor.to_owned(),
            ),
            (
                constructor.to_owned(),
                format!("(#pt-nat-literal #pt-nat \"{decimal}\")"),
            ),
        ] {
            checks(&format!(
                "(#theorem small (#universes) (#parameters)
                (#statement (#pt-eq #pt-nat {left} {right})) (#proof (#pt-refl #pt-nat {left})))"
            ));
        }
    }
}

#[test]
fn user_defined_natural_families_keep_their_own_nominal_identity() {
    checks(&format!(
        r#"{TALLY}
      (#theorem tallies (#universes) (#parameters)
        (#statement (#pt-eq (#pt-use tally ()) (#pt-nat-literal tally "1")
          (#pt-construct tally () () next ((#pt-nat-literal tally "0")))))
        (#proof (#pt-refl (#pt-use tally ()) (#pt-nat-literal tally "1"))))"#
    ));
    rejects(
        &format!(
            r#"{TALLY}
      (#math-definition wrong () #pt-nat (#pt-nat-literal tally "7"))"#
        ),
        "type mismatch",
    );
    rejects(
        &format!(
            r#"{TALLY}
      (#math-definition wrong () (#pt-use tally ()) (#pt-nat-literal #pt-nat "7"))"#
        ),
        "type mismatch",
    );
}

#[test]
fn false_large_equalities_are_not_proved_by_reflexivity_or_truncation() {
    for (left, right) in [
        ("184467440737095516160", "184467440737095516161"),
        ("184467440737095516160", "0"),
        ("100000000000000000000", "99999999999999999999"),
    ] {
        rejects(
            &format!(
                r#"(#theorem false-equality (#universes) (#parameters)
          (#statement (#pt-eq #pt-nat (#pt-nat-literal #pt-nat "{left}") (#pt-nat-literal #pt-nat "{right}")))
          (#proof (#pt-refl #pt-nat (#pt-nat-literal #pt-nat "{left}"))))"#
            ),
            "type mismatch",
        );
    }
}

#[test]
fn compact_literals_require_canonical_decimal_strings_and_exact_arity() {
    for decimal in ["", "00", "01", "-1", "+1", "1_000", "1.0", "１２", " 1"] {
        rejects(
            &format!(r#"(#math-definition bad () #pt-nat (#pt-nat-literal #pt-nat "{decimal}"))"#),
            "canonical unsigned decimal",
        );
    }
    for form in [
        "(#pt-nat-literal #pt-nat 12)",
        "(#pt-nat-literal #pt-nat)",
        "(#pt-nat-literal #pt-nat \"12\" #pt-zero)",
    ] {
        rejects(
            &format!("(#math-definition bad () #pt-nat {form})"),
            "#pt-nat-literal",
        );
    }
}

#[test]
fn a_maximum_length_natural_is_compact_and_one_extra_digit_is_rejected() {
    let decimal = "9".repeat(4096);
    checks(&format!(
        r#"(#theorem large (#universes) (#parameters)
      (#statement (#pt-eq #pt-nat (#pt-nat-literal #pt-nat "{decimal}") (#pt-nat-literal #pt-nat "{decimal}")))
      (#proof (#pt-refl #pt-nat (#pt-nat-literal #pt-nat "{decimal}"))))"#
    ));
    rejects(
        &format!(r#"(#math-definition bad () #pt-nat (#pt-nat-literal #pt-nat "{decimal}9"))"#),
        "digit limit",
    );
}

#[test]
fn empty_singleton_wrong_successor_and_propositional_families_are_rejected() {
    for declaration in [
        "(#math-inductive wrong () () (#pt-type 0) ())",
        "(#math-inductive wrong () () (#pt-type 0) ((only ())))",
        "(#math-inductive wrong () () (#pt-type 0) ((zero ()) (next ((previous #pt-nat)))))",
        "(#math-inductive wrong () () #pt-prop ((zero ()) (next ((previous #pt-self)))))",
    ] {
        rejects(
            &format!(
                r#"{declaration}
          (#math-definition bad () (#pt-use wrong ()) (#pt-nat-literal wrong "1"))"#
            ),
            "zero and successor",
        );
    }
}

#[test]
fn parameterized_indexed_polymorphic_and_alias_types_cannot_be_literal_families() {
    for declaration in [
        "(#math-inductive wrong () ((A (#pt-type 0))) (#pt-type 0) ((zero ()) (next ((previous #pt-self)))))",
        "(#math-inductive wrong () () (#indices (i #pt-nat)) (#pt-type 0) ((zero () (#indices #pt-zero)) (next () (#indices #pt-zero))))",
        "(#math-inductive wrong (u) () (#pt-type 0) ((zero ()) (next ((previous #pt-self)))))",
        "(#math-definition wrong () (#pt-type 0) #pt-nat)",
    ] {
        let source = format!(r#"{declaration}
          (#math-definition bad () #pt-nat (#pt-nat-literal wrong "1"))"#);
        let program = lim::parse_program(&source).unwrap();
        let why = lim::check_types(&program).unwrap_err();
        assert!(!why.contains("resource limit"), "{why}");
    }
}

#[test]
fn unused_invalid_literals_cannot_hide_in_zeta_reduction() {
    rejects(
        r#"(#math-inductive wrong () () (#pt-type 0) ((only ())))
      (#math-definition bad () #pt-nat
        (#pt-let (#parameter ignored (#pt-use wrong ())) (#pt-nat-literal wrong "1") #pt-zero))"#,
        "zero and successor",
    );
}

#[test]
fn induction_on_a_thousand_digit_power_of_ten_exposes_only_one_predecessor() {
    let value = format!("1{}", "0".repeat(4095));
    let previous = "9".repeat(4095);
    checks(&format!(
        r#"{EXAMPLE}
      (#theorem maximum-predecessor (#universes) (#parameters)
        (#statement (#pt-eq #pt-nat
          (#pt-app (#pt-use predecessor ()) (#pt-nat-literal #pt-nat "{value}"))
          (#pt-nat-literal #pt-nat "{previous}")))
        (#proof (#pt-refl #pt-nat (#pt-nat-literal #pt-nat "{previous}"))))"#
    ));
}
