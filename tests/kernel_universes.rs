//! Source-level tests of Sort polymorphism and conditional universe constraints.
//! These fixtures do not inspect or reuse the kernel's level representation.

fn accepts(source: &str) {
    let program = lim::parse_program(source)
        .unwrap_or_else(|error| panic!("universe fixture must parse: {error}\n{source}"));
    lim::check_types(&program)
        .unwrap_or_else(|error| panic!("universe fixture must typecheck: {error}\n{source}"));
}

fn rejects(source: &str, diagnostic: &str) {
    // A malformed runtime program must not stand in for a kernel rejection.
    let program = lim::parse_program(source)
        .unwrap_or_else(|error| panic!("kernel fixture must parse: {error}\n{source}"));
    let error = lim::check_types(&program).expect_err("invalid universe claim was accepted");
    assert!(
        error.starts_with("theorem '"),
        "not a theorem diagnostic: {error}"
    );
    assert!(
        error.contains(diagnostic),
        "expected {diagnostic:?}: {error}\n{source}"
    );
    assert!(
        !error.contains("resource limit"),
        "a budget error masked the expected rejection: {error}"
    );
}

const IDENTITY: &str = r#"
    (#math-definition identity (u)
      (#pt-pi ((a (#pt-sort u)) (value a)) a)
      (#pt-lambda ((a (#pt-sort u)) (value a)) value))
"#;

const ARROW: &str = r#"
    (#math-definition arrow (u v)
      (#pt-pi ((a (#pt-sort u)) (b (#pt-sort v)))
        (#pt-sort (#pt-level-imax u v)))
      (#pt-lambda ((a (#pt-sort u)) (b (#pt-sort v)))
        (#pt-pi ((argument a)) b)))
"#;

const CHOICE: &str = r#"
    (#math-inductive choice (u) () (#pt-sort u)
      ((left ()) (right ())))
"#;

const CHOOSE: &str = r#"
    (#math-definition choose (u)
      (#pt-pi ((a (#pt-sort u)) (left a) (right a)
               (tag (#pt-use choice (u)))) a)
      (#pt-lambda ((a (#pt-sort u)) (left a) (right a)
                   (tag (#pt-use choice (u))))
        (#pt-induct choice (u) ()
          (#pt-lambda ((ignored (#pt-use choice (u)))) a)
          (left right) tag)))
"#;

fn level_equality(left: &str, right: &str) -> String {
    // Sort l has type Sort(succ l). Refl therefore tests conversion of levels,
    // rather than assuming cumulativity or adding a theorem about level syntax.
    format!(
        r#"
      (#theorem levels-agree
        (#universes u v w)
        (#parameters)
        (#statement (#pt-eq (#pt-sort (#pt-level-succ {left}))
          (#pt-sort {left}) (#pt-sort {right})))
        (#proof (#pt-refl (#pt-sort (#pt-level-succ {left})) (#pt-sort {left}))))
    "#
    )
}

fn selector(source_sort: &str, target_sort: &str) -> String {
    // Multiple constructors prevent singleton elimination. No inhabitance
    // assumption hides the Prop case: the subject is an explicit parameter.
    format!(
        r#"
      (#math-inductive choice (u v w) () (#pt-sort {source_sort})
        ((left ()) (right ())))
      (#math-definition select (u v w)
        (#pt-pi ((a (#pt-sort {target_sort})) (left a) (right a)
                 (tag (#pt-use choice (u v w)))) a)
        (#pt-lambda ((a (#pt-sort {target_sort})) (left a) (right a)
                     (tag (#pt-use choice (u v w))))
          (#pt-induct choice (u v w) ()
            (#pt-lambda ((ignored (#pt-use choice (u v w)))) a)
            (left right) tag)))
    "#
    )
}

#[test]
fn sort_zero_is_definitionally_prop() {
    accepts(
        r#"
      (#theorem sort-zero
        (#universes) (#parameters)
        (#statement (#pt-eq (#pt-sort 1) (#pt-sort 0) #pt-prop))
        (#proof (#pt-refl (#pt-sort 1) #pt-prop)))
    "#,
    );
}

#[test]
fn successor_sort_is_definitionally_type() {
    accepts(
        r#"
      (#theorem successor-sort
        (#universes u) (#parameters)
        (#statement (#pt-eq (#pt-sort (#pt-level-succ (#pt-level-succ u)))
          (#pt-sort (#pt-level-succ u)) (#pt-type u)))
        (#proof (#pt-refl (#pt-sort (#pt-level-succ (#pt-level-succ u))) (#pt-type u))))
    "#,
    );
}

#[test]
fn one_sort_polymorphic_identity_computes_for_both_proofs_and_naturals() {
    accepts(&format!(
        r#"{IDENTITY}
      (#theorem identity-on-proofs
        (#universes) (#parameters)
        (#statement (#pt-eq (#pt-eq #pt-nat #pt-zero #pt-zero)
          (#pt-app (#pt-use identity (0))
            (#pt-eq #pt-nat #pt-zero #pt-zero) (#pt-refl #pt-nat #pt-zero))
          (#pt-refl #pt-nat #pt-zero)))
        (#proof (#pt-refl (#pt-eq #pt-nat #pt-zero #pt-zero) (#pt-refl #pt-nat #pt-zero))))
      (#theorem identity-on-naturals
        (#universes) (#parameters)
        (#statement (#pt-eq #pt-nat
          (#pt-app (#pt-use identity (1)) #pt-nat (#pt-succ #pt-zero))
          (#pt-succ #pt-zero)))
        (#proof (#pt-refl #pt-nat (#pt-succ #pt-zero))))
    "#
    ));
}

#[test]
fn sort_polymorphic_identity_also_accepts_a_type_as_its_value() {
    accepts(&format!(
        r#"{IDENTITY}
      (#theorem identity-on-types
        (#universes) (#parameters)
        (#statement (#pt-eq (#pt-sort 1)
          (#pt-app (#pt-use identity (2)) (#pt-sort 1) #pt-nat) #pt-nat))
        (#proof (#pt-refl (#pt-sort 1) #pt-nat)))
    "#
    ));
}

#[test]
fn generic_arrow_uses_imax_without_rejecting_an_unknown_prop_codomain() {
    accepts(ARROW);
    accepts(&format!(
        r#"{ARROW}
      (#math-definition arrows-to-prop (u)
        (#pt-pi ((a (#pt-sort u)) (p #pt-prop)) #pt-prop)
        (#pt-use arrow (u 0)))
    "#
    ));
}

#[test]
fn successor_and_maximum_identities_are_conversion_rules() {
    for (left, right) in [
        ("(#pt-level-max u 0)", "u"),
        ("(#pt-level-max u u)", "u"),
        ("(#pt-level-max u v)", "(#pt-level-max v u)"),
        ("(#pt-level-max u (#pt-level-succ u))", "(#pt-level-succ u)"),
        (
            "(#pt-level-succ (#pt-level-max u v))",
            "(#pt-level-max (#pt-level-succ u) (#pt-level-succ v))",
        ),
    ] {
        accepts(&level_equality(left, right));
    }
}

#[test]
fn imax_zero_successor_and_shared_variable_identities_are_conversion_rules() {
    for (left, right) in [
        ("(#pt-level-imax u 0)", "0"),
        ("(#pt-level-imax 0 u)", "u"),
        ("(#pt-level-imax 1 u)", "u"),
        ("(#pt-level-imax u u)", "u"),
        (
            "(#pt-level-imax u (#pt-level-succ v))",
            "(#pt-level-max u (#pt-level-succ v))",
        ),
        (
            "(#pt-level-max u (#pt-level-imax u v))",
            "(#pt-level-max u v)",
        ),
        (
            "(#pt-level-imax (#pt-level-max u v) u)",
            "(#pt-level-imax v u)",
        ),
    ] {
        accepts(&level_equality(left, right));
    }
}

#[test]
fn nested_imax_and_maximum_normalize_with_the_correct_zero_conditions() {
    for (left, right) in [
        (
            "(#pt-level-imax (#pt-level-max u v) w)",
            "(#pt-level-max (#pt-level-imax u w) (#pt-level-imax v w))",
        ),
        (
            "(#pt-level-imax u (#pt-level-max v w))",
            "(#pt-level-max (#pt-level-imax u v) (#pt-level-imax u w))",
        ),
        (
            "(#pt-level-imax u (#pt-level-imax v w))",
            "(#pt-level-imax (#pt-level-max u v) w)",
        ),
        (
            "(#pt-level-max (#pt-level-imax u v) (#pt-level-imax v u))",
            "(#pt-level-max u v)",
        ),
    ] {
        accepts(&level_equality(left, right));
    }
}

#[test]
fn imax_is_not_maximum_commutative_or_associative() {
    for (left, right) in [
        ("0", "1"),
        ("u", "(#pt-level-succ u)"),
        ("(#pt-level-max u v)", "u"),
        ("(#pt-level-imax u v)", "(#pt-level-max u v)"),
        ("(#pt-level-imax u v)", "(#pt-level-imax v u)"),
        ("(#pt-level-imax u v)", "v"),
        (
            "(#pt-level-imax (#pt-level-imax u v) w)",
            "(#pt-level-imax u (#pt-level-imax v w))",
        ),
    ] {
        rejects(&level_equality(left, right), "type mismatch");
    }
}

#[test]
fn simultaneous_universe_substitution_does_not_capture_or_reapply_names() {
    accepts(&format!(
        r#"{IDENTITY} {ARROW}
      (#math-definition lifted (u)
        (#pt-pi ((a (#pt-sort (#pt-level-succ u))) (value a)) a)
        (#pt-use identity ((#pt-level-succ u))))
      (#math-definition conditional (u v)
        (#pt-pi ((a (#pt-sort (#pt-level-imax u v))) (value a)) a)
        (#pt-use identity ((#pt-level-imax u v))))
      (#math-definition swapped (u v)
        (#pt-pi ((a (#pt-sort v)) (b (#pt-sort u))) (#pt-sort (#pt-level-imax v u)))
        (#pt-use arrow (v u)))
    "#
    ));
}

#[test]
fn specializing_a_conditional_level_at_zero_or_one_preserves_computation() {
    accepts(&format!(
        r#"{IDENTITY}
      (#math-definition conditional (u v)
        (#pt-pi ((a (#pt-sort (#pt-level-imax u v))) (value a)) a)
        (#pt-use identity ((#pt-level-imax u v))))
      (#theorem at-prop
        (#universes) (#parameters)
        (#statement (#pt-eq (#pt-eq #pt-nat #pt-zero #pt-zero)
          (#pt-app (#pt-use conditional (3 0))
            (#pt-eq #pt-nat #pt-zero #pt-zero) (#pt-refl #pt-nat #pt-zero))
          (#pt-refl #pt-nat #pt-zero)))
        (#proof (#pt-refl (#pt-eq #pt-nat #pt-zero #pt-zero) (#pt-refl #pt-nat #pt-zero))))
      (#theorem at-nat
        (#universes) (#parameters)
        (#statement (#pt-eq #pt-nat
          (#pt-app (#pt-use conditional (0 1)) #pt-nat #pt-zero) #pt-zero))
        (#proof (#pt-refl #pt-nat #pt-zero)))
    "#
    ));
}

#[test]
fn sort_universes_do_not_introduce_cumulativity_or_type_in_type() {
    for source in [
        "(#math-definition type-in-type () (#pt-sort 1) (#pt-sort 1))",
        "(#math-definition prop-in-prop () (#pt-sort 0) #pt-prop)",
        "(#math-definition upward-cast () (#pt-sort 2) #pt-nat)",
        "(#math-definition downward-cast () (#pt-sort 0) #pt-nat)",
    ] {
        rejects(source, "type mismatch");
    }
}

#[test]
fn a_theorem_statement_at_unknown_sort_is_not_assumed_to_be_prop() {
    rejects(
        r#"
      (#theorem not-always-prop
        (#universes u)
        (#parameters (#parameter a (#pt-sort u)) (#parameter value a))
        (#statement a) (#proof value))
    "#,
        "proposition",
    );
}

#[test]
fn multiple_constructor_sort_family_cannot_eliminate_into_nat_generically() {
    rejects(&selector("u", "1"), "elimination");
}

#[test]
fn multiple_constructor_sort_family_can_eliminate_into_its_own_sort() {
    accepts(&format!("{CHOICE} {CHOOSE}"));
}

#[test]
fn fixed_data_universe_allows_nat_elimination_and_iota_reduction() {
    accepts(&format!(
        r#"{CHOICE}
      (#math-definition chosen () #pt-nat
        (#pt-induct choice (1) ()
          (#pt-lambda ((tag (#pt-use choice (1)))) #pt-nat)
          (#pt-zero (#pt-succ #pt-zero))
          (#pt-construct choice (1) () right ())))
      (#theorem selected-right
        (#universes) (#parameters)
        (#statement (#pt-eq #pt-nat (#pt-use chosen ()) (#pt-succ #pt-zero)))
        (#proof (#pt-refl #pt-nat (#pt-succ #pt-zero))))
    "#
    ));
}

#[test]
fn fixed_prop_universe_forbids_nat_elimination_even_for_a_known_constructor() {
    rejects(
        &format!(
            r#"{CHOICE}
      (#math-definition forbidden () #pt-nat
        (#pt-induct choice (0) ()
          (#pt-lambda ((tag (#pt-use choice (0)))) #pt-nat)
          (#pt-zero (#pt-succ #pt-zero))
          (#pt-construct choice (0) () left ())))
    "#
        ),
        "elimination",
    );
}

#[test]
fn choosing_inside_sort_zero_is_proof_elimination_not_large_elimination() {
    accepts(&format!(
        r#"{CHOICE} {CHOOSE}
      (#theorem choice-of-proof
        (#universes) (#parameters)
        (#statement (#pt-eq (#pt-eq #pt-nat #pt-zero #pt-zero)
          (#pt-app (#pt-use choose (0))
            (#pt-eq #pt-nat #pt-zero #pt-zero)
            (#pt-refl #pt-nat #pt-zero) (#pt-refl #pt-nat #pt-zero)
            (#pt-construct choice (0) () right ()))
          (#pt-refl #pt-nat #pt-zero)))
        (#proof (#pt-refl (#pt-eq #pt-nat #pt-zero #pt-zero) (#pt-refl #pt-nat #pt-zero))))
    "#
    ));
}

#[test]
fn source_maximum_zero_implies_each_component_is_zero() {
    for target in ["u", "v", "(#pt-level-imax u v)"] {
        accepts(&selector("(#pt-level-max u v)", target));
    }
}

#[test]
fn independent_target_universes_do_not_follow_from_source_zero() {
    for target in ["v", "(#pt-level-max u v)", "(#pt-level-succ u)"] {
        rejects(&selector("u", target), "elimination");
    }
}

#[test]
fn source_imax_zero_implies_its_right_operand_is_zero() {
    accepts(&selector("(#pt-level-imax u v)", "v"));
    accepts(&selector(
        "(#pt-level-imax u (#pt-level-max v w))",
        "(#pt-level-max v w)",
    ));
}

#[test]
fn source_imax_zero_does_not_imply_its_left_operand_is_zero() {
    rejects(&selector("(#pt-level-imax u v)", "u"), "elimination");
}

#[test]
fn provably_positive_source_sorts_allow_unrelated_target_sorts() {
    for source in ["(#pt-level-succ u)", "(#pt-level-max u 1)"] {
        accepts(&selector(source, "v"));
    }
}

#[test]
fn singleton_fields_that_are_proofs_whenever_the_family_is_prop_allow_large_elimination() {
    accepts(
        r#"
      (#math-inductive box (u) ((a (#pt-sort u))) (#pt-sort u)
        ((pack ((value a)))))
      (#math-definition marker (u)
        (#pt-pi ((a (#pt-sort u)) (subject (#pt-app (#pt-use box (u)) a))) #pt-nat)
        (#pt-lambda ((a (#pt-sort u)) (subject (#pt-app (#pt-use box (u)) a)))
          (#pt-induct box (u) (a)
            (#pt-lambda ((ignored (#pt-app (#pt-use box (u)) a))) #pt-nat)
            ((#pt-lambda ((value a)) #pt-zero)) subject)))
    "#,
    );
}

const WITNESS: &str = r#"
    (#math-inductive witness (u) () (#pt-sort u)
      ((make ((number #pt-nat)))))
"#;

fn extract_witness(level: &str) -> String {
    format!(
        r#"{WITNESS}
      (#math-definition extract (u)
        (#pt-pi ((subject (#pt-use witness ({level})))) #pt-nat)
        (#pt-lambda ((subject (#pt-use witness ({level}))))
          (#pt-induct witness ({level}) ()
            (#pt-lambda ((ignored (#pt-use witness ({level})))) #pt-nat)
            ((#pt-lambda ((number #pt-nat)) number)) subject)))
    "#
    )
}

#[test]
fn impredicative_prop_fields_are_allowed_but_do_not_make_them_proof_fields() {
    // imax(1,u) <= u holds even at u=0, so Nat is a legal field in this family.
    accepts(WITNESS);
    rejects(&extract_witness("u"), "elimination");
    rejects(&extract_witness("0"), "elimination");
}

#[test]
fn a_singleton_with_data_fields_can_extract_them_at_fixed_positive_level() {
    accepts(&format!(
        r#"{}
      (#theorem extract-zero
        (#universes) (#parameters)
        (#statement (#pt-eq #pt-nat
          (#pt-app (#pt-use extract (0)) (#pt-construct witness (1) () make (#pt-zero)))
          #pt-zero))
        (#proof (#pt-refl #pt-nat #pt-zero)))
    "#,
        extract_witness("1")
    ));
}

#[test]
fn conditional_family_field_universes_are_checked_impredicatively() {
    accepts(
        r#"
      (#math-inductive guarded-box (u v) ((a (#pt-sort v)))
        (#pt-sort (#pt-level-imax u v)) ((pack ((value a)))))
    "#,
    );
    for source in [
        "(#math-inductive too-high (u) ((a (#pt-sort (#pt-level-succ u)))) (#pt-sort u) ((pack ((value a)))))",
        "(#math-inductive unrelated (u v) ((a (#pt-sort v))) (#pt-sort u) ((pack ((value a)))))",
        "(#math-inductive too-high () ((a (#pt-sort 2))) (#pt-sort 1) ((pack ((value a)))))",
    ] {
        rejects(source,"universe");
    }
}

#[test]
fn sort_and_imax_arity_and_universe_scope_are_not_inferred_or_admitted() {
    for value in [
        "(#pt-sort)",
        "(#pt-sort 0 1)",
        "(#pt-sort (#pt-level-imax))",
        "(#pt-sort (#pt-level-imax u))",
        "(#pt-sort (#pt-level-imax u v w))",
    ] {
        let source = format!("(#math-definition malformed (u v w) (#pt-sort 2) {value})");
        rejects(&source, "operand");
    }
    for source in [
        "(#math-definition free-level () (#pt-sort 2) (#pt-sort missing))",
        "(#math-definition free-argument (u) (#pt-sort 2) (#pt-sort (#pt-level-imax u missing)))",
        "(#math-definition duplicate-level (u u) (#pt-sort 1) (#pt-sort 0))",
    ] {
        rejects(source, "universe");
    }
}
