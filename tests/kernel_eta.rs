//! Source-level tests for typed function eta and primitive Sigma pair eta.
//! These deliberately do not claim eta for user inductives or data units.

fn accepts(source: &str) {
    let program = lim::parse_program(source)
        .unwrap_or_else(|error| panic!("eta fixture must parse: {error}\n{source}"));
    lim::check_types(&program)
        .unwrap_or_else(|error| panic!("eta fixture must typecheck: {error}\n{source}"));
}

fn rejects(source: &str) {
    let program = lim::parse_program(source)
        .unwrap_or_else(|error| panic!("negative eta fixture must parse: {error}\n{source}"));
    let error = lim::check_types(&program).expect_err("kernel accepted an invalid eta conversion");
    assert!(
        error.starts_with("theorem '"),
        "not a theorem diagnostic: {error}\n{source}"
    );
    assert!(
        !error.contains("resource limit"),
        "resource error masked rejection: {error}\n{source}"
    );
}

#[test]
fn function_eta_holds_from_function_to_expansion() {
    accepts(
        r#"
      (#theorem function-eta
        (#universes) (#parameters (#parameter f (#pt-pi ((x #pt-nat)) #pt-nat)))
        (#statement (#pt-eq (#pt-pi ((x #pt-nat)) #pt-nat)
          f (#pt-lambda ((x #pt-nat)) (#pt-app f x))))
        (#proof (#pt-refl (#pt-pi ((x #pt-nat)) #pt-nat) f)))
    "#,
    );
}

#[test]
fn function_eta_holds_from_expansion_to_function() {
    accepts(
        r#"
      (#theorem function-eta-reversed
        (#universes) (#parameters (#parameter f (#pt-pi ((x #pt-nat)) #pt-nat)))
        (#statement (#pt-eq (#pt-pi ((x #pt-nat)) #pt-nat)
          (#pt-lambda ((x #pt-nat)) (#pt-app f x)) f))
        (#proof (#pt-refl (#pt-pi ((x #pt-nat)) #pt-nat)
          (#pt-lambda ((x #pt-nat)) (#pt-app f x)))))
    "#,
    );
}

#[test]
fn dependent_function_eta_preserves_the_result_index() {
    accepts(
        r#"
      (#theorem dependent-eta
        (#universes) (#parameters
          (#parameter F (#pt-pi ((index #pt-nat)) (#pt-type 0)))
          (#parameter f (#pt-pi ((index #pt-nat)) (#pt-app F index))))
        (#statement (#pt-eq
          (#pt-pi ((index #pt-nat)) (#pt-app F index))
          f (#pt-lambda ((index #pt-nat)) (#pt-app f index))))
        (#proof (#pt-refl (#pt-pi ((index #pt-nat)) (#pt-app F index)) f)))
    "#,
    );
}

#[test]
fn function_eta_is_polymorphic_in_the_value_universe() {
    accepts(
        r#"
      (#theorem universe-polymorphic-eta
        (#universes u)
        (#parameters
          (#parameter A (#pt-sort u))
          (#parameter f (#pt-pi ((value A)) A)))
        (#statement (#pt-eq (#pt-pi ((value A)) A)
          f (#pt-lambda ((value A)) (#pt-app f value))))
        (#proof (#pt-refl (#pt-pi ((value A)) A) f)))
    "#,
    );
}

#[test]
fn nested_lambdas_eta_expand_a_curried_function() {
    accepts(
        r#"
      (#theorem nested-function-eta
        (#universes) (#parameters
          (#parameter f (#pt-pi ((x #pt-nat)) (#pt-pi ((y #pt-nat)) #pt-nat))))
        (#statement (#pt-eq
          (#pt-pi ((x #pt-nat)) (#pt-pi ((y #pt-nat)) #pt-nat))
          f (#pt-lambda ((x #pt-nat))
            (#pt-lambda ((y #pt-nat)) (#pt-app f x y)))))
        (#proof (#pt-refl
          (#pt-pi ((x #pt-nat)) (#pt-pi ((y #pt-nat)) #pt-nat)) f)))
    "#,
    );
}

#[test]
fn distinct_function_parameters_do_not_become_equal_by_eta() {
    rejects(
        r#"
      (#theorem distinct-functions
        (#universes) (#parameters (#parameter f (#pt-pi ((x #pt-nat)) #pt-nat))
          (#parameter g (#pt-pi ((x #pt-nat)) #pt-nat)))
        (#statement (#pt-eq (#pt-pi ((x #pt-nat)) #pt-nat) f g))
        (#proof (#pt-refl (#pt-pi ((x #pt-nat)) #pt-nat) f)))
    "#,
    );
}

#[test]
fn eta_expansion_must_preserve_the_function_argument() {
    rejects(
        r#"
      (#theorem changed-argument
        (#universes) (#parameters (#parameter f (#pt-pi ((x #pt-nat)) #pt-nat)))
        (#statement (#pt-eq (#pt-pi ((x #pt-nat)) #pt-nat)
          f (#pt-lambda ((x #pt-nat)) (#pt-app f (#pt-succ x)))))
        (#proof (#pt-refl (#pt-pi ((x #pt-nat)) #pt-nat) f)))
    "#,
    );
}

#[test]
fn function_eta_rejects_a_lambda_with_the_wrong_domain_annotation() {
    rejects(
        r#"
      (#theorem wrong-domain
        (#universes) (#parameters (#parameter f (#pt-pi ((x #pt-nat)) #pt-nat)))
        (#statement (#pt-eq (#pt-pi ((x #pt-nat)) #pt-nat)
          f (#pt-lambda ((x #pt-prop)) #pt-zero)))
        (#proof (#pt-refl (#pt-pi ((x #pt-nat)) #pt-nat) f)))
    "#,
    );
}

#[test]
fn function_eta_rejects_a_lambda_with_the_wrong_range() {
    rejects(
        r#"
      (#theorem wrong-range
        (#universes) (#parameters (#parameter f (#pt-pi ((x #pt-nat)) #pt-nat)))
        (#statement (#pt-eq (#pt-pi ((x #pt-nat)) #pt-nat)
          f (#pt-lambda ((x #pt-nat)) #pt-nat)))
        (#proof (#pt-refl (#pt-pi ((x #pt-nat)) #pt-nat) f)))
    "#,
    );
}

#[test]
fn beta_reduction_cannot_hide_an_ill_typed_function_eta_argument() {
    rejects(
        r#"
      (#theorem bad-ignored-function-argument
        (#universes) (#parameters (#parameter f (#pt-pi ((x #pt-nat)) #pt-nat)))
        (#statement (#pt-eq (#pt-pi ((x #pt-nat)) #pt-nat)
          f (#pt-lambda ((x #pt-nat))
            (#pt-app (#pt-lambda ((ignored #pt-nat)) (#pt-app f x))
              (#pt-refl #pt-nat #pt-zero)))))
        (#proof (#pt-refl (#pt-pi ((x #pt-nat)) #pt-nat) f)))
    "#,
    );
}

#[test]
fn nondependent_sigma_pair_eta_holds_in_both_orientations() {
    accepts(
        r#"
      (#theorem sigma-eta
        (#universes) (#parameters
          (#parameter pair (#pt-sigma ((first #pt-nat)) #pt-nat)))
        (#statement (#pt-eq (#pt-sigma ((first #pt-nat)) #pt-nat)
          pair (#pt-pair (#pt-sigma ((first #pt-nat)) #pt-nat)
            (#pt-first pair) (#pt-second pair))))
        (#proof (#pt-refl (#pt-sigma ((first #pt-nat)) #pt-nat) pair)))
      (#theorem sigma-eta-reversed
        (#universes) (#parameters
          (#parameter pair (#pt-sigma ((first #pt-nat)) #pt-nat)))
        (#statement (#pt-eq (#pt-sigma ((first #pt-nat)) #pt-nat)
          (#pt-pair (#pt-sigma ((first #pt-nat)) #pt-nat)
            (#pt-first pair) (#pt-second pair)) pair))
        (#proof (#pt-refl (#pt-sigma ((first #pt-nat)) #pt-nat)
          (#pt-pair (#pt-sigma ((first #pt-nat)) #pt-nat)
            (#pt-first pair) (#pt-second pair)))))
    "#,
    );
}

#[test]
fn dependent_sigma_pair_eta_preserves_the_first_projection_index() {
    accepts(
        r#"
      (#theorem dependent-sigma-eta
        (#universes) (#parameters
          (#parameter pair (#pt-sigma ((index #pt-nat))
            (#pt-eq #pt-nat index index))))
        (#statement (#pt-eq
          (#pt-sigma ((index #pt-nat)) (#pt-eq #pt-nat index index))
          pair (#pt-pair
            (#pt-sigma ((index #pt-nat)) (#pt-eq #pt-nat index index))
            (#pt-first pair) (#pt-second pair))))
        (#proof (#pt-refl
          (#pt-sigma ((index #pt-nat)) (#pt-eq #pt-nat index index)) pair)))
    "#,
    );
}

#[test]
fn beta_reduction_cannot_hide_an_ill_typed_ignored_sigma_eta_argument() {
    rejects(
        r#"
      (#theorem bad-ignored-sigma-argument
        (#universes) (#parameters
          (#parameter pair (#pt-sigma ((first #pt-nat)) #pt-nat)))
        (#statement (#pt-eq (#pt-sigma ((first #pt-nat)) #pt-nat)
          pair (#pt-app
            (#pt-lambda ((ignored #pt-nat))
              (#pt-pair (#pt-sigma ((first #pt-nat)) #pt-nat)
                (#pt-first pair) (#pt-second pair)))
            (#pt-refl #pt-nat #pt-zero))))
        (#proof (#pt-refl (#pt-sigma ((first #pt-nat)) #pt-nat) pair)))
    "#,
    );
}

#[test]
fn distinct_sigma_pairs_do_not_become_equal_by_eta() {
    rejects(
        r#"
      (#theorem swapped-pair
        (#universes) (#parameters
          (#parameter pair (#pt-sigma ((first #pt-nat)) #pt-nat)))
        (#statement (#pt-eq (#pt-sigma ((first #pt-nat)) #pt-nat)
          pair (#pt-pair (#pt-sigma ((first #pt-nat)) #pt-nat)
            (#pt-second pair) (#pt-first pair))))
        (#proof (#pt-refl (#pt-sigma ((first #pt-nat)) #pt-nat) pair)))
    "#,
    );
}

#[test]
fn sigma_pair_eta_rejects_mismatched_data_components() {
    rejects(
        r#"
      (#theorem wrong-pair-data
        (#universes) (#parameters)
        (#statement (#pt-eq (#pt-sigma ((first #pt-nat)) #pt-nat)
          (#pt-pair (#pt-sigma ((first #pt-nat)) #pt-nat) #pt-zero #pt-zero)
          (#pt-pair (#pt-sigma ((first #pt-nat)) #pt-nat) #pt-zero (#pt-succ #pt-zero))))
        (#proof (#pt-refl (#pt-sigma ((first #pt-nat)) #pt-nat)
          (#pt-pair (#pt-sigma ((first #pt-nat)) #pt-nat) #pt-zero #pt-zero))))
    "#,
    );
}

#[test]
fn sigma_eta_rejects_an_ill_typed_dependent_second_projection() {
    rejects(
        r#"
      (#theorem bad-dependent-pair-eta
        (#universes) (#parameters
          (#parameter pair (#pt-sigma ((index #pt-nat))
            (#pt-eq #pt-nat index index))))
        (#statement (#pt-eq
          (#pt-sigma ((index #pt-nat)) (#pt-eq #pt-nat index index))
          pair (#pt-pair
            (#pt-sigma ((index #pt-nat)) (#pt-eq #pt-nat index index))
            (#pt-first pair) (#pt-refl #pt-nat #pt-zero))))
        (#proof (#pt-refl
          (#pt-sigma ((index #pt-nat)) (#pt-eq #pt-nat index index)) pair)))
    "#,
    );
}

#[test]
fn ill_typed_sigma_annotations_and_projections_are_rejected() {
    for value in [
        "(#pt-first #pt-zero)",
        "(#pt-second #pt-zero)",
        "(#pt-pair #pt-nat #pt-zero #pt-zero)",
    ] {
        rejects(&format!(
            "(#theorem malformed-sigma\n (#universes) (#parameters)\n (#statement (#pt-eq #pt-nat #pt-zero #pt-zero))\n (#proof (#pt-refl #pt-nat {value})))"
        ));
    }
}

#[test]
fn neutral_proof_pairs_and_functions_into_them_preserve_eta_transitivity() {
    accepts(
        r#"
      (#theorem neutral-proof-pairs
        (#universes)
        (#parameters
          (#parameter P #pt-prop)
          (#parameter left (#pt-sigma ((first P)) P))
          (#parameter right (#pt-sigma ((first P)) P)))
        (#statement (#pt-eq (#pt-sigma ((first P)) P) left right))
        (#proof (#pt-refl (#pt-sigma ((first P)) P) left)))
      (#theorem neutral-pair-functions
        (#universes)
        (#parameters
          (#parameter P #pt-prop)
          (#parameter left (#pt-pi ((input #pt-nat)) (#pt-sigma ((first P)) P)))
          (#parameter right (#pt-pi ((input #pt-nat)) (#pt-sigma ((first P)) P))))
        (#statement (#pt-eq (#pt-pi ((input #pt-nat)) (#pt-sigma ((first P)) P)) left right))
        (#proof (#pt-refl (#pt-pi ((input #pt-nat)) (#pt-sigma ((first P)) P)) left)))
    "#,
    );
}

#[test]
fn neutral_data_pairs_and_pointwise_equality_assumptions_do_not_collapse_data() {
    rejects(
        r#"
      (#theorem no-function-extensionality-rule
        (#universes)
        (#parameters
          (#parameter left (#pt-pi ((input #pt-nat)) #pt-nat))
          (#parameter right (#pt-pi ((input #pt-nat)) #pt-nat))
          (#parameter agreement (#pt-pi ((input #pt-nat))
            (#pt-eq #pt-nat (#pt-app left input) (#pt-app right input)))))
        (#statement (#pt-eq (#pt-pi ((input #pt-nat)) #pt-nat) left right))
        (#proof (#pt-refl (#pt-pi ((input #pt-nat)) #pt-nat) left)))
    "#,
    );
    rejects(
        r#"
      (#theorem neutral-data-pairs
        (#universes)
        (#parameters
          (#parameter left (#pt-sigma ((first #pt-nat)) #pt-nat))
          (#parameter right (#pt-sigma ((first #pt-nat)) #pt-nat)))
        (#statement (#pt-eq (#pt-sigma ((first #pt-nat)) #pt-nat) left right))
        (#proof (#pt-refl (#pt-sigma ((first #pt-nat)) #pt-nat) left)))
    "#,
    );
}
