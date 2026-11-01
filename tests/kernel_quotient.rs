//! Quotient operations check all inputs and never expose a representative.
mod support;
const EXAMPLE: &str = include_str!("../examples/proof_quotient.lim");
fn accepts(source: &str) {
    let program = lim::parse_program(source).unwrap_or_else(|why| panic!("{why}\n{source}"));
    lim::check_types(&program).unwrap_or_else(|why| panic!("{why}\n{source}"));
}
fn rejects(source: &str, expected: &str) {
    let program = lim::parse_program(source)
        .unwrap_or_else(|why| panic!("invalid negative syntax: {why}\n{source}"));
    let error = lim::check_types(&program).unwrap_err();
    assert!(!error.contains("resource limit"), "{error}");
    assert!(error.contains(expected), "{error}\n{source}");
}
fn change(before: &str, after: &str) -> String {
    assert!(EXAMPLE.contains(before));
    EXAMPLE.replacen(before, after, 1)
}
#[test]
fn lifts_and_generic_induction_check_without_axioms() {
    accepts(EXAMPLE);
}

#[test]
fn erased_respect_proofs_and_constructor_inputs_must_typecheck() {
    rejects(
        &change(
            "(#pt-use identity ()) (#pt-use respects ()) value",
            "(#pt-use identity ()) #pt-zero value",
        ),
        "type mismatch",
    );
    rejects(
        &change(
            "(#pt-quot-make 1 #pt-nat (#pt-use related ()) value)",
            "(#pt-quot-make 1 #pt-nat (#pt-use related ()) (#pt-type 0))",
        ),
        "type mismatch",
    );
    rejects(
        &change(
            "(#pt-quot 1 #pt-nat (#pt-use related ()))",
            "(#pt-quot 0 #pt-nat (#pt-use related ()))",
        ),
        "type mismatch",
    );
    rejects(&change("(#pt-use identity ()) (#pt-use respects ()) value",
        "(#pt-use identity ()) (#pt-let (#parameter unused #pt-nat) (#pt-type 0) (#pt-use respects ())) value"),"type mismatch");
}

#[test]
fn relation_function_and_target_universes_are_explicit() {
    rejects(
        &change(
            "(#pt-quot 1 #pt-nat (#pt-use related ()))",
            "(#pt-quot 1 #pt-nat #pt-zero)",
        ),
        "type mismatch",
    );
    rejects(
        &change("(#pt-quot-lift (1 1)", "(#pt-quot-lift (1 0)"),
        "type mismatch",
    );
    rejects(
        &change(
            "(#pt-use identity ()) (#pt-use respects ()) value",
            "#pt-zero (#pt-use respects ()) value",
        ),
        "type mismatch",
    );
}

#[test]
fn quotient_induction_cannot_extract_unrestricted_data() {
    rejects(
        r#"
      (#math-definition relation () (#pt-pi ((x #pt-nat) (y #pt-nat)) #pt-prop)
        (#pt-lambda ((x #pt-nat) (y #pt-nat)) (#pt-eq #pt-nat x y)))
      (#math-definition bad () #pt-nat
        (#pt-quot-induct 1 #pt-nat (#pt-use relation ())
          (#pt-lambda ((q (#pt-quot 1 #pt-nat (#pt-use relation ())))) #pt-nat)
          (#pt-lambda ((x #pt-nat)) x)
          (#pt-quot-make 1 #pt-nat (#pt-use relation ()) #pt-zero)))
    "#,
        "type mismatch",
    );
}

#[test]
fn related_values_do_not_become_definitionally_equal() {
    rejects(
        r#"
      (#math-definition universal () (#pt-pi ((x #pt-nat) (y #pt-nat)) #pt-prop)
        (#pt-lambda ((x #pt-nat) (y #pt-nat)) (#pt-eq #pt-nat #pt-zero #pt-zero)))
      (#theorem false-equality (#universes) (#parameters)
        (#statement (#pt-eq (#pt-quot 1 #pt-nat (#pt-use universal ()))
          (#pt-quot-make 1 #pt-nat (#pt-use universal ()) #pt-zero)
          (#pt-quot-make 1 #pt-nat (#pt-use universal ()) (#pt-succ #pt-zero))))
        (#proof (#pt-refl (#pt-quot 1 #pt-nat (#pt-use universal ()))
          (#pt-quot-make 1 #pt-nat (#pt-use universal ()) #pt-zero))))
    "#,
        "type mismatch",
    );
}

#[test]
fn polymorphic_lift_checks_for_every_sort_including_prop() {
    accepts(
        r#"
      (#theorem polymorphic-lift (#universes u)
        (#parameters (#parameter A (#pt-sort u)) (#parameter value A))
        (#statement (#pt-eq A
          (#pt-quot-lift (u u) A
            (#pt-lambda ((left A) (right A)) (#pt-eq A left right))
            A (#pt-lambda ((item A)) item)
            (#pt-lambda ((left A) (right A) (related (#pt-eq A left right))) related)
            (#pt-quot-make u A
              (#pt-lambda ((left A) (right A)) (#pt-eq A left right)) value)) value))
        (#proof (#pt-refl A value)))
    "#,
    );
}

#[test]
fn lifting_function_values_supports_overapplication() {
    accepts(
        r#"
      (#math-definition related () (#pt-pi ((x #pt-nat) (y #pt-nat)) #pt-prop)
        (#pt-lambda ((x #pt-nat) (y #pt-nat)) (#pt-eq #pt-nat x y)))
      (#math-definition function-type () (#pt-type 0) (#pt-pi ((x #pt-nat)) #pt-nat))
      (#theorem extra-argument (#universes) (#parameters)
        (#statement (#pt-eq #pt-nat
          (#pt-app
            (#pt-quot-lift (1 1) #pt-nat (#pt-use related ()) (#pt-use function-type ())
              (#pt-lambda ((x #pt-nat) (y #pt-nat)) y)
              (#pt-lambda ((x #pt-nat) (y #pt-nat) (h (#pt-eq #pt-nat x y)))
                (#pt-refl (#pt-use function-type ()) (#pt-lambda ((n #pt-nat)) n)))
              (#pt-quot-make 1 #pt-nat (#pt-use related ()) #pt-zero)) (#pt-succ #pt-zero))
          (#pt-succ #pt-zero)))
        (#proof (#pt-refl #pt-nat (#pt-succ #pt-zero))))
    "#,
    );
}

#[test]
fn imported_aliases_do_not_rewrite_universe_metadata() {
    let scratch = support::Scratch::new("kernel-quotient-roles");
    std::fs::write(
        scratch.path().join("types.lim"),
        "(#math-definition u () (#pt-type 0) #pt-nat)",
    )
    .unwrap();
    let source = r#"
      (#alias u = ./types.lim::u)
      (#math-definition polymorphic-quotient (u)
        (#pt-pi ((A (#pt-sort u)) (relation (#pt-pi ((x A) (y A)) #pt-prop))) (#pt-sort u))
        (#pt-lambda ((A (#pt-sort u)) (relation (#pt-pi ((x A) (y A)) #pt-prop)))
          (#pt-quot u A relation)))
      (#math-definition imported () (#pt-type 0) (#pt-use u ()))
    "#;
    let program = lim::parse_program_from_path(source, &scratch.path().join("main.lim")).unwrap();
    lim::check_types(&program).unwrap();
}

#[test]
fn different_relations_do_not_share_a_quotient_subject_type() {
    let source = EXAMPLE.replace(
        "(#pt-quot-make 1 #pt-nat (#pt-use related ()) value)",
        "(#pt-quot-make 1 #pt-nat (#pt-lambda ((left #pt-nat) (right #pt-nat)) #pt-false) value)",
    );
    rejects(&source, "type mismatch");
}

#[test]
fn an_invalid_lift_cannot_hide_behind_a_constructor_reduction() {
    rejects(
        r#"
      (#math-definition universal () (#pt-pi ((x #pt-nat) (y #pt-nat)) #pt-prop)
        (#pt-lambda ((x #pt-nat) (y #pt-nat)) (#pt-eq #pt-nat #pt-zero #pt-zero)))
      (#math-definition bad () #pt-nat
        (#pt-quot-lift (1 1) #pt-nat (#pt-use universal ()) #pt-nat
          (#pt-lambda ((x #pt-nat)) x)
          (#pt-lambda ((x #pt-nat) (y #pt-nat) (proof (#pt-eq #pt-nat #pt-zero #pt-zero)))
            (#pt-refl #pt-nat #pt-zero))
          (#pt-quot-make 1 #pt-nat (#pt-use universal ()) #pt-zero)))
    "#,
        "type mismatch",
    );
}

#[test]
fn generated_quotient_terms_are_checked_after_expansion() {
    for valid in [true, false] {
        let scratch = support::Scratch::new("generated-quotient");
        let body = if valid {
            EXAMPLE.to_owned()
        } else {
            change(
                "(#pt-use identity ()) (#pt-use respects ()) value",
                "(#pt-use identity ()) #pt-zero value",
            )
        };
        let source = format!("(#gn emit () `({body}))\n(#generate emit)");
        for _ in 0..2 {
            let program =
                lim::parse_program_from_path(&source, &scratch.path().join("main.lim")).unwrap();
            let result = lim::check_types(&program);
            if valid {
                result.unwrap();
            } else {
                assert!(result.unwrap_err().contains("type mismatch"));
            }
        }
    }
}
