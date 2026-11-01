//! Source-level conformance tests for indexed inductive families.

fn accepts(source: &str) {
    lim::parse(source)
        .unwrap_or_else(|error| panic!("fixture must be valid S-expressions: {error}\n{source}"));
    let program = lim::parse_program(source)
        .unwrap_or_else(|error| panic!("indexed fixture must parse: {error}\n{source}"));
    lim::check_types(&program)
        .unwrap_or_else(|error| panic!("indexed fixture must typecheck: {error}\n{source}"));
}

fn rejects(source: &str) {
    lim::parse(source).unwrap_or_else(|error| {
        panic!("negative fixture must be valid S-expressions: {error}\n{source}")
    });
    let program = lim::parse_program(source).unwrap_or_else(|error| {
        panic!("semantic negative must parse as a program: {error}\n{source}")
    });
    let error = match lim::check_types(&program) {
        Ok(()) => panic!("kernel accepted an invalid indexed fixture:\n{source}"),
        Err(error) => error,
    };
    assert!(
        !error.contains("resource limit"),
        "resource error masked rejection: {error}\n{source}"
    );
    let expected = if source.contains("wrong-fixed-motive") {
        Some("induction motive has the wrong generic subject type")
    } else if source.contains("wrong-ih-index") || source.contains("missing-ih-fold") {
        Some("kernel type mismatch")
    } else if source.contains("bad-self") {
        Some("indexed recursive fields require #pt-self-at")
    } else if source.contains("hidden-self") {
        Some("strict positivity")
    } else {
        None
    };
    if let Some(expected) = expected {
        assert!(
            error.contains(expected),
            "rejected for the wrong reason; expected {expected:?}, got {error:?}\n{source}"
        );
    }
}

const VECTOR: &str = r#"
  (#math-inductive vector (u) ((A (#pt-type u)))
    (#indices (#parameter length #pt-nat)) (#pt-type u)
    ((nil () (#pt-zero))
     (cons ((n #pt-nat) (head A) (tail (#pt-self-at (n))))
       ((#pt-succ n)))))
"#;

#[test]
fn vector_constructors_and_indexed_recursion_compute() {
    accepts(&format!(
        r#"{VECTOR}
        (#math-definition vector-nat () (#pt-app (#pt-use vector (0)) #pt-nat #pt-zero)
          (#pt-construct vector (0) (#pt-nat) nil ()))
        (#theorem vector-length-zero
          (#universes) (#parameters)
          (#statement (#pt-eq (#pt-app (#pt-use vector (0)) #pt-nat #pt-zero)
            (#pt-use vector-nat ()) (#pt-use vector-nat ())))
          (#proof (#pt-refl (#pt-app (#pt-use vector (0)) #pt-nat #pt-zero)
            (#pt-use vector-nat ()))))
        (#theorem indexed-fold-computes
          (#universes) (#parameters)
          (#statement (#pt-eq #pt-nat
            (#pt-induct vector (0) (#pt-nat) (#indices (#pt-succ #pt-zero))
              (#pt-lambda ((length #pt-nat) (xs (#pt-app (#pt-use vector (0)) #pt-nat length))) #pt-nat)
              (#pt-zero
               (#pt-lambda ((n #pt-nat) (head #pt-nat) (tail (#pt-app (#pt-use vector (0)) #pt-nat n))
                 (ih #pt-nat)) (#pt-succ ih)))
              (#pt-construct vector (0) (#pt-nat) cons
                (#pt-zero #pt-zero (#pt-construct vector (0) (#pt-nat) nil ()))))
            (#pt-succ #pt-zero)))
          (#proof (#pt-refl #pt-nat (#pt-succ #pt-zero))))"#
    ));
}

#[test]
fn dependent_index_telescope_and_universe_polymorphism_are_supported() {
    accepts(&format!(
        r#"{VECTOR}
      (#math-inductive dependent-index-family () ()
        (#indices (#parameter A (#pt-type 0)) (#parameter x A)) (#pt-type 1)
        ((at-value ((B (#pt-type 0)) (value B)) (B value))))
      (#theorem dependent-index-telescope
        (#universes) (#parameters (#parameter B (#pt-type 0)) (#parameter value B))
        (#statement (#pt-eq (#pt-app (#pt-use dependent-index-family ()) B value)
          (#pt-construct dependent-index-family () () at-value (B value))
          (#pt-construct dependent-index-family () () at-value (B value))))
        (#proof (#pt-refl (#pt-app (#pt-use dependent-index-family ()) B value)
          (#pt-construct dependent-index-family () () at-value (B value)))))
      (#theorem vector-is-polymorphic-in-its-element-universe
        (#universes u) (#parameters (#parameter A (#pt-type u)))
        (#statement (#pt-eq (#pt-app (#pt-use vector (u)) A #pt-zero)
          (#pt-construct vector (u) (A) nil ())
          (#pt-construct vector (u) (A) nil ())))
        (#proof (#pt-refl (#pt-app (#pt-use vector (u)) A #pt-zero)
          (#pt-construct vector (u) (A) nil ()))))
      (#math-inductive proposition-indexed-unit () ()
        (#indices (#parameter proposition #pt-prop)) #pt-prop
        ((witness () (#pt-false))))
      (#theorem indexed-proposition-large-elimination
        (#universes) (#parameters)
        (#statement (#pt-eq #pt-nat (#pt-induct proposition-indexed-unit () () (#indices #pt-false)
            (#pt-lambda ((P #pt-prop)
              (v (#pt-app (#pt-use proposition-indexed-unit ()) P))) #pt-nat)
            (#pt-zero) (#pt-construct proposition-indexed-unit () () witness ())) (#pt-induct proposition-indexed-unit () () (#indices #pt-false)
            (#pt-lambda ((P #pt-prop)
              (v (#pt-app (#pt-use proposition-indexed-unit ()) P))) #pt-nat)
            (#pt-zero) (#pt-construct proposition-indexed-unit () () witness ()))))
        (#proof (#pt-refl #pt-nat (#pt-induct proposition-indexed-unit () () (#indices #pt-false)
            (#pt-lambda ((P #pt-prop)
              (v (#pt-app (#pt-use proposition-indexed-unit ()) P))) #pt-nat)
            (#pt-zero) (#pt-construct proposition-indexed-unit () () witness ())))))
    "#,
    ));
}

#[test]
fn recursive_fields_carry_their_own_indexed_induction_hypothesis() {
    let recursor = r#"(#pt-induct vector (0) (#pt-nat)
      (#indices (#pt-succ #pt-zero))
      (#pt-lambda ((length #pt-nat)
        (v (#pt-app (#pt-use vector (0)) #pt-nat length))) #pt-nat)
      (#pt-zero
       (#pt-lambda ((n #pt-nat) (head #pt-nat)
         (tail (#pt-app (#pt-use vector (0)) #pt-nat n))
         (tail-result #pt-nat)) tail-result))
      xs)"#;
    accepts(&format!(
        r#"{VECTOR}
      (#math-definition fold-vector ()
        (#pt-pi ((i #pt-nat)
          (value (#pt-app (#pt-use vector (0)) #pt-nat i))) #pt-nat)
        (#pt-lambda ((i #pt-nat)
          (value (#pt-app (#pt-use vector (0)) #pt-nat i)))
          (#pt-induct vector (0) (#pt-nat) (#indices i)
            (#pt-lambda ((index #pt-nat)
              (item (#pt-app (#pt-use vector (0)) #pt-nat index))) #pt-nat)
            (#pt-zero
             (#pt-lambda ((n #pt-nat) (head #pt-nat)
               (tail (#pt-app (#pt-use vector (0)) #pt-nat n))
               (ih #pt-nat)) ih))
            value)))
      (#theorem recursive-hypothesis-is-used
        (#universes) (#parameters
          (#parameter xs (#pt-app (#pt-use vector (0)) #pt-nat (#pt-succ #pt-zero))))
        (#statement (#pt-eq #pt-nat {recursor} {recursor}))
        (#proof (#pt-refl #pt-nat {recursor})))"#
    ));
}

#[test]
fn indexed_constructor_and_eliminator_rejections_are_proof_errors() {
    let fixtures = [
        r#"(#math-inductive fixed-zero () () (#indices (#parameter i #pt-nat)) (#pt-type 0)
             ((zero () (#pt-zero))))
           (#theorem constructor-at-wrong-index (#universes) (#parameters)
             (#statement (#pt-eq (#pt-app (#pt-use fixed-zero ()) (#pt-succ #pt-zero))
               (#pt-construct fixed-zero () () zero ())
               (#pt-construct fixed-zero () () zero ())))
             (#proof (#pt-refl (#pt-app (#pt-use fixed-zero ()) (#pt-succ #pt-zero))
               (#pt-construct fixed-zero () () zero ()))))"#,
        r#"(#math-inductive one-index () () (#indices (#parameter i #pt-nat)) (#pt-type 0)
             ((make () (#pt-zero))))
           (#theorem missing-index (#universes) (#parameters)
             (#statement (#pt-eq (#pt-use one-index ())
               (#pt-construct one-index () () make ()) (#pt-construct one-index () () make ())))
             (#proof (#pt-refl (#pt-use one-index ())
               (#pt-construct one-index () () make ()))))"#,
        r#"(#math-inductive wrong-index-type () ()
             (#indices (#parameter i #pt-nat)) (#pt-type 0)
             ((bad () (#pt-false))))"#,
        r#"(#math-inductive only-zero () () (#indices (#parameter i #pt-nat)) (#pt-type 0)
             ((make () (#pt-zero))))
           (#theorem wrong-fixed-motive (#universes) (#parameters)
             (#statement (#pt-eq #pt-nat #pt-zero #pt-zero))
             (#proof (#pt-induct only-zero () () (#indices #pt-zero)
               (#pt-lambda ((i #pt-nat)
                 (x (#pt-app (#pt-use only-zero ()) #pt-zero)))
                 (#pt-eq #pt-nat #pt-zero #pt-zero))
               ((#pt-refl #pt-nat #pt-zero))
               (#pt-construct only-zero () () make ()))))"#,
        r#"(#math-inductive recursive-index () () (#indices (#parameter i #pt-nat)) (#pt-type 0)
             ((base () (#pt-zero))
              (step ((j #pt-nat) (child (#pt-self-at (j)))) ((#pt-succ j)))))
           (#theorem wrong-ih-index (#universes) (#parameters
             (#parameter value (#pt-app (#pt-use recursive-index ()) (#pt-succ #pt-zero))))
             (#statement (#pt-eq #pt-nat (#pt-succ #pt-zero) #pt-zero))
             (#proof (#pt-induct recursive-index () () (#indices (#pt-succ #pt-zero))
               (#pt-lambda ((i #pt-nat) (x (#pt-app (#pt-use recursive-index ()) i)))
                 (#pt-eq #pt-nat i #pt-zero))
               ((#pt-refl #pt-nat #pt-zero)
                (#pt-lambda ((j #pt-nat) (child (#pt-app (#pt-use recursive-index ()) j))
                  (bad-ih (#pt-eq #pt-nat (#pt-succ j) #pt-zero))) bad-ih))
               value)))"#,
        r#"(#math-inductive recursive-index () () (#indices (#parameter i #pt-nat)) (#pt-type 0)
             ((base () (#pt-zero))
              (step ((j #pt-nat) (child (#pt-self-at (j)))) ((#pt-succ j)))))
           (#math-definition missing-ih-fold ()
             (#pt-pi ((i #pt-nat)
               (value (#pt-app (#pt-use recursive-index ()) i))) #pt-nat)
             (#pt-lambda ((i #pt-nat)
               (value (#pt-app (#pt-use recursive-index ()) i)))
               (#pt-induct recursive-index () () (#indices i)
                 (#pt-lambda ((index #pt-nat)
                   (item (#pt-app (#pt-use recursive-index ()) index))) #pt-nat)
                 (#pt-zero
                  (#pt-lambda ((j #pt-nat)
                    (child (#pt-app (#pt-use recursive-index ()) j))) #pt-zero))
                 value)))"#,
        // The index telescope is required even when the selected index is apparent from the subject.
        r#"(#math-inductive nat-index () () (#indices (#parameter i #pt-nat)) (#pt-type 0)
             ((zero () (#pt-zero))))
           (#theorem omitted-recursor-indexes (#universes) (#parameters)
             (#statement (#pt-eq #pt-nat #pt-zero #pt-zero))
             (#proof (#pt-induct nat-index () ()
               (#pt-lambda ((i #pt-nat) (x (#pt-app (#pt-use nat-index ()) i))) #pt-nat)
               (#pt-zero) (#pt-construct nat-index () () zero ()))))"#,
        r#"(#math-inductive bad-self () () (#indices (#parameter i #pt-nat)) (#pt-type 0)
             ((bad ((child #pt-self)) (#pt-zero))))"#,
        r#"(#math-inductive hidden-self () () (#indices (#parameter i #pt-nat)) (#pt-type 0)
             ((bad ((n #pt-nat)
                   (child (#pt-pi ((argument (#pt-self-at (n)))) #pt-nat))) (n))))"#,
        r#"(#math-inductive undeclared-result () () (#indices (#parameter i #pt-nat)) (#pt-type 0)
             ((bad () (j))))"#,
    ];
    for fixture in fixtures {
        rejects(fixture);
    }
}

#[test]
fn malformed_index_grammar_is_rejected_after_sexpr_parsing() {
    for fixture in [
        "(#math-inductive missing-index-type () () (#indices (#parameter i)) (#pt-type 0) ())",
        "(#math-inductive malformed-index-entry () () (#indices (i #pt-nat)) (#pt-type 0) ())",
    ] {
        lim::parse(fixture).expect("grammar-negative fixture must have balanced S-expressions");
        let program = lim::parse_program(fixture).unwrap_or_else(|error| {
            panic!("S-expression program parse failed: {error}\n{fixture}")
        });
        let result = lim::check_types(&program);
        assert!(
            result.is_err(),
            "malformed indexed grammar was accepted: {fixture}"
        );
        assert!(!format!("{result:?}").contains("resource limit"));
    }
}

#[test]
fn indexed_zero_field_types_do_not_gain_unit_conversion_or_neutral_reduction() {
    rejects(
        r#"
      (#math-inductive indexed-unit () ()
        (#indices (#parameter i #pt-nat)) (#pt-type 0)
        ((only () (#pt-zero))))
      (#theorem distinct-indexed-values (#universes) (#parameters
        (#parameter left (#pt-app (#pt-use indexed-unit ()) #pt-zero))
        (#parameter right (#pt-app (#pt-use indexed-unit ()) #pt-zero)))
        (#statement (#pt-eq (#pt-app (#pt-use indexed-unit ()) #pt-zero) left right))
        (#proof (#pt-refl (#pt-app (#pt-use indexed-unit ()) #pt-zero) left)))
    "#,
    );
    rejects(
        r#"
      (#math-inductive indexed-unit () ()
        (#indices (#parameter i #pt-nat)) (#pt-type 0)
        ((only () (#pt-zero))))
      (#theorem neutral-indexed-recursion-does-not-reduce (#universes)
        (#parameters (#parameter value (#pt-app (#pt-use indexed-unit ()) #pt-zero)))
        (#statement (#pt-eq #pt-nat
          (#pt-induct indexed-unit () () (#indices #pt-zero)
            (#pt-lambda ((i #pt-nat) (x (#pt-app (#pt-use indexed-unit ()) i))) #pt-nat)
            (#pt-zero) value)
          #pt-zero))
        (#proof (#pt-refl #pt-nat #pt-zero)))
    "#,
    );
}
