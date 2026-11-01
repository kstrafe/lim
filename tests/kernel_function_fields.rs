//! Source-level conformance tests for strictly positive recursive function fields.

fn accepts(source: &str) {
    lim::parse(source)
        .unwrap_or_else(|error| panic!("invalid S-expression fixture: {error}\n{source}"));
    let program = lim::parse_program(source)
        .unwrap_or_else(|error| panic!("fixture must parse as a program: {error}\n{source}"));
    lim::check_types(&program)
        .unwrap_or_else(|error| panic!("fixture must typecheck: {error}\n{source}"));
}

fn rejects(source: &str, expected: Option<&str>) {
    lim::parse(source).unwrap_or_else(|error| {
        panic!("semantic negative has invalid S-expressions: {error}\n{source}")
    });
    let program = lim::parse_program(source).unwrap_or_else(|error| {
        panic!("semantic negative must parse as a program: {error}\n{source}")
    });
    let error = lim::check_types(&program)
        .expect_err("kernel accepted an invalid recursive function field");
    let message = error.to_string();
    assert!(
        !message.contains("resource limit"),
        "resource failure masked rejection: {message}\n{source}"
    );
    if let Some(expected) = expected {
        assert!(
            message.contains(expected),
            "expected diagnostic {expected:?}, got {message:?}\n{source}"
        );
    }
}

fn rejects_grammar(source: &str) {
    lim::parse(source)
        .unwrap_or_else(|error| panic!("grammar fixture must be balanced: {error}\n{source}"));
    if let Ok(program) = lim::parse_program(source) {
        let error = lim::check_types(&program)
            .expect_err("malformed recursive field declaration was accepted");
        assert!(
            !error.to_string().contains("resource limit"),
            "resource failure masked grammar rejection: {error}\n{source}"
        );
    }
}

#[test]
fn function_fields_insert_pointwise_hypotheses_and_compute() {
    accepts(include_str!("../examples/proof_function_fields.lim"));
    accepts(
        r#"
      (#math-inductive wrapped-codomain () () (#pt-type 0)
        ((leaf ())
         (node ((children (#pt-pi ((key #pt-nat))
           (#pt-let (#parameter result-type #pt-nat) #pt-zero #pt-self)))))))
    "#,
    );
}

#[test]
fn dependent_telescope_and_universe_polymorphic_parameters_are_supported() {
    accepts(
        r#"
      (#math-inductive poly-fan (u) ((A (#pt-type u))) (#pt-type u)
        ((empty ())
         (branch ((children (#pt-pi ((key A)
           (same-key (#pt-eq A key key))) #pt-self))))))
    "#,
    );
}

#[test]
fn indexed_function_fields_keep_argument_dependent_child_indices() {
    accepts(include_str!("../examples/proof_accessibility.lim"));
}

#[test]
fn invalid_function_recursive_fields_are_rejected_semantically() {
    let fixtures = [
        (
            "self-in-function-domain",
            r#"(#math-inductive bad () () (#pt-type 0)
          ((node ((f (#pt-pi ((x #pt-self)) #pt-nat))))))"#,
            Some("strict positivity"),
        ),
        (
            "double-negative",
            r#"(#math-inductive bad () () (#pt-type 0)
          ((node ((f (#pt-pi ((x (#pt-pi ((y #pt-nat)) #pt-self))) #pt-nat))))))"#,
            Some("strict positivity"),
        ),
        (
            "changed-parameter",
            r#"(#math-inductive bad (u) ((A (#pt-type u))) (#pt-type u)
          ((node ((f (#pt-pi ((x #pt-nat)) (#pt-app (#pt-use bad (u)) #pt-nat)))))))"#,
            Some("cyclic kernel declaration dependencies"),
        ),
        (
            "negative-occurrence",
            r#"(#math-inductive bad () () (#pt-type 0)
          ((node ((f (#pt-pi ((x (#pt-pi ((y #pt-self)) #pt-nat))) #pt-nat))))))"#,
            Some("strict positivity"),
        ),
        (
            "nested-sigma",
            r#"(#math-inductive bad () () (#pt-type 0)
          ((node ((pair (#pt-sigma ((x #pt-nat)) #pt-self))))))"#,
            Some("strict positivity"),
        ),
        (
            "bad-self-index",
            r#"(#math-inductive bad () () (#indices (#parameter i #pt-nat)) (#pt-type 0)
          ((node ((f (#pt-pi ((x #pt-nat)) (#pt-self-at ())))) (#pt-zero))))"#,
            Some("#pt-self-at"),
        ),
        (
            "hidden-self",
            r#"(#math-inductive bad () () (#pt-type 0)
          ((node ((f (#pt-pi ((x #pt-nat))
            (#pt-let (#parameter hidden #pt-self) #pt-zero #pt-nat)))))))"#,
            Some("strict positivity"),
        ),
    ];
    for (tag, fixture, expected) in fixtures {
        let fixture = fixture.replace("invalid-recursive-function-field", tag);
        rejects(&fixture, expected);
    }
}

#[test]
fn malformed_recursive_function_field_forms_are_rejected() {
    for fixture in [
        "(#math-inductive malformed () () (#indices (#parameter i)) (#pt-type 0) ((node () (#pt-zero))))",
        "(#math-inductive malformed () () (#pt-indices (#parameter i #pt-nat)) (#pt-type 0) ((node () (#pt-zero))))",
        "(#math-inductive malformed () () (#indices ()) (#pt-type 0) ((node () (#pt-zero))))",
    ] {
        rejects_grammar(fixture);
    }
}
