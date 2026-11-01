//! Source-level conformance tests for typed proof-term let bindings.

fn accepts(source: &str) {
    let program = lim::parse_program(source)
        .unwrap_or_else(|error| panic!("let fixture must parse: {error}\n{source}"));
    lim::check_types(&program)
        .unwrap_or_else(|error| panic!("let fixture must typecheck: {error}\n{source}"));
}

fn rejects(source: &str) {
    let program = lim::parse_program(source)
        .unwrap_or_else(|error| panic!("semantic negative must parse: {error}\n{source}"));
    let error = lim::check_types(&program).expect_err("kernel accepted an invalid let term");
    assert!(
        !error.contains("resource limit"),
        "resource error masked rejection: {error}\n{source}"
    );
}

fn rejects_kernel_syntax(source: &str) {
    lim::parse(source).unwrap_or_else(|error| {
        panic!("malformed-let fixture must be balanced S-expressions: {error}\n{source}")
    });
    let program = lim::parse_program(source).unwrap_or_else(|error| {
        panic!("malformed-kernel fixture must parse as a program: {error}\n{source}")
    });
    let error = lim::check_types(&program).expect_err("kernel accepted malformed let syntax");
    assert!(
        !error.contains("resource limit"),
        "resource error masked rejection: {error}\n{source}"
    );
}

#[test]
fn let_value_is_available_in_the_body() {
    accepts(
        r#"
      (#math-definition locally-bound-zero () #pt-nat
        (#pt-let (#parameter value #pt-nat) #pt-zero value))
      (#theorem use-local-definition
        (#universes) (#parameters)
        (#statement (#pt-eq #pt-nat #pt-zero #pt-zero))
        (#proof (#pt-refl #pt-nat (#pt-use locally-bound-zero ()))))
    "#,
    );
}

#[test]
fn let_body_type_can_depend_on_the_bound_value() {
    accepts(
        r#"
      (#theorem dependent-let-proof
        (#universes) (#parameters)
        (#statement (#pt-eq #pt-nat #pt-zero #pt-zero))
        (#proof (#pt-let (#parameter value #pt-nat) #pt-zero
          (#pt-refl #pt-nat value))))
    "#,
    );
}

#[test]
fn type_alias_let_substitutes_into_the_body_proof_type() {
    accepts(
        r#"
      (#theorem type-alias-let
        (#universes) (#parameters)
        (#statement (#pt-eq #pt-nat #pt-zero #pt-zero))
        (#proof (#pt-let (#parameter Alias (#pt-type 0)) #pt-nat
          (#pt-refl Alias #pt-zero))))
    "#,
    );
}

#[test]
fn aliases_under_polymorphic_lambdas_preserve_dependent_result_types() {
    accepts(
        r#"
      (#math-definition local-pair (u)
        (#pt-pi ((A (#pt-sort u)) (value A))
          (#pt-sigma ((copy A)) (#pt-eq A copy value)))
        (#pt-lambda ((A (#pt-sort u)) (value A))
          (#pt-let (#parameter Alias (#pt-sort u)) A
            (#pt-let (#parameter saved Alias) value
              (#pt-pair (#pt-sigma ((copy Alias)) (#pt-eq Alias copy value))
                saved (#pt-refl Alias saved))))))
      (#theorem local-pair-instance
        (#universes) (#parameters)
        (#statement (#pt-eq #pt-nat
          (#pt-first (#pt-app (#pt-use local-pair (1)) #pt-nat #pt-zero))
          #pt-zero))
        (#proof (#pt-refl #pt-nat #pt-zero)))
    "#,
    );
}

#[test]
fn unused_let_annotations_and_values_still_check_universe_scope() {
    for binding in [
        "(#pt-let (#parameter ignored (#pt-sort unknown)) #pt-nat (#pt-refl #pt-nat #pt-zero))",
        "(#pt-let (#parameter ignored (#pt-type 1)) (#pt-sort unknown) (#pt-refl #pt-nat #pt-zero))",
    ] {
        rejects(&format!(
            "(#theorem unused-universe (#universes) (#parameters)\n (#statement (#pt-eq #pt-nat #pt-zero #pt-zero))\n (#proof {binding}))"
        ));
    }
}

#[test]
fn a_type_valued_let_can_build_a_dependent_function_type() {
    accepts(
        r#"
      (#math-definition local-identity-type () (#pt-type 0)
        (#pt-let (#parameter A (#pt-type 0)) #pt-nat
          (#pt-pi ((value A)) A)))
      (#math-definition local-identity ()
        (#pt-let (#parameter A (#pt-type 0)) #pt-nat
          (#pt-pi ((value A)) A))
        (#pt-lambda ((value #pt-nat)) value))
      (#theorem local-identity-computes
        (#universes) (#parameters)
        (#statement (#pt-eq #pt-nat
          (#pt-app (#pt-use local-identity ()) #pt-zero) #pt-zero))
        (#proof (#pt-refl #pt-nat #pt-zero)))
    "#,
    );
}

#[test]
fn nested_nonshadowing_lets_scope_values_sequentially() {
    accepts(
        r#"
      (#theorem nested-lets
        (#universes) (#parameters)
        (#statement (#pt-eq #pt-nat #pt-zero #pt-zero))
        (#proof (#pt-let (#parameter first #pt-nat) #pt-zero
          (#pt-let (#parameter second #pt-nat) first
            (#pt-refl #pt-nat second)))))
    "#,
    );
}

#[test]
fn polymorphic_let_values_work_at_symbolic_sort_levels() {
    accepts(
        r#"
      (#math-definition identity-through-let (u)
        (#pt-pi ((A (#pt-sort u)) (value A)) A)
        (#pt-lambda ((A (#pt-sort u)) (value A))
          (#pt-let (#parameter saved A) value saved)))
      (#theorem polymorphic-let-instance
        (#universes) (#parameters)
        (#statement (#pt-eq #pt-nat
          (#pt-app (#pt-use identity-through-let (1)) #pt-nat #pt-zero)
          #pt-zero))
        (#proof (#pt-refl #pt-nat #pt-zero)))
    "#,
    );
}

#[test]
fn a_fresh_local_name_can_be_used_without_becoming_a_global() {
    accepts(
        r#"
      (#theorem fresh-local
        (#universes) (#parameters)
        (#statement (#pt-eq #pt-nat #pt-zero #pt-zero))
        (#proof (#pt-let (#parameter freshly-bound #pt-nat) #pt-zero
          (#pt-refl #pt-nat freshly-bound))))
    "#,
    );
}

#[test]
fn an_ill_typed_let_value_is_checked_even_when_unused() {
    rejects(
        r#"
      (#theorem unused-bad-value
        (#universes) (#parameters)
        (#statement (#pt-eq #pt-nat #pt-zero #pt-zero))
        (#proof (#pt-let (#parameter ignored #pt-nat)
          (#pt-refl #pt-nat #pt-zero) (#pt-refl #pt-nat #pt-zero))))
    "#,
    );
}

#[test]
fn an_explicit_let_type_must_match_the_value() {
    rejects(
        r#"
      (#theorem wrong-let-type
        (#universes) (#parameters)
        (#statement (#pt-eq #pt-nat #pt-zero #pt-zero))
        (#proof (#pt-let (#parameter evidence #pt-prop) #pt-zero
          (#pt-refl #pt-nat #pt-zero))))
    "#,
    );
}

#[test]
fn a_let_value_cannot_refer_to_its_own_binder() {
    rejects(
        r#"
      (#theorem self-referential-value
        (#universes) (#parameters)
        (#statement (#pt-eq #pt-nat #pt-zero #pt-zero))
        (#proof (#pt-let (#parameter value #pt-nat) value #pt-zero)))
    "#,
    );
}

#[test]
fn a_let_name_is_not_in_scope_after_the_let_expression() {
    rejects(
        r#"
      (#theorem local-out-of-scope
        (#universes) (#parameters)
        (#statement (#pt-eq #pt-nat #pt-zero #pt-zero))
        (#proof (#pt-let (#parameter local #pt-nat) #pt-zero local-after-let)))
    "#,
    );
}

#[test]
fn the_let_name_is_scoped_only_in_its_body() {
    rejects(
        r#"
      (#theorem bad-let-body
        (#universes) (#parameters)
        (#statement (#pt-eq #pt-nat #pt-zero #pt-zero))
        (#proof (#pt-let (#parameter value #pt-nat) #pt-zero
          (#pt-succ #pt-false))))
    "#,
    );
}

#[test]
fn nested_let_binders_cannot_duplicate_or_shadow_local_names() {
    rejects(
        r#"
      (#theorem duplicate-local
        (#universes) (#parameters)
        (#statement (#pt-eq #pt-nat #pt-zero #pt-zero))
        (#proof (#pt-let (#parameter item #pt-nat) #pt-zero
          (#pt-let (#parameter item #pt-nat) #pt-zero
            (#pt-refl #pt-nat item)))))
    "#,
    );
}

#[test]
fn a_let_binder_cannot_shadow_a_theorem_parameter() {
    rejects(
        r#"
      (#theorem parameter-shadowing
        (#universes) (#parameters (#parameter item #pt-nat))
        (#statement (#pt-eq #pt-nat item item))
        (#proof (#pt-let (#parameter item #pt-nat) #pt-zero
          (#pt-refl #pt-nat item))))
    "#,
    );
}

#[test]
fn a_let_binder_cannot_shadow_a_universe_name() {
    rejects(
        r#"
      (#theorem universe-shadowing
        (#universes u) (#parameters)
        (#statement (#pt-eq #pt-nat #pt-zero #pt-zero))
        (#proof (#pt-let (#parameter u #pt-nat) #pt-zero
          (#pt-refl #pt-nat u))))
    "#,
    );
}

#[test]
fn let_arguments_cannot_reference_unknown_globals() {
    rejects(
        r#"
      (#theorem unknown-global-in-let
        (#universes) (#parameters)
        (#statement (#pt-eq #pt-nat #pt-zero #pt-zero))
        (#proof (#pt-let (#parameter value #pt-nat) (#pt-use missing-global ())
          (#pt-refl #pt-nat value))))
    "#,
    );
}

#[test]
fn global_cycles_cannot_be_hidden_in_let_values() {
    rejects(
        r#"
      (#math-definition cycle-left () #pt-nat
        (#pt-let (#parameter value #pt-nat) (#pt-use cycle-right ()) value))
      (#math-definition cycle-right () #pt-nat
        (#pt-let (#parameter value #pt-nat) (#pt-use cycle-left ()) value))
    "#,
    );
}

#[test]
fn malformed_let_binder_and_expression_arities_are_syntax_errors() {
    for source in [
        "(#theorem bad-binder-arity (#universes) (#parameters) (#statement (#pt-eq #pt-nat #pt-zero #pt-zero)) (#proof (#pt-let (#parameter local) #pt-zero #pt-zero)))",
        "(#theorem extra-binder-arity (#universes) (#parameters) (#statement (#pt-eq #pt-nat #pt-zero #pt-zero)) (#proof (#pt-let (#parameter local #pt-nat extra) #pt-zero #pt-zero)))",
        "(#theorem missing-body (#universes) (#parameters) (#statement (#pt-eq #pt-nat #pt-zero #pt-zero)) (#proof (#pt-let (#parameter local #pt-nat) #pt-zero)))",
    ] {
        rejects_kernel_syntax(source);
    }
}

#[test]
fn qualified_let_binders_are_not_local_identifiers() {
    rejects_kernel_syntax(
        r#"
      (#theorem qualified-binder
        (#universes) (#parameters)
        (#statement (#pt-eq #pt-nat #pt-zero #pt-zero))
        (#proof (#pt-let (#parameter module::local #pt-nat) #pt-zero
          (#pt-refl #pt-nat module::local))))
    "#,
    );
}
