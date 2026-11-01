//! Source-level tests for indexed singleton Prop large elimination.

fn accepts(source: &str) {
    lim::parse(source)
        .unwrap_or_else(|error| panic!("fixture must be valid S-expressions: {error}\n{source}"));
    let program = lim::parse_program(source)
        .unwrap_or_else(|error| panic!("fixture must parse as a program: {error}\n{source}"));
    lim::check_types(&program)
        .unwrap_or_else(|error| panic!("fixture must typecheck: {error}\n{source}"));
}

fn rejects_large_elimination(source: &str) {
    lim::parse(source).unwrap_or_else(|error| {
        panic!("semantic negative has invalid S-expressions: {error}\n{source}")
    });
    let program = lim::parse_program(source).unwrap_or_else(|error| {
        panic!("semantic negative must parse as a program: {error}\n{source}")
    });
    let error =
        lim::check_types(&program).expect_err("kernel accepted a forbidden large elimination");
    let message = error.to_string();
    assert!(
        !message.contains("resource limit"),
        "resource failure masked rejection: {message}\n{source}"
    );
    assert!(
        message.contains("large elimination"),
        "expected the large-elimination rule to reject this fixture, got {message:?}\n{source}"
    );
}

#[test]
fn indexed_nat_field_is_recoverable_from_its_direct_index() {
    accepts(
        r#"
      (#math-inductive nat-indexed-proof () ()
        (#indices (#parameter index #pt-nat)) #pt-prop
        ((make ((value #pt-nat)) (value))))
      (#math-definition recover-index ()
        (#pt-pi ((index #pt-nat)
          (proof (#pt-app (#pt-use nat-indexed-proof ()) index))) #pt-nat)
        (#pt-lambda ((index #pt-nat)
          (proof (#pt-app (#pt-use nat-indexed-proof ()) index)))
          (#pt-induct nat-indexed-proof () () (#indices index)
            (#pt-lambda ((generic-index #pt-nat)
              (subject (#pt-app (#pt-use nat-indexed-proof ()) generic-index))) #pt-nat)
            ((#pt-lambda ((value #pt-nat)) value))
            proof)))
      (#theorem recover-index-computes (#universes) (#parameters)
        (#statement (#pt-eq #pt-nat
          (#pt-app (#pt-use recover-index ()) #pt-zero
            (#pt-construct nat-indexed-proof () () make (#pt-zero)))
          #pt-zero))
        (#proof (#pt-refl #pt-nat #pt-zero)))
    "#,
    );
}

#[test]
fn computational_accessibility_recursion_has_a_dependent_unfolding_proof() {
    accepts(include_str!("../examples/proof_accessibility.lim"));
}

#[test]
fn accessibility_data_recursion_cannot_use_proof_children_as_data_results() {
    fn wrong_argument(node: &lim::SpannedExpr) -> Option<lim::Span> {
        if matches!(&node.expr, lim::Expr::List(parts)
            if parts.len() == 4
                && matches!(&parts[0], lim::Expr::Symbol(name) if name == "#pt-app")
                && matches!(&parts[1], lim::Expr::Symbol(name) if name == "step")
                && matches!(&parts[3], lim::Expr::Symbol(name) if name == "ih"))
        {
            return Some(node.children[3].span);
        }
        node.children.iter().find_map(wrong_argument)
    }
    let source = include_str!("../examples/proof_accessibility.lim");
    let span = lim::parse(source)
        .unwrap()
        .iter()
        .find_map(wrong_argument)
        .unwrap();
    let mutant = format!("{}lower{}", &source[..span.start], &source[span.end..]);
    let program = lim::parse_program(&mutant).unwrap();
    let error = lim::check_types(&program)
        .expect_err("proof-valued children are not data-valued recursive results");
    assert!(error.contains("type mismatch"), "{error}");
    assert!(!error.contains("resource limit"), "{error}");
}

#[test]
fn dependent_type_and_value_indices_recover_both_constructor_fields() {
    accepts(
        r#"
      (#math-inductive dependent-indexed-proof (u) ()
        (#indices (#parameter A (#pt-type u)) (#parameter value A)) #pt-prop
        ((make ((type (#pt-type u)) (item type)) (type item))))
      (#math-definition recover-indexed-type (u)
        (#pt-pi ((A (#pt-type u)) (value A)
          (proof (#pt-app (#pt-use dependent-indexed-proof (u)) A value)))
          (#pt-type u))
        (#pt-lambda ((A (#pt-type u)) (value A)
          (proof (#pt-app (#pt-use dependent-indexed-proof (u)) A value)))
          (#pt-induct dependent-indexed-proof (u) () (#indices A value)
            (#pt-lambda ((generic-type (#pt-type u)) (generic-value generic-type)
              (subject (#pt-app (#pt-use dependent-indexed-proof (u)) generic-type generic-value)))
              (#pt-type u))
            ((#pt-lambda ((type (#pt-type u)) (item type)) type))
            proof)))
      (#math-definition recover-indexed-value (u)
        (#pt-pi ((A (#pt-type u)) (value A)
          (proof (#pt-app (#pt-use dependent-indexed-proof (u)) A value))) A)
        (#pt-lambda ((A (#pt-type u)) (value A)
          (proof (#pt-app (#pt-use dependent-indexed-proof (u)) A value)))
          (#pt-induct dependent-indexed-proof (u) () (#indices A value)
            (#pt-lambda ((generic-type (#pt-type u)) (generic-value generic-type)
              (subject (#pt-app (#pt-use dependent-indexed-proof (u)) generic-type generic-value)))
              generic-type)
            ((#pt-lambda ((type (#pt-type u)) (item type)) item))
            proof)))
      (#theorem recover-dependent-indices-computes (#universes u)
        (#parameters (#parameter A (#pt-type u)) (#parameter value A))
        (#statement (#pt-eq A
          (#pt-app (#pt-use recover-indexed-value (u)) A value
            (#pt-construct dependent-indexed-proof (u) () make (A value)))
          value))
        (#proof (#pt-refl A value)))
      (#theorem recover-dependent-type-computes (#universes u)
        (#parameters (#parameter A (#pt-type u)) (#parameter value A))
        (#statement (#pt-eq (#pt-type u)
          (#pt-app (#pt-use recover-indexed-type (u)) A value
            (#pt-construct dependent-indexed-proof (u) () make (A value)))
          A))
        (#proof (#pt-refl (#pt-type u) A)))
    "#,
    );
}

#[test]
fn indexed_prop_type_field_is_recoverable_when_it_is_an_index() {
    accepts(
        r#"
      (#math-inductive proposition-indexed-proof () ()
        (#indices (#parameter proposition #pt-prop)) #pt-prop
        ((make ((value #pt-prop)) (value))))
      (#math-definition recover-proposition ()
        (#pt-pi ((proposition #pt-prop)
          (proof (#pt-app (#pt-use proposition-indexed-proof ()) proposition))) #pt-prop)
        (#pt-lambda ((proposition #pt-prop)
          (proof (#pt-app (#pt-use proposition-indexed-proof ()) proposition)))
          (#pt-induct proposition-indexed-proof () () (#indices proposition)
            (#pt-lambda ((generic-proposition #pt-prop)
              (subject (#pt-app (#pt-use proposition-indexed-proof ()) generic-proposition))) #pt-prop)
            ((#pt-lambda ((value #pt-prop)) value))
            proof)))
      (#theorem recover-proposition-computes (#universes) (#parameters
        (#parameter proposition #pt-prop))
        (#statement (#pt-eq #pt-prop
          (#pt-app (#pt-use recover-proposition ()) proposition
            (#pt-construct proposition-indexed-proof () () make (proposition)))
          proposition))
        (#proof (#pt-refl #pt-prop proposition)))
    "#,
    );
}

#[test]
fn unindexed_data_fields_cannot_escape_a_prop_constructor() {
    rejects_large_elimination(
        r#"
      (#math-inductive hidden-secret () () #pt-prop
        ((make ((secret #pt-nat)))))
      (#math-definition reveal-secret ()
        (#pt-pi ((proof (#pt-use hidden-secret ()))) #pt-nat)
        (#pt-lambda ((proof (#pt-use hidden-secret ())))
          (#pt-induct hidden-secret () ()
            (#pt-lambda ((subject (#pt-use hidden-secret ()))) #pt-nat)
            ((#pt-lambda ((secret #pt-nat)) secret)) proof)))
    "#,
    );
}

#[test]
fn indexed_constant_tag_does_not_expose_an_unindexed_nat_field() {
    rejects_large_elimination(
        r#"
      (#math-inductive tagged-secret () ()
        (#indices (#parameter tag #pt-nat)) #pt-prop
        ((make ((secret #pt-nat)) (#pt-zero))))
      (#math-definition reveal-tagged-secret ()
        (#pt-pi ((proof (#pt-app (#pt-use tagged-secret ()) #pt-zero))) #pt-nat)
        (#pt-lambda ((proof (#pt-app (#pt-use tagged-secret ()) #pt-zero)))
          (#pt-induct tagged-secret () () (#indices #pt-zero)
            (#pt-lambda ((tag #pt-nat)
              (subject (#pt-app (#pt-use tagged-secret ()) tag))) #pt-nat)
            ((#pt-lambda ((secret #pt-nat)) secret)) proof)))
    "#,
    );
}

#[test]
fn every_data_field_must_be_directly_exposed_by_the_result_indices() {
    rejects_large_elimination(
        r#"
      (#math-inductive partly-indexed-secret () ()
        (#indices (#parameter tag #pt-nat)) #pt-prop
        ((make ((exposed #pt-nat) (hidden #pt-nat)) (exposed))))
      (#math-definition reveal-hidden-field ()
        (#pt-pi ((tag #pt-nat)
          (proof (#pt-app (#pt-use partly-indexed-secret ()) tag))) #pt-nat)
        (#pt-lambda ((tag #pt-nat)
          (proof (#pt-app (#pt-use partly-indexed-secret ()) tag)))
          (#pt-induct partly-indexed-secret () () (#indices tag)
            (#pt-lambda ((index #pt-nat)
              (subject (#pt-app (#pt-use partly-indexed-secret ()) index))) #pt-nat)
            ((#pt-lambda ((exposed #pt-nat) (hidden #pt-nat)) hidden)) proof)))
    "#,
    );
}

#[test]
fn multiple_constructors_forbid_large_elimination_even_when_indexed() {
    rejects_large_elimination(
        r#"
      (#math-inductive multiple-indexed-fields () ()
        (#indices (#parameter index #pt-nat)) #pt-prop
        ((first ((value #pt-nat)) (value))
         (second ((value #pt-nat)) (value))))
      (#math-definition reveal-multiple-indexed ()
        (#pt-pi ((index #pt-nat)
          (proof (#pt-app (#pt-use multiple-indexed-fields ()) index))) #pt-nat)
        (#pt-lambda ((index #pt-nat)
          (proof (#pt-app (#pt-use multiple-indexed-fields ()) index)))
          (#pt-induct multiple-indexed-fields () () (#indices index)
            (#pt-lambda ((generic-index #pt-nat)
              (subject (#pt-app (#pt-use multiple-indexed-fields ()) generic-index))) #pt-nat)
            ((#pt-lambda ((value #pt-nat)) value)
             (#pt-lambda ((value #pt-nat)) value)) proof)))
    "#,
    );
}

#[test]
fn successor_index_does_not_count_as_direct_field_exposure() {
    rejects_large_elimination(
        r#"
      (#math-inductive successor-indexed-secret () ()
        (#indices (#parameter index #pt-nat)) #pt-prop
        ((make ((secret #pt-nat)) ((#pt-succ secret)))))
      (#math-definition reveal-successor-indexed-secret ()
        (#pt-pi ((index #pt-nat)
          (proof (#pt-app (#pt-use successor-indexed-secret ()) index))) #pt-nat)
        (#pt-lambda ((index #pt-nat)
          (proof (#pt-app (#pt-use successor-indexed-secret ()) index)))
          (#pt-induct successor-indexed-secret () () (#indices index)
            (#pt-lambda ((generic-index #pt-nat)
              (subject (#pt-app (#pt-use successor-indexed-secret ()) generic-index))) #pt-nat)
            ((#pt-lambda ((secret #pt-nat)) secret)) proof)))
    "#,
    );
}

#[test]
fn nonindexed_prop_type_field_is_data_not_a_proof_field() {
    rejects_large_elimination(
        r#"
      (#math-inductive hidden-proposition-field () ()
        (#indices (#parameter tag #pt-nat)) #pt-prop
        ((make ((proposition #pt-prop)) (#pt-zero))))
      (#math-definition reveal-hidden-proposition ()
        (#pt-pi ((proof (#pt-app (#pt-use hidden-proposition-field ()) #pt-zero))) #pt-prop)
        (#pt-lambda ((proof (#pt-app (#pt-use hidden-proposition-field ()) #pt-zero)))
          (#pt-induct hidden-proposition-field () () (#indices #pt-zero)
            (#pt-lambda ((tag #pt-nat)
              (subject (#pt-app (#pt-use hidden-proposition-field ()) tag))) #pt-prop)
            ((#pt-lambda ((proposition #pt-prop)) proposition)) proof)))
    "#,
    );
}
