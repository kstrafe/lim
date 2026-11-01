//! Source level conformance tests for checked mathematical record projections
//! and record eta.

fn accepts(source: &str) {
    let program = lim::parse_program(source)
        .unwrap_or_else(|error| panic!("record fixture must parse: {error}\n{source}"));
    lim::check_types(&program)
        .unwrap_or_else(|error| panic!("record fixture must typecheck: {error}\n{source}"));
}

fn rejects(source: &str) {
    let program = lim::parse_program(source)
        .unwrap_or_else(|error| panic!("negative record fixture must parse: {error}\n{source}"));
    let error = lim::check_types(&program).expect_err("kernel accepted invalid record evidence");
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
fn projections_recover_parameters_and_dependent_field_types() {
    accepts(
        r#"
      (#math-inductive dependent-record () ((A (#pt-type 0))) (#pt-type 0)
        ((pack ((index A) (witness (#pt-eq A index index))))))
      (#theorem projection-types
        (#universes) (#parameters (#parameter A (#pt-type 0))
          (#parameter value (#pt-app (#pt-use dependent-record ()) A)))
        (#statement (#pt-eq A
          (#pt-project dependent-record 0 value)
          (#pt-project dependent-record 0 value)))
        (#proof (#pt-refl A (#pt-project dependent-record 0 value))))
      (#theorem constructor-reduces
        (#universes) (#parameters (#parameter A (#pt-type 0)) (#parameter x A))
        (#statement (#pt-eq A
          (#pt-project dependent-record 0
            (#pt-construct dependent-record () (A) pack
              (x (#pt-refl A x)))) x))
        (#proof (#pt-refl A x)))
    "#,
    );
}

#[test]
fn record_eta_reconstructs_neutral_values_and_preserves_data() {
    accepts(
        r#"
      (#math-inductive record-pair () () (#pt-type 0)
        ((pack ((first #pt-nat) (second #pt-nat)))))
      (#theorem pair-eta
        (#universes) (#parameters (#parameter value (#pt-use record-pair ())))
        (#statement (#pt-eq (#pt-use record-pair ()) value
          (#pt-construct record-pair () () pack
            ((#pt-project record-pair 0 value) (#pt-project record-pair 1 value)))))
        (#proof (#pt-refl (#pt-use record-pair ()) value)))
    "#,
    );
}

#[test]
fn eta_does_not_collapse_distinct_data_fields() {
    rejects(
        r#"
      (#math-inductive record-one-nat () () (#pt-type 0) ((pack ((value #pt-nat)))))
      (#theorem unequal-data-does-not-collapse
        (#universes) (#parameters (#parameter left #pt-nat) (#parameter right #pt-nat))
        (#statement (#pt-eq (#pt-use record-one-nat ())
          (#pt-construct record-one-nat () () pack (left))
          (#pt-construct record-one-nat () () pack (right))))
        (#proof (#pt-refl (#pt-use record-one-nat ())
          (#pt-construct record-one-nat () () pack (left)))))
    "#,
    );
}

#[test]
fn neutral_record_recursion_computes_through_projection_reconstruction() {
    accepts(
        r#"
      (#math-inductive record-one-nat () () (#pt-type 0)
        ((pack ((value #pt-nat)))))
      (#theorem neutral-record-recursion
        (#universes) (#parameters
          (#parameter value (#pt-use record-one-nat ())))
        (#statement (#pt-eq #pt-nat
          (#pt-induct record-one-nat () ()
            (#pt-lambda ((subject (#pt-use record-one-nat ()))) #pt-nat)
            ((#pt-lambda ((field #pt-nat)) field))
            value)
          (#pt-project record-one-nat 0 value)))
        (#proof (#pt-refl #pt-nat (#pt-project record-one-nat 0 value))))

      ; Elimination into a proposition may use the proof field directly.
      (#math-inductive proposition-proof-record () ((P #pt-prop)) #pt-prop
        ((pack ((evidence P)))))
      (#theorem proof-valued-elimination
        (#universes) (#parameters (#parameter P #pt-prop)
          (#parameter value (#pt-app (#pt-use proposition-proof-record ()) P)))
        (#statement P)
        (#proof (#pt-induct proposition-proof-record () (P)
          (#pt-lambda ((subject (#pt-app (#pt-use proposition-proof-record ()) P))) P)
          ((#pt-lambda ((evidence P)) evidence))
          value)))
    "#,
    );
}

#[test]
fn record_eta_uses_proof_irrelevance_and_neutral_proofs() {
    accepts(
        r#"
      (#math-inductive proof-record () ((P #pt-prop)) (#pt-type 0)
        ((pack ((evidence P)))))
      (#theorem neutral-proofs
        (#universes) (#parameters (#parameter P #pt-prop)
          (#parameter left (#pt-app (#pt-use proof-record ()) P))
          (#parameter right (#pt-app (#pt-use proof-record ()) P)))
        (#statement (#pt-eq (#pt-app (#pt-use proof-record ()) P) left right))
        (#proof (#pt-refl (#pt-app (#pt-use proof-record ()) P) left)))
      (#theorem transitive-neutral-eta
        (#universes) (#parameters (#parameter P #pt-prop)
          (#parameter value (#pt-app (#pt-use proof-record ()) P)))
        (#statement (#pt-eq (#pt-app (#pt-use proof-record ()) P)
          (#pt-construct proof-record () (P) pack
            ((#pt-project proof-record 0 value))) value))
        (#proof (#pt-refl (#pt-app (#pt-use proof-record ()) P) value)))
    "#,
    );
}

#[test]
fn projection_checks_family_index_subject_and_constructor_evidence() {
    rejects(
        r#"
      (#math-inductive record-a () () (#pt-type 0) ((pack ((value #pt-nat)))))
      (#math-inductive record-b () () (#pt-type 0) ((pack ((value #pt-nat)))))
      (#theorem wrong-family (#universes) (#parameters (#parameter value (#pt-use record-a ())))
        (#statement (#pt-eq #pt-nat (#pt-project record-b 0 value) #pt-zero))
        (#proof (#pt-refl #pt-nat #pt-zero)))
    "#,
    );
    rejects(
        r#"
      (#math-inductive record-a () () (#pt-type 0) ((pack ((value #pt-nat)))))
      (#theorem bad-index (#universes) (#parameters (#parameter value (#pt-use record-a ())))
        (#statement (#pt-eq #pt-nat (#pt-project record-a 1 value) #pt-zero))
        (#proof (#pt-refl #pt-nat #pt-zero)))
    "#,
    );
    rejects(
        r#"
      (#math-inductive record-a () () (#pt-type 0) ((pack ((value #pt-nat)))))
      (#theorem wrong-subject (#universes) (#parameters)
        (#statement (#pt-eq #pt-nat (#pt-project record-a 0 #pt-zero) #pt-zero))
        (#proof (#pt-refl #pt-nat #pt-zero)))
    "#,
    );
    rejects(
        r#"
      (#math-inductive record-a () () (#pt-type 0) ((pack ((value #pt-nat)))))
      (#theorem malformed-constructor (#universes) (#parameters)
        (#statement (#pt-eq #pt-nat
          (#pt-project record-a 0
            (#pt-construct record-a () () pack ((#pt-refl #pt-nat #pt-zero)))) #pt-zero))
        (#proof (#pt-refl #pt-nat #pt-zero)))
    "#,
    );
}

#[test]
fn only_unindexed_nonrecursive_single_constructor_records_are_projectable() {
    for (declaration, family, subject_type) in [
      ("(#math-inductive indexed-record () () (#indices (#parameter n #pt-nat)) (#pt-type 0) ((pack () (#pt-zero))))",
       "indexed-record", "(#pt-app (#pt-use indexed-record ()) #pt-zero)"),
      ("(#math-inductive multiple-record () () (#pt-type 0) ((one ()) (two ())))",
       "multiple-record", "(#pt-use multiple-record ())"),
      ("(#math-inductive recursive-record () () (#pt-type 0) ((pack ((next #pt-self)))))",
       "recursive-record", "(#pt-use recursive-record ())"),
    ] {
        rejects(&format!(r#"{declaration}
          (#theorem projection-rejected (#universes)
            (#parameters (#parameter subject {subject_type}))
            (#statement (#pt-eq #pt-nat (#pt-project {family} 0 subject) #pt-zero))
            (#proof (#pt-refl #pt-nat #pt-zero)))"#));
    }
}

#[test]
fn proposition_projection_does_not_expose_data_or_dependent_fields() {
    rejects(
        r#"
      (#math-inductive proposition-record () () #pt-prop ((pack ((payload #pt-nat)))))
      (#theorem no-data-extraction (#universes) (#parameters (#parameter value (#pt-use proposition-record ())))
        (#statement (#pt-eq #pt-nat (#pt-project proposition-record 0 value) #pt-zero))
        (#proof (#pt-refl #pt-nat #pt-zero)))
    "#,
    );
    rejects(
        r#"
      (#math-inductive dependent-proposition-record () () #pt-prop
        ((pack ((payload #pt-nat) (proof (#pt-eq #pt-nat payload payload))))))
      (#theorem no-dependent-proof-extraction (#universes)
        (#parameters (#parameter value (#pt-use dependent-proposition-record ())))
        (#statement (#pt-eq (#pt-eq #pt-nat #pt-zero #pt-zero)
          (#pt-project dependent-proposition-record 1 value) (#pt-refl #pt-nat #pt-zero)))
        (#proof (#pt-refl (#pt-eq #pt-nat #pt-zero #pt-zero)
          (#pt-refl #pt-nat #pt-zero))))
    "#,
    );
}

#[test]
fn sort_polymorphic_record_eta_is_checked_at_the_subject_universe() {
    accepts(
        r#"
      (#math-inductive polymorphic-record (u) ((A (#pt-sort u))) (#pt-sort u)
        ((pack ((index A) (witness (#pt-eq A index index))))))
      (#theorem polymorphic-eta
        (#universes u) (#parameters (#parameter A (#pt-sort u))
          (#parameter value (#pt-app (#pt-use polymorphic-record (u)) A)))
        (#statement (#pt-eq (#pt-app (#pt-use polymorphic-record (u)) A)
          value (#pt-construct polymorphic-record (u) (A) pack
            ((#pt-project polymorphic-record 0 value)
             (#pt-project polymorphic-record 1 value)))))
        (#proof (#pt-refl (#pt-app (#pt-use polymorphic-record (u)) A) value)))
    "#,
    );
}

#[test]
fn checked_example_is_a_source_fixture() {
    accepts(include_str!("../examples/proof_records.lim"));
}

#[test]
fn type_valued_fields_have_dependent_polymorphic_projections() {
    accepts(
        r#"
      (#math-inductive package (u) () (#pt-type (#pt-level-succ u))
        ((pack ((A (#pt-type u)) (item A)))))
      (#theorem package-eta (#universes u)
        (#parameters (#parameter value (#pt-use package (u))))
        (#statement (#pt-eq (#pt-use package (u)) value
          (#pt-construct package (u) () pack
            ((#pt-project package 0 value) (#pt-project package 1 value)))))
        (#proof (#pt-refl (#pt-use package (u)) value)))
      (#math-definition package-item (u)
        (#pt-pi ((value (#pt-use package (u)))) (#pt-project package 0 value))
        (#pt-lambda ((value (#pt-use package (u)))) (#pt-project package 1 value)))
    "#,
    );
}

#[test]
fn projecting_one_field_does_not_erase_a_bad_unused_field() {
    rejects(
        r#"
      (#math-inductive pair-nat () () (#pt-type 0)
        ((pack ((first #pt-nat) (second #pt-nat)))))
      (#theorem invalid-erased-field (#universes) (#parameters)
        (#statement (#pt-eq #pt-nat
          (#pt-project pair-nat 0 (#pt-construct pair-nat () () pack
            (#pt-zero (#pt-refl #pt-nat #pt-zero)))) #pt-zero))
        (#proof (#pt-refl #pt-nat #pt-zero)))
    "#,
    );
}
