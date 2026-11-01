//! Source-level conformance tests for definitional proof irrelevance.
//!
//! Every fixture passes through the public parser and typechecker. In
//! particular, negative cases must be rejected by the kernel, not by parsing.

fn accepts(source: &str) {
    let program = lim::parse_program(source)
        .unwrap_or_else(|error| panic!("proof-irrelevance fixture must parse: {error}\n{source}"));
    lim::check_types(&program).unwrap_or_else(|error| {
        panic!("proof-irrelevance fixture must typecheck: {error}\n{source}")
    });
}

fn rejects(source: &str) {
    let program = lim::parse_program(source)
        .unwrap_or_else(|error| panic!("negative fixture must parse: {error}\n{source}"));
    let error = lim::check_types(&program).expect_err("kernel accepted an invalid conversion");
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
fn arbitrary_proofs_of_a_generic_proposition_are_definitionally_equal() {
    accepts(
        r#"
      (#theorem proof-irrelevant
        (#universes u)
        (#parameters
          (#parameter P #pt-prop)
          (#parameter p P)
          (#parameter q P))
        (#statement (#pt-eq P p q))
        (#proof (#pt-refl P p)))
    "#,
    );
}

#[test]
fn opaque_theorem_constants_of_the_same_proposition_are_equal() {
    accepts(
        r#"
      (#theorem left-proof (#universes)
        (#parameters (#parameter P #pt-prop) (#parameter p P))
        (#statement P) (#proof p))
      (#theorem right-proof (#universes)
        (#parameters (#parameter P #pt-prop) (#parameter q P))
        (#statement P) (#proof q))
      (#theorem opaque-proofs
        (#universes) (#parameters (#parameter P #pt-prop)
          (#parameter p P) (#parameter q P))
        (#statement (#pt-eq P
          (#pt-app (#pt-use left-proof ()) P p)
          (#pt-app (#pt-use right-proof ()) P q)))
        (#proof (#pt-refl P (#pt-app (#pt-use left-proof ()) P p)))
      )
    "#,
    );
}

#[test]
fn distinct_propositions_are_still_distinct_types() {
    rejects(
        r#"
      (#theorem propositions-equal
        (#universes) (#parameters (#parameter P #pt-prop) (#parameter Q #pt-prop))
        (#statement (#pt-eq #pt-prop P Q))
        (#proof (#pt-refl #pt-prop P)))
    "#,
    );
}

#[test]
fn proofs_cannot_be_exchanged_across_distinct_proposition_types() {
    rejects(
        r#"
      (#theorem wrong-proposition
        (#universes) (#parameters (#parameter P #pt-prop) (#parameter Q #pt-prop)
          (#parameter p P) (#parameter q Q))
        (#statement P) (#proof q))
    "#,
    );
}

#[test]
fn natural_data_values_remain_distinct() {
    rejects(
        r#"
      (#theorem naturals-equal
        (#universes) (#parameters)
        (#statement (#pt-eq #pt-nat #pt-zero (#pt-succ #pt-zero)))
        (#proof (#pt-refl #pt-nat #pt-zero)))
    "#,
    );
}

#[test]
fn generic_sort_values_are_not_proofs() {
    rejects(
        r#"
      (#theorem generic-data-equal
        (#universes u)
        (#parameters (#parameter A (#pt-sort u)) (#parameter x A) (#parameter y A))
        (#statement (#pt-eq A x y))
        (#proof (#pt-refl A x)))
    "#,
    );
}

#[test]
fn equality_of_dependent_fibers_converts_at_proof_indices() {
    accepts(
        r#"
      (#theorem fiber-indices
        (#universes)
        (#parameters (#parameter P #pt-prop) (#parameter p P) (#parameter q P)
          (#parameter F (#pt-pi ((proof P)) (#pt-type 0))))
        (#statement (#pt-eq (#pt-type 0) (#pt-app F p) (#pt-app F q)))
        (#proof (#pt-refl (#pt-type 0) (#pt-app F p))))
    "#,
    );
}

#[test]
fn dependent_family_applications_convert_after_specializing_proof_parameters() {
    accepts(
        r#"
      (#theorem specialize-fiber
        (#universes) (#parameters (#parameter P #pt-prop)
          (#parameter p P) (#parameter q P)
          (#parameter F (#pt-pi ((proof P)) (#pt-type 0))))
        (#statement (#pt-eq (#pt-type 0)
          (#pt-app (#pt-lambda ((proof P)) (#pt-app F proof)) p)
          (#pt-app (#pt-lambda ((proof P)) (#pt-app F proof)) q)))
        (#proof (#pt-refl (#pt-type 0) (#pt-app F p))))
    "#,
    );
}

#[test]
fn proofs_are_irrelevant_under_function_binders() {
    accepts(
        r#"
      (#theorem under-lambda
        (#universes) (#parameters (#parameter P #pt-prop) (#parameter p P))
        (#statement (#pt-eq (#pt-pi ((proof P)) P)
          (#pt-lambda ((proof P)) p)
          (#pt-lambda ((other P)) other)))
        (#proof (#pt-refl (#pt-pi ((proof P)) P)
          (#pt-lambda ((proof P)) p))))
    "#,
    );
}

#[test]
fn proofs_are_irrelevant_in_dependent_pi_indices() {
    accepts(
        r#"
      (#theorem under-dependent-binder
        (#universes) (#parameters (#parameter P #pt-prop)
          (#parameter p P)
          (#parameter F (#pt-pi ((proof P)) (#pt-type 0))))
        (#statement (#pt-eq (#pt-type 0)
          (#pt-pi ((proof P)) (#pt-app F proof))
          (#pt-pi ((other P)) (#pt-app F p))))
        (#proof (#pt-refl (#pt-type 0) (#pt-pi ((proof P)) (#pt-app F proof)))))
    "#,
    );
}

#[test]
fn proof_fields_of_data_records_convert_but_data_records_do_not_collapse() {
    accepts(
        r#"
      (#math-inductive proof-pair () ((P #pt-prop)) (#pt-type 0)
        ((pack ((first P) (second P)))))
      (#theorem records
        (#universes) (#parameters (#parameter P #pt-prop)
          (#parameter p P) (#parameter q P))
        (#statement (#pt-eq (#pt-app (#pt-use proof-pair ()) P)
          (#pt-construct proof-pair () (P) pack (p p))
          (#pt-construct proof-pair () (P) pack (q q))))
        (#proof (#pt-refl (#pt-app (#pt-use proof-pair ()) P)
          (#pt-construct proof-pair () (P) pack (p p)))))
    "#,
    );
}

#[test]
fn proof_irrelevance_does_not_make_distinct_record_data_equal() {
    rejects(
        r#"
      (#math-inductive proof-tagged () ((P #pt-prop)) (#pt-type 0)
        ((pack ((tag #pt-nat) (proof P)))))
      (#theorem record-data-remains-distinct
        (#universes) (#parameters (#parameter P #pt-prop) (#parameter p P))
        (#statement (#pt-eq (#pt-app (#pt-use proof-tagged ()) P)
          (#pt-construct proof-tagged () (P) pack (#pt-zero p))
          (#pt-construct proof-tagged () (P) pack ((#pt-succ #pt-zero) p))))
        (#proof (#pt-refl (#pt-app (#pt-use proof-tagged ()) P)
          (#pt-construct proof-tagged () (P) pack (#pt-zero p)))))
    "#,
    );
}

#[test]
fn separate_native_program_facts_are_not_interchangeable() {
    rejects(
        r#"
      (#fn leaf () #u64 (#return 42u64))
      (#fn main () #u64 (#return (#call leaf (:))))
      (#theorem calls (#proof-calls-directly main leaf))
      (#theorem no-effects (#proof-no-effects leaf (#proof-io)))
      (#theorem facts-remain-distinct
        (#universes) (#parameters)
        (#statement (#pt-program calls))
        (#proof (#pt-certificate no-effects)))
    "#,
    );
}

#[test]
fn malformed_proof_terms_are_not_rescued_by_proof_irrelevance() {
    rejects(
        r#"
      (#theorem ill-typed-reflexivity
        (#universes) (#parameters (#parameter P #pt-prop) (#parameter p P))
        (#statement (#pt-eq #pt-nat #pt-zero #pt-zero))
        (#proof (#pt-refl #pt-nat p)))
    "#,
    );
}

#[test]
fn beta_reduction_does_not_erase_an_ill_typed_ignored_argument() {
    rejects(
        r#"
      (#theorem ignored-argument
        (#universes) (#parameters)
        (#statement (#pt-eq #pt-nat #pt-zero #pt-zero))
        (#proof (#pt-app
          (#pt-lambda ((ignored #pt-nat)) (#pt-refl #pt-nat #pt-zero))
          (#pt-refl #pt-nat #pt-zero))))
    "#,
    );
}

#[test]
fn normalization_cannot_hide_invalid_equality_or_singleton_elimination() {
    rejects(
        r#"
      (#math-definition invalid-j () #pt-nat
        (#pt-eq-elim #pt-nat #pt-zero
          (#pt-lambda ((endpoint #pt-nat) (path (#pt-eq #pt-nat #pt-zero endpoint))) #pt-nat)
          #pt-zero #pt-zero #pt-zero))
    "#,
    );
    for (motive, branches, subject) in [
        (
            "(#pt-lambda ((value (#pt-use unit-proof ()))) #pt-nat)",
            "(#pt-zero)",
            "#pt-zero",
        ),
        (
            "(#pt-lambda ((value #pt-nat)) #pt-nat)",
            "(#pt-zero)",
            "(#pt-construct unit-proof () () unit ())",
        ),
        (
            "(#pt-lambda ((value (#pt-use unit-proof ()))) #pt-nat)",
            "(#pt-zero #pt-zero)",
            "(#pt-construct unit-proof () () unit ())",
        ),
        (
            "(#pt-lambda ((value (#pt-use unit-proof ()))) #pt-nat)",
            "(#pt-prop)",
            "(#pt-construct unit-proof () () unit ())",
        ),
    ] {
        rejects(&format!(
            r#"
          (#math-inductive unit-proof () () #pt-prop ((unit ())))
          (#math-definition invalid-singleton () #pt-nat
            (#pt-induct unit-proof () () {motive} {branches} {subject}))
        "#
        ));
    }
}

#[test]
fn proof_conversion_keeps_context_after_recursive_fields_and_induction_hypotheses() {
    accepts(
        r#"
      (#math-inductive chain () ((P #pt-prop)) (#pt-type 0)
        ((end ()) (link ((tail #pt-self) (left P) (right P)))))
      (#theorem recursive-context
        (#universes)
        (#parameters (#parameter P #pt-prop)
          (#parameter subject (#pt-app (#pt-use chain ()) P)))
        (#statement (#pt-pi ((p P) (q P)) (#pt-eq P p q)))
        (#proof (#pt-induct chain () (P)
          (#pt-lambda ((value (#pt-app (#pt-use chain ()) P)))
            (#pt-pi ((p P) (q P)) (#pt-eq P p q)))
          ((#pt-lambda ((p P) (q P)) (#pt-refl P p))
           (#pt-lambda ((tail (#pt-app (#pt-use chain ()) P))
                        (ih (#pt-pi ((a P) (b P)) (#pt-eq P a b)))
                        (left P) (right P) (p P) (q P)) (#pt-refl P p)))
          subject)))
    "#,
    );
}

#[test]
fn ordinary_type_errors_are_not_accepted_as_proof_irrelevance() {
    // A regular type error remains a theorem failure; the rejection helper
    // explicitly excludes resource-limit diagnostics for every negative case.
    rejects(
        r#"
      (#theorem no-type-in-type
        (#universes) (#parameters)
        (#statement (#pt-eq (#pt-sort 1) #pt-prop #pt-nat))
        (#proof (#pt-refl (#pt-sort 1) #pt-prop)))
    "#,
    );
}
