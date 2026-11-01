//! Source-level checks for neutral recursion on indexed singleton Prop families.

fn accepts(source: &str) {
    lim::parse(source).expect("fixture must have balanced S-expressions");
    let program = lim::parse_program(source)
        .unwrap_or_else(|error| panic!("singleton-Prop fixture must parse: {error}\n{source}"));
    lim::check_types(&program)
        .unwrap_or_else(|error| panic!("singleton-Prop fixture must typecheck: {error}\n{source}"));
}

fn rejects(source: &str) {
    lim::parse(source).expect("negative fixture must have balanced S-expressions");
    let program = lim::parse_program(source)
        .unwrap_or_else(|error| panic!("semantic negative must parse: {error}\n{source}"));
    let error = lim::check_types(&program).expect_err("kernel accepted a negative fixture");
    assert!(
        error.contains("kernel type mismatch"),
        "expected a type mismatch, got {error:?}\n{source}"
    );
    assert!(
        !error.contains("resource limit"),
        "resource error masked rejection: {error}\n{source}"
    );
}

const FAMILY: &str = r#"
  (#math-inductive singleton-prop () ((P #pt-prop))
    (#indices (#parameter i #pt-nat)) #pt-prop
    ((witness () (#pt-zero))))
"#;

fn recursor(index: &str, subject: &str, branch: &str) -> String {
    format!(
        r#"(#pt-induct singleton-prop () (P) (#indices {index})
      (#pt-lambda ((j #pt-nat)
        (value (#pt-app (#pt-use singleton-prop ()) P j)))
        (#pt-pi ((equality (#pt-eq #pt-nat j #pt-zero))) #pt-nat))
      ({branch}) {subject})"#
    )
}

#[test]
fn neutral_matching_fibre_reduces_with_parameter_and_dependent_motive() {
    let fold = recursor(
        "#pt-zero",
        "subject",
        "(#pt-lambda ((equality (#pt-eq #pt-nat #pt-zero #pt-zero))) #pt-zero)",
    );
    accepts(&format!(
        r#"{FAMILY}
        (#theorem matching-neutral-proof (#universes) (#parameters
          (#parameter P #pt-prop)
          (#parameter h (#pt-eq #pt-nat #pt-zero #pt-zero))
          (#parameter subject (#pt-app (#pt-use singleton-prop ()) P #pt-zero)))
          (#statement (#pt-eq #pt-nat
            (#pt-app {fold} h) #pt-zero))
          (#proof (#pt-refl #pt-nat #pt-zero)))"#
    ));
}

#[test]
fn an_opaque_theorem_proof_computes_without_unfolding_its_body() {
    let fold = recursor_for(
        "singleton-prop",
        "P",
        "#pt-zero",
        "(#pt-app (#pt-use opaque-witness ()) P)",
        "#pt-zero",
    );
    accepts(&format!(
        r#"{FAMILY}
      (#theorem opaque-witness (#universes) (#parameters (#parameter P #pt-prop))
        (#statement (#pt-app (#pt-use singleton-prop ()) P #pt-zero))
        (#proof (#pt-construct singleton-prop () (P) witness ())))
      (#theorem opaque-proof-computation (#universes) (#parameters (#parameter P #pt-prop))
        (#statement (#pt-eq #pt-nat {fold} #pt-zero))
        (#proof (#pt-refl #pt-nat #pt-zero)))"#
    ));
}

#[test]
fn generic_or_mismatching_fibres_remain_stuck() {
    let generic = recursor(
        "i",
        "subject",
        "(#pt-lambda ((equality (#pt-eq #pt-nat #pt-zero #pt-zero))) #pt-zero)",
    );
    accepts(&format!(
        r#"{FAMILY}
        (#math-definition generic-recursion-is-welltyped ()
          (#pt-pi ((P #pt-prop) (i #pt-nat)
            (evidence (#pt-eq #pt-nat i #pt-zero))
            (subject (#pt-app (#pt-use singleton-prop ()) P i))) #pt-nat)
          (#pt-lambda ((P #pt-prop) (i #pt-nat)
            (evidence (#pt-eq #pt-nat i #pt-zero))
            (subject (#pt-app (#pt-use singleton-prop ()) P i)))
            (#pt-app {generic} evidence)))"#
    ));
    rejects(&format!(
        r#"{FAMILY}
        (#theorem generic-fibre-stays-stuck (#universes) (#parameters
          (#parameter P #pt-prop) (#parameter i #pt-nat)
          (#parameter evidence (#pt-eq #pt-nat i #pt-zero))
          (#parameter subject (#pt-app (#pt-use singleton-prop ()) P i)))
          (#statement (#pt-eq #pt-nat
            (#pt-app {generic} evidence) #pt-zero))
          (#proof (#pt-refl #pt-nat #pt-zero)))"#
    ));
    let mismatching = recursor(
        "(#pt-succ #pt-zero)",
        "subject",
        "(#pt-lambda ((equality (#pt-eq #pt-nat #pt-zero #pt-zero))) #pt-zero)",
    );
    accepts(&format!(
        r#"{FAMILY}
        (#math-definition mismatching-recursion-is-welltyped ()
          (#pt-pi ((P #pt-prop)
            (evidence (#pt-eq #pt-nat (#pt-succ #pt-zero) #pt-zero))
            (subject (#pt-app (#pt-use singleton-prop ()) P (#pt-succ #pt-zero)))) #pt-nat)
          (#pt-lambda ((P #pt-prop)
            (evidence (#pt-eq #pt-nat (#pt-succ #pt-zero) #pt-zero))
            (subject (#pt-app (#pt-use singleton-prop ()) P (#pt-succ #pt-zero))))
            (#pt-app {mismatching} evidence)))"#
    ));
    rejects(&format!(
        r#"{FAMILY}
        (#theorem mismatching-fibre-stays-stuck (#universes) (#parameters
          (#parameter P #pt-prop)
          (#parameter evidence (#pt-eq #pt-nat (#pt-succ #pt-zero) #pt-zero))
          (#parameter subject (#pt-app (#pt-use singleton-prop ()) P (#pt-succ #pt-zero))))
          (#statement (#pt-eq #pt-nat
            (#pt-app {mismatching} evidence) #pt-zero))
          (#proof (#pt-refl #pt-nat #pt-zero)))"#
    ));
}

#[test]
fn shortcut_does_not_apply_to_indexed_data_or_fielded_propositions() {
    let data = recursor_for("indexed-data", "P", "#pt-zero", "subject", "#pt-zero");
    rejects(&format!(
        r#"(#math-inductive indexed-data () ((P #pt-prop))
          (#indices (#parameter i #pt-nat)) (#pt-type 0) ((witness () (#pt-zero))))
        (#theorem data-neutral-stays-stuck (#universes) (#parameters
          (#parameter P #pt-prop)
          (#parameter subject (#pt-app (#pt-use indexed-data ()) P #pt-zero)))
          (#statement (#pt-eq #pt-nat {data} #pt-zero)) (#proof (#pt-refl #pt-nat #pt-zero)))"#
    ));
    let fielded = recursor_for(
        "fielded-prop",
        "P",
        "#pt-zero",
        "subject",
        "(#pt-lambda ((evidence P)) #pt-zero)",
    );
    rejects(&format!(
        r#"(#math-inductive fielded-prop () ((P #pt-prop))
          (#indices (#parameter i #pt-nat)) #pt-prop
          ((witness ((evidence P)) (#pt-zero))))
        (#theorem fielded-neutral-stays-stuck (#universes) (#parameters
          (#parameter P #pt-prop)
          (#parameter subject (#pt-app (#pt-use fielded-prop ()) P #pt-zero)))
          (#statement (#pt-eq #pt-nat {fielded} #pt-zero)) (#proof (#pt-refl #pt-nat #pt-zero)))"#
    ));
}

fn recursor_for(family: &str, parameter: &str, index: &str, subject: &str, branch: &str) -> String {
    format!(
        r#"(#pt-induct {family} () ({parameter}) (#indices {index})
      (#pt-lambda ((j #pt-nat) (value (#pt-app (#pt-use {family} ()) {parameter} j))) #pt-nat)
      ({branch}) {subject})"#
    )
}

#[test]
fn subject_and_branch_types_are_still_checked() {
    let wrong_subject = recursor(
        "#pt-zero",
        "#pt-zero",
        "(#pt-lambda ((equality (#pt-eq #pt-nat #pt-zero #pt-zero))) #pt-zero)",
    );
    rejects(&format!(
        r#"{FAMILY}
        (#theorem malformed-subject (#universes) (#parameters
          (#parameter P #pt-prop))
          (#statement (#pt-eq #pt-nat
            (#pt-app {wrong_subject} (#pt-refl #pt-nat #pt-zero)) #pt-zero))
          (#proof (#pt-refl #pt-nat #pt-zero)))"#
    ));
    let wrong_branch = recursor("#pt-zero", "subject", "#pt-zero");
    rejects(&format!(
        r#"{FAMILY}
        (#theorem malformed-branch (#universes) (#parameters
          (#parameter P #pt-prop)
          (#parameter subject (#pt-app (#pt-use singleton-prop ()) P #pt-zero)))
          (#statement (#pt-eq #pt-nat
            (#pt-app {wrong_branch} (#pt-refl #pt-nat #pt-zero)) #pt-zero))
          (#proof (#pt-refl #pt-nat #pt-zero)))"#
    ));
}
