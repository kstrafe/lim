fn check(source: &str) -> Result<(), String> {
    let program = lim::parse_program(source)?;
    lim::check_types(&program)
}

fn accepts(source: &str) {
    check(source).unwrap_or_else(|error| panic!("{error}\nsource:\n{source}"));
}

fn rejects(source: &str) {
    assert!(check(source).is_err(), "unexpectedly accepted:\n{source}");
}

#[test]
fn forward_references_and_theorems_are_checked() {
    accepts(
        r#"
      (#math-definition use-later () #pt-nat (#pt-use later ()))
      (#theorem early-proof
        (#universes)
        (#parameters)
        (#statement (#pt-eq #pt-nat #pt-zero #pt-zero))
        (#proof (#pt-use later-proof ())))
      (#math-definition later () #pt-nat #pt-zero)
      (#theorem later-proof
        (#universes)
        (#parameters)
        (#statement (#pt-eq #pt-nat #pt-zero #pt-zero))
        (#proof (#pt-refl #pt-nat #pt-zero)))
    "#,
    );
}

#[test]
fn independent_declarations_and_reverse_transitive_chain_verify() {
    accepts(
        r#"
      (#math-definition leaf () #pt-nat #pt-zero)
      (#math-definition middle () #pt-nat (#pt-use leaf ()))
      (#math-definition root () #pt-nat (#pt-use middle ()))
      (#math-definition separate () #pt-nat #pt-zero)
      (#theorem actual-proof
        (#universes)
        (#parameters)
        (#statement (#pt-eq #pt-nat #pt-zero #pt-zero))
        (#proof (#pt-refl #pt-nat #pt-zero)))
    "#,
    );
    accepts(
        r#"
      (#math-definition root () #pt-nat (#pt-use middle ()))
      (#math-definition middle () #pt-nat (#pt-use leaf ()))
      (#math-definition leaf () #pt-nat #pt-zero)
    "#,
    );
}

#[test]
fn ordinary_self_and_cross_definition_cycles_are_rejected() {
    rejects("(#math-definition self () #pt-nat (#pt-use self ()))");
    rejects(
        r#"
      (#math-definition left () #pt-nat (#pt-use right ()))
      (#math-definition right () #pt-nat (#pt-use left ()))
    "#,
    );
}

#[test]
fn declared_mutual_group_is_accepted_and_checked_as_a_group() {
    accepts(
        r#"
      (#math-inductive left () () (#mutual left right) (#pt-type 0)
        ((wrap ((children (#pt-recur right ()))))))
      (#math-inductive right () () (#mutual left right) (#pt-type 0)
        ((back ((children (#pt-recur left ()))))))
    "#,
    );
}

#[test]
fn malformed_or_incomplete_mutual_groups_are_rejected() {
    rejects(
        r#"
      (#math-inductive left () () (#mutual left right) (#pt-type 0) ((wrap ())))
      (#math-inductive right () () (#mutual right left) (#pt-type 0) ((back ())))
    "#,
    );
    rejects(
        r#"
      (#math-inductive left () () (#mutual left right) (#pt-type 0) ((wrap ())))
      (#math-inductive right () () (#mutual left missing) (#pt-type 0) ((back ())))
    "#,
    );
    rejects(
        r#"
      (#math-inductive left () () (#mutual left right) (#pt-type 0) ((wrap ())))
      (#math-definition right () #pt-nat #pt-zero)
    "#,
    );
}

#[test]
fn mutual_annotation_cannot_hide_an_ordinary_definition_cycle() {
    rejects(
        r#"
      (#math-definition left () #pt-nat (#pt-use right ()))
      (#math-definition right () #pt-nat (#pt-use left ()))
    "#,
    );
}

#[test]
fn unused_later_declaration_body_is_still_typechecked() {
    rejects(
        r#"
      (#math-definition use-valid () #pt-nat (#pt-use valid-later ()))
      (#math-definition unused-bad () #pt-nat (#pt-succ #pt-prop))
      (#math-definition valid-later () #pt-nat #pt-zero)
    "#,
    );
}

#[test]
fn duplicate_math_declarations_are_rejected() {
    rejects(
        r#"
      (#math-definition repeated () #pt-nat #pt-zero)
      (#math-definition repeated () #pt-nat #pt-zero)
    "#,
    );
}

#[test]
fn tiny_shared_proof_budget_fails_closed() {
    let mut config = lim::CompileConfig::default();
    config.set_proof_budget(lim::ProofBudget::new(1, 64 << 20, 256 << 20).unwrap());
    let path = std::env::temp_dir().join(format!("lim-proof-schedule-{}.lim", std::process::id()));
    let source = r#"(#theorem actual-proof
      (#universes u)
      (#parameters (#parameter a (#pt-type u)) (#parameter value a))
      (#statement (#pt-eq a value value))
      (#proof (#pt-refl a value)))"#;
    let error =
        lim::check_theorem_details_from_path_with_config(source, &path, &config, "actual-proof")
            .expect_err("a one-unit shared profile must not certify a proof");
    assert_eq!(error.code, lim::DiagnosticCode::Proof);
}
