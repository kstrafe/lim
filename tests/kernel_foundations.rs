//! Fixed logical assumptions are typed, opaque and inventoried explicitly.
mod support;
use lim::CheckedTheorem;
use std::{fs, process::Command};

const EXAMPLE: &str = include_str!("../examples/proof_foundations.lim");
fn accepts(source: &str) {
    lim::check_types(&lim::parse_program(source).unwrap()).unwrap();
}
fn rejects(source: &str, expected: &str) {
    let program = lim::parse_program(source).unwrap();
    let why = lim::check_types(&program).unwrap_err();
    assert!(why.contains(expected), "expected {expected}: {why}");
    assert!(!why.contains("resource limit"), "{why}");
}
fn audit(source: &str, target: &str) -> CheckedTheorem {
    let scratch = support::Scratch::new("native-foundation-audit");
    lim::check_theorem_details_from_path_with_config(
        source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        target,
    )
    .unwrap()
}

#[test]
fn standard_fixed_foundations_check_with_exact_transitive_basis() {
    accepts(EXAMPLE);
    for (target, basis) in [
        ("selected-natural-reflexive", "Classical.choice"),
        ("proposition-extensionality", "propext"),
        ("quotient-related-representatives", "Quot.sound"),
    ] {
        let checked = audit(EXAMPLE, target);
        assert!(checked.name.ends_with(target));
        assert_eq!(checked.foundations, [basis]);
    }
}

#[test]
fn constructive_theorems_do_not_inherit_unrelated_foundations_in_the_environment() {
    let source = format!(
        "{EXAMPLE}\n(#theorem constructive (#universes) (#parameters)
      (#statement (#pt-eq #pt-nat #pt-zero #pt-zero)) (#proof (#pt-refl #pt-nat #pt-zero)))"
    );
    assert!(audit(&source, "constructive").foundations.is_empty());
}

#[test]
fn choice_is_opaque_and_does_not_reduce_to_a_supplied_witness() {
    rejects(
        &format!(
            "{EXAMPLE}\n(#theorem chosen-is-zero (#universes) (#parameters)
      (#statement (#pt-eq #pt-nat (#pt-use selected-natural ()) #pt-zero))
      (#proof (#pt-refl #pt-nat #pt-zero)))"
        ),
        "type mismatch",
    );
}

#[test]
fn bad_choice_evidence_universe_arity_and_universe_instantiation_are_rejected() {
    for (before, after, expected) in [
        (
            "(#pt-use inhabited-naturals ())",
            "#pt-zero",
            "type mismatch",
        ),
        (
            "#pt-foundation-choice (1)",
            "#pt-foundation-choice ()",
            "explicit universe",
        ),
        (
            "#pt-foundation-choice (1)",
            "#pt-foundation-choice (0)",
            "type mismatch",
        ),
    ] {
        rejects(&EXAMPLE.replacen(before, after, 1), expected);
    }
}

#[test]
fn propext_checks_both_implications_and_does_not_accept_data_types() {
    rejects(
        &EXAMPLE.replace("P Q forward backward)", "P Q #pt-zero backward)"),
        "type mismatch",
    );
    rejects(
        &EXAMPLE.replace("P Q forward backward)", "P Q forward #pt-zero)"),
        "type mismatch",
    );
    rejects(
        &EXAMPLE.replace("P Q forward backward)", "#pt-nat #pt-nat forward backward)"),
        "type mismatch",
    );
}

#[test]
fn quotient_soundness_requires_the_relation_evidence_and_correct_representatives() {
    rejects(
        &EXAMPLE.replace(
            "A relation left right related)",
            "A relation left right #pt-zero)",
        ),
        "type mismatch",
    );
    rejects(
        &EXAMPLE.replace(
            "A relation left right related)",
            "A relation #pt-zero right related)",
        ),
        "type mismatch",
    );
}

#[test]
fn quotient_soundness_does_not_turn_related_representatives_into_definitional_equals() {
    rejects(
        r#"
      (#math-definition related () (#pt-pi ((a #pt-nat) (b #pt-nat)) #pt-prop)
        (#pt-lambda ((a #pt-nat) (b #pt-nat)) (#pt-eq #pt-nat #pt-zero #pt-zero)))
      (#math-definition q-type () (#pt-type 0) (#pt-quot 1 #pt-nat (#pt-use related ())))
      (#math-definition equality () (#pt-eq (#pt-use q-type ())
        (#pt-quot-make 1 #pt-nat (#pt-use related ()) #pt-zero)
        (#pt-quot-make 1 #pt-nat (#pt-use related ()) (#pt-succ #pt-zero)))
        (#pt-app (#pt-use #pt-foundation-quot-sound (1)) #pt-nat (#pt-use related ())
          #pt-zero (#pt-succ #pt-zero) (#pt-refl #pt-nat #pt-zero)))
      (#theorem bad (#universes) (#parameters)
        (#statement (#pt-eq (#pt-use q-type ())
          (#pt-quot-make 1 #pt-nat (#pt-use related ()) #pt-zero)
          (#pt-quot-make 1 #pt-nat (#pt-use related ()) (#pt-succ #pt-zero))))
        (#proof (#pt-refl (#pt-use q-type ()) (#pt-quot-make 1 #pt-nat (#pt-use related ()) #pt-zero))))
    "#,
        "type mismatch",
    );
}

#[test]
fn opaque_initializers_and_erased_local_values_remain_in_the_audit() {
    let source = EXAMPLE.replace(
        "#math-definition selected-natural",
        "#math-opaque selected-natural",
    );
    assert_eq!(
        audit(&source, "selected-natural-reflexive").foundations,
        ["Classical.choice"]
    );
    let source = format!(
        "{EXAMPLE}\n(#theorem erased (#universes) (#parameters)
      (#statement (#pt-eq #pt-nat #pt-zero #pt-zero))
      (#proof (#pt-let (#parameter unused #pt-nat) (#pt-use selected-natural ())
        (#pt-refl #pt-nat #pt-zero))))"
    );
    assert_eq!(audit(&source, "erased").foundations, ["Classical.choice"]);
    let source = format!(
        "{EXAMPLE}\n(#theorem type-only (#universes)
      (#parameters (#parameter unused (#pt-eq #pt-nat (#pt-use selected-natural ()) #pt-zero)))
      (#statement (#pt-eq #pt-nat #pt-zero #pt-zero)) (#proof (#pt-refl #pt-nat #pt-zero)))"
    );
    assert_eq!(
        audit(&source, "type-only").foundations,
        ["Classical.choice"]
    );
}

#[test]
fn combined_foundation_inventory_is_complete_sorted_and_deduplicated() {
    let source = format!(
        r#"{EXAMPLE}
      (#math-definition rel () (#pt-pi ((a #pt-nat) (b #pt-nat)) #pt-prop)
        (#pt-lambda ((a #pt-nat) (b #pt-nat)) (#pt-eq #pt-nat a b)))
      (#math-definition q-type () (#pt-type 0) (#pt-quot 1 #pt-nat (#pt-use rel ())))
      (#theorem combined (#universes) (#parameters)
        (#statement (#pt-eq #pt-nat #pt-zero #pt-zero))
        (#proof
          (#pt-let (#parameter value #pt-nat) (#pt-use selected-natural ())
            (#pt-let (#parameter proposition-equality
              (#pt-eq #pt-prop (#pt-eq #pt-nat #pt-zero #pt-zero) (#pt-eq #pt-nat #pt-zero #pt-zero)))
              (#pt-app (#pt-use proposition-extensionality ())
                (#pt-eq #pt-nat #pt-zero #pt-zero) (#pt-eq #pt-nat #pt-zero #pt-zero)
                (#pt-lambda ((p (#pt-eq #pt-nat #pt-zero #pt-zero))) p)
                (#pt-lambda ((p (#pt-eq #pt-nat #pt-zero #pt-zero))) p))
              (#pt-let (#parameter quotient-equality (#pt-eq (#pt-use q-type ())
                (#pt-quot-make 1 #pt-nat (#pt-use rel ()) #pt-zero)
                (#pt-quot-make 1 #pt-nat (#pt-use rel ()) #pt-zero)))
                (#pt-app (#pt-use quotient-related-representatives (1)) #pt-nat (#pt-use rel ())
                  #pt-zero #pt-zero (#pt-refl #pt-nat #pt-zero))
                (#pt-refl #pt-nat #pt-zero))))))"#
    );
    assert_eq!(
        audit(&source, "combined").foundations,
        ["Classical.choice", "Quot.sound", "propext"]
    );
}

#[test]
fn imported_aliases_preserve_foundations_from_library_private_initializers() {
    let scratch = support::Scratch::new("foundation-aliases");
    let library = scratch.path().join("math");
    fs::create_dir(&library).unwrap();
    fs::write(
        library.join("lib.lim"),
        format!("{EXAMPLE}\n(#export selected-natural-reflexive)\n"),
    )
    .unwrap();
    let source = "(#alias proof = ./math/lib.lim::selected-natural-reflexive)";
    let checked = lim::check_theorem_details_from_path_with_config(
        source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        "proof",
    )
    .unwrap();
    assert_eq!(checked.foundations, ["Classical.choice"]);
}

#[test]
fn nonempty_to_church_bridge_has_the_standard_unbounded_choice_signature() {
    accepts(
        r#"
      (#math-inductive nonempty (u) ((A (#pt-sort u))) #pt-prop ((intro ((witness A)))))
      (#math-definition church (u)
        (#pt-pi ((A (#pt-sort u))) #pt-prop)
        (#pt-lambda ((A (#pt-sort u)))
          (#pt-pi ((P #pt-prop) (consume (#pt-pi ((value A)) P))) P)))
      (#math-definition to-church (u)
        (#pt-pi ((A (#pt-sort u)) (evidence (#pt-app (#pt-use nonempty (u)) A)))
          (#pt-app (#pt-use church (u)) A))
        (#pt-lambda ((A (#pt-sort u)) (evidence (#pt-app (#pt-use nonempty (u)) A)))
          (#pt-induct nonempty (u) (A)
            (#pt-lambda ((subject (#pt-app (#pt-use nonempty (u)) A))) (#pt-app (#pt-use church (u)) A))
            ((#pt-lambda ((witness A) (P #pt-prop) (consume (#pt-pi ((value A)) P))) (#pt-app consume witness))) evidence)))
      (#math-definition from-church (u)
        (#pt-pi ((A (#pt-sort u)) (evidence (#pt-app (#pt-use church (u)) A)))
          (#pt-app (#pt-use nonempty (u)) A))
        (#pt-lambda ((A (#pt-sort u)) (evidence (#pt-app (#pt-use church (u)) A)))
          (#pt-app evidence (#pt-app (#pt-use nonempty (u)) A)
            (#pt-lambda ((value A)) (#pt-construct nonempty (u) (A) intro (value))))))
      (#math-definition choose (u)
        (#pt-pi ((A (#pt-sort u)) (evidence (#pt-app (#pt-use nonempty (u)) A))) A)
        (#pt-lambda ((A (#pt-sort u)) (evidence (#pt-app (#pt-use nonempty (u)) A)))
          (#pt-app (#pt-use #pt-foundation-choice (u)) A (#pt-app (#pt-use to-church (u)) A evidence))))
    "#,
    );
}

#[test]
fn choice_cannot_establish_false_without_a_nonempty_false_premise() {
    rejects(
        r#"(#theorem cannot-admit-false (#universes) (#parameters)
      (#statement #pt-false)
      (#proof (#pt-app (#pt-use #pt-foundation-choice (0)) #pt-false
        (#pt-lambda ((P #pt-prop) (consume (#pt-pi ((value #pt-false)) P))) #pt-zero))))"#,
        "type mismatch",
    );
}

#[test]
fn cli_prints_used_assumptions_and_leaves_constructive_output_unchanged() {
    let scratch = support::Scratch::new("native-foundation-cli");
    let entry = scratch.path().join("main.lim");
    fs::write(&entry, EXAMPLE).unwrap();
    let output = support::run(
        &mut Command::new(env!("CARGO_BIN_EXE_lim")).args([
            "--check-theorem",
            entry.to_str().unwrap(),
            "selected-natural-reflexive",
        ]),
        std::time::Duration::from_secs(15),
        1024 * 1024,
    )
    .unwrap();
    assert!(output.0.success(), "{}", String::from_utf8_lossy(&output.2));
    assert!(String::from_utf8(output.1)
        .unwrap()
        .contains("logical foundations: Classical.choice"));
    fs::write(&entry,"(#theorem plain (#universes) (#parameters) (#statement (#pt-eq #pt-nat #pt-zero #pt-zero)) (#proof (#pt-refl #pt-nat #pt-zero)))").unwrap();
    let output = support::run(
        &mut Command::new(env!("CARGO_BIN_EXE_lim")).args([
            "--check-theorem",
            entry.to_str().unwrap(),
            "plain",
        ]),
        std::time::Duration::from_secs(15),
        1024 * 1024,
    )
    .unwrap();
    assert!(output.0.success());
    assert_eq!(
        String::from_utf8(output.1).unwrap(),
        "checked theorem plain\n"
    );
}
