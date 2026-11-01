mod support;

use lim::{CheckedProgram, Diagnostic, DiagnosticCode, Expr, Item};
use std::{collections::HashMap, fs, process::Command, time::Duration};

const EXAMPLE: &str = include_str!("../examples/mathematical_proofs.lim");

fn accepts(source: &str) {
    let program = lim::parse_program(source).unwrap_or_else(|error| panic!("{error}\n{source}"));
    CheckedProgram::validate(&program).unwrap_or_else(|error| panic!("{error}\n{source}"));
}

fn rejects(source: &str) -> Diagnostic {
    // Rejection must come from proof checking, not an invalid runtime fixture.
    lim::parse_program(source).unwrap_or_else(|error| panic!("{error}\n{source}"));
    let scratch = support::Scratch::new("kernel-rejection");
    let error = lim::check_source_for_editor(
        source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &HashMap::new(),
    )
    .expect_err(&format!(
        "the kernel must reject this declaration:\n{source}"
    ));
    assert_eq!(error.code, DiagnosticCode::Proof, "{error:?}\n{source}");
    assert_eq!(error.code_string(), "E4400");
    error
}

/// Keep focused fixtures in the example's actual topological source order.
fn declarations(names: &[&str]) -> String {
    let mut source = String::new();
    let mut found = 0;
    for node in lim::parse(EXAMPLE).unwrap() {
        let Expr::List(items) = &node.expr else {
            continue;
        };
        if !matches!(items.first(), Some(Expr::Symbol(head)) if head == "#proof") {
            continue;
        }
        if matches!(items.get(1), Some(Expr::Symbol(name)) if names.contains(&name.as_str())) {
            source.push_str(&EXAMPLE[node.span.start..node.span.end]);
            source.push('\n');
            found += 1;
        }
    }
    assert_eq!(
        found,
        names.len(),
        "missing example declarations: {names:?}"
    );
    source
}

#[test]
fn polymorphic_identity_reduces_at_multiple_universe_instances() {
    let source = declarations(&["identity"]);
    accepts(&format!(
        "{source}
      (#proof identity-at-nat (#proof-theorem ()
        (#pt-eq #pt-nat (#pt-app (#pt-use identity (0)) #pt-nat #pt-zero) #pt-zero)
        (#pt-refl #pt-nat #pt-zero)))
      (#proof identity-at-types (#proof-theorem ()
        (#pt-eq (#pt-type 0)
          (#pt-app (#pt-use identity (1)) (#pt-type 0) #pt-nat) #pt-nat)
        (#pt-refl (#pt-type 0) #pt-nat)))"
    ));
}

#[test]
fn universe_max_type_operator_builds_a_mixed_universe_product() {
    let source = declarations(&["product"]);
    accepts(&format!(
        "{source}
      (#proof mixed-pair (#proof-definition ()
        (#pt-app (#pt-use product (0 1)) #pt-nat (#pt-type 0))
        (#pt-pair (#pt-app (#pt-use product (0 1)) #pt-nat (#pt-type 0))
          #pt-zero #pt-nat)))
      (#proof mixed-first (#proof-theorem ()
        (#pt-eq #pt-nat (#pt-first (#pt-use mixed-pair ())) #pt-zero)
        (#pt-refl #pt-nat #pt-zero)))
      (#proof mixed-second (#proof-theorem ()
        (#pt-eq (#pt-type 0) (#pt-second (#pt-use mixed-pair ())) #pt-nat)
        (#pt-refl (#pt-type 0) #pt-nat)))"
    ));
}

#[test]
fn symbolic_successor_universe_parameters_substitute_correctly() {
    accepts(
        "(#proof next-universe (#proof-definition (u)
      (#pt-type (#pt-level-succ u)) (#pt-type u)))
      (#proof concrete-universe (#proof-theorem ()
        (#pt-eq (#pt-type 1) (#pt-use next-universe (0)) (#pt-type 0))
        (#pt-refl (#pt-type 1) (#pt-type 0))))",
    );
}

#[test]
fn implication_composition_is_a_polymorphic_impredicative_proposition() {
    accepts(&declarations(&["compose-implications"]));
    rejects(
        "(#proof fake-composition (#proof-theorem ()
      (#pt-pi ((p #pt-prop) (q #pt-prop) (premise p)) q)
      (#pt-lambda ((p #pt-prop) (q #pt-prop) (premise p)) premise)))",
    );
}

#[test]
fn equality_symmetry_is_derived_with_j() {
    let source = declarations(&["symmetry"]);
    accepts(&format!(
        "{source}
      (#proof reverse-reflexivity (#proof-theorem ()
        (#pt-eq #pt-nat (#pt-numeral 3) (#pt-numeral 3))
        (#pt-app (#pt-use symmetry (0)) #pt-nat
          (#pt-numeral 3) (#pt-numeral 3)
          (#pt-refl #pt-nat (#pt-numeral 3)))))"
    ));
}

#[test]
fn dependent_transport_computes_on_reflexivity() {
    let source = declarations(&["transport"]);
    accepts(&format!(
        "{source}
      (#proof transported-zero (#proof-theorem ()
        (#pt-eq #pt-nat
          (#pt-app (#pt-use transport (0 0)) #pt-nat
            (#pt-lambda ((point #pt-nat)) #pt-nat)
            #pt-zero #pt-zero (#pt-refl #pt-nat #pt-zero) #pt-zero)
          #pt-zero)
        (#pt-refl #pt-nat #pt-zero)))"
    ));
}

#[test]
fn j_rejects_wrong_motives_bases_and_equality_witnesses() {
    for term in [
        "(#pt-eq-elim #pt-nat #pt-zero #pt-nat #pt-zero #pt-zero (#pt-refl #pt-nat #pt-zero))",
        "(#pt-eq-elim #pt-nat #pt-zero
          (#pt-lambda ((other #pt-nat) (path (#pt-eq #pt-nat #pt-zero other))) #pt-nat)
          (#pt-refl #pt-nat #pt-zero) #pt-zero (#pt-refl #pt-nat #pt-zero))",
        "(#pt-eq-elim #pt-nat #pt-zero
          (#pt-lambda ((other #pt-nat) (path (#pt-eq #pt-nat #pt-zero other))) #pt-nat)
          #pt-zero (#pt-succ #pt-zero) (#pt-refl #pt-nat #pt-zero))",
    ] {
        rejects(&format!(
            "(#proof bad-j (#proof-definition () #pt-nat {term}))"
        ));
    }
}

#[test]
fn natural_addition_right_zero_requires_and_accepts_induction() {
    let source = declarations(&["congruence", "plus", "plus-right-zero"]);
    accepts(&format!(
        "{source}
      (#proof seven-plus-zero (#proof-theorem ()
        (#pt-eq #pt-nat
          (#pt-app (#pt-use plus ()) (#pt-numeral 7) #pt-zero) (#pt-numeral 7))
        (#pt-app (#pt-use plus-right-zero ()) (#pt-numeral 7))))"
    ));
    let plus = declarations(&["plus"]);
    rejects(&format!(
        "{plus}
      (#proof unproved-right-zero (#proof-theorem ()
        (#pt-pi ((number #pt-nat))
          (#pt-eq #pt-nat (#pt-app (#pt-use plus ()) number #pt-zero) number))
        (#pt-lambda ((number #pt-nat)) (#pt-refl #pt-nat number))))"
    ));
}

#[test]
fn natural_addition_right_successor_is_proved_by_induction() {
    accepts(&declarations(&[
        "congruence",
        "plus",
        "plus-right-successor",
    ]));
}

#[test]
fn natural_induction_checks_zero_and_successor_cases() {
    for branches in [
        "(#pt-refl #pt-nat #pt-zero)
          (#pt-lambda ((previous #pt-nat) (hypothesis #pt-nat)) (#pt-succ hypothesis))",
        "#pt-zero (#pt-lambda ((hypothesis #pt-nat)) (#pt-succ hypothesis))",
        "#pt-zero (#pt-lambda ((previous #pt-nat) (hypothesis #pt-nat))
          (#pt-refl #pt-nat previous))",
    ] {
        rejects(&format!(
            "(#proof bad-induction (#proof-definition () #pt-nat
          (#pt-nat-induct (#pt-lambda ((number #pt-nat)) #pt-nat)
            {branches} (#pt-numeral 2))))"
        ));
    }
}

#[test]
fn generic_list_length_uses_constructor_induction_and_its_recursive_hypothesis() {
    let source = declarations(&["list", "length", "length-nil", "length-cons"]);
    accepts(&format!(
        "{source}
      (#proof two-elements (#proof-theorem ()
        (#pt-eq #pt-nat
          (#pt-app (#pt-use length (0)) #pt-nat
            (#pt-construct list (0) (#pt-nat) cons
              (#pt-zero (#pt-construct list (0) (#pt-nat) cons
                ((#pt-succ #pt-zero) (#pt-construct list (0) (#pt-nat) nil ()))))))
          (#pt-numeral 2))
        (#pt-refl #pt-nat (#pt-numeral 2))))"
    ));
}

#[test]
fn constructors_check_universe_parameter_name_and_field_arity() {
    let list = declarations(&["list"]);
    for term in [
        "(#pt-construct list () (#pt-nat) nil ())",
        "(#pt-construct list (0) () nil ())",
        "(#pt-construct list (0) (#pt-nat) missing ())",
        "(#pt-construct list (0) (#pt-nat) cons (#pt-zero))",
        "(#pt-construct list (0) (#pt-nat) nil (#pt-zero))",
        "(#pt-construct list (0) (#pt-nat) cons
          ((#pt-type 0) (#pt-construct list (0) (#pt-nat) nil ())))",
    ] {
        rejects(&format!(
            "{list} (#proof bad-constructor (#proof-definition ()
          (#pt-app (#pt-use list (0)) #pt-nat) {term}))"
        ));
    }
}

#[test]
fn constructor_induction_rejects_missing_or_misordered_recursive_hypotheses() {
    let list = declarations(&["list"]);
    for branches in [
        "(#pt-zero)",
        "(#pt-zero (#pt-lambda ((head #pt-nat)
          (tail (#pt-app (#pt-use list (0)) #pt-nat))) #pt-zero))",
        "(#pt-zero (#pt-lambda ((head #pt-nat) (hypothesis #pt-nat)
          (tail (#pt-app (#pt-use list (0)) #pt-nat))) hypothesis))",
    ] {
        rejects(&format!(
            "{list}
          (#proof bad-branches (#proof-definition () #pt-nat
            (#pt-induct list (0) (#pt-nat)
              (#pt-lambda ((items (#pt-app (#pt-use list (0)) #pt-nat))) #pt-nat)
              {branches} (#pt-construct list (0) (#pt-nat) nil ()))))"
        ));
    }
}

#[test]
fn dependent_pair_second_projection_retains_its_first_projection_index() {
    accepts(&declarations(&[
        "a-dependent-pair",
        "pair-projection",
        "pair-evidence",
    ]));
    rejects(
        "(#proof bad-dependent-pair (#proof-definition ()
      (#pt-sigma ((first #pt-nat)) (#pt-eq #pt-nat first first))
      (#pt-pair (#pt-sigma ((first #pt-nat)) (#pt-eq #pt-nat first first))
        #pt-zero (#pt-refl #pt-nat (#pt-succ #pt-zero)))))",
    );
}

#[test]
fn sigma_requires_exactly_one_binder_and_both_projections_require_a_pair() {
    for (ty, term) in [
        ("(#pt-type 0)", "(#pt-sigma () #pt-nat)"),
        (
            "(#pt-type 0)",
            "(#pt-sigma ((first #pt-nat) (second #pt-nat)) #pt-nat)",
        ),
        ("#pt-nat", "(#pt-first #pt-zero)"),
        ("#pt-nat", "(#pt-second #pt-zero)"),
    ] {
        rejects(&format!(
            "(#proof bad-sigma (#proof-definition () {ty} {term}))"
        ));
    }
}

#[test]
fn an_empty_user_proposition_eliminates_into_any_proposition() {
    accepts(&declarations(&["empty", "empty-elimination"]));
    let empty = declarations(&["empty"]);
    rejects(&format!(
        "{empty} (#proof impossible (#proof-theorem ()
      (#pt-use empty ()) (#pt-construct empty () () invented ())))"
    ));
}

#[test]
fn builtin_false_has_no_zero_refl_certificate_or_admit_constructor() {
    for term in [
        "#pt-zero",
        "(#pt-refl #pt-nat #pt-zero)",
        "(#pt-certificate missing)",
        "(#pt-admit)",
        "(#pt-unsafe)",
    ] {
        rejects(&format!(
            "(#proof impossible (#proof-theorem () #pt-false {term}))"
        ));
    }
}

#[test]
fn theorems_must_prove_propositions_and_cannot_be_axioms() {
    for declaration in [
        "(#proof data-theorem (#proof-theorem () #pt-nat #pt-zero))",
        "(#proof missing-proof (#proof-theorem () #pt-false))",
        "(#proof fake-axiom (#proof-axiom () #pt-false))",
    ] {
        rejects(declaration);
    }
}

#[test]
fn transparent_definitions_support_delta_beta_and_iota_conversion() {
    accepts(
        "(#proof two (#proof-definition () #pt-nat (#pt-succ (#pt-succ #pt-zero))))
      (#proof computed (#proof-theorem ()
        (#pt-eq #pt-nat
          (#pt-app (#pt-lambda ((value #pt-nat)) value) (#pt-use two ()))
          (#pt-numeral 2))
        (#pt-refl #pt-nat (#pt-numeral 2))))",
    );
}

#[test]
fn theorem_bodies_remain_opaque_during_conversion() {
    let witness = "(#proof witness (#proof-theorem ()
      (#pt-eq #pt-nat #pt-zero #pt-zero) (#pt-refl #pt-nat #pt-zero)))";
    rejects(&format!(
        "{witness}
      (#proof forbidden-unfolding (#proof-theorem ()
        (#pt-eq (#pt-eq #pt-nat #pt-zero #pt-zero)
          (#pt-use witness ()) (#pt-refl #pt-nat #pt-zero))
        (#pt-refl (#pt-eq #pt-nat #pt-zero #pt-zero) (#pt-use witness ()))))"
    ));
}

#[test]
fn universes_reject_type_in_type_unknown_levels_and_wrong_instantiation_arity() {
    for source in [
        "(#proof type-in-type (#proof-definition () (#pt-type 0) (#pt-type 0)))",
        "(#proof natural-is-not-prop (#proof-definition () #pt-prop #pt-nat))",
        "(#proof missing-level (#proof-definition () (#pt-type u) #pt-nat))",
        "(#proof negative-level (#proof-definition () (#pt-type -1) #pt-nat))",
        "(#proof duplicate-level (#proof-definition (u u)
          (#pt-pi ((a (#pt-type u)) (value a)) a)
          (#pt-lambda ((a (#pt-type u)) (value a)) value)))",
    ] {
        rejects(source);
    }
    let identity = declarations(&["identity"]);
    for levels in ["()", "(0 1)", "(missing)"] {
        rejects(&format!(
            "{identity} (#proof bad-instance (#proof-definition ()
          (#pt-pi ((value #pt-nat)) #pt-nat)
          (#pt-app (#pt-use identity {levels}) #pt-nat)))"
        ));
    }
}

#[test]
fn free_variables_shadowed_binders_and_malformed_applications_are_rejected() {
    for source in [
        "(#proof free (#proof-definition () #pt-nat missing))",
        "(#proof shadow (#proof-definition ()
          (#pt-pi ((first #pt-nat) (second #pt-nat)) #pt-nat)
          (#pt-lambda ((value #pt-nat) (value #pt-nat)) value)))",
        "(#proof bad-binder (#proof-definition () (#pt-type 0) (#pt-pi ((value)) #pt-nat)))",
        "(#proof apply-data (#proof-definition () #pt-nat (#pt-app #pt-zero #pt-zero)))",
        "(#proof wrong-refl (#proof-theorem ()
          (#pt-eq #pt-nat #pt-zero (#pt-succ #pt-zero)) (#pt-refl #pt-nat #pt-zero)))",
    ] {
        rejects(source);
    }
}

#[test]
fn self_and_mutual_cycles_are_not_recursive_definitions() {
    for source in [
        "(#proof self-reference (#proof-definition () #pt-nat (#pt-use self-reference ())))",
        "(#proof first (#proof-definition () #pt-nat (#pt-use second ())))
          (#proof second (#proof-definition () #pt-nat (#pt-use first ())))",
    ] {
        rejects(source);
    }
}

#[test]
fn acyclic_forward_references_do_not_reorder_source_declarations() {
    let source = "(#proof before (#proof-definition () #pt-nat (#pt-use later ())))
      (#proof later (#proof-definition () #pt-nat #pt-zero))";
    let program = lim::parse_program(source).unwrap();
    let names = || {
        program
            .items
            .iter()
            .map(|item| {
                let Item::Proof { name, .. } = item else {
                    panic!("expected a proof declaration")
                };
                name.as_str()
            })
            .collect::<Vec<_>>()
    };
    assert_eq!(names(), ["before", "later"]);
    CheckedProgram::validate(&program).unwrap();
    assert_eq!(names(), ["before", "later"]);
}

#[test]
fn indexed_nested_and_negative_recursive_inductives_fail_closed() {
    for source in [
        "(#proof vector (#proof-inductive (u) (: a (#pt-type u))
          (#pt-pi ((size #pt-nat)) (#pt-type u)) ((nil ()))))",
        "(#proof negative (#proof-inductive () () (#pt-type 0)
          ((make (: callback (#pt-pi ((input #pt-self)) #pt-nat))))))",
        "(#proof nested (#proof-inductive () () (#pt-type 0)
          ((make (: wrapped (#pt-sigma ((tag #pt-nat)) #pt-self))))))",
        "(#proof duplicated (#proof-inductive () () (#pt-type 0)
          ((make ()) (make ()))))",
        "(#proof outside-self (#proof-definition () (#pt-type 0) #pt-self))",
    ] {
        rejects(source);
    }
}

#[test]
fn machine_certificates_work_before_or_after_their_procedural_declaration() {
    let runtime = "(#fn leaf () #u64 (#return 42u64))
      (#fn main () #u64 (#return (#call leaf (:))))";
    let fact = "(#proof calls (#proof-calls-directly main leaf))";
    let theorem = "(#proof certified (#proof-theorem ()
      (#pt-program calls) (#pt-certificate calls)))";
    for source in [
        format!("{runtime} {fact} {theorem}"),
        format!("{runtime} {theorem} {fact}"),
    ] {
        accepts(&source);
    }
}

#[test]
fn program_certificates_cannot_forge_or_substitute_a_different_fact() {
    let runtime = "(#fn leaf () #u64 (#return 42u64))
      (#fn main () #u64 (#return (#call leaf (:))))";
    for declarations in [
        "(#proof forged (#proof-theorem () (#pt-program missing) (#pt-certificate missing)))",
        "(#proof left (#proof-calls-directly main leaf))
          (#proof right (#proof-no-effects leaf (#proof-io)))
          (#proof mismatched (#proof-theorem () (#pt-program left) (#pt-certificate right)))",
        "(#proof failed false)
          (#proof forged (#proof-theorem () (#pt-program failed) (#pt-certificate failed)))",
        "(#proof math (#proof-theorem () (#pt-eq #pt-nat #pt-zero #pt-zero)
            (#pt-refl #pt-nat #pt-zero)))
          (#proof forged (#proof-theorem () (#pt-program math) (#pt-certificate math)))",
    ] {
        rejects(&format!("{runtime} {declarations}"));
    }
}

#[test]
fn kernel_diagnostic_marks_the_whole_wrapper_proposition() {
    let wrapper = "(#proof-theorem () (#pt-eq #pt-nat #pt-zero (#pt-succ #pt-zero))
      (#pt-refl #pt-nat #pt-zero))";
    let source = format!("(#proof mistaken {wrapper})");
    let error = rejects(&source);
    let span = error.span.expect("kernel declaration diagnostic span");
    assert_eq!(&source[span.start..span.end], wrapper);
    assert!(lim::render_diagnostic_json(&error, "main.lim").contains("\"category\":\"proof\""));
}

#[test]
fn mathematical_keywords_require_their_source_prefix() {
    for source in [
        "(#proof bad (proof-definition () #pt-nat #pt-zero))",
        "(#proof bad (#proof-definition () pt-nat #pt-zero))",
        "(#proof bad (#proof-definition () #pt-nat (pt-succ #pt-zero)))",
        "(#proof bad (#proof-definition () (#pt-type 2) (#pt-type (pt-level-succ 0))))",
    ] {
        // Missing prefixes may be diagnosed by the source parser or kernel
        // adapter. Each fixture would otherwise be well typed.
        if let Ok(program) = lim::parse_program(source) {
            assert!(
                CheckedProgram::validate(&program).is_err(),
                "accepted unprefixed syntax: {source}"
            );
        }
    }
}

#[test]
fn kernel_math_cannot_execute_runtime_operations() {
    rejects(
        "(#fn main () #u64 (#return 42u64))
      (#proof not-a-kernel-value (#proof-definition () #pt-nat (#call main (:))))",
    );
}

#[test]
fn native_example_returns_42_and_mathematics_has_no_assembly_cost() {
    let proved = lim::parse_program(EXAMPLE).unwrap();
    let assembly = lim::generate_assembly(&proved).unwrap();
    let mut runtime = proved.clone();
    runtime
        .items
        .retain(|item| !matches!(item, Item::Proof { .. }));
    assert_eq!(assembly, lim::generate_assembly(&runtime).unwrap());
    let scratch = support::Scratch::new("kernel-native-example");
    let binary = scratch.path().join("mathematical-proofs");
    lim::link_native_binary(
        &assembly,
        &binary,
        &[],
        &[],
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    let (status, stdout, stderr) =
        support::run(&mut Command::new(&binary), Duration::from_secs(5), 4096).unwrap();
    assert_eq!(status.code(), Some(42), "{stderr:?}");
    assert!(stdout.is_empty(), "{stdout:?}");
    assert!(stderr.is_empty(), "{stderr:?}");
}

#[test]
fn source_compilation_checks_kernel_declarations_on_cold_and_warm_cache_paths() {
    let scratch = support::Scratch::new("kernel-cache");
    let path = scratch.path().join("main.lim");
    let cache = scratch.path().join("cache");
    let config = lim::CompileConfig::default();
    let target = lim::TargetDescription::X86_64_SYSTEM_V;
    let source = "(#fn main () #u64 (#return 42u64))
      (#proof checked (#proof-theorem () (#pt-eq #pt-nat #pt-zero #pt-zero)
        (#pt-refl #pt-nat #pt-zero)))";
    fs::write(&path, source).unwrap();
    let cold = lim::compile_source_to_assembly(source, &path, &config, &cache, target).unwrap();
    assert_eq!(
        cold,
        lim::compile_source_to_assembly(source, &path, &config, &cache, target).unwrap()
    );
    let invalid = source.replace("(#pt-refl #pt-nat #pt-zero)", "#pt-zero");
    fs::write(&path, &invalid).unwrap();
    for _ in 0..2 {
        let error =
            lim::compile_source_to_assembly(&invalid, &path, &config, &cache, target).unwrap_err();
        assert_eq!(error.code, DiagnosticCode::Proof);
    }
}

#[test]
fn builtin_false_eliminates_only_from_a_hypothetical_proof() {
    accepts(&declarations(&["false-elimination"]));
    rejects(
        "(#proof false-from-nat (#proof-theorem () #pt-false
      (#pt-induct #pt-false () ()
        (#pt-lambda ((impossible #pt-false)) #pt-false) () #pt-zero)))",
    );
}

#[test]
fn nonpropositional_pi_sorts_use_the_maximum_universe() {
    accepts(
        "(#proof function-space (#proof-definition (u v)
      (#pt-pi ((a (#pt-type u)) (b (#pt-type v))) (#pt-type (#pt-level-max u v)))
      (#pt-lambda ((a (#pt-type u)) (b (#pt-type v))) (#pt-pi ((input a)) b))))",
    );
    rejects(
        "(#proof lowered-universe (#proof-definition () (#pt-type 0)
      (#pt-pi ((a (#pt-type 0))) #pt-nat)))",
    );
}

#[test]
fn natural_terms_require_well_typed_nonnegative_kernel_constructors() {
    for term in [
        "(#pt-numeral -1)",
        "(#pt-numeral 129)",
        "(#pt-succ #pt-prop)",
        "0u64",
    ] {
        rejects(&format!(
            "(#proof bad-natural (#proof-definition () #pt-nat {term}))"
        ));
    }
}

#[test]
fn transparent_type_aliases_reduce_during_term_checking() {
    accepts(
        "(#proof natural-type (#proof-definition () (#pt-type 0) #pt-nat))
      (#proof zero-value (#proof-definition () (#pt-use natural-type ()) #pt-zero))
      (#proof alias-value (#proof-theorem ()
        (#pt-eq #pt-nat (#pt-use zero-value ()) #pt-zero)
        (#pt-refl #pt-nat #pt-zero)))",
    );
}

#[test]
fn natural_addition_commutativity_follows_from_induction_and_the_right_lemmas() {
    let source = declarations(&[
        "symmetry",
        "transitivity",
        "congruence",
        "plus",
        "plus-right-zero",
        "plus-right-successor",
        "plus-commutative",
    ]);
    accepts(&format!(
        "{source}
      (#proof two-plus-three (#proof-theorem ()
        (#pt-eq #pt-nat
          (#pt-app (#pt-use plus ()) (#pt-numeral 2) (#pt-numeral 3))
          (#pt-app (#pt-use plus ()) (#pt-numeral 3) (#pt-numeral 2)))
        (#pt-app (#pt-use plus-commutative ()) (#pt-numeral 2) (#pt-numeral 3))))"
    ));
}

fn compile_kernel_fixture(source: &str, scratch: &support::Scratch) -> Result<String, Diagnostic> {
    lim::compile_source_to_assembly(
        source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
}

#[test]
fn an_exported_mathematical_theorem_is_instantiated_through_a_library_alias() {
    let scratch = support::Scratch::new("kernel-exported-theorem");
    let math = scratch.path().join("math");
    fs::create_dir_all(&math).unwrap();
    let library = declarations(&[
        "symmetry",
        "transitivity",
        "congruence",
        "plus",
        "plus-right-zero",
        "plus-right-successor",
        "plus-commutative",
    ]);
    fs::write(
        math.join("lib.lim"),
        format!("(#export plus-commutative)\n{library}"),
    )
    .unwrap();
    let source = "(#alias commutes = ./math/lib.lim::plus-commutative)
      (#proof imported-arithmetic (#proof-theorem ()
        (#pt-eq #pt-nat (#pt-numeral 5) (#pt-numeral 5))
        (#pt-app (#pt-use commutes ()) (#pt-numeral 2) (#pt-numeral 3))))
      (#fn main () #u64 (#return 42u64))";
    fs::write(scratch.path().join("main.lim"), source).unwrap();
    let cold = compile_kernel_fixture(source, &scratch).unwrap();
    assert_eq!(cold, compile_kernel_fixture(source, &scratch).unwrap());
}

#[test]
fn private_mathematical_proofs_cannot_be_reached_by_alias_or_qualified_use() {
    let scratch = support::Scratch::new("kernel-private-theorem");
    let math = scratch.path().join("math");
    fs::create_dir_all(&math).unwrap();
    let library = declarations(&["reflexivity", "symmetry"]);
    fs::write(
        math.join("lib.lim"),
        format!("(#export symmetry)\n{library}"),
    )
    .unwrap();
    for source in [
        "(#alias stolen = ./math/lib.lim::reflexivity)
          (#proof stolen-evidence (#proof-theorem ()
            (#pt-eq #pt-nat #pt-zero #pt-zero)
            (#pt-app (#pt-use stolen (0)) #pt-nat #pt-zero)))
          (#fn main () #u64 (#return 42u64))",
        "(#proof stolen-evidence (#proof-theorem ()
            (#pt-eq #pt-nat #pt-zero #pt-zero)
            (#pt-app (#pt-use ./math/lib.lim::reflexivity (0)) #pt-nat #pt-zero)))
          (#fn main () #u64 (#return 42u64))",
    ] {
        fs::write(scratch.path().join("main.lim"), source).unwrap();
        for _ in 0..2 {
            let error = compile_kernel_fixture(source, &scratch)
                .expect_err("a nonexported theorem must remain private");
            assert!(error.message.contains("private"), "{error:?}");
            assert!(error.message.contains("reflexivity"), "{error:?}");
        }
    }
}

#[test]
fn generated_kernel_theorems_are_rechecked_after_cold_and_warm_cache_tampering() {
    let scratch = support::Scratch::new("kernel-generated-cache");
    let path = scratch.path().join("main.lim");
    let source = "(#gn emit ()
        `((#proof generated-equality (#proof-theorem ()
            (#pt-eq #pt-nat #pt-zero #pt-zero)
            (#pt-refl #pt-nat #pt-zero)))))
      (#generate emit)
      (#proof use-generated (#proof-theorem ()
        (#pt-eq #pt-nat #pt-zero #pt-zero) (#pt-use generated-equality ())))
      (#fn main () #u64 (#return 42u64))";
    fs::write(&path, source).unwrap();
    let cold = compile_kernel_fixture(source, &scratch).unwrap();
    assert_eq!(cold, compile_kernel_fixture(source, &scratch).unwrap());

    let invalid = source.replacen(
        "(#pt-eq #pt-nat #pt-zero #pt-zero)",
        "(#pt-eq #pt-nat #pt-zero (#pt-succ #pt-zero))",
        1,
    );
    fs::write(&path, &invalid).unwrap();
    for _ in 0..2 {
        let error = compile_kernel_fixture(&invalid, &scratch)
            .expect_err("cached generation cannot certify zero equals successor zero");
        assert_eq!(error.code, DiagnosticCode::Proof);
        assert!(error.message.contains("generated-equality"), "{error:?}");
    }
    fs::write(&path, source).unwrap();
    assert_eq!(cold, compile_kernel_fixture(source, &scratch).unwrap());
}

#[test]
fn numeral_universe_and_level_syntax_limits_fail_closed() {
    for (source, expected) in [
        (
            "(#proof large-numeral (#proof-definition () #pt-nat (#pt-numeral 129)))",
            "numeral",
        ),
        (
            "(#proof large-universe (#proof-definition () (#pt-type 65536) #pt-nat))",
            "universe level",
        ),
        (
            "(#proof overflowing-level (#proof-definition ()
          (#pt-type (#pt-level-succ 65535)) #pt-nat))",
            "universe level",
        ),
        (
            "(#proof empty-maximum (#proof-definition ()
          (#pt-type (#pt-level-max)) #pt-nat))",
            "operands",
        ),
        (
            "(#proof malformed-successor (#proof-definition ()
          (#pt-type (#pt-level-succ 0 1)) #pt-nat))",
            "operand",
        ),
    ] {
        let error = rejects(source);
        assert!(error.message.contains(expected), "{error:?}");
    }
}
