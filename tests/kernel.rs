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
        if !matches!(items.first(), Some(Expr::Symbol(head)) if matches!(head.as_str(), "#theorem" | "#math-definition" | "#math-inductive"))
        {
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
      (#theorem identity-at-nat
        (#universes)
        (#parameters)
        (#statement (#pt-eq #pt-nat (#pt-app (#pt-use identity (0)) #pt-nat #pt-zero) #pt-zero))
        (#proof (#pt-refl #pt-nat #pt-zero)))
      (#theorem identity-at-types
        (#universes)
        (#parameters)
        (#statement (#pt-eq (#pt-type 0)
          (#pt-app (#pt-use identity (1)) (#pt-type 0) #pt-nat) #pt-nat))
        (#proof (#pt-refl (#pt-type 0) #pt-nat)))"
    ));
}

#[test]
fn universe_max_type_operator_builds_a_mixed_universe_product() {
    let source = declarations(&["product"]);
    accepts(&format!(
        "{source}
      (#math-definition mixed-pair ()
        (#pt-app (#pt-use product (0 1)) #pt-nat (#pt-type 0))
        (#pt-pair (#pt-app (#pt-use product (0 1)) #pt-nat (#pt-type 0))
          #pt-zero #pt-nat))
      (#theorem mixed-first
        (#universes)
        (#parameters)
        (#statement (#pt-eq #pt-nat (#pt-first (#pt-use mixed-pair ())) #pt-zero))
        (#proof (#pt-refl #pt-nat #pt-zero)))
      (#theorem mixed-second
        (#universes)
        (#parameters)
        (#statement (#pt-eq (#pt-type 0) (#pt-second (#pt-use mixed-pair ())) #pt-nat))
        (#proof (#pt-refl (#pt-type 0) #pt-nat)))"
    ));
}

#[test]
fn symbolic_successor_universe_parameters_substitute_correctly() {
    accepts(
        "(#math-definition next-universe (u)
      (#pt-type (#pt-level-succ u)) (#pt-type u))
      (#theorem concrete-universe
        (#universes)
        (#parameters)
        (#statement (#pt-eq (#pt-type 1) (#pt-use next-universe (0)) (#pt-type 0)))
        (#proof (#pt-refl (#pt-type 1) (#pt-type 0))))",
    );
}

#[test]
fn implication_composition_is_a_polymorphic_impredicative_proposition() {
    accepts(&declarations(&["compose-implications"]));
    rejects(
        "(#theorem fake-composition
  (#universes)
  (#parameters
    (#parameter p #pt-prop)
    (#parameter q #pt-prop)
    (#parameter premise p))
  (#statement q)
  (#proof premise))",
    );
}

#[test]
fn equality_symmetry_is_derived_with_j() {
    let source = declarations(&["symmetry"]);
    accepts(&format!(
        "{source}
      (#theorem reverse-reflexivity
        (#universes)
        (#parameters)
        (#statement (#pt-eq #pt-nat (#pt-numeral 3) (#pt-numeral 3)))
        (#proof (#pt-app (#pt-use symmetry (0)) #pt-nat
          (#pt-numeral 3) (#pt-numeral 3)
          (#pt-refl #pt-nat (#pt-numeral 3)))))"
    ));
}

#[test]
fn dependent_transport_computes_on_reflexivity() {
    let source = declarations(&["transport"]);
    accepts(&format!(
        "{source}
      (#theorem transported-zero
        (#universes)
        (#parameters)
        (#statement (#pt-eq #pt-nat
          (#pt-app (#pt-use transport (0 0)) #pt-nat
            (#pt-lambda ((point #pt-nat)) #pt-nat)
            #pt-zero #pt-zero (#pt-refl #pt-nat #pt-zero) #pt-zero)
          #pt-zero))
        (#proof (#pt-refl #pt-nat #pt-zero)))"
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
        rejects(&format!("(#math-definition bad-j () #pt-nat {term})"));
    }
}

#[test]
fn natural_addition_right_zero_requires_and_accepts_induction() {
    let source = declarations(&["congruence", "plus", "plus-right-zero"]);
    accepts(&format!(
        "{source}
      (#theorem seven-plus-zero
        (#universes)
        (#parameters)
        (#statement (#pt-eq #pt-nat
          (#pt-app (#pt-use plus ()) (#pt-numeral 7) #pt-zero) (#pt-numeral 7)))
        (#proof (#pt-app (#pt-use plus-right-zero ()) (#pt-numeral 7))))"
    ));
    let plus = declarations(&["plus"]);
    rejects(&format!(
        "{plus}
      (#theorem unproved-right-zero
        (#universes)
        (#parameters
          (#parameter number #pt-nat))
        (#statement (#pt-eq #pt-nat (#pt-app (#pt-use plus ()) number #pt-zero) number))
        (#proof (#pt-refl #pt-nat number)))"
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
            "(#math-definition bad-induction () #pt-nat
          (#pt-nat-induct (#pt-lambda ((number #pt-nat)) #pt-nat)
            {branches} (#pt-numeral 2)))"
        ));
    }
}

#[test]
fn generic_list_length_uses_constructor_induction_and_its_recursive_hypothesis() {
    let source = declarations(&["list", "length", "length-nil", "length-cons"]);
    accepts(&format!(
        "{source}
      (#theorem two-elements
        (#universes)
        (#parameters)
        (#statement (#pt-eq #pt-nat
          (#pt-app (#pt-use length (0)) #pt-nat
            (#pt-construct list (0) (#pt-nat) cons
              (#pt-zero (#pt-construct list (0) (#pt-nat) cons
                ((#pt-succ #pt-zero) (#pt-construct list (0) (#pt-nat) nil ()))))))
          (#pt-numeral 2)))
        (#proof (#pt-refl #pt-nat (#pt-numeral 2))))"
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
            "{list} (#math-definition bad-constructor ()
          (#pt-app (#pt-use list (0)) #pt-nat) {term})"
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
          (#math-definition bad-branches () #pt-nat
            (#pt-induct list (0) (#pt-nat)
              (#pt-lambda ((items (#pt-app (#pt-use list (0)) #pt-nat))) #pt-nat)
              {branches} (#pt-construct list (0) (#pt-nat) nil ())))"
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
        "(#math-definition bad-dependent-pair ()
      (#pt-sigma ((first #pt-nat)) (#pt-eq #pt-nat first first))
      (#pt-pair (#pt-sigma ((first #pt-nat)) (#pt-eq #pt-nat first first))
        #pt-zero (#pt-refl #pt-nat (#pt-succ #pt-zero))))",
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
        rejects(&format!("(#math-definition bad-sigma () {ty} {term})"));
    }
}

#[test]
fn an_empty_user_proposition_eliminates_into_any_proposition() {
    accepts(&declarations(&["empty", "empty-elimination"]));
    let empty = declarations(&["empty"]);
    rejects(&format!(
        "{empty} (#theorem impossible
  (#universes)
  (#parameters)
  (#statement (#pt-use empty ()))
  (#proof (#pt-construct empty () () invented ())))"
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
            "(#theorem impossible
  (#universes)
  (#parameters)
  (#statement #pt-false)
  (#proof {term}))"
        ));
    }
}

#[test]
fn theorems_must_prove_propositions_and_cannot_be_axioms() {
    rejects(
        "(#theorem data-theorem
      (#universes) (#parameters) (#statement #pt-nat) (#proof #pt-zero))",
    );
    for declaration in [
        "(#theorem missing-proof (#universes) (#parameters) (#statement #pt-false))",
        "(#theorem fake-axiom (#universes) (#parameters) (#statement #pt-false) (#axiom))",
        "(#proof legacy true)",
        "(#theorem legacy-wrapper (#proof-theorem () #pt-false #pt-zero))",
    ] {
        assert!(
            lim::parse_program(declaration).is_err(),
            "accepted malformed theorem: {declaration}"
        );
    }
}

#[test]
fn transparent_definitions_support_delta_beta_and_iota_conversion() {
    accepts(
        "(#math-definition two () #pt-nat (#pt-succ (#pt-succ #pt-zero)))
      (#theorem computed
        (#universes)
        (#parameters)
        (#statement (#pt-eq #pt-nat
          (#pt-app (#pt-lambda ((value #pt-nat)) value) (#pt-use two ()))
          (#pt-numeral 2)))
        (#proof (#pt-refl #pt-nat (#pt-numeral 2))))",
    );
}

#[test]
fn opaque_theorem_proofs_compare_without_unfolding_their_bodies() {
    let witness = "(#theorem witness
  (#universes)
  (#parameters)
  (#statement (#pt-eq #pt-nat #pt-zero #pt-zero))
  (#proof (#pt-refl #pt-nat #pt-zero)))";
    accepts(&format!(
        "{witness}
      (#theorem opaque-evidence
        (#universes)
        (#parameters)
        (#statement (#pt-eq (#pt-eq #pt-nat #pt-zero #pt-zero)
          (#pt-use witness ()) (#pt-refl #pt-nat #pt-zero)))
        (#proof (#pt-refl (#pt-eq #pt-nat #pt-zero #pt-zero) (#pt-use witness ()))))"
    ));
}

#[test]
fn universes_reject_type_in_type_unknown_levels_and_wrong_instantiation_arity() {
    for source in [
        "(#math-definition type-in-type () (#pt-type 0) (#pt-type 0))",
        "(#math-definition natural-is-not-prop () #pt-prop #pt-nat)",
        "(#math-definition missing-level () (#pt-type u) #pt-nat)",
        "(#math-definition negative-level () (#pt-type -1) #pt-nat)",
        "(#math-definition duplicate-level (u u)
          (#pt-pi ((a (#pt-type u)) (value a)) a)
          (#pt-lambda ((a (#pt-type u)) (value a)) value))",
    ] {
        rejects(source);
    }
    let identity = declarations(&["identity"]);
    for levels in ["()", "(0 1)", "(missing)"] {
        rejects(&format!(
            "{identity} (#math-definition bad-instance ()
          (#pt-pi ((value #pt-nat)) #pt-nat)
          (#pt-app (#pt-use identity {levels}) #pt-nat))"
        ));
    }
}

#[test]
fn free_variables_shadowed_binders_and_malformed_applications_are_rejected() {
    for source in [
        "(#math-definition free () #pt-nat missing)",
        "(#math-definition shadow ()
          (#pt-pi ((first #pt-nat) (second #pt-nat)) #pt-nat)
          (#pt-lambda ((value #pt-nat) (value #pt-nat)) value))",
        "(#math-definition bad-binder () (#pt-type 0) (#pt-pi ((value)) #pt-nat))",
        "(#math-definition apply-data () #pt-nat (#pt-app #pt-zero #pt-zero))",
        "(#theorem wrong-refl
  (#universes)
  (#parameters)
  (#statement (#pt-eq #pt-nat #pt-zero (#pt-succ #pt-zero)))
  (#proof (#pt-refl #pt-nat #pt-zero)))",
    ] {
        rejects(source);
    }
}

#[test]
fn self_and_mutual_cycles_are_not_recursive_definitions() {
    for source in [
        "(#math-definition self-reference () #pt-nat (#pt-use self-reference ()))",
        "(#math-definition first () #pt-nat (#pt-use second ()))
          (#math-definition second () #pt-nat (#pt-use first ()))",
    ] {
        rejects(source);
    }
}

#[test]
fn acyclic_forward_references_do_not_reorder_source_declarations() {
    let source = "(#math-definition before () #pt-nat (#pt-use later ()))
      (#math-definition later () #pt-nat #pt-zero)";
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
        "(#math-inductive vector (u) (: a (#pt-type u))
          (#pt-pi ((size #pt-nat)) (#pt-type u)) ((nil ())))",
        "(#math-inductive negative () () (#pt-type 0)
          ((make (: callback (#pt-pi ((input #pt-self)) #pt-nat)))))",
        "(#math-inductive nested () () (#pt-type 0)
          ((make (: wrapped (#pt-sigma ((tag #pt-nat)) #pt-self)))))",
        "(#math-inductive duplicated () () (#pt-type 0)
          ((make ()) (make ())))",
        "(#math-definition outside-self () (#pt-type 0) #pt-self)",
    ] {
        rejects(source);
    }
}

#[test]
fn machine_certificates_work_before_or_after_their_procedural_declaration() {
    let runtime = "(#fn leaf () #u64 (#return 42u64))
      (#fn main () #u64 (#return (#call leaf (:))))";
    let fact = "(#theorem calls (#proof-calls-directly main leaf))";
    let theorem = "(#theorem certified
  (#universes)
  (#parameters)
  (#statement (#pt-program calls))
  (#proof (#pt-certificate calls)))";
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
        "(#theorem forged
  (#universes)
  (#parameters)
  (#statement (#pt-program missing))
  (#proof (#pt-certificate missing)))",
        "(#theorem left (#proof-calls-directly main leaf))
          (#theorem right (#proof-no-effects leaf (#proof-io)))
          (#theorem mismatched
            (#universes)
            (#parameters)
            (#statement (#pt-program left))
            (#proof (#pt-certificate right)))",
        "(#theorem failed false)
          (#theorem forged
            (#universes)
            (#parameters)
            (#statement (#pt-program failed))
            (#proof (#pt-certificate failed)))",
        "(#theorem math
  (#universes)
  (#parameters)
  (#statement (#pt-eq #pt-nat #pt-zero #pt-zero))
  (#proof (#pt-refl #pt-nat #pt-zero)))
          (#theorem forged
            (#universes)
            (#parameters)
            (#statement (#pt-program math))
            (#proof (#pt-certificate math)))",
    ] {
        rejects(&format!("{runtime} {declarations}"));
    }
}

#[test]
fn kernel_diagnostic_marks_the_whole_canonical_theorem() {
    let source = "(#theorem mistaken
      (#universes)
      (#parameters)
      (#statement (#pt-eq #pt-nat #pt-zero (#pt-succ #pt-zero)))
      (#proof (#pt-refl #pt-nat #pt-zero)))";
    let error = rejects(source);
    let span = error.span.expect("kernel declaration diagnostic span");
    assert_eq!(&source[span.start..span.end], source);
    assert!(lim::render_diagnostic_json(&error, "main.lim").contains("\"category\":\"proof\""));
}

#[test]
fn mathematical_keywords_require_their_source_prefix() {
    for source in [
        "(math-definition bad () #pt-nat #pt-zero)",
        "(#math-definition bad () pt-nat #pt-zero)",
        "(#math-definition bad () #pt-nat (pt-succ #pt-zero))",
        "(#math-definition bad () (#pt-type 2) (#pt-type (pt-level-succ 0)))",
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
      (#math-definition not-a-kernel-value () #pt-nat (#call main (:)))",
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
      (#theorem checked
        (#universes)
        (#parameters)
        (#statement (#pt-eq #pt-nat #pt-zero #pt-zero))
        (#proof (#pt-refl #pt-nat #pt-zero)))";
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
        "(#theorem false-from-nat
  (#universes)
  (#parameters)
  (#statement #pt-false)
  (#proof (#pt-induct #pt-false () ()
        (#pt-lambda ((impossible #pt-false)) #pt-false) () #pt-zero)))",
    );
}

#[test]
fn nonpropositional_pi_sorts_use_the_maximum_universe() {
    accepts(
        "(#math-definition function-space (u v)
      (#pt-pi ((a (#pt-type u)) (b (#pt-type v))) (#pt-type (#pt-level-max u v)))
      (#pt-lambda ((a (#pt-type u)) (b (#pt-type v))) (#pt-pi ((input a)) b)))",
    );
    rejects(
        "(#math-definition lowered-universe () (#pt-type 0)
      (#pt-pi ((a (#pt-type 0))) #pt-nat))",
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
        rejects(&format!("(#math-definition bad-natural () #pt-nat {term})"));
    }
}

#[test]
fn transparent_type_aliases_reduce_during_term_checking() {
    accepts(
        "(#math-definition natural-type () (#pt-type 0) #pt-nat)
      (#math-definition zero-value () (#pt-use natural-type ()) #pt-zero)
      (#theorem alias-value
        (#universes)
        (#parameters)
        (#statement (#pt-eq #pt-nat (#pt-use zero-value ()) #pt-zero))
        (#proof (#pt-refl #pt-nat #pt-zero)))",
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
      (#theorem two-plus-three
        (#universes)
        (#parameters)
        (#statement (#pt-eq #pt-nat
          (#pt-app (#pt-use plus ()) (#pt-numeral 2) (#pt-numeral 3))
          (#pt-app (#pt-use plus ()) (#pt-numeral 3) (#pt-numeral 2))))
        (#proof (#pt-app (#pt-use plus-commutative ()) (#pt-numeral 2) (#pt-numeral 3))))"
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
      (#theorem imported-arithmetic
        (#universes)
        (#parameters)
        (#statement (#pt-eq #pt-nat (#pt-numeral 5) (#pt-numeral 5)))
        (#proof (#pt-app (#pt-use commutes ()) (#pt-numeral 2) (#pt-numeral 3))))
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
          (#theorem stolen-evidence
            (#universes)
            (#parameters)
            (#statement (#pt-eq #pt-nat #pt-zero #pt-zero))
            (#proof (#pt-app (#pt-use stolen (0)) #pt-nat #pt-zero)))
          (#fn main () #u64 (#return 42u64))",
        "(#theorem stolen-evidence
  (#universes)
  (#parameters)
  (#statement (#pt-eq #pt-nat #pt-zero #pt-zero))
  (#proof (#pt-app (#pt-use ./math/lib.lim::reflexivity (0)) #pt-nat #pt-zero)))
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
        `((#theorem generated-equality
  (#universes)
  (#parameters)
  (#statement (#pt-eq #pt-nat #pt-zero #pt-zero))
  (#proof (#pt-refl #pt-nat #pt-zero)))))
      (#generate emit)
      (#theorem use-generated
        (#universes)
        (#parameters)
        (#statement (#pt-eq #pt-nat #pt-zero #pt-zero))
        (#proof (#pt-use generated-equality ())))
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
            "(#math-definition large-numeral () #pt-nat (#pt-numeral 129))",
            "numeral",
        ),
        (
            "(#math-definition large-universe () (#pt-type 65536) #pt-nat)",
            "universe level",
        ),
        (
            "(#math-definition overflowing-level ()
          (#pt-type (#pt-level-succ 65535)) #pt-nat)",
            "universe level",
        ),
        (
            "(#math-definition empty-maximum ()
          (#pt-type (#pt-level-max)) #pt-nat)",
            "operands",
        ),
        (
            "(#math-definition malformed-successor ()
          (#pt-type (#pt-level-succ 0 1)) #pt-nat)",
            "operand",
        ),
    ] {
        let error = rejects(source);
        assert!(error.message.contains(expected), "{error:?}");
    }
}
