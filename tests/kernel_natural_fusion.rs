//! Source typing and capture guards for natural recursor observations.
const EXAMPLE: &str = include_str!("../examples/proof_observed_arithmetic.lim");

fn checks(source: &str) {
    let program = lim::parse_program(source).unwrap_or_else(|why| panic!("{why}\n{source}"));
    lim::check_types(&program).unwrap_or_else(|why| panic!("{why}\n{source}"));
}
fn rejects(source: &str) {
    let program = lim::parse_program(source).unwrap();
    let why = lim::check_types(&program).unwrap_err();
    assert!(why.contains("type mismatch"), "{why}");
    assert!(!why.contains("resource limit"), "{why}");
}

#[test]
fn huge_record_observations_and_fixed_function_arguments_use_no_axioms() {
    checks(EXAMPLE);
    for target in ["observe-huge", "count-functions"] {
        let checked = lim::check_theorem_details_from_path_with_config(
            EXAMPLE,
            &std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("examples/proof_observed_arithmetic.lim"),
            &lim::CompileConfig::default(),
            target,
        )
        .unwrap();
        assert!(checked.foundations.is_empty());
    }
}

#[test]
fn false_observed_results_are_rejected_instead_of_becoming_reduction_rules() {
    rejects(&EXAMPLE.replace("184467440737095516167", "184467440737095516168"));
    rejects(&EXAMPLE.replace("184467440737095516202", "184467440737095516203"));
}

#[test]
fn observations_depend_on_checked_shapes_not_family_or_function_spellings() {
    checks(
        &EXAMPLE
            .replace("history-cell", "unrelated-record")
            .replace("history-count", "some-calculation")
            .replace("count-function", "another-calculation"),
    );
}

#[test]
fn an_invalid_unselected_record_field_is_still_typechecked() {
    let before = "(#pt-succ (#pt-project history-cell 1 state))";
    assert!(EXAMPLE.contains(before));
    rejects(&EXAMPLE.replace(before, "#pt-false"));
    rejects(&EXAMPLE.replace(
        before,
        "(#pt-let (#parameter ignored #pt-nat) #pt-false (#pt-project history-cell 1 state))",
    ));
}

#[test]
fn bool_recursors_keep_their_normal_meaning() {
    checks("(#math-inductive flag () () (#pt-type 0) ((off ()) (on ())))
      (#math-definition read-flag () (#pt-pi ((value (#pt-use flag ()))) #pt-nat)
        (#pt-lambda ((value (#pt-use flag ())))
          (#pt-induct flag () () (#pt-lambda ((subject (#pt-use flag ()))) #pt-nat)
            (#pt-zero (#pt-numeral 1)) value)))
      (#theorem flag-computes (#universes) (#parameters)
        (#statement (#pt-eq #pt-nat (#pt-app (#pt-use read-flag ()) (#pt-construct flag () () on ())) (#pt-numeral 1)))
        (#proof (#pt-refl #pt-nat (#pt-numeral 1))))");
}

#[test]
fn a_propositional_record_cannot_hide_data_for_observation() {
    let source = "(#math-inductive hidden-data () ((A (#pt-type 0))) #pt-prop ((make ((value A)))))
      (#math-definition extract () #pt-nat
        (#pt-project hidden-data 0 (#pt-construct hidden-data () (#pt-nat) make (#pt-zero))))";
    let why = lim::check_types(&lim::parse_program(source).unwrap()).unwrap_err();
    assert!(why.contains("cannot extract data"), "{why}");
    assert!(!why.contains("resource limit"), "{why}");
}
