use lim::{CompileConfig, ProofOutcome};

const TWO_INPUTS: &str = r#"
  (#fn validate (: user (#ref #u8) : accepted #bool) #bool (#return accepted))
  (#fn perform (: user (#ref #u8)) () (#return ()))
  (#fn entry (: first (#ref #u8) : second (#ref #u8)) ()
    (#let valid #bool (#call validate (: user second : accepted true)))
    (#let failed #bool (#call validate (: user first : accepted false)))
    (#call perform (: user second))
    (#return ()))
"#;

fn theorem(source: &str, name: &str) -> Result<lim::CheckedTheorem, lim::Diagnostic> {
    lim::check_theorem_details_from_path_with_config(
        source,
        std::path::Path::new("scalar-aliases.lim"),
        &CompileConfig::default(),
        name,
    )
}

fn assert_outcome(source: &str, expected: ProofOutcome) -> String {
    let error = theorem(source, "claim").expect_err("theorem should not be proved");
    assert_eq!(
        error.proof_outcome(),
        Some(expected),
        "{}\n{source}",
        error.message
    );
    error.message
}

fn validation_claim(entry: &str) -> String {
    format!(
        "(#proof-requires-validation {entry} (#parameter-of validate user) (#parameter-of perform user))"
    )
}

#[test]
fn scalar_alias_counterexample_is_concrete_and_its_negation_is_proved() {
    lim::check_types(&lim::parse_program(TWO_INPUTS).unwrap()).unwrap();
    let claim = validation_claim("entry");
    let source = format!("{TWO_INPUTS} (#theorem claim {claim})");
    let error = assert_outcome(&source, ProofOutcome::Counterexample);
    assert!(error.contains("disproved"), "{error}");
    assert!(error.contains("ref#"), "{error}");
    assert!(
        error.contains("first = ref#0") && error.contains("second = ref#0"),
        "{error}"
    );

    let negated = format!("{TWO_INPUTS} (#theorem claim (#proof-not {claim}))");
    theorem(&negated, "claim").unwrap();
}

#[test]
fn scalar_partitions_preserve_boolean_character_and_machine_integer_types() {
    for ty in ["#bool", "#char", "#i8", "#i128", "#u128", "#usize"] {
        let source = TWO_INPUTS.replace("#u8", ty);
        lim::check_types(&lim::parse_program(&source).unwrap()).unwrap();
        let claim = validation_claim("entry");
        assert_outcome(
            &format!("{source} (#theorem claim {claim})"),
            ProofOutcome::Counterexample,
        );
        theorem(
            &format!("{source} (#theorem claim (#proof-not {claim}))"),
            "claim",
        )
        .unwrap();
    }
}

#[test]
fn owned_records_preserve_shared_scalar_aliases_in_their_fields() {
    let source = r#"
      (#struct Inputs () (: first (#ref #u8) : second (#ref #u8)))
      (#fn validate (: user (#ref #u8) : accepted #bool) #bool (#return accepted))
      (#fn perform (: user (#ref #u8)) () (#return ()))
      (#fn entry (: inputs Inputs) ()
        (#let valid #bool (#call validate (: user (#get inputs second) : accepted true)))
        (#let failed #bool (#call validate (: user (#get inputs first) : accepted false)))
        (#call perform (: user (#get inputs second)))
        (#forget inputs)
        (#return ()))
    "#;
    lim::check_types(&lim::parse_program(source).unwrap()).unwrap();
    let claim = validation_claim("entry");
    assert_outcome(
        &format!("{source} (#theorem claim {claim})"),
        ProofOutcome::Counterexample,
    );
    theorem(
        &format!("{source} (#theorem claim (#proof-not {claim}))"),
        "claim",
    )
    .unwrap();
}

#[test]
fn three_scalar_roots_include_a_world_where_all_roots_alias() {
    let source = r#"
      (#fn validate (: user (#ref #u8) : accepted #bool) #bool (#return accepted))
      (#fn perform (: user (#ref #u8)) () (#return ()))
      (#fn entry (: first (#ref #u8) : second (#ref #u8) : third (#ref #u8)) ()
        (#let valid #bool (#call validate (: user third : accepted true)))
        (#let failed #bool (#call validate (: user first : accepted false)))
        (#call perform (: user third))
        (#return ()))
    "#;
    lim::check_types(&lim::parse_program(source).unwrap()).unwrap();
    let claim = validation_claim("entry");
    let error = assert_outcome(
        &format!("{source} (#theorem claim {claim})"),
        ProofOutcome::Counterexample,
    );
    assert!(error.contains("ref#"), "{error}");
    theorem(
        &format!("{source} (#theorem claim (#proof-not {claim}))"),
        "claim",
    )
    .unwrap();
}

#[test]
fn seven_scalar_inputs_take_the_success_and_no_event_fast_paths() {
    let names = (0..7).map(|index| format!("r{index}")).collect::<Vec<_>>();
    let parameters = names
        .iter()
        .map(|name| format!(": {name} (#ref #u8)"))
        .collect::<Vec<_>>()
        .join(" ");
    let mut body = String::new();
    for name in &names {
        body.push_str(&format!(
            "(#call validate (: user {name} : accepted true)) "
        ));
    }
    body.push_str(&format!(
        "(#call perform (: user {})) (#return ())",
        names[6]
    ));
    let source = format!(
        "(#fn validate (: user (#ref #u8) : accepted #bool) #bool (#return accepted))\n\
         (#fn perform (: user (#ref #u8)) () (#return ()))\n\
         (#fn entry ({parameters}) () {body})"
    );
    lim::check_types(&lim::parse_program(&source).unwrap()).unwrap();
    let claim = validation_claim("entry");
    theorem(&format!("{source} (#theorem claim {claim})"), "claim").unwrap();

    let no_event = format!(
        "{source} (#fn quiet ({parameters}) () (#return ())) (#theorem claim {})",
        validation_claim("quiet")
    );
    lim::check_types(&lim::parse_program(&no_event).unwrap()).unwrap();
    theorem(&no_event, "claim").unwrap();
}

#[test]
fn loop_alias_uncertainty_remains_an_induction_failure() {
    let source = r#"
      (#fn validate (: user (#ref #u8) : accepted #bool) #bool (#return accepted))
      (#fn perform (: user (#ref #u8)) () (#return ()))
      (#fn entry (: first (#ref #u8) : second (#ref #u8) : count #u8) ()
        (#let checked #bool (#call validate (: user second : accepted true)))
        (#let-mut remaining #u8 count)
        (#label again (#while (#u8::gt remaining 0u8)
          (#let failed #bool (#call validate (: user first : accepted false)))
          (#if checked (#call perform (: user second)))
          (#set remaining (#u8::sub-wrap remaining 1u8))))
        (#return ()))
    "#;
    lim::check_types(&lim::parse_program(source).unwrap()).unwrap();
    let claim = validation_claim("entry");
    let theorem_source = |claim: &str| {
        format!(
        "{source} (#theorem claim (#proof-loop-limit 1 (#proof-with-invariants ((entry again (#proof-implies checked (#proof-validated (#parameter-of validate user) second)) remaining)) {claim})))"
    )
    };
    assert_outcome(&theorem_source(&claim), ProofOutcome::InductionFailure);
    assert_outcome(
        &theorem_source(&format!("(#proof-not {claim})")),
        ProofOutcome::InductionFailure,
    );
}

#[test]
fn seven_same_type_roots_exceed_the_alias_partition_bound() {
    let names = (0..7).map(|index| format!("r{index}")).collect::<Vec<_>>();
    let parameters = names
        .iter()
        .map(|name| format!(": {name} (#ref #u8)"))
        .collect::<Vec<_>>()
        .join(" ");
    let source = format!(
        "(#fn validate (: user (#ref #u8) : accepted #bool) #bool (#return accepted))\n\
         (#fn perform (: user (#ref #u8)) () (#return ()))\n\
         (#fn entry ({parameters}) () (#let valid #bool (#call validate (: user r6 : accepted true)))\
         (#let failed #bool (#call validate (: user r0 : accepted false)))\
         (#call perform (: user r6)) (#return ()))"
    );
    lim::check_types(&lim::parse_program(&source).unwrap()).unwrap();
    let claim = validation_claim("entry");
    assert_outcome(
        &format!("{source} (#theorem claim {claim})"),
        ProofOutcome::ResourceLimit,
    );
    assert_outcome(
        &format!("{source} (#theorem claim (#proof-not {claim}))"),
        ProofOutcome::ResourceLimit,
    );
}

#[test]
fn pinned_parents_with_possible_self_references_keep_the_conservative_guard() {
    let source = r#"
      (#struct Frame () (: value #u8 : first (#pin-ref #u8) : second (#pin-ref #u8)))
      (#fn validate (: user (#pin-ref #u8) : accepted #bool) #bool (#return accepted))
      (#fn perform (: user (#pin-ref #u8)) () (#return ()))
      (#fn entry (: frame (#pin-ref-mut Frame)) ()
        (#let valid #bool (#call validate (: user (#get frame second) : accepted true)))
        (#let failed #bool (#call validate (: user (#get frame first) : accepted false)))
        (#let restored #bool (#call validate (: user (#get frame first) : accepted true)))
        (#let rejected #bool (#call validate (: user (#pin-borrow (#get frame value)) : accepted false)))
        (#call perform (: user (#get frame second)))
        (#return ()))
    "#;
    lim::check_types(&lim::parse_program(source).unwrap()).unwrap();
    let claim = validation_claim("entry");
    assert_outcome(
        &format!("{source} (#theorem claim {claim})"),
        ProofOutcome::Unsupported,
    );
    assert_outcome(
        &format!("{source} (#theorem claim (#proof-not {claim}))"),
        ProofOutcome::Unsupported,
    );
    let simpler = source
        .replace(
            "(#let failed #bool (#call validate (: user (#get frame first) : accepted false)))",
            "",
        )
        .replace(
            "(#let restored #bool (#call validate (: user (#get frame first) : accepted true)))",
            "",
        );
    assert_outcome(
        &format!("{simpler} (#theorem claim {claim})"),
        ProofOutcome::Unsupported,
    );
}
