fn check(source: &str) -> Result<(), String> {
    lim::check_types(&lim::parse_program(source)?)
}

#[test]
fn reserved_certificate_names_cannot_be_guessed_through_global_use() {
    let source = "(#theorem native true)
      (#theorem forged
        (#universes)
        (#parameters)
        (#statement #pt-false)
        (#proof (#pt-use $certificate:native ())))";
    assert!(check(source).is_err());
}

#[test]
fn metadata_lists_and_binders_do_not_turn_names_into_runtime_keywords() {
    check(
        "(#math-definition identity (index)
        (#pt-pi (: index-value (#pt-type index) : value index-value) index-value)
        (#pt-lambda (: index-value (#pt-type index) : value index-value) value))
      (#math-definition specialized (index)
        (#pt-pi (: value #pt-nat) #pt-nat)
        (#pt-app (#pt-use identity (index)) #pt-nat))",
    )
    .unwrap_err();
    // Nat belongs to Type 0, so specialize at level zero explicitly.
    check(
        "(#math-definition identity (index)
        (#pt-pi (: index-value (#pt-type index) : value index-value) index-value)
        (#pt-lambda (: index-value (#pt-type index) : value index-value) value))
      (#math-definition specialized ()
        (#pt-pi (: value #pt-nat) #pt-nat)
        (#pt-app (#pt-use identity (0)) #pt-nat))",
    )
    .unwrap();
    check(
        "(#math-definition identity (index)
        (#pt-pi (: a (#pt-type index) : value a) a)
        (#pt-lambda (: a (#pt-type index) : value a) value))
      (#math-definition partial (index)
        (#pt-pi (: a (#pt-type index) : value a) a)
        (#pt-lambda (: a (#pt-type index))
          (#pt-app (#pt-use identity (index)) a)))",
    )
    .unwrap();
}

#[test]
fn beta_reduction_cannot_capture_an_outer_variable() {
    let prefix = "(#math-definition first ()
      (#pt-pi (: left #pt-nat : right #pt-nat) #pt-nat)
      (#pt-lambda (: left #pt-nat : right #pt-nat) left))";
    check(&format!(
        "{prefix} (#theorem valid
  (#universes)
  (#parameters
    (#parameter outer #pt-nat))
  (#statement (#pt-eq #pt-nat
        (#pt-app (#pt-use first ()) outer #pt-zero) outer))
  (#proof (#pt-refl #pt-nat outer)))"
    ))
    .unwrap();
    assert!(check(&format!(
        "{prefix} (#theorem invalid
  (#universes)
  (#parameters
    (#parameter outer #pt-nat))
  (#statement (#pt-eq #pt-nat
        (#pt-app (#pt-use first ()) outer #pt-zero) #pt-zero))
  (#proof (#pt-refl #pt-nat #pt-zero)))"
    ))
    .is_err());
}

#[test]
fn independent_inductive_families_cannot_exchange_constructors() {
    assert!(check(
        "(#math-inductive left () () (#pt-type 0) ((make ())))
      (#math-inductive right () () (#pt-type 0) ((make ())))
      (#math-definition forged () (#pt-use left ())
        (#pt-construct right () () make ()))"
    )
    .is_err());
}

#[test]
fn oversized_flat_applications_are_rejected_before_building_deep_term_spines() {
    let arguments = " #pt-zero".repeat(10_000);
    let error = check(&format!(
        "(#math-definition oversized () #pt-nat
      (#pt-app #pt-zero{arguments}))"
    ))
    .unwrap_err();
    assert!(error.contains("argument limit"), "{error}");
}

#[test]
fn numeral_and_universe_limits_never_wrap_into_valid_proofs() {
    for source in [
        "(#math-definition bad () #pt-nat (#pt-numeral 129))",
        "(#math-definition bad () (#pt-type 65535) (#pt-type 65535))",
        "(#math-definition bad () (#pt-type -1) #pt-zero)",
    ] {
        assert!(check(source).is_err(), "{source}");
    }
}

#[test]
fn theorem_bodies_cannot_refer_to_future_native_certificates_that_failed() {
    assert!(check(
        "(#theorem forged
  (#universes)
  (#parameters)
  (#statement (#pt-program failed))
  (#proof (#pt-certificate failed)))
      (#theorem failed (#proof-eq 1u8 2u8))"
    )
    .is_err());
}
