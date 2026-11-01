fn check(source: &str) -> Result<(), String> {
    lim::check_types(&lim::parse_program(source)?)
}

const REFLEXIVITY: &str = "(#theorem reflexivity
  (#universes u)
  (#parameters (#parameter a (#pt-type u)) (#parameter value a))
  (#statement (#pt-eq a value value))
  (#proof (#pt-refl a value)))";

#[test]
fn shared_parameters_are_declared_once_and_scope_both_statement_and_evidence() {
    check(REFLEXIVITY).unwrap();
    assert_eq!(REFLEXIVITY.matches("#parameter a ").count(), 1);
    check(&format!(
        "{REFLEXIVITY}
      (#theorem specialized (#universes) (#parameters)
        (#statement (#pt-eq #pt-nat #pt-zero #pt-zero))
        (#proof (#pt-app (#pt-use reflexivity (0)) #pt-nat #pt-zero)))"
    ))
    .unwrap();
}

#[test]
fn malformed_or_ambiguous_clause_structures_are_rejected() {
    for source in [
        "(#theorem missing (#universes) (#statement #pt-false) (#proof #pt-zero))",
        "(#theorem duplicate (#universes) (#parameters) (#statement #pt-false) (#statement #pt-false) (#proof #pt-zero))",
        "(#theorem reordered (#parameters) (#universes) (#statement #pt-false) (#proof #pt-zero))",
        "(#theorem extra (#universes) (#parameters) (#statement #pt-false #pt-false) (#proof #pt-zero))",
        "(#theorem bad (#universes) (#parameters (#parameter value)) (#statement #pt-false) (#proof #pt-zero))",
        "(#proof obsolete true)",
        "(#theorem obsolete (#proof-theorem () #pt-false #pt-zero))",
        "(#theorem obsolete (#proof-definition () #pt-nat #pt-zero))",
    ] {
        assert!(check(source).is_err(), "accepted {source}");
    }
}

#[test]
fn parameters_are_sequential_and_never_shadow_or_escape() {
    for source in [
        "(#theorem bad (#universes u) (#parameters (#parameter value a) (#parameter a (#pt-type u))) (#statement (#pt-eq a value value)) (#proof (#pt-refl a value)))",
        "(#theorem bad (#universes u) (#parameters (#parameter a (#pt-type u)) (#parameter a (#pt-type u))) (#statement #pt-false) (#proof a))",
        "(#theorem bad (#universes u) (#parameters (#parameter u #pt-nat)) (#statement #pt-false) (#proof u))",
    ] {
        assert!(check(source).is_err(), "accepted {source}");
    }
    assert!(check(&format!(
        "{REFLEXIVITY}
      (#math-definition escaped () #pt-nat value)"
    ))
    .is_err());
}

#[test]
fn formatting_retains_the_checked_declarations_and_explicit_bindings() {
    let source = include_str!("../examples/mathematical_proofs.lim");
    let formatted = lim::format_source(source).unwrap();
    assert_eq!(
        lim::parse_program(source).unwrap().items,
        lim::parse_program(&formatted).unwrap().items
    );
    check(&formatted).unwrap();
    assert!(formatted.contains("(#parameter a (#pt-type u))"));
}

#[test]
fn procedural_predicates_still_require_prefixed_keywords() {
    assert!(check("(#theorem bad (proof-eq 1u8 1u8))").is_err());
    check("(#theorem valid (#proof-eq 1u8 1u8))").unwrap();
}
