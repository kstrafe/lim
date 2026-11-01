use lim::{check_theorem_from_path_with_config, check_types, parse_program, CompileConfig};

mod support;

fn check(source: &str) -> Result<(), String> {
    check_types(&parse_program(source)?)
}

fn parsed_but_unchecked(source: &str) {
    let program = parse_program(source).unwrap();
    let error = check_types(&program).unwrap_err();
    assert!(
        !error.contains("resource limit"),
        "resource failure masked rejection: {error}\n{source}"
    );
}

#[test]
fn opaque_values_are_checked_then_hidden_from_conversion() {
    check("(#math-opaque hidden () #pt-nat #pt-zero)").unwrap();
    assert!(check(
        "(#math-opaque hidden () #pt-nat #pt-zero)
        (#theorem bad (#universes) (#parameters)
          (#statement (#pt-eq #pt-nat (#pt-use hidden ()) #pt-zero))
          (#proof (#pt-refl #pt-nat #pt-zero)))"
    )
    .is_err());
}

#[test]
fn opaque_values_require_well_typed_closed_acyclic_bodies() {
    for source in [
        "(#math-opaque bad () #pt-nat (#pt-type 0))",
        "(#math-opaque bad () #pt-nat (#pt-let (#parameter unused #pt-nat) (#pt-type 0) #pt-zero))",
        "(#math-opaque bad () #pt-nat missing)",
        "(#math-opaque bad () #pt-nat (#pt-use absent ()))",
        "(#math-opaque bad () #pt-nat (#pt-use bad ()))",
    ] {
        parsed_but_unchecked(source);
    }
}

#[test]
fn opaque_propositions_are_not_theorem_targets() {
    check("(#math-opaque proposition () #pt-prop #pt-false)").unwrap();
    check("(#math-opaque opaque-evidence () (#pt-eq #pt-nat #pt-zero #pt-zero) (#pt-refl #pt-nat #pt-zero))").unwrap();
    let source = "(#math-opaque opaque-evidence () (#pt-eq #pt-nat #pt-zero #pt-zero) (#pt-refl #pt-nat #pt-zero))";
    let scratch = support::Scratch::new("kernel-opaque-theorem-target");
    let error = check_theorem_from_path_with_config(
        source,
        &scratch.path().join("main.lim"),
        &CompileConfig::default(),
        "opaque-evidence",
    )
    .unwrap_err();
    assert!(error.message.contains("not a theorem"), "{error:?}");
}

#[test]
fn aliases_and_generated_opaque_declarations_are_checked() {
    let scratch = support::Scratch::new("kernel-opaque-alias");
    std::fs::write(
        scratch.path().join("lib.lim"),
        "(#export hidden)\n(#math-opaque hidden () #pt-nat #pt-zero)",
    )
    .unwrap();
    let source = "(#alias visible = ./lib.lim::hidden)\n(#math-definition use () #pt-nat (#pt-use visible ()))";
    let program = lim::parse_program_from_path(source, &scratch.path().join("main.lim")).unwrap();
    check_types(&program).unwrap();

    let generated = "(#gn emit () `((#math-opaque generated () #pt-nat #pt-zero))) (#generate emit) (#math-definition use () #pt-nat (#pt-use generated ()))";
    check(generated).unwrap();
}

#[test]
fn internal_opaque_wrappers_cannot_be_injected_as_source() {
    for source in [
        "(#proof-opaque hidden () #pt-nat #pt-zero)",
        "(#theorem forged (#proof-opaque () #pt-nat #pt-zero))",
        "(#theorem forged (proof-opaque () #pt-nat #pt-zero))",
    ] {
        match parse_program(source) {
            Ok(program) => {
                let error = check_types(&program).unwrap_err();
                assert!(
                    !error.contains("resource limit"),
                    "resource failure masked rejection: {error}\n{source}"
                );
            }
            Err(_) => (),
        }
    }
}
