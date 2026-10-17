mod support;

use std::fs;

fn check(source: &str) -> Result<(), lim::Diagnostic> {
    let scratch = support::Scratch::new("declaration-wellformedness");
    lim::check_source_with_generated_sources(
        source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join(".lim/cache"),
        &scratch.path().join(".lim/generated"),
    )
}

#[test]
fn unused_unknown_payloads_and_aliases_fail_at_the_missing_type_token() {
    for declaration in [
        "(#enum Broken () ((Bad MissingType)))",
        "(#enum Broken () ((Bad 42 (#ref MissingType))))",
        "(#struct Broken () ((payload (#tuple #u64 (#ref MissingType)))))",
        "(#type Broken (#ptr MissingType))",
        "(#struct Broken () ((payload Alias))) (#type Alias MissingType)",
    ] {
        let source = format!("{declaration}\n(#fn main () #u64 (#return 0u64))");
        let error = check(&source).unwrap_err();
        assert_eq!(error.code, lim::DiagnosticCode::Type, "{error:?}");
        assert!(
            error.message.contains("undeclared type 'MissingType'"),
            "{error:?}"
        );
        let text = error.source_text.as_deref().unwrap();
        let span = error.span.unwrap();
        assert_eq!(&text[span.start..span.end], "MissingType", "{error:?}");
    }
}

#[test]
fn forward_references_and_indirected_cycles_remain_valid() {
    for source in [
        "(#struct First () ((payload Second))) (#enum Second () ((Value Alias))) (#type Alias #u64)",
        "(#struct First () ((next (#ptr Second)))) (#enum Second () ((Back (#ptr First))))",
        "(#struct First () ((next (#ref Second)))) (#struct Second () ((back (#ref First))))",
    ] { check(source).unwrap_or_else(|error| panic!("{error:?}")); }
}

#[test]
fn unused_by_value_cycles_are_rejected_without_layout_recursion() {
    for source in [
        "(#struct A () ((payload A)))",
        "(#enum A () ((Again A)))",
        "(#enum A () ((Again 42 A)))",
        "(#struct A () ((payload (#tuple #u64 (#array B 1))))) (#enum B () ((Back A)))",
        "(#type Alias A) (#struct A () ((payload Alias)))",
        "(#type A B) (#type B A)",
    ] {
        let error = check(source).unwrap_err();
        assert!(
            error.message.contains("cycle")
                || error.message.contains("cyclic")
                || error.message.contains("recursive"),
            "{error:?}"
        );
        assert!(error.span.is_some(), "{error:?}");
    }
    let source = "(#struct A () ((payload A)))";
    let error = check(source).unwrap_err();
    assert_eq!(error.span.unwrap().start, source.rfind('A').unwrap());
}

#[test]
fn imported_and_generated_unused_payload_errors_keep_exact_sources() {
    let scratch = support::Scratch::new("declaration-wellformedness-import");
    let entry = scratch.path().join("main.lim");
    let module = scratch.path().join("types.lim");
    let declaration = "(#enum Broken () ((Bad MissingType)))";
    fs::write(&module, declaration).unwrap();
    let source = "(#import \"types.lim\") (#fn main () #u64 (#return 0u64))";
    let error = lim::check_source_with_generated_sources(
        source,
        &entry,
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        &scratch.path().join("generated"),
    )
    .unwrap_err();
    assert_eq!(error.source_name.as_deref(), module.to_str());
    let span = error.span.unwrap();
    assert_eq!(&declaration[span.start..span.end], "MissingType");

    let source = format!("(#gn emit () `({declaration}))\n(@emit)");
    for _ in 0..2 {
        let error = lim::check_source_with_generated_sources(
            &source,
            &entry,
            &lim::CompileConfig::default(),
            &scratch.path().join("cache"),
            &scratch.path().join("generated"),
        )
        .unwrap_err();
        let span = error.span.unwrap();
        assert_eq!(
            &error.source_text.as_ref().unwrap()[span.start..span.end],
            "MissingType"
        );
        assert!(!error.expansion_provenance.is_empty(), "{error:?}");
    }
}
