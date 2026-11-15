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
        "#enum Broken () ((Broken.Bad MissingType))\n",
        "#enum Broken () ((Broken.Bad 42 (#ref MissingType)))\n",
        "#struct Broken () ((payload (#tuple #u64 (#ref MissingType))))\n",
        "#type Broken (#ptr MissingType)\n",
        "#struct Broken () ((payload Alias))\n#type Alias MissingType\n",
    ] {
        let source = format!("{declaration}\n#fn main {{\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 0u64)\n  );\n}}\n");
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
        "#struct First () ((payload Second))\n#enum Second () ((Second.Value Alias))\n#type Alias #u64\n",
        "#struct First () ((next (#ptr Second)))\n#enum Second () ((Second.Back (#ptr First)))\n",
        "#struct First () ((next (#ref Second)))\n#struct Second () ((back (#ref First)))\n",
    ] { check(source).unwrap_or_else(|error| panic!("{error:?}")); }
}

#[test]
fn unused_by_value_cycles_are_rejected_without_layout_recursion() {
    for source in [
        "#struct A () ((payload A))\n",
        "#enum A () ((A.Again A))\n",
        "#enum A () ((A.Again 42 A))\n",
        "#struct A () ((payload (#tuple #u64 (#array B 1))))\n#enum B () ((B.Back A))\n",
        "#type Alias A\n#struct A () ((payload Alias))\n",
        "#type A B\n#type B A\n",
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
    let source = "#struct A () ((payload A))\n";
    let error = check(source).unwrap_err();
    assert_eq!(error.span.unwrap().start, source.rfind('A').unwrap());
}

#[test]
fn imported_and_generated_unused_payload_errors_keep_exact_sources() {
    let scratch = support::Scratch::new("declaration-wellformedness-import");
    let entry = scratch.path().join("main.lim");
    let module = scratch.path().join("types.lim");
    let declaration = "#enum Broken () ((Broken.Bad MissingType))\n";
    fs::write(&module, declaration).unwrap();
    let source = "#alias Broken = ./types.lim::Broken\n#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 0u64)\n  );\n}\n";
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

    let source = format!("#gn emit () `(({declaration}))\n#generate emit\n");
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
