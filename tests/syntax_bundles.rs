use lim::parse_program;
mod support;

#[test]
fn bundles_expand_parameters_calls_and_nested_forward_references() {
    let source = r#"
        (#syntax Parameters ((value u64)))
        (#syntax Arguments ((value (#syntax-splice Value))))
        (#syntax Value ((#syntax-splice Number)))
        (#syntax Number (42u64))
        (#syntax Empty ())
        (#fn identity ((#syntax-splice Parameters)) u64 (#return value))
        (#fn main ((#syntax-splice Empty)) u64
          (#return (#call identity ((#syntax-splice Arguments)))))
    "#;
    parse_program(source).unwrap();
}

#[test]
fn rejects_invalid_bundles_even_when_unused() {
    for (source, expected) in [
        (
            "(#syntax A ((#syntax-splice B))) (#syntax B ((#syntax-splice A)))",
            "recursive syntax bundle",
        ),
        (
            "(#syntax A ((#syntax-splice Missing)))",
            "unknown syntax bundle",
        ),
        ("(#syntax A 42)", "literal list"),
        ("(#syntax A ()) (#syntax A ())", "duplicate syntax bundle"),
        ("(#syntax-splice A)", "surrounding list"),
        ("(#syntax A ((#syntax-splice)))", "exactly one"),
        (
            "(#syntax A ()) (#fn A () () (#return ()))",
            "conflicts with a syntax bundle",
        ),
        (
            "(#fn main () () (#syntax A ()) (#return ()))",
            "only allowed at top level",
        ),
        (
            "(#syntax Value ()) (#fn main ((Value u64)) u64 (#return Value))",
            "shadowing is not allowed",
        ),
    ] {
        let error = parse_program(source).unwrap_err();
        assert!(error.contains(expected), "{source}: {error}");
    }
}

#[test]
fn generated_templates_can_emit_bundles() {
    parse_program(
        r#"
      (#gn emit () `((#syntax Value (42u64))
        (#fn generated () u64 (#return (#syntax-splice Value)))))
      (@emit)
      (#fn main () u64 (#return (#call generated ())))
    "#,
    )
    .unwrap();
}

#[test]
fn bundles_expand_literal_generator_arguments() {
    parse_program(
        r#"
      (#syntax Arguments (Answer u64))
      (#gn make (name ty) `((#type ,name ,ty)))
      (@make (#syntax-splice Arguments))
      (#fn main () u64 (#return 42u64))
    "#,
    )
    .unwrap();
}

#[test]
fn imported_bundles_are_prefixed_and_checked_at_the_use() {
    let scratch = support::Scratch::new("syntax-bundles");
    std::fs::write(
        scratch.path().join("library.lim"),
        "(#syntax Value (42u64)) (#fn answer () u64 (#return (#syntax-splice Value)))",
    )
    .unwrap();
    let source = "(#import-external \"library.lim\" ext-)\n(#fn main () u64 (#return (#syntax-splice ext-Value)))";
    lim::parse_program_from_path(source, &scratch.path().join("main.lim")).unwrap();
    let source = "(#syntax Bad (false))\n(#fn main () u64 (#return (#syntax-splice Bad)))";
    let error = lim::compile_source_to_assembly(
        source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err();
    let span = error.span.unwrap();
    assert_eq!(
        &source[span.start..span.end],
        "(#syntax-splice Bad)",
        "{error:?}"
    );
    assert!(
        error
            .labels
            .iter()
            .any(|label| label.message.contains("syntax bundle defined")),
        "{error:?}"
    );
}

#[test]
fn expanding_bundles_has_a_bounded_output_size() {
    let mut source = "(#syntax B0 (x x))\n".to_owned();
    for i in 1..25 {
        source.push_str(&format!(
            "(#syntax B{i} ((#syntax-splice B{}) (#syntax-splice B{})))\n",
            i - 1,
            i - 1
        ));
    }
    assert!(parse_program(&source).unwrap_err().contains("node limit"));
}

#[test]
fn changing_a_bundle_invalidates_generated_code_cache() {
    let scratch = support::Scratch::new("syntax-bundle-cache");
    let path = scratch.path().join("main.lim");
    let cache = scratch.path().join("cache");
    let compile = |value| {
        let source = format!(
            r#"
          (#syntax Value ({value}u64))
          (#gn emit (value) `((#fn answer () u64 (#return ,value))))
          (@emit (#syntax-splice Value))
          (#fn main () u64 (#return (#call answer ())))
        "#
        );
        lim::compile_source_to_assembly(
            &source,
            &path,
            &lim::CompileConfig::default(),
            &cache,
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap()
    };
    let first = compile(42);
    assert_eq!(first, compile(42));
    assert_ne!(first, compile(43));
}

#[test]
fn cfg_selection_precedes_bundle_collection() {
    let mut config = lim::CompileConfig::default();
    config.set("backend", "asm");
    lim::parse_program_with_config(
        r#"
      (#cfg-if (#cfg-is #backend asm)
        (#syntax Value (42u64))
        (#cfg-else (#syntax Value ((#syntax-splice Missing)))))
      (#fn main () u64 (#return (#syntax-splice Value)))
    "#,
        &config,
    )
    .unwrap();
}
