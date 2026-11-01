mod support;

fn compile(source: &str) -> Result<String, lim::Diagnostic> {
    let scratch = support::Scratch::new("reserved-generators");
    lim::compile_source_to_assembly(
        source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
}

#[test]
fn builtin_names_are_reserved_and_old_spellings_have_no_compatibility_route() {
    compile("(#generate #optional (: type #u64 : name Maybe)) (#fn main () #u64 (#return 42u64))")
        .unwrap();
    let error = compile("(#generate optional (: type #u64 : name Maybe))").unwrap_err();
    assert!(error.message.contains("unknown"), "{error:?}");
    // Unprefixed names genuinely belong to users, even if a reserved builtin
    // has the same suffix. There is no ambiguity or special-case dispatch.
    compile(
        "(#gn optional () `((#type UserWord #u64))) (#generate optional)
      (#generate #optional (: type UserWord : name Maybe))
      (#fn main () #u64 (#return 42u64))",
    )
    .unwrap();
    compile(
        "(#gn cell () `((#type UserCell #u64))) (#generate cell)
      (#fn main () #u64 (#return 42u64))",
    )
    .unwrap();
}

#[test]
fn users_and_generated_output_cannot_declare_reserved_names() {
    for source in [
        "(#gn #optional () ())",
        "(#gn #future-library-generator () ())",
        "(#gn-fn #helper () ())",
        "(#gn #cell (value-type name create get set) ())",
        "(#struct #Future () ())",
        "(#struct Ordinary () ((#field #u64)))",
        "(#struct Ordinary () ((#mut Ordinary)))",
        "(#struct Ordinary (#repr-c) ((#field #u64)))",
        "(#enum Ordinary () (#Case))",
        "(#type #Word #u64)",
        "(#fn #future-function () () (#return ()))",
        "(#fn ordinary ((#argument #u64)) () (#return ()))",
        "(#fn ordinary () () (#let #local #u64 1u64) (#return ()))",
        "(#fn ordinary () () (#for-range (#local #usize) 0usize 1usize ()) (#return ()))",
        "(#gn emit () (#gn-for-each #local () ())) (#generate emit)",
        "(#gn emit () `((#struct #Future () ()))) (#generate emit)",
        "(#generate #optional (: type #u64 : name #Maybe))",
    ] {
        let error = compile(source).unwrap_err();
        assert!(error.message.contains("reserved"), "{source}: {error:?}");
        assert!(error.span.is_some(), "{source}: {error:?}");
    }
}

#[test]
fn standard_generators_can_be_explicitly_aliased() {
    let library = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("library/cell.lim");
    for import in [
        format!("(#alias cell-generator = \"{}::#cell\")", library.display()),
        format!("(#alias cell-generator = \"{}::#cell\")", library.display()),
    ] {
        compile(&format!(
            "{import}
          (#generate cell-generator #u64 Cell create-cell get-cell set-cell)
          (#fn main () #u64 (#return 42u64))"
        ))
        .unwrap();
    }
}

#[test]
fn bundled_standard_generator_uses_the_same_reserved_spelling() {
    compile(
        "(#std) (#generate #utf8-view (: name ByteView : owner (#slice #u8)))
      (#fn main () #u64 (#return 42u64))",
    )
    .unwrap();
}

#[test]
fn reserved_binding_error_points_to_the_identifier_not_the_function_header() {
    let source = "(#fn ordinary () ()\n  (#let #local #u64 1u64)\n  (#return ()))";
    let error = compile(source).unwrap_err();
    let span = error.span.unwrap();
    assert_eq!(span.line, 2);
    assert_eq!(&source[span.start..span.end], "#local");
}
