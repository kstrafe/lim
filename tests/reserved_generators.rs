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
    compile("#generate #optional ((type #u64) (name Maybe))\n#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 42u64)\n  );\n}\n")
        .unwrap();
    let error = compile("#generate optional ((type #u64) (name Maybe))\n").unwrap_err();
    assert!(error.message.contains("unknown"), "{error:?}");
    // Unprefixed names genuinely belong to users, even if a reserved builtin
    // has the same suffix. There is no ambiguity or special-case dispatch.
    compile(
        "#gn optional {} `((#type UserWord #u64))
#generate optional {}
#generate #optional ((type UserWord) (name Maybe))
#fn main {
  #params = ();
  #returns = #u64;
  #body = ( (#return 42u64)\n  );\n}\n",
    )
    .unwrap();
    compile(
        "#gn cell {} `((#type UserCell #u64))
#generate cell {}
#fn main {
  #params = ();
  #returns = #u64;
  #body = ( (#return 42u64)\n  );\n}\n",
    )
    .unwrap();
}

#[test]
fn users_and_generated_output_cannot_declare_reserved_names() {
    for source in [
        "#gn #optional {} ()\n",
        "#gn #future-library-generator {} ()\n",
        "#gn-fn #helper {} ()\n",
        "#gn #cell { value-type; name; create; get; set; } ()\n",
        "#struct #Future () ()\n",
        "#struct Ordinary () ((#field #u64))\n",
        "#struct Ordinary () ((#mut Ordinary))\n",
        "#struct Ordinary (#repr-c) ((#field #u64))\n",
        "#enum Ordinary () (#Case)\n",
        "#type #Word #u64\n",
        "#fn #future-function {\n  #params = ();\n  #returns = ();\n  #body = ( (#return ())\n  );\n}\n",
        "#fn ordinary {\n  #params = ((#argument #u64));\n  #returns = ();\n  #body = ( (#return ())\n  );\n}\n",
        "#fn ordinary {\n  #params = ();\n  #returns = ();\n  #body = ( (#let #local #u64 1u64) (#return ())\n  );\n}\n",
        "#fn ordinary {\n  #params = ();\n  #returns = ();\n  #body = ( (#for-range (#local #usize) 0usize 1usize ()) (#return ())\n  );\n}\n",
        "#gn emit {} (#gn-for-each #local () ())\n#generate emit {}\n",
        "#gn emit {} `((#struct #Future () ()))\n#generate emit {}\n",
        "#generate #optional ((type #u64) (name #Maybe))\n",
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
        "#alias cell-generator = #std/cell.lim::cell\n".to_owned(),
        format!("#alias cell-generator = \"{}::cell\"\n", library.display()),
    ] {
        compile(&format!(
            "{import}
#generate cell-generator {{ value-type = #u64; name = Cell; create = create-cell; get = get-cell; set = set-cell; }}
#fn main {{
  #params = ();
  #returns = #u64;
  #body = ( (#return 42u64)\n  );\n}}\n"
        ))
        .unwrap();
    }
}

#[test]
fn bundled_standard_generator_uses_an_ordinary_prelude_alias() {
    compile(
        "#std
#generate utf8-view { config = ((name ByteView) (owner (#slice #u8))); }
#fn main {
  #params = ();
  #returns = #u64;
  #body = ( (#return 42u64)\n  );\n}\n",
    )
    .unwrap();
}

#[test]
fn reserved_binding_error_points_to_the_identifier_not_the_function_header() {
    let source = "#fn ordinary {\n  #params = ();\n  #returns = ();\n  #body = (\n    (#let #local #u64 1u64)\n    (#return ())\n  );\n}\n";
    let error = compile(source).unwrap_err();
    let span = error.span.unwrap();
    assert_eq!(span.line, 5);
    assert_eq!(&source[span.start..span.end], "#local");
}
