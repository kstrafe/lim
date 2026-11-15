mod support;

fn expand(expression: &str) -> Result<String, lim::Diagnostic> {
    let scratch = support::Scratch::new("generator-syntax-values");
    let source = format!(
        "#gn alias (options) `((#type ,{expression} #u64))
#generate alias ((name Word) (suffix \"Alias\"))
#fn main {{
  #params = ();
  #returns = #u64;
  #body = ( (#return 42u64)\n  );\n}}\n"
    );
    lim::compile_source_to_assembly(
        &source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
}

#[test]
fn named_syntax_lookup_and_identifier_composition_are_literal_operations() {
    for expression in [
        "(#gn-get options name)",
        "(#gn-get options absent Fallback)",
        "(#gn-get options name (#gn-error \"unused fallback must not run\"))",
        "(#gn-symbol-append (#gn-get options name) (#gn-get options suffix))",
        "(#gn-symbol-append Word Alias)",
        "(#gn-gensym \"task\")",
        "(#gn-gensym (#gn-get ((hint \"task\")) hint))",
    ] {
        expand(expression).unwrap();
    }
}

#[test]
fn syntax_lookup_and_symbol_composition_fail_with_invocation_spans() {
    for (expression, expected) in [
        ("(#gn-get options absent)", "missing key"),
        ("(#gn-get ((name Word) (name Other)) name)", "repeats key"),
        ("(#gn-get ((name Word) (malformed)) name)", "pairs"),
        ("(#gn-get (name Word) name)", "pairs"),
        ("(#gn-get options 1)", "symbol key"),
        ("(#gn-get options)", "requires"),
        (
            "(#gn-symbol-append Word \" extra\")",
            "one ordinary identifier",
        ),
        ("(#gn-symbol-append Word \"()\")", "one ordinary identifier"),
        ("(#gn-symbol-append 1 \"-alias\")", "symbol base"),
        ("(#gn-symbol-append Word 1)", "suffix"),
        ("(#gn-symbol-append Word)", "requires"),
        ("(#gn-gensym)", "requires"),
        ("(#gn-gensym \"task\" \"extra\")", "requires"),
        ("(#gn-gensym task)", "string hint"),
        ("(#gn-gensym 1)", "string hint"),
        ("(#gn-gensym \"\")", "ordinary identifier"),
        ("(#gn-gensym \"task other\")", "ordinary identifier"),
        ("(#gn-gensym \"#let\")", "ordinary identifier"),
        ("(#gn-gensym \"lim.gensym.fake\")", "ordinary identifier"),
        ("(#gn-symbol \"lim.gensym.fake\")", "cannot forge"),
        ("(#gn-symbol \"word lim.gensym.fake\")", "one identifier"),
        (
            "(#gn-symbol-append (#gn-gensym \"task\") \"-other\")",
            "cannot alter",
        ),
    ] {
        let error = expand(expression).unwrap_err();
        assert!(error.message.contains(expected), "{expression}: {error:?}");
        let span = error
            .span
            .expect("generator error must have an invocation span");
        assert_eq!(span.source_id, 0);
        assert_eq!(span.line, 2);
        assert!(span.end > span.start);
    }
}

#[test]
fn symbol_append_inserts_double_colons_for_literal_suffixes_and_nested_calls() {
    for (expression, expected) in [
        ("(#gn-symbol-append Word \"alias\")", "Word::alias"),
        ("(#gn-symbol-append Word alias)", "Word::alias"),
        (
            "(#gn-symbol-append (#gn-symbol-append Word State) Ready)",
            "Word::State::Ready",
        ),
        (
            "(#gn-symbol-append Word::State Ready)",
            "Word::State::Ready",
        ),
        ("(#gn-symbol-append Word \"::alias\")", "Word::::alias"),
        ("(#gn-symbol-append Word \"-alias\")", "Word::-alias"),
    ] {
        expand(&format!(
            "(#gn-if (#gn-equal {expression} {expected}) Word (#gn-error \"incorrect symbol join\"))"
        ))
        .unwrap();
    }
    // Joining cannot accidentally enter the compiler-owned gensym domain.
    expand("(#gn-if (#gn-equal (#gn-symbol-append lim. \"gensym.fake\") lim.::gensym.fake) Word (#gn-error \"incorrect gensym join\"))").unwrap();
}

#[test]
fn source_cannot_claim_gensym_identity_and_parser_can_inspect_generated_syntax() {
    let source =
        "#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = (\n    (#let lim.gensym.fake #u64 42u64)\n    (#return lim.gensym.fake)\n  );\n}\n";
    lim::parse_source_unit(source).unwrap(); // Program inspection uses the same source-unit reader as compilation.
    let scratch = support::Scratch::new("gensym-source");
    let error = lim::compile_source_to_assembly(
        source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err();
    assert!(error.message.contains("reserved"), "{error:?}");
    let span = error.span.unwrap();
    assert_eq!(&source[span.start..span.end], "lim.gensym.fake");
    assert_eq!(span.line, 5);
}

#[test]
fn joined_names_are_inspectable_and_reused_from_the_generated_cache() {
    let scratch = support::Scratch::new("symbol-append-cache");
    let source = r#"
#gn emit (name)
          `((#fn ,(#gn-symbol-append name "read") () #u64 (#return 42u64)))
#generate emit Word
#fn main {
  #params = ();
  #returns = #u64;
  #body = ( (#return (#call Word::read ()))
  );
}
    "#;
    let compile = || {
        lim::compile_source_with_generated_sources(
            source,
            &scratch.path().join("main.lim"),
            &lim::CompileConfig::default(),
            &scratch.path().join(".lim/cache"),
            lim::TargetDescription::X86_64_SYSTEM_V,
            None,
            &scratch.path().join(".lim"),
        )
        .unwrap()
    };
    let cold = compile();
    let files = std::fs::read_dir(scratch.path().join(".lim/generated"))
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|extension| extension == "lim"))
        .collect::<Vec<_>>();
    assert_eq!(files.len(), 1);
    let generated = std::fs::read_to_string(&files[0]).unwrap();
    assert!(generated.contains("#fn Word::read"), "{generated}");
    let modified = std::fs::metadata(&files[0]).unwrap().modified().unwrap();
    assert_eq!(compile(), cold);
    assert_eq!(std::fs::read_to_string(&files[0]).unwrap(), generated);
    assert_eq!(
        std::fs::metadata(&files[0]).unwrap().modified().unwrap(),
        modified
    );
}

#[test]
fn imports_cannot_hide_or_construct_compiler_owned_identifiers() {
    let scratch = support::Scratch::new("gensym-import");
    let imported = scratch.path().join("module.lim");
    let compile = |source: &str| {
        lim::compile_source_to_assembly(
            source,
            &scratch.path().join("main.lim"),
            &lim::CompileConfig::default(),
            &scratch.path().join("cache"),
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap_err()
    };
    std::fs::write(&imported, "#type lim.gensym.fake #u64\n").unwrap();
    for source in [
        "#alias Value = ./module.lim::lim.gensym.fake\n",
        "#alias Value = ./module.lim::lim.gensym.fake\n",
    ] {
        let error = compile(source);
        assert!(error.message.contains("reserved"), "{error:?}");
        assert_eq!(error.span.unwrap().source_id, 1);
        assert_eq!(
            error.source_text.as_deref(),
            Some("#type lim.gensym.fake #u64\n")
        );
    }
    std::fs::write(&imported, "#fn gensym.fake {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 42u64)\n  );\n}\n").unwrap();
    let source = "#alias lim.gensym.fake = ./module.lim::gensym.fake\n";
    let error = compile(source);
    let span = error.span.unwrap();
    assert_eq!(&source[span.start..span.end], "lim.gensym.fake");
    assert!(error.message.contains("reserved"), "{error:?}");
}

#[test]
fn ordinary_generator_symbols_still_cannot_shadow_parameters() {
    let scratch = support::Scratch::new("gensym-no-implicit-hygiene");
    let source = "#gn emit (name) `((#fn ,name ((task #u64)) #u64
          (#let task #u64 42u64) (#return task)))\n#generate emit work\n";
    let error = lim::compile_source_to_assembly(
        source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err();
    assert!(error.message.contains("shadows"), "{error:?}");
}

#[test]
fn cached_generated_gensym_type_errors_preserve_exact_source_spans() {
    let scratch = support::Scratch::new("gensym-diagnostic-cache");
    let source = "#gn-fn emit (temporary) `((#fn broken () #u64
          (#let ,temporary #u64 false) (#return ,temporary)))
#gn generate () (#gn-call emit (#gn-gensym \"task\"))
#generate generate\n";
    let compile = || {
        lim::compile_source_to_assembly(
            source,
            &scratch.path().join("main.lim"),
            &lim::CompileConfig::default(),
            &scratch.path().join("cache"),
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap_err()
    };
    let cold = compile();
    let warm = compile();
    assert_eq!(cold.span, warm.span);
    assert_eq!(cold.source_text, warm.source_text);
    let span = cold.span.unwrap();
    let generated = cold.source_text.as_deref().unwrap();
    assert!(generated.contains("lim.gensym."), "{cold:?}");
    assert_eq!(&generated[span.start..span.end], "false");
    assert_eq!(cold.code, lim::DiagnosticCode::Type);
    assert!(
        cold.labels
            .iter()
            .any(|label| label.message.contains("invocation")),
        "{cold:?}"
    );
}

#[test]
fn gensym_example_reuses_identical_inspectable_cached_files() {
    let scratch = support::Scratch::new("gensym-example-cache");
    let source = include_str!("../examples/gensym.lim");
    let cache = scratch.path().join(".lim/cache");
    let compile = || {
        lim::compile_source_with_generated_sources(
            source,
            &scratch.path().join("main.lim"),
            &lim::CompileConfig::default(),
            &cache,
            lim::TargetDescription::X86_64_SYSTEM_V,
            None,
            &scratch.path().join(".lim"),
        )
        .unwrap()
    };
    let artifacts = || {
        let mut artifacts = std::fs::read_dir(scratch.path().join(".lim/generated"))
            .unwrap()
            .filter_map(Result::ok)
            .filter(|entry| {
                entry
                    .path()
                    .extension()
                    .is_some_and(|extension| extension == "lim")
            })
            .map(|entry| {
                (
                    entry.file_name(),
                    std::fs::read_to_string(entry.path()).unwrap(),
                )
            })
            .collect::<Vec<_>>();
        artifacts.sort();
        artifacts
    };
    let cold = compile();
    let files = artifacts();
    let mut functions = files.iter().flat_map(|(_, source)| lim::parse_source_unit(source).unwrap())
        .filter_map(|node| match node.expr {
            lim::Expr::List(items) if matches!(items.first(), Some(lim::Expr::Symbol(head)) if head == "#fn") => Some(items[1].clone()),
            _ => None,
        }).collect::<Vec<_>>();
    functions.sort_by_key(|name| format!("{name:?}"));
    assert_eq!(
        functions,
        [
            lim::Expr::Symbol("first".into()),
            lim::Expr::Symbol("second".into())
        ],
        "duplicate invocation emits no duplicate declaration"
    );
    assert!(files
        .iter()
        .all(|(_, source)| source.contains("lim.gensym.") && source.contains("task #u64")));
    assert_eq!(compile(), cold);
    assert_eq!(artifacts(), files);
}

#[test]
fn external_imported_generators_keep_fresh_locals_and_explicit_prefixed_api_keys() {
    let scratch = support::Scratch::new("gensym-external-generator");
    std::fs::write(
        scratch.path().join("module.lim"),
        "#gn-fn emit (name temporary)
          `((#fn ,name ((task #u64)) #u64 (#let ,temporary #u64 task) (#return ,temporary)))
#gn make (name) (#gn-call emit name (#gn-gensym \"task\"))
#generate make first\n",
    )
    .unwrap();
    let source = "#alias lib@first = ./module.lim::first
#fn main {
  #params = ();
  #returns = #u64;
  #body = ( (#return (#call lib@first ((task 42u64))))\n  );\n}\n";
    lim::compile_source_to_assembly(
        source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
}
