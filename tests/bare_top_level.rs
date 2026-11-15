use lim::{CompileConfig, DiagnosticCode, Expr, TargetDescription};
use std::{
    fs,
    sync::atomic::{AtomicU64, Ordering},
};

static NEXT: AtomicU64 = AtomicU64::new(0);

fn scratch() -> std::path::PathBuf {
    let path = std::env::temp_dir().join(format!(
        "lim-bare-roots-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir(&path).unwrap();
    path
}

fn trees(source: &str) -> Vec<Expr> {
    lim::parse_source_unit(source)
        .unwrap()
        .into_iter()
        .map(|n| n.expr)
        .collect()
}

#[test]
fn logical_roots_share_streaming_boundaries_and_keep_authored_spans() {
    for source in [
        "#generate #array:\n  element #u64;\n  length 2;\n  name Pair;\n#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 42u64)\n  );\n}\n",
        "#fn main { #params = {}; #returns = #u64; #body: #return 42; }",
        "#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = (\n  (#return 42u64)\n  );\n}\n",
        "// before\r\n#type Answer #u64; #fn main {\n  #params = ();\n  #returns = Answer;\n  #body = ( (#return 42u64)\n  );\n} // after\r\n",
        "#struct Pair () { left = #u64; right = #u64; }\n#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = (\n  (#let pair Pair (#struct-literal Pair { left = 20u64; right = 22u64; }))\n  (#return (#u64::add-wrap (#get pair left) (#get pair right)))\n  );\n}\n",
        "#fn main {\n #params = {};\n #returns = #u64;\n #body:\n  #let value #u64 42;\n  #return value;\n}\n// boundary\n#type Number #u64\n",
    ] {
        let nodes = lim::parse_source_unit(source).unwrap();
        for node in &nodes {
            assert!(source[node.span.start..node.span.end].starts_with('#'));
            assert_eq!(node.children[0].span.start, node.span.start);
        }
        let formatted = lim::format_source(source).unwrap();
        assert_eq!(trees(source), trees(&formatted), "{formatted}");
        assert_eq!(lim::format_source(&formatted).unwrap(), formatted);
        lim::check_types(&lim::parse_program(source).unwrap()).unwrap();
    }
}

#[test]
fn explicit_root_wrappers_reject_but_nested_and_quoted_trees_are_data() {
    for source in [
        "(#fn main () #u64 (#return 42u64))",
        "(#fn main { #params = {}; #returns = #u64; #body: #return 42; })",
        "((#fn main () #u64 (#return 42u64)))",
        ": #fn main () #u64 (#return 42u64)",
        "'(#fn main () #u64 (#return 42u64))",
    ] {
        assert!(lim::parse_source_unit(source)
            .unwrap_err()
            .contains("bare root"));
        assert!(lim::parse_program(source).is_err());
        assert!(lim::format_source(source).is_err());
    }
    // A syntax-tree API is not an alternate compilation-unit grammar.
    assert!(lim::parse("'((#fn main () #u64 (#return 42u64)))").is_ok());
    let source = "#cfg-if (#cfg-is #platform linux)\n  (#fn main {\n    #params = ();\n    #returns = #u64;\n    #body = ( (#return 42u64)\n    );\n  })\n";
    assert!(lim::parse_source_unit(source).is_ok());
    assert!(lim::parse_source_unit(
        "#fn main { #params = {}; #returns = (); #body: #return (); } #type X #u64"
    )
    .is_err());
}

#[test]
fn source_errors_keep_delimiters_and_unicode_positions() {
    let source = "// λ\n(#fn main () #u64 (#return 42u64))";
    let dir = scratch();
    let error = lim::compile_source_to_assembly(
        source,
        &dir.join("case.lim"),
        &CompileConfig::default(),
        &dir.join("cache"),
        TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err();
    assert_eq!(error.code, DiagnosticCode::Parse);
    let span = error.span.unwrap();
    assert_eq!(&source[span.start..span.end], "(");
    assert_eq!((span.line, span.column), (2, 1));
    for source in [
        "#fn main {",
        "#type X (#tuple #u64]",
        "#fn main () #u64 (#return 42u64))",
    ] {
        assert!(lim::parse_source_unit(source).is_err(), "{source}");
    }
    fs::remove_dir_all(dir).unwrap();
}

#[test]
fn generated_documents_use_bare_roots_with_stable_cold_warm_artifacts() {
    let dir = scratch();
    let source = "#gn emit ()\n  `((#fn answer () #u64 (#return 42u64)))\n#generate emit\n#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return (#call answer ()))\n  );\n}\n";
    let compile = || {
        lim::compile_source_with_generated_sources(
            source,
            &dir.join("main.lim"),
            &CompileConfig::default(),
            &dir.join("cache"),
            TargetDescription::X86_64_SYSTEM_V,
            None,
            &dir.join("generated"),
        )
    };
    let cold = compile().unwrap();
    let artifacts = fs::read_dir(dir.join("generated"))
        .unwrap()
        .map(|entry| {
            let path = entry.unwrap().path();
            let text = fs::read_to_string(&path).unwrap();
            assert!(lim::parse_source_unit(&text).is_ok(), "{text}");
            assert!(!text.lines().any(|line| line.starts_with("(#")), "{text}");
            assert!(text.contains("#generated-context"));
            (path, text)
        })
        .collect::<Vec<_>>();
    assert!(!artifacts.is_empty());
    let (warm, report) = lim::with_cache_report(compile);
    assert_eq!(warm.unwrap(), cold);
    assert!(report.contains("\"decision\":\"hit\""), "{report}");
    for (path, text) in artifacts {
        assert_eq!(fs::read_to_string(path).unwrap(), text);
    }
    fs::remove_dir_all(dir).unwrap();
}

#[test]
fn all_declaration_payloads_keep_their_existing_tree_shapes() {
    for payload in [
        "#std",
        "#alias value = ./value.lim::value",
        "#export Value value",
        "#type Value #u64",
        "#struct Value (#linear) ((value #u64))",
        "#enum Choice () ((Choice.Some #u64) Choice.None)",
        "#opaque Value",
        "#unsafe-impl #send Value",
        "#const count #u64 1u64",
        "#static count #u64 1u64",
        "#let count #u64 1u64",
        "#fn value {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 1u64)\n  );\n}",
        "#unsafe-fn value {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 1u64)\n  );\n}",
        "#extern-fn  value {\n  #abi = #abi-c;\n  #params = ();\n  #returns = #u64;\n}",
        "#thread-task Task worker",
        "#distributed-enum Choice ()",
        "#enum-contribute Choice (Some #u64)",
        "#gn make (name) `((#type ,name #u64))",
        "#gn-fn make (name) `(#type ,name #u64)",
        "#generate make Value",
        "#require-generated Value make",
        "#capability readable #u64 ((read () #u64))",
        "#syntax Body ((#return 1u64))",
        "#cfg-if (#cfg-is #platform linux) (#type Word #u64)",
    ] {
        let canonical = format!("({payload})");
        assert_eq!(
            trees(payload),
            lim::parse(&canonical)
                .unwrap()
                .into_iter()
                .map(|n| n.expr)
                .collect::<Vec<_>>(),
            "{payload}"
        );
        assert!(lim::parse_source_unit(&canonical).is_err(), "{canonical}");
    }
}

#[test]
fn imported_source_obeys_the_same_root_rule() {
    let dir = scratch();
    fs::write(dir.join("value.lim"), "(#fn value () #u64 (#return 42u64))").unwrap();
    let source = "#alias value = ./value.lim::value\n#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return (#call value ()))\n  );\n}\n";
    let compile = || {
        lim::compile_source_to_assembly(
            source,
            &dir.join("main.lim"),
            &CompileConfig::default(),
            &dir.join("cache"),
            TargetDescription::X86_64_SYSTEM_V,
        )
    };
    let error = compile().unwrap_err();
    assert_eq!(error.code, DiagnosticCode::Parse);
    assert!(error.message.contains("bare root"));
    fs::write(dir.join("value.lim"), "#fn value {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 42u64)\n  );\n}\n").unwrap();
    compile().unwrap();
    fs::remove_dir_all(dir).unwrap();
}

#[test]
fn builtin_and_async_published_sources_reuse_bare_warm_artifacts() {
    for source in [
        include_str!("../examples/optional.lim"),
        include_str!("../examples/async_block_loop.lim"),
    ] {
        let dir = scratch();
        let compile = || {
            lim::compile_source_with_generated_sources(
                source,
                &dir.join("main.lim"),
                &CompileConfig::default(),
                &dir.join("cache"),
                TargetDescription::X86_64_SYSTEM_V,
                None,
                &dir.join("generated"),
            )
        };
        let cold = compile().unwrap();
        let artifacts = fs::read_dir(dir.join("generated"))
            .unwrap()
            .map(|entry| {
                let path = entry.unwrap().path();
                let text = fs::read_to_string(&path).unwrap();
                lim::parse_source_unit(&text).unwrap_or_else(|e| panic!("{e}\n{text}"));
                (path, text)
            })
            .collect::<Vec<_>>();
        assert!(!artifacts.is_empty());
        let (warm, report) = lim::with_cache_report(compile);
        assert_eq!(warm.unwrap(), cold);
        assert!(report.contains("\"decision\":\"hit\""), "{report}");
        let async_artifact = artifacts
            .iter()
            .find(|(_, text)| text.contains("Work::poll"))
            .cloned();
        for (path, text) in artifacts {
            assert_eq!(fs::read_to_string(path).unwrap(), text);
        }
        if let Some((path, text)) = async_artifact {
            fs::write(path, format!("{text}\n// corrupted after validation\n")).unwrap();
            let error = compile().unwrap_err();
            assert!(
                error.message.contains("invalid async graph cache entry"),
                "{error:?}"
            );
        }
        fs::remove_dir_all(dir).unwrap();
    }
}

#[test]
fn bare_library_exports_remain_literal_and_generated_exports_cannot_grant_authority() {
    let dir = scratch();
    let library = dir.join("lib.lim");
    let authored = "#export value\n#fn value {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 42u64)\n  );\n}\n";
    fs::write(&library, authored).unwrap();
    let caller = "#alias value = ./lib.lim::value\n#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return (#call value ()))\n  );\n}\n";
    let program = lim::parse_program_from_path(caller, &dir.join("main.lim")).unwrap();
    lim::check_types(&program).unwrap();
    let forged =
        "#fn value {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 42u64)\n  );\n}\n#gn emit () `((#export value))\n#generate emit\n";
    let error = lim::parse_program_from_path(forged, &library).unwrap_err();
    assert!(error.contains("#export must be literal"), "{error}");
    fs::remove_dir_all(dir).unwrap();
}

#[test]
fn unprefixed_bare_heads_report_the_missing_prefix_at_the_written_head() {
    for head in ["fn", "alias", "struct", "generate"] {
        let error = lim::parse_source_unit(&format!("{head} main")).unwrap_err();
        assert!(error.contains("must use its '#' prefix"), "{error}");
        assert!(!error.contains("outer parentheses"), "{error}");
    }
    let dir = scratch();
    let source = "fn main () #u64 (#return 42u64)";
    let error = lim::compile_source_to_assembly(
        source,
        &dir.join("main.lim"),
        &CompileConfig::default(),
        &dir.join("cache"),
        TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err();
    assert_eq!(error.code, DiagnosticCode::Parse);
    let span = error.span.unwrap();
    assert_eq!(&source[span.start..span.end], "fn");
    assert_eq!((span.line, span.column), (1, 1));
    let wrapped = lim::parse_source_unit("(fn main () #u64 (#return 42u64))").unwrap_err();
    assert!(wrapped.contains("bare root"), "{wrapped}");
    fs::remove_dir_all(dir).unwrap();
}

#[test]
fn root_colon_operands_can_contain_inline_and_indented_cfg_declarations() {
    let expected = lim::parse(
        "(#cfg-if (#cfg-is #feature selected) (#fn main () #u64 (#return 42u64)))",
    )
    .unwrap()
    .into_iter()
    .map(|node| node.expr)
    .collect::<Vec<_>>();
    let mut config = CompileConfig::default();
    config.set("feature", "selected");
    for source in [
        "#cfg-if (#cfg-is #feature selected): #fn main { #params = {}; #returns = #u64; #body: #return 42u64; }",
        "#cfg-if (#cfg-is #feature selected):\n  #fn main { #params = {}; #returns = #u64; #body: #return 42u64; }\n",
    ] {
        assert_eq!(trees(source), expected, "{source}");
        let formatted = lim::format_source(source).unwrap();
        assert_eq!(trees(&formatted), expected);
        assert_eq!(lim::format_source(&formatted).unwrap(), formatted);
        let program = lim::parse_program_with_config(source, &config).unwrap();
        lim::check_types(&program).unwrap();
    }
}

#[test]
fn root_colon_generator_arguments_keep_nested_function_data() {
    for invocation in [
        "#generate emit: #fn answer { #params = {}; #returns = #u64; #body: #return 42u64; }",
        "#generate emit:\n  #fn answer { #params = {}; #returns = #u64; #body: #return 42u64; }",
    ] {
        let source = format!(
            "#gn emit (declaration) (#gn-list declaration)\n{invocation}\n#fn main {{\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return (#call answer ()))\n  );\n}}\n"
        );
        let formatted = lim::format_source(&source).unwrap();
        assert_eq!(trees(&source), trees(&formatted));
        let program = lim::parse_program(&source).unwrap();
        lim::check_types(&program).unwrap();
    }
}

#[test]
fn colon_exemptions_do_not_accept_unseparated_source_roots() {
    for source in [
        "#fn main { #params = {}; #returns = #u64; #body: #return 42u64; } #type Extra #u64",
        "#type First #u64 #type Second #u64",
        "#cfg-if (#cfg-is #feature selected):\n  #fn selected () #u64 (#return 42u64)\n#fn main { #params = {}; #returns = #u64; #body: #return 42u64; } #type Extra #u64",
    ] {
        let error = lim::parse_source_unit(source).unwrap_err();
        assert!(error.contains("newline or semicolon separator"), "{error}");
        assert!(lim::format_source(source).is_err());
    }
    assert!(lim::parse_source_unit(": #fn main () #u64 (#return 42u64)").is_err());
}

#[test]
fn quoted_trailing_colon_symbols_do_not_hide_adjacent_roots_in_inactive_cfg() {
    let mut config = CompileConfig::default();
    config.set("feature", "selected");
    for prefix in ["'", "`", ",@", "',", "`,", ",'", ",@,"] {
        let source = format!(
            "#cfg-if (#cfg-is #feature inactive) {prefix}symbol: #fn ignored {{ #params = {{}}; #returns = #u64; #body: #return 0u64; }}\n#fn main () #u64 (#return 42u64)\n"
        );
        let error = lim::parse_source_unit(&source).unwrap_err();
        assert!(error.contains("newline or semicolon separator"), "{error}");
        assert!(lim::format_source(&source).is_err());
        let error = lim::parse_program_with_config(&source, &config).unwrap_err();
        assert!(error.contains("newline or semicolon separator"), "{error}");
    }
}

#[test]
fn quoted_trailing_colon_data_is_preserved_with_proper_source_boundaries() {
    let mut config = CompileConfig::default();
    config.set("feature", "selected");
    for prefix in ["'", "`", ",@", "',", "`,", ",'", ",@,"] {
        let source = format!(
            "#cfg-if (#cfg-is #feature inactive) {prefix}symbol:\n#fn main {{\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 42u64)\n  );\n}}\n"
        );
        let expected = lim::parse(&format!(
            "(#cfg-if (#cfg-is #feature inactive) {prefix}symbol:) (#fn main () #u64 (#return 42u64))"
        ))
        .unwrap()
        .into_iter()
        .map(|node| node.expr)
        .collect::<Vec<_>>();
        assert_eq!(trees(&source), expected);
        let formatted = lim::format_source(&source).unwrap();
        assert_eq!(trees(&formatted), expected);
        let program = lim::parse_program_with_config(&source, &config).unwrap();
        lim::check_types(&program).unwrap();
    }
}

#[test]
fn explicit_colon_tokens_still_group_nested_syntax_under_quote_wrappers() {
    for prefix in ["'", "`", ",@", "',"] {
        let invocation = format!(
            "#generate emit {prefix}: #fn ignored {{ #params = {{}}; #returns = #u64; #body: #return 0u64; }}"
        );
        let expected = lim::parse(&format!(
            "(#generate emit {prefix}(#fn ignored () #u64 (#return 0u64)))"
        ))
        .unwrap()
        .into_iter()
        .map(|node| node.expr)
        .collect::<Vec<_>>();
        assert_eq!(trees(&invocation), expected);
        let source = format!(
            "#gn emit (ignored) `((#fn answer () #u64 (#return 42u64)))\n{invocation}\n#fn main {{\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return (#call answer ()))\n  );\n}}\n"
        );
        let program = lim::parse_program(&source).unwrap();
        lim::check_types(&program).unwrap();
    }
    let source = "#cfg-if (#cfg-is #feature selected): #fn main { #params = {}; #returns = #u64; #body: #return 42u64; }";
    let mut config = CompileConfig::default();
    config.set("feature", "selected");
    let program = lim::parse_program_with_config(source, &config).unwrap();
    lim::check_types(&program).unwrap();
}

#[test]
fn closed_colon_operands_cannot_hide_outdented_or_continued_declaration_heads() {
    let mut config = CompileConfig::default();
    config.set("feature", "selected");
    let indented = "#cfg-if (#cfg-is #feature inactive):\n  #fn first { #params = {}; #returns = #u64; #body: #return 0u64; }\n #fn second { #params = {}; #returns = #u64; #body: #return 1u64; }\n#fn main () #u64 (#return 42u64)\n";
    let inline = "#cfg-if (#cfg-is #feature inactive): #fn first { #params = {}; #returns = #u64; #body: #return 0u64; }\n #fn second { #params = {}; #returns = #u64; #body: #return 1u64; }\n#fn main () #u64 (#return 42u64)\n";
    for source in [indented, inline] {
        assert!(lim::parse_source_unit(source).is_err());
        assert!(lim::format_source(source).is_err());
        assert!(lim::parse_program_with_config(source, &config).is_err());
    }
    let error = lim::parse_source_unit(inline).unwrap_err();
    assert!(error.contains("2:2:"), "{error}");
    assert!(error.contains("newline or semicolon separator"), "{error}");
    let properly_separated = "#cfg-if (#cfg-is #feature inactive): #fn first { #params = {}; #returns = #u64; #body: #return 0u64; }\n#fn second () #u64 (#return 1u64)\n#fn main () #u64 (#return 42u64)\n";
    assert_eq!(trees(properly_separated).len(), 3);
    let formatted = lim::format_source(properly_separated).unwrap();
    assert_eq!(trees(properly_separated), trees(&formatted));
    let program = lim::parse_program_with_config(properly_separated, &config).unwrap();
    lim::check_types(&program).unwrap();
}

#[test]
fn multiline_string_tokens_do_not_create_a_same_line_root_boundary() {
    let mut config = CompileConfig::default();
    config.set("feature", "selected");
    let prefix = "#cfg-if (#cfg-is #feature inactive) \"line one\nline two\"";
    let same_closing_line = format!(
        "{prefix} #fn hidden () #u64 (#return 0u64)\n#fn main {{\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 42u64)\n  );\n}}\n"
    );
    let error = lim::parse_source_unit(&same_closing_line).unwrap_err();
    assert!(error.contains("newline or semicolon separator"), "{error}");
    assert!(lim::format_source(&same_closing_line).is_err());
    assert!(lim::parse_program_with_config(&same_closing_line, &config).is_err());
    let following_newline = format!("{prefix}\n#fn main {{\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 42u64)\n  );\n}}\n");
    let nodes = lim::parse_source_unit(&following_newline).unwrap();
    assert_eq!(nodes.len(), 2);
    assert_eq!(
        nodes[0].children[2].expr,
        Expr::String("line one\nline two".into())
    );
    let formatted = lim::format_source(&following_newline).unwrap();
    assert_eq!(trees(&following_newline), trees(&formatted));
    assert_eq!(lim::format_source(&formatted).unwrap(), formatted);
    let program = lim::parse_program_with_config(&following_newline, &config).unwrap();
    lim::check_types(&program).unwrap();
}
