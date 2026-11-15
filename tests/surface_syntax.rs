#[test]
fn slash_comments_do_not_consume_literals_and_keep_source_positions() {
    let source = "first// adjacent comment\n\"https://example.test\" #\\/ last";
    let forms = lim::parse(source).unwrap();
    assert_eq!(forms.len(), 4);
    assert_eq!(forms[0].expr, lim::Expr::Symbol("first".into()));
    assert_eq!(
        forms[1].expr,
        lim::Expr::String("https://example.test".into())
    );
    assert_eq!(forms[2].expr, lim::Expr::Char('/'));
    assert_eq!(forms[3].span.start, source.rfind("last").unwrap());
    let formatted = lim::format_syntax(source).unwrap();
    assert!(formatted.contains("// adjacent comment"));
    assert_eq!(lim::format_syntax(&formatted).unwrap(), formatted);
}
mod support;

fn trees(source: &str) -> Vec<lim::Expr> {
    lim::parse(source)
        .unwrap()
        .into_iter()
        .map(|node| node.expr)
        .collect()
}

#[test]
fn records_calls_and_semicolon_lists_lower_to_existing_forms() {
    assert_eq!(
        trees("{ left = x; right = 4; }"),
        trees("((left x) (right 4))")
    );
    assert_eq!(
        trees("read { index = x; }"),
        trees("(#call read ((index x)))")
    );
    assert_eq!(
        trees("(read { index = x; })"),
        trees("(#call read ((index x)))")
    );
    assert_eq!(
        trees("(#call read { index = x; })"),
        trees("(#call read ((index x)))")
    );
    assert_eq!(
        trees("(#let next #u64 read { index = x; }; #return next;)"),
        trees("((#let next #u64 (#call read ((index x)))) (#return next))")
    );
    assert_eq!(trees("((#return x);)"), trees("((#return x))"));
    assert_eq!(
        trees("(finish {}; #return ();)"),
        trees("((#call finish ()) (#return ()))")
    );
}

#[test]
fn colons_group_the_remaining_line_and_nest_without_a_head_position_rule() {
    for (source, canonical) in [
        ("(a : b c)", "(a (b c))"),
        ("(a : b : c)", "(a (b (c)))"),
        ("a : b : c", "(a (b (c)))"),
        (": a b", "(a b)"),
        ("(: a b)", "((a b))"),
        ("(a : b\n c)", "(a (b) c)"),
        ("(:\n  a b\n)", "((a b))"),
        (
            "(#return : #u64::add-wrap 20 22)",
            "(#return (#u64::add-wrap 20 22))",
        ),
        ("{ row = : x y; tail = z; }", "((row (x y)) (tail z))"),
        ("{ row: x y; tail = z; }", "((row (x y)) (tail z))"),
        (
            "(#let answer #u64 : #u64::add-wrap 20 22; #return answer;)",
            "((#let answer #u64 (#u64::add-wrap 20 22)) (#return answer))",
        ),
        ("`(a : b : c)", "`(a (b (c)))"),
    ] {
        assert_eq!(trees(source), trees(canonical), "{source}");
        let formatted = lim::format_syntax(source).unwrap();
        assert_eq!(trees(source), trees(&formatted), "{source}");
        assert_eq!(lim::format_syntax(&formatted).unwrap(), formatted);
    }
    for source in [":", "(:)", "(a :)", "{ value:; }", "(:\nvalue\n)"] {
        assert!(lim::parse(source).is_err(), "accepted {source}");
    }
    let nested = format!("({}value)", "a : ".repeat(600));
    assert!(lim::parse(&nested).unwrap_err().contains("nesting"));
    let source =
        "#fn main { #params = {}; #returns = #u64; #body: #return : #u64::add-wrap 20 22; }";
    lim::check_types(&lim::parse_program(source).unwrap()).unwrap();
}

#[test]
fn infix_has_fixed_precedence_and_explicit_scoped_modes() {
    assert_eq!(
        trees("[#u64 #wrap; a + b * c]"),
        trees("(#u64::add-wrap a (#u64::mul-wrap b c))")
    );
    assert_eq!(
        trees("[#u64 #wrap; [a + b] * c]"),
        trees("(#u64::mul-wrap (#u64::add-wrap a b) c)")
    );
    assert_eq!(
        trees("[#u64 #wrap; a - b - c]"),
        trees("(#u64::sub-wrap (#u64::sub-wrap a b) c)")
    );
    assert_eq!(
        trees("[#u64 #wrap; a + [#u64 #saturate; b * c]]"),
        trees("(#u64::add-wrap a (#u64::mul-saturate b c))")
    );
    assert_eq!(
        trees("[#usize; index < 4]"),
        trees("(#usize::lt index 4usize)")
    );
    assert_eq!(
        trees("[#usize; index < 4 && index > 0]"),
        trees("(#bool::and (#usize::lt index 4usize) (#usize::gt index 0usize))")
    );
    for source in [
        "[a + b]",
        "[#u64; a + b]",
        "[#u64 #wrap; a < b < c]",
        "[#u64 #wrap; a + read { value = [b + c]; }]",
        "[#u64 #wrap; a + (read { value = [b + c]; })]",
        "[#f64 #wrap; a + b]",
    ] {
        assert!(lim::parse(source).is_err(), "accepted {source}");
    }
    let invalid =
        "#fn invalid {\n  #params = ((a #u64) (b #u64) (c #u64));\n  #returns = #u64;\n  #body = ( (#return [#u64 #wrap; a + (b * c)])\n  );\n}\n";
    assert!(lim::parse_program(invalid)
        .and_then(|program| lim::check_types(&program))
        .is_err());
}

#[test]
fn declaration_records_normalize_with_required_fields_and_empty_defaults() {
    assert_eq!(trees("#fn ignore { #params = { value = #u64; }; #returns = (); #body = (#forget value; #return ();); }"), trees("(#fn ignore ((value #u64)) () (#forget value) (#return ()))"));
    assert_eq!(
        trees("#static limit { #type = #u64; #value = 100; }"),
        trees("(#static limit #u64 100)")
    );
    assert_eq!(trees("(#fn ignore (#params { value = #u64; }) (#returns ()) (#requires) (#ensures) (#preserves) (#body (#forget value) (#return ())))"), trees("(#fn ignore ((value #u64)) () (#forget value) (#return ()))"));
    for source in [
        "#fn missing { #returns = (); #body = (); }",
        "#fn missing { #params = {}; #body = (); }",
        "#fn missing { #params = {}; #returns = (); }",
        "#fn duplicate { #params = {}; #returns = (); #returns = #u64; #body = (); }",
        "#fn unknown { #params = {}; #returns = (); #body = (); #other = (); }",
        "#fn bad { #params = {}; #returns = (); #requires = 0u64; #body = (#return ();); }",
        "#fn bad { #params = {}; #returns = (); #ensures = 0u64; #body = (#return ();); }",
        "#fn bad { #params = {}; #returns = (); #preserves = 0u64; #body = (#return ();); }",
        "#fn bad { #params = {}; #returns = (); #body = 0u64; }",
        "{ key = value }",
        "{ key value; }",
        "{ key = ; }",
        "(first; last)",
    ] {
        assert!(lim::parse(source).is_err(), "accepted {source}");
    }
}

#[test]
fn generated_function_records_keep_unquoted_names_and_canonical_structure() {
    let source = "#gn make { name; } `((#fn ,name { #params = {}; #returns = #u64; #body = (#return 42u64;); }))\n#generate make { name = read; }\n#fn main { #params = {}; #returns = #u64; #body = (#return read {};); }";
    lim::check_types(&lim::parse_program(source).unwrap()).unwrap();
    let aggregate = "#gn make { name; } `((#struct ,name () ((value #u64))) (#fn create ((value #u64)) ,name (#return (#struct-literal ,name ((value value))))))\n#generate make { name = Item; }\n#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return (#get (create ((value 42))) value))\n  );\n}\n";
    lim::check_types(&lim::parse_program(aggregate).unwrap()).unwrap();
    for keyword in ["#fn", "#static", "#const", "#unsafe-fn"] {
        assert_eq!(trees(keyword), vec![lim::Expr::Symbol(keyword.into())]);
    }
}

#[test]
fn implicit_calls_use_aliases_of_quoted_file_targets() {
    let scratch = support::Scratch::new("surface-file-call");
    std::fs::write(
        scratch.path().join("value with spaces.lim"),
        "#fn read {\n  #params = ((value #u64));\n  #returns = #u64;\n  #body = ( (#return value)\n  );\n}\n",
    )
    .unwrap();
    for call in [
        "read { value = 42; }",
        "(read { value = 42; })",
        "(read ((value 42)))",
    ] {
        let source = "#alias read = \"./value with spaces.lim::read\"\n#fn main { #params = {}; #returns = #u64; #body = (#return CALL;); }"
            .replace("CALL", call);
        let program =
            lim::parse_program_from_path(&source, &scratch.path().join("main.lim")).unwrap();
        lim::check_types(&program).unwrap();
        let formatted = lim::format_syntax(&source).unwrap();
        assert_eq!(trees(&source), trees(&formatted));
    }
    assert_eq!(
        trees("\"./value.lim::read\""),
        vec![lim::Expr::String("./value.lim::read".into())]
    );
}

#[test]
fn marker_free_calls_retain_function_identity_and_unsafe_requirements() {
    let source = "#fn panic {\n  #params = ((value #u64));\n  #returns = #u64;\n  #body = ( (#return value)\n  );\n}\n#fn main { #params = {}; #returns = #u64; #body: \n  #return panic { value = 42; };\n}";
    lim::check_types(&lim::parse_program(source).unwrap()).unwrap();
    assert_eq!(
        trees("((name Example) (fields ((value #u64))))"),
        trees("((name Example) (fields ((value #u64))))")
    );
    assert_eq!(
        trees("((argument identity ((value 42))))"),
        trees("((argument identity ((value 42))))")
    );
    for call in ["danger {}", "(danger ())", "danger ()"] {
        let source = format!("#unsafe-fn danger {{\n  #params = ();\n  #returns = ();\n  #body = ( (#return ())\n  );\n}}\n#fn main {{ #params = {{}}; #returns = (); #body = (#unsafe ({call}); #return ();); }}");
        assert!(lim::parse_program(&source)
            .unwrap_err()
            .contains("#unsafe-call"));
    }
    for arguments in ["((wrong 1))", "((value 1) (value 2))", "()"] {
        let source = format!("#fn read {{\n  #params = ((value #u64));\n  #returns = #u64;\n  #body = ( (#return value)\n  );\n}}\n#fn main {{\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return (read {arguments}))\n  );\n}}\n");
        assert!(lim::parse_program(&source).is_err(), "accepted {source}");
    }
}

#[test]
fn flat_infix_chains_cannot_bypass_the_reader_nesting_budget() {
    let source = format!("[#u64 #wrap; {}]", vec!["value"; 1024].join(" + "));
    assert!(lim::parse(&source).unwrap_err().contains("nesting"));
}

#[test]
fn every_container_reports_excessive_nesting_without_overflowing_the_stack() {
    for source in [
        format!("{}x{}", "(".repeat(600), ")".repeat(600)),
        format!("{}x{}", "{ key = ".repeat(600), "; }".repeat(600)),
        format!("[#u64 #wrap; {}x{}]", "[".repeat(600), "]".repeat(600)),
        format!("{}x", "'".repeat(600)),
    ] {
        assert!(lim::parse(&source).is_err());
    }
}

#[test]
fn layout_is_local_and_delimited_operands_keep_their_own_semicolons() {
    let source = "#fn next {\n  #params = { value = #u64; };\n  #returns = #u64;\n  #requires =:\n    [#u64; value < 99];\n  #ensures =:\n    [#u64; (#result) < 100];\n  #body =:\n    // preserve this comment\n    #let next #u64 [#u64 #wrap; value + 1];\n    #return next;\n}\n";
    assert_eq!(trees(source), trees("(#fn next ((value #u64)) #u64 (#requires (#u64::lt value 99u64)) (#ensures (#u64::lt (#result) 100u64)) (#let next #u64 (#u64::add-wrap value 1u64)) (#return next))"));
    lim::check_types(&lim::parse_program(source).unwrap()).unwrap();
    let shorthand = source.replace(" =:", ":");
    assert_eq!(trees(&shorthand), trees(source));
    lim::check_types(&lim::parse_program(&shorthand).unwrap()).unwrap();
    let outdented = "#fn identity {\n  #params = ((value #u64));\n  #returns = #u64;\n  #body = ( (#return value)\n  );\n}\n#fn main {\n  #params = {};\n  #returns = #u64;\n  #body =:\n    #return identity {\n      value = 42;\n};\n}\n";
    lim::check_types(&lim::parse_program(outdented).unwrap()).unwrap();
    let string = "#fn text {\n  #params = {};\n  #returns = (#array #char 3);\n  #body =:\n    #return \"x \n\";\n}\n";
    lim::check_types(&lim::parse_program(string).unwrap()).unwrap();
    assert_eq!(trees(string), trees(&lim::format_syntax(string).unwrap()));
    for source in [
        "{ body =:\nvalue;\n}",
        "{ body =:\n\tvalue;\n}",
        "{ body =:\n    one;\n  two;\n}",
    ] {
        for source in [source.to_owned(), source.replace(" =:", ":")] {
            assert!(lim::parse(&source).is_err(), "accepted {source}");
        }
    }
}

#[test]
fn indented_record_values_can_omit_equals_without_changing_symbols_or_key_spans() {
    let source = "#fn identity {\n  #params:\n    value #u64;\n  #returns = #u64;\n  #body :\n    #return value;\n}\n";
    assert_eq!(
        trees(source),
        trees("(#fn identity ((value #u64)) #u64 (#return value))")
    );
    lim::check_types(&lim::parse_program(source).unwrap()).unwrap();

    let nested =
        "{ entries:\n  collect { items:\n    first;\n    second;\n  };\n  last;\nafter = done;\n}";
    assert_eq!(trees(nested), trees(&nested.replace(":\n", " =:\n")));
    let generated = "`{ ,key:\n  value;\n}";
    assert_eq!(trees(generated), trees(&generated.replace(":\n", " =:\n")));

    let source = "{ λ:\n  value;\n}";
    let record = lim::parse(source).unwrap().remove(0);
    let key = &record.children[0].children[0];
    assert_eq!(&source[key.span.start..key.span.end], "λ");
    let value = &record.children[0].children[1];
    assert_eq!(&source[value.span.start..value.span.start + 1], ":");
    assert_eq!(value.span.column, 4);

    assert_eq!(
        trees("'name: Type::member key::"),
        vec![
            lim::Expr::Quote(Box::new(lim::Expr::Symbol("name:".into()))),
            lim::Expr::Symbol("Type::member".into()),
            lim::Expr::Symbol("key::".into()),
        ]
    );
    assert_eq!(trees("{ key: = value; }"), trees("((key (= value)))"));
    for source in ["{ key\n  value;\n}", "{ key::\n  value;\n}"] {
        assert!(lim::parse(source).is_err(), "accepted {source}");
    }
}

#[test]
fn statement_headers_append_nested_indented_forms_and_end_on_dedent() {
    let source = r#"#fn total {
  #params = {};
  #returns = #u64;
  #body:
    #let-mut sum #u64 0;
    #for-range (outer #u64) 1 4:
      #for-range (inner #u64) 1 3 :
        #set sum [#u64 #wrap; sum + outer * inner];
    #while [#u64; sum < 20]:
      #set sum [#u64 #wrap; sum + 1];
    #loop:
      #break;
    #return sum;
}
"#;
    let canonical = "(#fn total () #u64 (#let-mut sum #u64 0) (#for-range (outer #u64) 1 4 (#for-range (inner #u64) 1 3 (#set sum (#u64::add-wrap sum (#u64::mul-wrap outer inner))))) (#while (#u64::lt sum 20u64) (#set sum (#u64::add-wrap sum 1u64))) (#loop (#break)) (#return sum))";
    assert_eq!(trees(source), trees(canonical));
    lim::check_types(&lim::parse_program(source).unwrap()).unwrap();
    assert_eq!(trees(source), trees(&lim::format_syntax(source).unwrap()));
    assert_eq!(
        trees("(\n  #loop:\n    #break;\n  #return 0;\n)"),
        trees("((#loop (#break)) (#return 0))")
    );
    assert_eq!(
        trees("`{ #body:\n  #for-range (i #u64) 0 ,end:\n    use { value = i; };\n}"),
        trees("`{ #body = ((#for-range (i #u64) 0 ,end (#call use ((value i))))); }")
    );
    for source in [
        "{ #body:\n  #loop:\n  #break;\n}",
        "{ #body:\n  #loop:\n\t#break;\n}",
        "{ #body:\n  #loop:\n      #break;\n    #return 0;\n}",
    ] {
        assert!(lim::parse(source).is_err(), "accepted {source}");
    }
    let mut nested = String::from("{ #body:\n");
    for depth in 1..600 {
        nested.push_str(&format!("{}#loop:\n", "  ".repeat(depth)));
    }
    nested.push_str(&format!("{}#break;\n}}", "  ".repeat(600)));
    assert!(lim::parse(&nested).unwrap_err().contains("nesting"));
}

const PROGRAM: &str = include_str!("../examples/surface_syntax.lim");

#[test]
fn surface_diagnostics_suggest_public_syntax_and_point_to_the_written_operation() {
    let scratch = support::Scratch::new("surface-diagnostics");
    for (expression, operation) in [
        ("(#u64::div 10u64 2u64)", "#u64::div"),
        ("#u64::div { left = 10u64; right = 2u64; }", "#u64::div"),
        ("[#u64; 10 / 2]", "/"),
    ] {
        let source = format!(
            "#fn main {{ #params = {{}}; #returns = #u64; #body = (#return {expression};); }}"
        );
        let error = lim::compile_source_to_assembly(
            &source,
            &scratch.path().join("main.lim"),
            &lim::CompileConfig::default(),
            &scratch.path().join("cache"),
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap_err();
        assert!(
            error.message.contains("[#u64 #wrap; ...]"),
            "{}",
            error.message
        );
        assert!(!error.message.contains("u64./"), "{}", error.message);
        let span = error.span.unwrap();
        assert_eq!(&source[span.start..span.end], operation);
    }
    let source =
        "#fn main { #params = {}; #returns = #u64; #body = (#return (#if true (#break) 0u64);); }";
    let error = lim::compile_source_to_assembly(
        source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err();
    assert!(error.message.contains("#block"), "{}", error.message);
    assert!(
        !error.message.contains("unknown function"),
        "{}",
        error.message
    );
    let span = error.span.unwrap();
    assert_eq!(&source[span.start..span.end], "#break");
    lim::check_types(
        &lim::parse_program(
            "#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#loop (#if true (#block (#break)) ())) (#return 42u64)\n  );\n}\n",
        )
        .unwrap(),
    )
    .unwrap();
}

#[test]
fn formatter_preserves_surface_layout_comments_and_canonical_trees() {
    for source in [
        PROGRAM,
        "{ left=x; right=[#u64 #wrap; a + b]; }",
        "\n  #fn f { #params = {}; #returns = (); #body =:\n    #return ();\n  }\n",
    ] {
        let formatted = lim::format_syntax(source).unwrap();
        assert_eq!(lim::format_syntax(&formatted).unwrap(), formatted);
        assert_eq!(trees(source), trees(&formatted));
    }
    let literal =
        "#fn text { #params = {}; #returns = (#array #char 3); #body = (#return \"x \n\";); }";
    assert_eq!(trees(literal), trees(&lim::format_syntax(literal).unwrap()));
}

#[test]
fn surface_program_executes_in_both_contract_modes_and_still_needs_evidence() {
    let scratch = support::Scratch::new("surface-syntax");
    for program in [PROGRAM, include_str!("../examples/surface_statics.lim")] {
        for instrumented in [false, true] {
            let mut config = lim::CompileConfig::default();
            if instrumented {
                config.set("contracts", "check");
            }
            let assembly = lim::compile_source_to_assembly(
                program,
                &scratch.path().join("main.lim"),
                &config,
                &scratch.path().join("cache"),
                lim::TargetDescription::X86_64_SYSTEM_V,
            )
            .unwrap_or_else(|error| panic!("{}", error.message));
            let binary = scratch.path().join("program");
            lim::link_native_binary(
                &assembly,
                &binary,
                &[],
                &[],
                lim::TargetDescription::X86_64_SYSTEM_V,
            )
            .unwrap();
            let status = support::run(
                &mut std::process::Command::new(binary),
                std::time::Duration::from_secs(5),
                4096,
            )
            .unwrap()
            .0;
            assert_eq!(status.code(), Some(42));
        }
    }
    let invalid = PROGRAM.replace("(widen { index = index; })", "()");
    let error = lim::check_types(&lim::parse_program(&invalid).unwrap()).unwrap_err();
    assert!(error.contains("missing evidence"), "{error}");
}

#[test]
fn surface_function_records_compose_with_async_generation() {
    fn work(nodes: &[lim::SpannedExpr]) -> Option<&lim::SpannedExpr> {
        for node in nodes {
            if matches!(&node.expr, lim::Expr::List(parts) if matches!(parts.first(), Some(lim::Expr::Symbol(head)) if head == "#fn") && matches!(parts.get(1), Some(lim::Expr::Symbol(name)) if name == "work"))
            {
                return Some(node);
            }
            if let Some(found) = work(&node.children) {
                return Some(found);
            }
        }
        None
    }
    let mut source = include_str!("../examples/async_fn.lim").to_owned();
    let nodes = lim::parse_source_unit(&source).unwrap();
    let function = work(&nodes).unwrap();
    let (effects, body_start) = match function.children.get(4) {
        Some(clause)
            if matches!(&clause.expr, lim::Expr::List(parts)
                if matches!(parts.first(), Some(lim::Expr::Symbol(head)) if head == "#effects")) =>
        {
            let value = &clause.children[1];
            (
                format!("#effects = {}; ", &source[value.span.start..value.span.end]),
                5,
            )
        }
        _ => (String::new(), 4),
    };
    let body = function.children[body_start..]
        .iter()
        .map(|node| &source[node.span.start..node.span.end])
        .collect::<Vec<_>>()
        .join("\n")
        .replace(
            "(#u64::add-wrap total offset)",
            "[#u64 #wrap; total + offset]",
        );
    let replacement = format!(
        "(#fn work {{ #params = {{ offset = #u64; }}; #returns = #u64; {effects}#body = ({body}); }})"
    );
    source.replace_range(function.span.start..function.span.end, &replacement);
    let scratch = support::Scratch::new("surface-async");
    let entry = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/async_fn.lim");
    for instrumented in [false, true] {
        let mut config = lim::CompileConfig::default();
        if instrumented {
            config.set("contracts", "check");
        }
        lim::compile_source_to_assembly(
            &source,
            &entry,
            &config,
            &scratch.path().join("cache"),
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap_or_else(|error| panic!("{}", error.message));
    }
}
