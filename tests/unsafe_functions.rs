use std::{fs, path::Path, process::Command, time::Duration};

mod support;

const DECLARATION: &str = "#unsafe-fn answer {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 42u64)\n  );\n}\n";

fn compile(source: &str, path: &Path, cache: &Path) -> Result<String, lim::Diagnostic> {
    lim::compile_source_to_assembly(
        source,
        path,
        &lim::CompileConfig::default(),
        cache,
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
}

#[test]
fn unsafe_calls_require_a_block_and_highlight_the_callee() {
    let scratch = support::Scratch::new("unsafe-function");
    let source = format!("{DECLARATION}\n#fn main {{\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return (#unsafe-call answer ()))\n  );\n}}\n");
    let error = compile(
        &source,
        &scratch.path().join("main.lim"),
        &scratch.path().join("cache"),
    )
    .unwrap_err();
    assert_eq!(error.code_string(), "E4300");
    assert!(error.message.contains("call to unsafe function 'answer'"));
    let span = error.span.unwrap();
    assert_eq!(&source[span.start..span.end], "answer");
    let source =
        format!("{DECLARATION}\n#fn main {{\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return (#unsafe (#unsafe-call answer ())))\n  );\n}}\n");
    let assembly = compile(
        &source,
        &scratch.path().join("main.lim"),
        &scratch.path().join("cache"),
    )
    .unwrap();
    let binary = scratch.path().join("program");
    lim::link_native_binary(
        &assembly,
        &binary,
        &[],
        &[],
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    let (status, stdout, stderr) =
        support::run(&mut Command::new(binary), Duration::from_secs(5), 1024).unwrap();
    assert_eq!(status.code(), Some(42));
    assert!(stdout.is_empty() && stderr.is_empty());
}

#[test]
fn declaration_does_not_make_the_function_body_implicitly_unsafe() {
    let scratch = support::Scratch::new("unsafe-body");
    let source = "#unsafe-fn read-byte {\n  #params = ((pointer (#ptr #u8)));\n  #returns = #u8;\n  #body = ( (#return (#ptr-read pointer))\n  );\n}\n";
    let error = compile(
        source,
        &scratch.path().join("main.lim"),
        &scratch.path().join("cache"),
    )
    .unwrap_err();
    assert_eq!(error.code_string(), "E4300");
    let span = error.span.unwrap();
    assert_eq!(&source[span.start..span.end], "#ptr-read");
}

fn assert_error(source: &str, code: &str, message: &str, highlighted: &str) -> lim::Diagnostic {
    let scratch = support::Scratch::new("unsafe-call-diagnostic");
    let error = compile(
        source,
        &scratch.path().join("main.lim"),
        &scratch.path().join("cache"),
    )
    .unwrap_err();
    assert_eq!(error.code_string(), code, "{error:?}");
    assert!(error.message.contains(message), "{error:?}");
    let span = error.span.expect("call diagnostic must have a source span");
    assert_eq!(&source[span.start..span.end], highlighted, "{error:?}");
    error
}

#[test]
fn call_spelling_must_match_the_declarations_safety_even_inside_unsafe() {
    for (declaration, call, message) in [
        (DECLARATION, "#call", "#unsafe-call"),
        (
            "#extern-fn  answer {\n  #abi = #abi-c;\n  #params = ();\n  #returns = #u64;\n}\n",
            "#call",
            "#unsafe-call",
        ),
        (
            "#fn answer {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 42u64)\n  );\n}\n",
            "#unsafe-call",
            "safe function",
        ),
    ] {
        for block in ["#block", "#unsafe"] {
            let source =
                format!("{declaration}\n#fn main {{\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return ({block} ({call} answer ())))\n  );\n}}\n");
            assert_error(&source, "E4000", message, "answer");
        }
    }
}

#[test]
fn unsafe_calls_in_an_unsafe_function_body_still_require_a_block() {
    let scratch = support::Scratch::new("unsafe-body-explicit");
    let source =
        format!("{DECLARATION}\n#unsafe-fn caller {{\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return (#unsafe-call answer ()))\n  );\n}}\n");
    assert_error(
        &source,
        "E4300",
        "call to unsafe function 'answer'",
        "answer",
    );
    compile(
        &source.replace(
            "(#unsafe-call answer ())",
            "(#unsafe (#unsafe-call answer ()))",
        ),
        &scratch.path().join("main.lim"),
        &scratch.path().join("cache"),
    )
    .unwrap();
}

#[test]
fn unsafe_calls_normalize_named_arguments_and_preserve_error_spans() {
    let declaration = "#unsafe-fn combine {\n  #params = ((left #u64) (right #bool));\n  #returns = #u64;\n  #body = ( (#return left)\n  );\n}\n";
    for (arguments, code, message, highlighted) in [
        (
            "(right true) (left 2u64) (left 3u64)",
            "E4000",
            "more than once",
            "left",
        ),
        (
            "(right true) (other 2u64)",
            "E4000",
            "no parameter 'other'",
            "other",
        ),
        (
            "(right true)",
            "E4000",
            "missing parameter 'left'",
            "#unsafe-call",
        ),
        ("(right 1u64) (left 2u64)", "E4000", "expected Bool", "1u64"),
        (
            "(right true) (left false)",
            "E4000",
            "expected U64",
            "false",
        ),
    ] {
        let source = format!(
            "{declaration}\n#fn main {{\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return (#unsafe (#unsafe-call combine ({arguments}))))\n  );\n}}\n"
        );
        let error = assert_error(&source, code, message, highlighted);
        if message == "more than once" {
            assert_eq!(
                error.span.unwrap().start,
                source.rfind("left 3u64").unwrap()
            );
        }
    }
}

#[test]
fn nested_unsafe_named_argument_errors_highlight_the_inner_value() {
    let declarations = "
#unsafe-fn combine {
  #params = ((left #u64) (right #bool));
  #returns = #u64;
  #body = ( (#return left)
  );
}
#fn ready {
  #params = ((value #bool));
  #returns = #bool;
  #body = ( (#return value)
  );
}
#unsafe-fn guarded-ready {
  #params = ((value #bool));
  #returns = #bool;
  #body = ( (#return value)\n  );\n}\n";
    for call in ["#call ready", "#unsafe-call guarded-ready"] {
        let source = format!(
            "{declarations}
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
                (#return (#unsafe (#unsafe-call combine
                  ((right ({call} ((value 1u64)))) (left 2u64)))))
  );\n}}\n"
        );
        assert_error(&source, "E4000", "expected Bool", "1u64");
    }
}

#[test]
fn unsafe_named_arguments_evaluate_once_in_written_order() {
    let scratch = support::Scratch::new("unsafe-call-order");
    let source = "
#fn next {
  #params = ((counter (#ref-mut #u64)) (expected #u64));
  #returns = #u64;
  #body = (
          (#assert (#u64::eq (#deref counter) expected))
          (#deref-set counter (#u64::add-wrap expected 1u64))
          (#return expected)
  );
}
#unsafe-fn combine {
  #params = ((left #u64) (right #u64));
  #returns = #u64;
  #body = (
          (#assert (#u64::eq left 1u64))
          (#assert (#u64::eq right 0u64))
          (#return 42u64)
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let-mut counter #u64 0u64)
          (#let result #u64 (#unsafe (#unsafe-call combine
            ((right (#call next ((counter (#borrow-mut counter)) (expected 0u64))))
             (left (#call next ((counter (#borrow-mut counter)) (expected 1u64))))))))
          (#assert (#u64::eq counter 2u64))
          (#return result)\n  );\n}\n";
    let assembly = compile(
        source,
        &scratch.path().join("main.lim"),
        &scratch.path().join("cache"),
    )
    .unwrap();
    let binary = scratch.path().join("program");
    lim::link_native_binary(
        &assembly,
        &binary,
        &[],
        &[],
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    let (status, stdout, stderr) =
        support::run(&mut Command::new(binary), Duration::from_secs(5), 1024).unwrap();
    assert_eq!(status.code(), Some(42), "{stderr:?}");
    assert!(stdout.is_empty() && stderr.is_empty());
}

#[test]
fn external_imports_and_generated_declarations_preserve_safety() {
    let scratch = support::Scratch::new("unsafe-import-generator");
    fs::write(
        scratch.path().join("module.lim"),
        format!("{DECLARATION}\n#fn safe-answer {{\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 42u64)\n  );\n}}\n#extern-fn  foreign-answer {{\n  #abi = #abi-c;\n  #params = ();\n  #returns = #u64;\n}}\n"),
    )
    .unwrap();
    for (declarations, unsafe_names, safe_name) in [
        (
            "#alias answer = ./module.lim::answer\n#alias foreign-answer = ./module.lim::foreign-answer\n#alias safe-answer = ./module.lim::safe-answer\n",
            &["answer", "foreign-answer"][..],
            "safe-answer",
        ),
        (
            "#alias ext@answer = ./module.lim::answer\n#alias ext@foreign-answer = ./module.lim::foreign-answer\n#alias ext@safe-answer = ./module.lim::safe-answer\n",
            &["ext@answer", "ext@foreign-answer"][..],
            "ext@safe-answer",
        ),
        (
            "#gn make (name safe-name) `((#unsafe-fn ,name () #u64 (#return 42u64)) (#fn ,safe-name () #u64 (#return 42u64)))\n#generate make answer safe-answer\n",
            &["answer"][..],
            "safe-answer",
        ),
    ] {
        for name in unsafe_names {
            for (call, block, code, message) in [
                ("#call", "#block", Some("E4000"), "#unsafe-call"),
                ("#call", "#unsafe", Some("E4000"), "#unsafe-call"),
                ("#unsafe-call", "#block", Some("E4300"), "requires an enclosing"),
                ("#unsafe-call", "#unsafe", None, ""),
            ] {
                let source = format!("{declarations}\n#fn main {{\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return ({block} ({call} {name} ())))\n  );\n}}\n");
                let result = compile(&source, &scratch.path().join("main.lim"), &scratch.path().join("cache"));
                if let Some(code) = code {
                    let error = result.unwrap_err();
                    assert_eq!(error.code_string(), code, "{error:?}");
                    assert!(error.message.contains(message), "{error:?}");
                    let span = error.span.unwrap();
                    assert_eq!(&source[span.start..span.end], *name, "{error:?}");
                } else {
                    result.unwrap();
                }
            }
        }
        for (call, expected_code) in [("#call", None), ("#unsafe-call", Some("E4000"))] {
            let source = format!("{declarations}\n#fn main {{\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return (#unsafe ({call} {safe_name} ())))\n  );\n}}\n");
            let result = compile(&source, &scratch.path().join("main.lim"), &scratch.path().join("cache"));
            if let Some(code) = expected_code {
                let error = result.unwrap_err();
                assert_eq!(error.code_string(), code, "{error:?}");
                assert!(error.message.contains("safe function"), "{error:?}");
                let span = error.span.unwrap();
                assert_eq!(&source[span.start..span.end], safe_name);
            } else {
                result.unwrap();
            }
        }
    }
}

#[test]
fn generated_gensym_calls_preserve_safety_and_cached_diagnostic_spans() {
    let scratch = support::Scratch::new("unsafe-gensym-call");
    for (declaration, call, expected) in [
        ("#unsafe-fn", "#unsafe-call", None),
        ("#unsafe-fn", "#call", Some("#unsafe-call")),
        ("#fn", "#unsafe-call", Some("safe function")),
    ] {
        let source = format!(
            "#gn-fn emit (name) `(({declaration} ,name () #u64 (#return 42u64))
                (#fn main () #u64 (#return (#unsafe ({call} ,name ())))))
#gn generate () (#gn-call emit (#gn-gensym \"answer\"))\n#generate generate\n"
        );
        let compile = || {
            compile(
                &source,
                &scratch.path().join("main.lim"),
                &scratch.path().join("cache"),
            )
        };
        if let Some(message) = expected {
            let cold = compile().unwrap_err();
            let warm = compile().unwrap_err();
            assert_eq!(cold.code_string(), "E4000", "{cold:?}");
            assert!(cold.message.contains(message), "{cold:?}");
            assert_eq!(cold.span, warm.span);
            assert_eq!(cold.source_text, warm.source_text);
            let span = cold.span.unwrap();
            let generated = cold.source_text.as_deref().unwrap();
            assert!(
                generated[span.start..span.end].starts_with("lim.gensym."),
                "{cold:?}"
            );
        } else {
            compile().unwrap();
            compile().unwrap();
        }
    }
}

#[test]
fn implicit_entry_points_cannot_bypass_unsafe_calls() {
    let scratch = support::Scratch::new("unsafe-implicit-call");
    for (source, message) in [
        ("#unsafe-fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 42u64)\n  );\n}\n", "implicit entry point 'main' must be safe"),
        ("#struct Value () ((n #u64))\n#unsafe-fn Value::clone {\n  #params = ((value Value));\n  #returns = Value;\n  #body = ( (#return value)\n  );\n}\n", "implicit entry point 'Value::clone' must be safe"),
        ("#unsafe-fn worker {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return 42u64)\n  );\n}\n#generate #thread-spawn ((task Task) (worker worker))\n", "thread worker 'worker' must be safe"),
    ] {
        let error = compile(source, &scratch.path().join("main.lim"), &scratch.path().join("cache")).unwrap_err();
        assert!(error.message.contains(message), "{}", error.message);
        assert!(error.span.is_some());
    }
}

#[test]
fn io_uring_raw_pointer_contracts_are_enforced() {
    let scratch = support::Scratch::new("unsafe-syscall");
    let library = Path::new(env!("CARGO_MANIFEST_DIR")).join("library/linux_x86_64.lim");
    let source = format!("#alias linux-io-uring-setup = \"{}::linux-io-uring-setup\"\n#fn main {{\n  #params = ();\n  #returns = #i64;\n  #body = ( (#return (#unsafe-call linux-io-uring-setup ((entries 2u32) (parameters (#ptr-null (#ptr-mut #u8))))))\n  );\n}}\n", library.to_str().unwrap());
    let error = compile(
        &source,
        &scratch.path().join("main.lim"),
        &scratch.path().join("cache"),
    )
    .unwrap_err();
    assert_eq!(error.code_string(), "E4300");
    assert!(error.message.contains("linux-io-uring-setup"));
}

#[test]
fn every_unsafe_linux_wrapper_requires_a_block_in_both_cfg_branches() {
    use std::collections::BTreeMap;

    fn collect(
        node: &lim::SpannedExpr,
        source: &str,
        probes: &mut BTreeMap<String, (String, String)>,
    ) {
        if !matches!(node.expr, lim::Expr::List(_)) {
            return;
        }
        let items = &node.children;
        if matches!(items.first().map(|n| &n.expr), Some(lim::Expr::Symbol(head)) if head == "#unsafe-fn")
        {
            let lim::Expr::Symbol(name) = &items[1].expr else {
                panic!("function name")
            };
            let parameters = &source[items[2].span.start..items[2].span.end];
            let result = &source[items[3].span.start..items[3].span.end];
            let mut arguments = String::new();
            for parameter in &items[2].children {
                let lim::Expr::Symbol(name) = &parameter.children[0].expr else {
                    panic!("parameter name")
                };
                arguments.push_str(&format!(" ({name} {name})"));
            }
            let signature = format!("#fn probe-{name} {parameters} {result}");
            let call = format!("(#unsafe-call {name} ({arguments}))");
            // The structural coverage suite compares signatures. Here retain
            // one spelling: cfg branches may format the same types differently.
            probes.entry(name.clone()).or_insert((signature, call));
        }
        for child in items {
            collect(child, source, probes);
        }
    }

    let scratch = support::Scratch::new("unsafe-all-syscalls");
    let library = Path::new(env!("CARGO_MANIFEST_DIR")).join("library/linux_x86_64.lim");
    let contents = fs::read_to_string(&library).unwrap();
    let mut probes = BTreeMap::new();
    for node in lim::parse_source_unit(&contents).unwrap() {
        collect(&node, &contents, &mut probes);
    }
    assert!(probes.len() >= 201);
    let mut import = String::new();
    for node in lim::parse_source_unit(&contents).unwrap() {
        fn types(node: &lim::SpannedExpr, path: &Path, output: &mut String) {
            if matches!(node.children.first().map(|n| &n.expr), Some(lim::Expr::Symbol(head)) if matches!(head.as_str(), "#struct" | "#enum" | "#type"))
            {
                if let lim::Expr::Symbol(name) = &node.children[1].expr {
                    let line = format!("#alias {name} = \"{}::{name}\"\n", path.display());
                    if !output.contains(&line) {
                        output.push_str(&line);
                    }
                }
            }
            for child in &node.children {
                types(child, path, output);
            }
        }
        types(&node, &library, &mut import);
    }
    for name in probes.keys() {
        import.push_str(&format!(
            "#alias {name} = \"{}::{name}\"\n",
            library.display()
        ));
    }
    let path = scratch.path().join("main.lim");
    let cache = scratch.path().join("cache");
    for os in ["linux", "unsupported"] {
        let mut config = lim::CompileConfig::default();
        config.set("os", os);
        config.set("arch", "x86_64");
        let mut explicit = import.clone();
        for (name, (signature, call)) in &probes {
            let source = format!("{import}{signature} (#return {call})");
            let error = lim::compile_source_to_assembly(
                &source,
                &path,
                &config,
                &cache,
                lim::TargetDescription::X86_64_SYSTEM_V,
            )
            .unwrap_err();
            assert_eq!(
                error.code_string(),
                "E4300",
                "{os}: {name}: {}",
                error.message
            );
            assert!(
                error.message.contains("call to unsafe function") && error.message.contains(name),
                "{}",
                error.message
            );
            let span = error.span.unwrap();
            assert_eq!(
                &source[span.start..span.end],
                name,
                "{os}: diagnostic location"
            );
            explicit.push_str(&format!("{signature} (#return (#unsafe {call}))\n"));
        }
        // Compile but do not execute: these forwarders intentionally have no
        // resources or valid buffers of their own. Runtime behavior is tested
        // by the syscall examples with real allocation/lifetime management.
        lim::compile_source_to_assembly(
            &explicit,
            &path,
            &config,
            &cache,
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap_or_else(|error| panic!("{os}: explicit unsafe calls: {}", error.message));
    }
}

#[test]
fn safe_generator_capabilities_reject_unsafe_operations() {
    let scratch = support::Scratch::new("unsafe-capability");
    let source = "#unsafe-fn less {
  #params = ((a (#ref #u64)) (b (#ref #u64)));
  #returns = #bool;
  #body = ( (#return false)
  );
}
#capability ordered #u64 ((less ((#ref #u64) (#ref #u64)) #bool))\n";
    let error = compile(
        source,
        &scratch.path().join("main.lim"),
        &scratch.path().join("cache"),
    )
    .unwrap_err();
    assert!(
        error.message.contains("contract requires"),
        "{}",
        error.message
    );
    assert!(error.message.contains("unsafe"));
}
