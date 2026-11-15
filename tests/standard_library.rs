use std::{fs, path::Path, process::Command, time::Duration};

mod support;

fn compile(
    source: &str,
    path: &Path,
    config: &lim::CompileConfig,
) -> Result<String, lim::Diagnostic> {
    lim::compile_source_to_assembly(
        source,
        path,
        config,
        &path.parent().unwrap().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
}

fn execute(source: &str, label: &str, config: &lim::CompileConfig, expected: &[u8]) {
    let scratch = support::Scratch::new(label);
    let assembly = compile(source, &scratch.path().join("main.lim"), config)
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
    let (status, stdout, stderr) =
        support::run(&mut Command::new(binary), Duration::from_secs(5), 4096).unwrap();
    assert_eq!(status.code(), Some(42), "{stderr:?}");
    assert_eq!(stdout, expected);
    assert!(stderr.is_empty(), "{stderr:?}");
}

#[test]
fn std_string_append_and_println_example_runs_outside_checkout() {
    execute(
        include_str!("../examples/string_println.lim"),
        "std-example",
        &lim::CompileConfig::default(),
        include_bytes!("fixtures/string_println.stdout"),
    );
}

#[test]
fn println_borrows_and_writes_exact_utf8_including_nul_and_empty_strings() {
    execute(
        r#"#std
#fn main () #u64
          (#let bytes (#array #u8 5) (#array-of (#array #u8 5) 65u8 0u8 195u8 169u8 66u8))
          (#let-mut text String (#match (#call String::from-utf8 ((bytes (#slice-of (#borrow bytes)))))
            (#case (StringCreateResult.StringCreated created) created) (#case (StringCreateResult.StringCreateFailed error) (#panic))))
          (#assert (#i64::eq (#println (#borrow text)) 0i64))
          (#assert (#usize::eq (#call String::len ((string (#borrow text)))) 5usize))
          (#call String::clear ((string (#borrow-mut text))))
          (#assert (#i64::eq (#println (#borrow text)) 0i64))
          (#assert (#match (#call String::push-char ((string (#borrow-mut text)) (value #\!)))
            (#case StringStatus.StringOk true) (#case _ false)))
          (#assert (#i64::eq (#println (#borrow text)) 0i64))
          (#call String::free ((string text)))
          (#return 42u64)
"#,
        "std-print-bytes",
        &lim::CompileConfig::default(),
        b"A\0\xc3\xa9B\n\n!\n",
    );
}

#[test]
fn std_is_deduplicated_across_imports_and_cannot_be_shadowed_by_local_files() {
    let scratch = support::Scratch::new("std-imports");
    fs::write(
        scratch.path().join("std.lim"),
        "broken local standard library",
    )
    .unwrap();
    fs::write(scratch.path().join("string.lim"), "broken local String").unwrap();
    fs::write(
        scratch.path().join("a.lim"),
        "#std\n#fn a () #u64 (#return 20u64)\n",
    )
    .unwrap();
    fs::write(
        scratch.path().join("b.lim"),
        "#std\n#fn b () #u64 (#return 22u64)\n",
    )
    .unwrap();
    compile(
        "#std
#std
#alias a = ./a.lim::a
#alias b = ./b.lim::b
#fn main () #u64 (#let text String (#call String::new ()))
          (#call String::free ((string text)))
          (#return (#u64::add-wrap (#call a ()) (#call b ())))\n",
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
    )
    .unwrap();
}

#[test]
fn formatting_skips_embedded_std_but_formats_internal_imports() {
    let scratch = support::Scratch::new("std-format");
    let root = scratch.path().join("main.lim");
    let child = scratch.path().join("child.lim");
    fs::write(
        &root,
        "#std\n#alias helper = ./child.lim::helper\n#fn main () #u64 (#return 42u64)\n",
    )
    .unwrap();
    fs::write(&child, "#std\n#fn helper () () (#return ())\n").unwrap();
    let paths = lim::format_project_from_path(&root).unwrap();
    assert_eq!(paths.len(), 2);
    assert!(paths.contains(&root) && paths.contains(&child));
    let formatted = fs::read_to_string(&root).unwrap();
    assert_eq!(lim::format_source(&formatted).unwrap(), formatted);
    compile(&formatted, &root, &lim::CompileConfig::default()).unwrap();
}

#[test]
fn cfg_collection_includes_embedded_std_dependencies() {
    let scratch = support::Scratch::new("std-cfg-keys");
    let root = scratch.path().join("main.lim");
    fs::write(&root, "#std\n#fn main () #u64 (#return 42u64)\n").unwrap();
    assert_eq!(
        lim::collect_cfg_keys_from_path(&root).unwrap(),
        vec!["#arch", "#os"]
    );
}

#[test]
fn unsupported_stdio_cfg_returns_enosys_without_printing() {
    let mut config = lim::CompileConfig::default();
    config.set("os", "unsupported");
    execute(
        "#std
#fn main () #u64
        (#let text String (#call String::new ()))
        (#assert (#i64::eq (#println (#borrow text)) -38i64))
        (#call String::free ((string text))) (#return 42u64)\n",
        "std-unsupported",
        &config,
        b"",
    );
}

#[test]
fn std_and_println_errors_retain_exact_source_spans() {
    let cases = [
        ("#std wrong", "#std takes no arguments", "#std wrong"),
        (
            "#fn main () () (#println 1u64) (#return ())\n",
            "add (#std)",
            "#println",
        ),
        (
            "#std\n#fn main () () (#println) (#return ())\n",
            "exactly one shared String reference",
            "#println",
        ),
        (
            "#std\n#fn main () () (#println 1u64) (#return ())\n",
            "expected",
            "1u64",
        ),
        (
            "#fn consume ((status #i64)) () (#return ())
#fn main () () (#call consume ((status (#println 1u64)))) (#return ())\n",
            "add (#std)",
            "#println",
        ),
        (
            "#std\n#fn main () () (#std) (#return ())\n",
            "only valid as a top-level",
            "#std",
        ),
        (
            "#std
#fn main () () (#let text String (#call String::new ()))
               (#unsafe-call String::data-pointer ((string (#borrow text))))
               (#call String::free ((string text))) (#return ())\n",
            "unsafe",
            "String::data-pointer",
        ),
    ];
    for (index, (source, message, fragment)) in cases.into_iter().enumerate() {
        let scratch = support::Scratch::new(&format!("std-error-{index}"));
        let error = compile(
            source,
            &scratch.path().join("main.lim"),
            &lim::CompileConfig::default(),
        )
        .expect_err("invalid std use must fail");
        assert!(
            error.message.contains(message),
            "{index}: {}",
            error.message
        );
        let span = error.span.expect("error needs a precise span");
        assert_eq!(
            &source[span.start..span.end],
            fragment,
            "{index}: {}",
            error.message
        );
    }
}

#[test]
fn shared_string_cannot_be_appended_to_itself() {
    let scratch = support::Scratch::new("std-self-append");
    let source = "#std
#fn main () ()
        (#let-mut text String (#call String::new ()))
        (#call String::push-string ((string (#borrow-mut text)) (text (#borrow text))))
        (#call String::free ((string text))) (#return ())\n";
    let error = compile(
        source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
    )
    .expect_err("source and mutable target must be disjoint");
    assert_eq!(error.code_string(), "E4100", "{}", error.message);
}

#[test]
fn println_returns_descriptor_errors_without_consuming_the_string() {
    execute(
        r#"#std
#fn main () #u64
        (#let chars (#array #char 1) "x")
        (#let text String (#match (#call String::from-chars ((text (#slice-of (#borrow chars)))))
          (#case (StringCreateResult.StringCreated created) created) (#case _ (#panic))))
        (#assert (#i64::eq (#unsafe (#linux-syscall #i64 3usize (1i64))) 0i64))
        (#assert (#i64::eq (#println (#borrow text)) -9i64))
        (#assert (#usize::eq (#call String::len ((string (#borrow text)))) 1usize))
        (#call String::free ((string text))) (#return 42u64)
"#,
        "std-closed-stdout",
        &lim::CompileConfig::default(),
        b"",
    );
}

// Exercise the actual write-all loop with deterministic injected syscall
// outcomes, without depending on pipe capacity or timing signal delivery.
fn injected_stdio(syscall: &str) -> String {
    fn collect(node: &lim::SpannedExpr, syscall: &str, edits: &mut Vec<(usize, usize, String)>) {
        if matches!(node.children.first().map(|head| &head.expr),
            Some(lim::Expr::Symbol(head)) if head == "#unsafe-fn")
            && matches!(node.children.get(1).map(|name| &name.expr),
                Some(lim::Expr::Symbol(name)) if name == "std-write-all")
        {
            let position = node.children[3].span.end;
            edits.push((
                position,
                position,
                "\n  (#let-mut attempts #usize 0usize)".into(),
            ));
        }
        if matches!(node.children.first().map(|head| &head.expr),
            Some(lim::Expr::Symbol(head)) if head == "#linux-syscall")
        {
            edits.push((node.span.start, node.span.end, syscall.into()));
        }
        for child in &node.children {
            collect(child, syscall, edits);
        }
    }
    let mut source = include_str!("../library/stdio.lim").to_owned();
    let mut edits = Vec::new();
    for node in lim::parse_source_unit(&source).unwrap() {
        collect(&node, syscall, &mut edits);
    }
    assert_eq!(edits.len(), 2);
    edits.sort_by_key(|edit| edit.0);
    for (start, end, replacement) in edits.into_iter().rev() {
        source.replace_range(start..end, &replacement);
    }
    source
}

#[test]
fn write_all_retries_eintr_and_short_writes_and_stops_on_zero_progress() {
    for (label, replacement, result, expected) in [
        (
            "short-writes",
            r#"(#block
          (#set attempts (#usize::add-wrap attempts 1usize))
          (#if (#usize::eq attempts 1usize) -4i64
            (#linux-syscall #i64 1usize (1i64 (#ptr-offset pointer offset) 1usize))))"#,
            "0i64",
            b"abc\n".as_slice(),
        ),
        ("zero-progress", "0i64", "-5i64", b"".as_slice()),
    ] {
        let scratch = support::Scratch::new(label);
        fs::write(
            scratch.path().join("stdio.lim"),
            injected_stdio(replacement),
        )
        .unwrap();
        fs::write(
            scratch.path().join("string.lim"),
            include_str!("../library/string.lim"),
        )
        .unwrap();
        fs::write(
            scratch.path().join("system_allocator.lim"),
            include_str!("../library/system_allocator.lim"),
        )
        .unwrap();
        let source = format!(
            r#"#alias String = "{root}/string.lim::String"
#alias StringCreateResult = "{root}/string.lim::StringCreateResult"
#alias String::from-chars = "{root}/string.lim::String::from-chars"
#alias String::free = "{root}/string.lim::String::free"
#alias emit = "{root}/stdio.lim::std-println"
#fn main () #u64
            (#let chars (#array #char 3) "abc")
            (#let text String (#match (#call String::from-chars ((text (#slice-of (#borrow chars)))))
              (#case (StringCreateResult.StringCreated created) created) (#case _ (#panic))))
            (#assert (#i64::eq (#call emit ((text (#borrow text)))) {result}))
            (#call String::free ((string text))) (#return 42u64)
"#,
            root = scratch.path().display()
        );
        execute(&source, label, &lim::CompileConfig::default(), expected);
    }
}

#[test]
fn println_is_an_ordinary_borrow_checked_call_inside_async_functions() {
    execute(
        r#"#std
#generate #async-fn ((protocol work-await) (waker #u64) (function
          (#fn work ((text (#ref String))) #u64
            (#assert (#i64::eq (#println text) 0i64)) (#return 42u64))))
#fn main () #u64
          (#let chars (#array #char 2) "hi")
          (#let text String (#match (#call String::from-chars ((text (#slice-of (#borrow chars)))))
            (#case (StringCreateResult.StringCreated created) created) (#case _ (#panic))))
          (#let waker #u64 0u64)
          (#let result Work::Poll (#call Work::poll ((task (#call work ((text (#borrow text))))) (waker (#borrow waker)))))
          (#let answer #u64 (#match result (#case (Work::Poll.Ready value) value)
            (#case (Work::Poll.Pending unfinished) (#block (#forget unfinished) (#panic)))))
          (#call String::free ((string text))) (#return answer)
"#,
        "std-async-println",
        &lim::CompileConfig::default(),
        b"hi\n",
    );
}
