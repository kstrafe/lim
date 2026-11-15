use std::{
    fs,
    os::unix::process::CommandExt,
    process::{Command, Stdio},
    time::Duration,
};

mod support;

fn replace_call(source: &str, old: &str, new: &str) -> String {
    fn visit(node: &lim::SpannedExpr, old: &str, new: &str, edits: &mut Vec<(lim::Span, String)>) {
        if matches!(node.children.first().map(|child| &child.expr), Some(lim::Expr::Symbol(head)) if matches!(head.as_str(), "#call" | "#unsafe-call"))
        {
            if let Some(lim::Expr::Symbol(name)) = node.children.get(1).map(|child| &child.expr) {
                if name == old {
                    edits.push((node.children[1].span, new.to_owned()));
                }
            }
        }
        for child in &node.children {
            visit(child, old, new, edits);
        }
    }
    let mut output = source.to_owned();
    let mut edits = Vec::new();
    for node in lim::parse_source_unit(source).unwrap() {
        visit(&node, old, new, &mut edits);
    }
    edits.sort_by_key(|(span, _)| span.start);
    for (span, text) in edits.into_iter().rev() {
        output.replace_range(span.start..span.end, &text);
    }
    output
}

fn run(
    input: &[u8],
    seed: &str,
    expected_error: &str,
    close_stdin: bool,
    fail_realloc: bool,
) -> (i32, Vec<u8>, Vec<u8>) {
    let scratch = support::Scratch::new("stdin-strings");
    let input_path = scratch.path().join("input");
    fs::write(&input_path, input).unwrap();
    let library = scratch.path().join("stdin.lim");
    let stdio = scratch.path().join("stdio.lim");
    fs::write(&library, include_str!("../library/stdin.lim")).unwrap();
    fs::write(&stdio, include_str!("../library/stdio.lim")).unwrap();
    fs::write(
        scratch.path().join("string.lim"),
        include_str!("../library/string.lim"),
    )
    .unwrap();
    let mut allocator = include_str!("../library/system_allocator.lim").to_owned();
    if fail_realloc {
        allocator = replace_call(
            &allocator,
            "system-heap-reallocate",
            "stdin-failing-reallocate",
        );
        allocator.push_str("\n#unsafe-fn stdin-failing-reallocate {\n  #params = ((pointer (#ptr-mut #u8)) (size #usize));\n  #returns = (#ptr-mut #u8);\n  #body = (\n    (#return (#ptr-null (#ptr-mut #u8)))\n  );\n}\n");
    }
    fs::write(scratch.path().join("system_allocator.lim"), allocator).unwrap();
    let source = format!(
        "// stdin {0}, stdio {1}\n#alias StdReadResult = ./stdin.lim::StdReadResult\n#alias StdReadError = ./stdin.lim::StdReadError\n#alias std-read-line = ./stdin.lim::std-read-line\n#alias emit = ./stdio.lim::std-println\n#alias String = ./string.lim::String\n#alias StringStatus = ./string.lim::StringStatus\n#alias StringError = ./string.lim::StringError\n#alias String::new = ./string.lim::String::new\n#alias String::len = ./string.lim::String::len\n#alias String::clear = ./string.lim::String::clear\n#alias String::free = ./string.lim::String::free\n#alias String::push-chars = ./string.lim::String::push-chars\n#alias String::push-char = ./string.lim::String::push-char\n#fn main {{\n  #params = ();\n  #returns = #u64;\n  #effects = ((#effects-of String::free) (#effects-of emit) (#effects-of std-read-line)); #body = (\n    (#let-mut text String (#call String::new ()))\n    {2}\n    (#let-mut finished #bool false)\n    (#while (#bool::eq finished false)\n      (#let before #usize (#call String::len ((string (#borrow text)))))\n      (#match (#call std-read-line ((string (#borrow-mut text))))\n        (#case (StdReadResult.StdLineRead count) (#block\n          (#assert (#usize::eq (#usize::add-wrap before count) (#call String::len ((string (#borrow text))))))\n          (#assert (#i64::eq (#call emit ((text (#borrow text)))) 0i64))\n          (#call String::clear ((string (#borrow-mut text))))\n          ()))\n        (#case StdReadResult.StdEndOfInput (#block (#set finished true) ()))\n        (#case (StdReadResult.StdReadFailed error) (#block\n          (#assert {3})\n          (#assert (#i64::eq (#call emit ((text (#borrow text)))) 0i64))\n          (#set finished true)\n          ()))))\n    (#call String::free ((string text)))\n    (#return 42u64)\n  );\n}}\n",
        library.display(),
        stdio.display(),
        seed,
        expected_error
    );
    let assembly = lim::compile_source_to_assembly(
        &source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_or_else(|error| panic!("{error:?}"));
    let executable = scratch.path().join("program");
    lim::link_native_binary(
        &assembly,
        &executable,
        &[],
        &[],
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    let input_file = fs::File::open(input_path).unwrap();
    let mut command = Command::new(executable);
    if close_stdin {
        command.stdin(Stdio::null());
        unsafe {
            command.pre_exec(|| {
                unsafe extern "C" {
                    fn close(fd: i32) -> i32;
                }
                if close(0) == 0 {
                    Ok(())
                } else {
                    Err(std::io::Error::last_os_error())
                }
            });
        }
    } else {
        command.stdin(input_file);
    }
    let (status, stdout, stderr) =
        support::run(&mut command, Duration::from_secs(5), 4096).unwrap();
    (status.code().unwrap_or(-1), stdout, stderr)
}

#[test]
fn reads_empty_and_utf8_lines_and_handles_eof() {
    let (status, stdout, stderr) = run("\né🙂\na\0b\nlast".as_bytes(), "", "false", false, false);
    assert_eq!(status, 42, "{stderr:?}");
    assert_eq!(stdout, "\né🙂\na\0b\nlast\n".as_bytes());
    assert!(stderr.is_empty());
}

#[test]
fn malformed_and_incomplete_utf8_returns_exact_text_error() {
    for input in [
        &[0xff][..],
        &[0xc0, 0xaf],
        &[0xed, 0xa0, 0x80],
        &[0xf4, 0x90, 0x80, 0x80],
        &[0xe2, 0x82],
    ] {
        let (status, stdout, stderr) = run(
            input,
            "",
            "(#match error (#case (StdReadError.StdTextError StringError.StringInvalidUtf8) true) (#case _ false))",
            false,
            false,
        );
        assert_eq!(status, 42, "input {input:?}: {stderr:?}");
        assert_eq!(stdout, b"\n", "input {input:?}");
        assert!(stderr.is_empty());
    }
}

#[test]
fn invalid_utf8_preserves_existing_text_and_valid_prefix() {
    let seed = "(#assert (#match (#call String::push-char ((string (#borrow-mut text)) (value #\\P))) (#case StringStatus.StringOk true) (#case _ false)))";
    let (status, stdout, stderr) = run(
        b"x\xff",
        seed,
        "(#match error (#case (StdReadError.StdTextError StringError.StringInvalidUtf8) true) (#case _ false))",
        false,
        false,
    );
    assert_eq!(status, 42, "{stderr:?}");
    assert_eq!(stdout, b"Px\n");
    assert!(stderr.is_empty());
}

#[test]
fn empty_input_prints_nothing() {
    let (status, stdout, stderr) = run(b"", "", "false", false, false);
    assert_eq!(status, 42, "{stderr:?}");
    assert!(stdout.is_empty() && stderr.is_empty());
}

#[test]
fn closed_stdin_returns_exact_io_error() {
    let (status, stdout, stderr) = run(
        b"",
        "",
        "(#match error (#case (StdReadError.StdIoError code) (#i64::eq code -9i64)) (#case _ false))",
        true,
        false,
    );
    assert_eq!(status, 42, "{stderr:?}");
    assert_eq!(stdout, b"\n");
    assert!(stderr.is_empty());
}

#[test]
fn allocation_failure_preserves_appended_prefix() {
    let (status, stdout, stderr) = run(
        b"123456789\n",
        "",
        "(#match error (#case (StdReadError.StdTextError StringError.StringOutOfMemory) true) (#case _ false))",
        false,
        true,
    );
    assert_eq!(status, 42, "{stderr:?}");
    assert_eq!(stdout, b"12345678\n");
    assert!(stderr.is_empty());
}

#[test]
fn bundled_reader_example_echoes_utf8_input() {
    let scratch = support::Scratch::new("stdin-bundled-example");
    let input = scratch.path().join("input");
    fs::write(&input, "hello\né🙂\nlast").unwrap();
    let assembly = lim::compile_source_to_assembly(
        include_str!("../examples/string_stdin.lim"),
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_or_else(|error| panic!("{error:?}"));
    let executable = scratch.path().join("program");
    lim::link_native_binary(
        &assembly,
        &executable,
        &[],
        &[],
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    let (status, stdout, stderr) = support::run(
        Command::new(executable).stdin(fs::File::open(input).unwrap()),
        Duration::from_secs(5),
        4096,
    )
    .unwrap();
    assert_eq!(status.code(), Some(42), "{stderr:?}");
    assert_eq!(stdout, "hello\né🙂\nlast\n".as_bytes());
    assert!(stderr.is_empty());
}
