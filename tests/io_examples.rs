mod support;

use std::{
    collections::HashSet,
    io::Write,
    process::{Command, Stdio},
};

#[test]
fn native_x86_64_syscall_catalog_is_complete_and_ordered() {
    let source = include_str!("../library/linux_x86_64_syscall_numbers.lim");
    let mut names = HashSet::new();
    let mut entries = Vec::new();
    for line in source.lines() {
        let Some(rest) = line.strip_prefix("(#const LINUX-SYS-") else {
            continue;
        };
        let (name, rest) = rest.split_once(' ').expect("syscall name and type");
        let value = rest
            .strip_prefix("usize ")
            .and_then(|value| value.strip_suffix("usize)"))
            .expect("usize syscall number")
            .parse::<u16>()
            .expect("numeric syscall number");
        assert!(names.insert(name), "duplicate syscall name {name}");
        entries.push((name, value));
    }

    assert_eq!(entries.len(), 386);
    assert_eq!(entries.first(), Some(&("READ", 0)));
    assert_eq!(entries.last(), Some(&("FCHROOT", 472)));
    assert!(entries.windows(2).all(|pair| pair[0].1 < pair[1].1));
    for (name, number) in [
        ("PIPE2", 293),
        ("OPENAT2", 437),
        ("GETRANDOM", 318),
        ("MSEAL", 462),
    ] {
        assert!(entries.contains(&(name, number)), "missing {name}={number}");
    }
}

#[test]
fn echo_example_prints_the_bytes_read_from_standard_input() {
    let scratch = support::Scratch::new("io-example");
    let executable = scratch.path().join("echo-input");
    let example = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/echo_input.lim");
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(example)
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("run Lim compiler");
    assert!(
        compilation.status.success(),
        "compiler failed:\n{}",
        String::from_utf8_lossy(&compilation.stderr)
    );

    let assembly = scratch.path().join("echo-input.s");
    let emission = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg("--emit-asm")
        .arg(std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/echo_input.lim"))
        .arg(&assembly)
        .output()
        .expect("emit echo assembly");
    assert!(
        emission.status.success(),
        "assembly emission failed:\n{}",
        String::from_utf8_lossy(&emission.stderr)
    );
    let assembly = std::fs::read_to_string(assembly).expect("read emitted assembly");
    assert!(assembly.contains("syscall"));
    assert!(!assembly.contains(".extern read"));
    assert!(!assembly.contains(".extern write"));

    let input = b"hello from Lim\n";
    let mut child = Command::new(executable)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("run compiled echo example");
    child
        .stdin
        .take()
        .expect("piped stdin")
        .write_all(input)
        .expect("write test input");
    let output = child.wait_with_output().expect("wait for echo example");
    assert!(
        output.status.success(),
        "echo example failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(output.stdout, input);
}

#[test]
fn linux_syscall_wrappers_report_kernel_results() {
    let scratch = support::Scratch::new("linux-syscalls");
    let executable = scratch.path().join("syscall-checks");
    let example =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/linux_syscalls.lim");
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(example)
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("run Lim compiler");
    assert!(
        compilation.status.success(),
        "compiler failed:\n{}",
        String::from_utf8_lossy(&compilation.stderr)
    );

    let output = Command::new(executable)
        .output()
        .expect("run compiled syscall checks");
    assert_eq!(output.status.code(), Some(42));
    assert!(output.stdout.is_empty());
    assert!(output.stderr.is_empty());
}

#[test]
fn linux_process_queries_match_kernel_results() {
    let scratch = support::Scratch::new("linux-process-queries");
    let executable = scratch.path().join("process-queries");
    let example =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/linux_process_queries.lim");
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(example)
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("compile Lim process query example");
    assert!(
        compilation.status.success(),
        "compiler failed:\n{}",
        String::from_utf8_lossy(&compilation.stderr)
    );

    let output = Command::new(executable)
        .output()
        .expect("run compiled process query example");
    assert_eq!(output.status.code(), Some(42));
    assert!(output.stdout.is_empty());
    assert!(output.stderr.is_empty());
}

#[test]
fn linux_memfd_file_operations_match_kernel_results() {
    let scratch = support::Scratch::new("linux-memfd");
    let executable = scratch.path().join("memfd-checks");
    let example = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/linux_memfd.lim");
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(example)
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("compile Lim memfd example");
    assert!(
        compilation.status.success(),
        "compiler failed:\n{}",
        String::from_utf8_lossy(&compilation.stderr)
    );

    let output = Command::new(executable)
        .output()
        .expect("run compiled memfd example");
    assert_eq!(output.status.code(), Some(42));
    assert!(output.stdout.is_empty());
    assert!(output.stderr.is_empty());
}
