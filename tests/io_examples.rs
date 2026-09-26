mod support;

use std::{
    io::Write,
    process::{Command, Stdio},
};

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
