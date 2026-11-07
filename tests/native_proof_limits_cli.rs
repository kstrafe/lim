mod support;

use std::{fs, process::Command, time::Duration};

const IDENTITY: &str = include_str!("fixtures/lean_export/identity.ndjson");
const TARGET: &str = "Audit.identity.theorem";

fn cli(args: &[&str]) -> (std::process::ExitStatus, Vec<u8>, Vec<u8>) {
    let mut command = Command::new(env!("CARGO_BIN_EXE_lim"));
    command.args(args).env("PATH", "");
    support::run(&mut command, Duration::from_secs(10), 1024 * 1024).unwrap()
}

#[test]
fn emitted_identity_receipt_and_strict_artifact_check_share_native_profile() {
    let scratch = support::Scratch::new("native-proof-limits-cli");
    let input = scratch.path().join("identity.ndjson");
    let proof = scratch.path().join("identity.lim");
    let receipt = scratch.path().join("receipt.json");
    fs::write(&input, IDENTITY).unwrap();

    let (status, stdout, stderr) = cli(&[
        "--check-lean-export",
        input.to_str().unwrap(),
        TARGET,
        "--emit-proof",
        proof.to_str().unwrap(),
        "--report",
        receipt.to_str().unwrap(),
        "--native-proof-bytes",
        "16777216",
        "--native-proof-declarations",
        "5000",
    ]);
    assert!(status.success(), "{}", String::from_utf8_lossy(&stderr));
    let stdout = String::from_utf8(stdout).unwrap();
    assert!(stdout.contains("emitted native theorem"), "{stdout}");
    assert!(
        stdout.contains("native proof limits: bytes=16777216 declarations=5000"),
        "{stdout}"
    );
    let receipt = fs::read_to_string(&receipt).unwrap();
    assert!(receipt.contains("\"native_proof_limits\":"), "{receipt}");
    assert!(receipt.contains("\"max_bytes\":16777216"), "{receipt}");
    assert!(receipt.contains("\"max_declarations\":5000"), "{receipt}");

    let source = fs::read_to_string(&proof).unwrap();
    let native_target = source
        .lines()
        .find_map(|line| line.strip_prefix("; Native theorem: "))
        .expect("emitted proof names its native theorem");
    let (status, stdout, stderr) = cli(&[
        "--check-proof-artifact",
        proof.to_str().unwrap(),
        native_target,
        "--native-proof-bytes",
        "16777216",
        "--native-proof-declarations",
        "5000",
    ]);
    assert!(status.success(), "{}", String::from_utf8_lossy(&stderr));
    let stdout = String::from_utf8(stdout).unwrap();
    assert!(
        stdout.contains(&format!("checked proof artifact theorem {native_target}")),
        "{stdout}"
    );
    assert!(
        stdout.contains("native proof limits: bytes=16777216 declarations=5000"),
        "{stdout}"
    );
}

#[test]
fn validates_native_options_before_publishing_and_requires_emission() {
    let scratch = support::Scratch::new("native-proof-limit-errors");
    let input = scratch.path().join("identity.ndjson");
    let proof = scratch.path().join("existing.lim");
    fs::write(&input, IDENTITY).unwrap();
    fs::write(&proof, b"keep existing artifact").unwrap();

    let (status, stdout, _) = cli(&[
        "--check-lean-export",
        input.to_str().unwrap(),
        TARGET,
        "--emit-proof",
        proof.to_str().unwrap(),
        "--native-proof-bytes",
        "0",
    ]);
    assert!(!status.success());
    assert!(stdout.is_empty());
    assert_eq!(fs::read(&proof).unwrap(), b"keep existing artifact");

    for options in [
        vec!["--native-proof-bytes", "1", "--native-proof-bytes", "2"],
        vec!["--native-proof-bytes"],
        vec!["--native-proof-unknown", "1"],
    ] {
        let mut args = vec![
            "--check-lean-export",
            input.to_str().unwrap(),
            TARGET,
            "--emit-proof",
            proof.to_str().unwrap(),
        ];
        args.extend(options.iter().copied());
        let (status, stdout, _) = cli(&args);
        assert!(!status.success(), "accepted {options:?}");
        assert!(stdout.is_empty());
        assert_eq!(fs::read(&proof).unwrap(), b"keep existing artifact");
    }

    let (status, stdout, stderr) = cli(&[
        "--check-lean-export",
        input.to_str().unwrap(),
        TARGET,
        "--native-proof-bytes",
        "16777216",
    ]);
    assert!(!status.success());
    assert!(stdout.is_empty());
    assert!(String::from_utf8_lossy(&stderr).contains("require --emit-proof"));
}

#[test]
fn strict_artifact_checker_rejects_bad_proofs_and_nonmathematical_source() {
    let scratch = support::Scratch::new("native-proof-artifact-strict");
    let wrong = scratch.path().join("wrong.lim");
    let program = scratch.path().join("program.lim");
    fs::write(&wrong, "(#theorem wrong (#universes) (#parameters)\n  (#statement (#pt-eq #pt-nat #pt-zero (#pt-succ #pt-zero)))\n  (#proof (#pt-refl #pt-nat #pt-zero)))\n").unwrap();
    let (status, _, stderr) = cli(&["--check-proof-artifact", wrong.to_str().unwrap(), "wrong"]);
    assert!(!status.success());
    let diagnostic = String::from_utf8_lossy(&stderr);
    assert!(
        diagnostic.contains("wrong.lim") || diagnostic.contains("#pt-eq"),
        "{diagnostic}"
    );

    fs::write(&program, "#fn main\n  ()\n#import other\n").unwrap();
    let (status, _, stderr) = cli(&["--check-proof-artifact", program.to_str().unwrap(), "main"]);
    assert!(!status.success());
    assert!(!String::from_utf8_lossy(&stderr).is_empty());
}
