mod support;

use lim::{
    check_theorem_details_from_path_with_config, render_checked_theorem_json,
    render_diagnostic_json, CompileConfig, Diagnostic, DiagnosticCode, ProofOutcome,
};
use std::{
    fs,
    process::{Command, ExitStatus},
    time::Duration,
};

fn check(source: &str, name: &str) -> Result<lim::CheckedTheorem, Diagnostic> {
    check_theorem_details_from_path_with_config(
        source,
        std::path::Path::new("main.lim"),
        &CompileConfig::default(),
        name,
    )
}

fn cli(source: &str, name: &str, json: bool) -> (ExitStatus, String, String) {
    let scratch = support::Scratch::new("proof-outcomes-cli");
    fs::write(scratch.path().join("main.lim"), source).unwrap();
    let mut command = Command::new(env!("CARGO_BIN_EXE_lim"));
    command
        .current_dir(scratch.path())
        .env("PATH", "")
        .args(["--check-theorem", "main.lim", name]);
    if json {
        command.arg("--diagnostic-format=json");
    }
    let (status, stdout, stderr) =
        support::run(&mut command, Duration::from_secs(20), 1024 * 1024).unwrap();
    (
        status,
        String::from_utf8(stdout).unwrap(),
        String::from_utf8(stderr).unwrap(),
    )
}

#[test]
fn outcomes_are_structured_and_not_guessed_from_diagnostic_text() {
    assert_eq!(
        check("(#theorem t true)", "t").unwrap().outcome,
        ProofOutcome::Proved
    );
    let cases = [
        ("(#theorem t false)", ProofOutcome::Counterexample),
        ("(#theorem t (#proof-for-all (: v #f32) true))", ProofOutcome::Unsupported),
        ("(#theorem t (#proof-eq 1u8))", ProofOutcome::Invalid),
        ("(#fn identity-countdown (: count #u8) #u8 (#let-mut remaining #u8 count) (#let-mut answer #u8 0u8) (#label again (#while (#u8::gt remaining 0u8) (#set answer (#u8::add-wrap answer 1u8)) (#set remaining (#u8::sub-wrap remaining 1u8)))) (#return answer)) (#theorem t (#proof-with-invariants ((identity-countdown again true remaining)) (#proof-not (#proof-contract identity-countdown true (#proof-eq (#proof-result) count)))))", ProofOutcome::InductionFailure),
    ];
    for (source, expected) in cases {
        let error = check(source, "t").unwrap_err();
        assert_eq!(
            error.proof_outcome(),
            Some(expected),
            "{source}: {}",
            error.message
        );
    }
    let mut deep = String::from("true");
    for _ in 0..48 {
        deep = format!("(#proof-not {deep})");
    }
    let source = format!("(#theorem t {deep})");
    assert_eq!(
        check(&source, "t").unwrap_err().proof_outcome(),
        Some(ProofOutcome::ResourceLimit)
    );

    let misleading = Diagnostic::new(DiagnosticCode::Proof, "disproved: invalid proposition");
    assert_eq!(misleading.proof_outcome(), None);
    assert!(render_diagnostic_json(&misleading, "").contains("\"proof_outcome\":null"));
    for (code, outcome) in [
        (
            DiagnosticCode::ProofCounterexample,
            ProofOutcome::Counterexample,
        ),
        (DiagnosticCode::ProofUnsupported, ProofOutcome::Unsupported),
        (
            DiagnosticCode::ProofResourceLimit,
            ProofOutcome::ResourceLimit,
        ),
        (DiagnosticCode::ProofInvalid, ProofOutcome::Invalid),
        (
            DiagnosticCode::ProofInduction,
            ProofOutcome::InductionFailure,
        ),
        (DiagnosticCode::ProofInternal, ProofOutcome::CheckerError),
    ] {
        let error = Diagnostic::new(
            code,
            "proved disproved budget exhausted unsupported invalid",
        );
        assert_eq!(error.proof_outcome(), Some(outcome));
        assert!(error.code.is_proof());
        assert!(render_diagnostic_json(&error, "main.lim")
            .contains(&format!("\"proof_outcome\":\"{}\"", outcome.as_str())));
    }
}

#[test]
fn theorem_json_and_cli_render_proof_outcomes() {
    let checked = check("(#theorem canonical true)", "canonical").unwrap();
    assert_eq!(render_checked_theorem_json(&checked),
        "{\"schema_version\":1,\"category\":\"proof\",\"theorem\":\"canonical\",\"proof_outcome\":\"proved\"}");

    let (status, stdout, stderr) = cli("(#theorem actual true)", "actual", true);
    assert!(status.success(), "{stderr}");
    assert!(stderr.is_empty());
    assert!(stdout.contains("\"proof_outcome\":\"proved\""), "{stdout}");

    let (status, stdout, stderr) = cli("(#theorem actual false)", "actual", true);
    assert!(!status.success());
    assert!(stdout.is_empty());
    assert!(
        stderr.contains("\"proof_outcome\":\"counterexample\""),
        "{stderr}"
    );
}

#[test]
fn type_errors_have_no_proof_outcome() {
    let error = check("(#fn f () #u8 (#return true)) (#theorem t true)", "t").unwrap_err();
    assert_eq!(error.code, DiagnosticCode::Type);
    assert_eq!(error.proof_outcome(), None);
}
