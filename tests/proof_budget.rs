mod support;

use lim::{
    lsp::json::{self, Json},
    CompileConfig, LeanFoundationPolicy, ProofBudget,
};
use std::{fs, io::Cursor, process::Command, time::Duration};

const IDENTITY: &str = include_str!("fixtures/lean_export/identity.ndjson");
const NATIVE: &str = "(#theorem reflexivity\n  (#universes u)\n  (#parameters (#parameter a (#pt-type u)) (#parameter value a))\n  (#statement (#pt-eq a value value))\n  (#proof (#pt-refl a value)))";

#[test]
fn defaults_and_explicit_budgets_are_reported_and_native_checking_keeps_budget() {
    let default = ProofBudget::default();
    assert_eq!(
        (default.work(), default.phase_bytes(), default.total_bytes()),
        (200_000, 64 << 20, 256 << 20)
    );
    let larger = ProofBudget::new(1_000_000, 128 << 20, 512 << 20).unwrap();
    let baseline = lim::check_lean_export_with_budget(
        Cursor::new(IDENTITY),
        "Audit.identity.theorem",
        LeanFoundationPolicy::Constructive,
        default,
    )
    .unwrap();
    let checked = lim::check_lean_export_with_budget(
        Cursor::new(IDENTITY),
        "Audit.identity.theorem",
        LeanFoundationPolicy::Constructive,
        larger,
    )
    .unwrap();
    assert_eq!(baseline.target, checked.target);
    assert_eq!(baseline.foundations, checked.foundations);
    assert_eq!(checked.budget, larger);
    let Json::Object(report) = json::parse(&checked.render_json()).unwrap() else {
        panic!("report object")
    };
    assert_eq!(
        report
            .get("proof_budget")
            .unwrap()
            .get("work_per_phase")
            .unwrap()
            .integer(),
        Some(1_000_000)
    );

    let path = std::env::temp_dir().join(format!("lim-proof-budget-{}.lim", std::process::id()));
    let mut config = CompileConfig::default();
    config.set_proof_budget(larger);
    assert_eq!(config.proof_budget(), larger);
    let native =
        lim::check_theorem_details_from_path_with_config(NATIVE, &path, &config, "reflexivity")
            .unwrap();
    assert_eq!(native.budget, larger);
}

#[test]
fn tiny_export_budgets_fail_and_larger_budget_does_not_authorize_foundations() {
    for (budget, cause) in [
        (
            ProofBudget::new(1, 64 << 20, 256 << 20).unwrap(),
            "work units",
        ),
        (
            ProofBudget::new(200_000, 1, 256 << 20).unwrap(),
            "allocation limit",
        ),
        (
            ProofBudget::new(200_000, 64 << 20, 1).unwrap(),
            "cumulative",
        ),
    ] {
        let error = lim::check_lean_export_with_budget(
            Cursor::new(IDENTITY),
            "Audit.identity.theorem",
            LeanFoundationPolicy::Constructive,
            budget,
        )
        .unwrap_err();
        assert!(error.message.contains(cause), "{}", error.message);
    }
    let gcd = include_str!("fixtures/lean_export_gcd/gcd.ndjson");
    let budget = ProofBudget::new(1_000_000, 128 << 20, 512 << 20).unwrap();
    let error = lim::check_lean_export_with_budget(
        Cursor::new(gcd),
        "GcdSource.zeroRight",
        LeanFoundationPolicy::Constructive,
        budget,
    )
    .unwrap_err();
    assert!(
        error.message.contains("not authorized"),
        "{}",
        error.message
    );

    let incorrect = NATIVE.replace("(#pt-refl a value)", "(#pt-refl a a)");
    let path =
        std::env::temp_dir().join(format!("lim-proof-budget-bad-{}.lim", std::process::id()));
    let mut config = CompileConfig::default();
    config.set_proof_budget(budget);
    let error =
        lim::check_theorem_details_from_path_with_config(&incorrect, &path, &config, "reflexivity")
            .unwrap_err();
    assert_eq!(error.code, lim::DiagnosticCode::Proof);
    assert!(error.message.contains("type mismatch"), "{}", error.message);
}

#[test]
fn cli_budget_line_and_failure_preserve_report_and_proof_files() {
    let scratch = support::Scratch::new("proof-budget-cli");
    let input = scratch.path().join("identity.ndjson");
    fs::write(&input, IDENTITY).unwrap();
    let mut command = Command::new(env!("CARGO_BIN_EXE_lim"));
    command.env("PATH", "").args([
        "--check-lean-export",
        input.to_str().unwrap(),
        "Audit.identity.theorem",
        "--proof-work",
        "1000000",
    ]);
    let (status, stdout, stderr) =
        support::run(&mut command, Duration::from_secs(15), 65536).unwrap();
    assert!(status.success(), "{}", String::from_utf8_lossy(&stderr));
    assert!(String::from_utf8_lossy(&stdout).contains("proof budget: work=1000000"));

    let report = scratch.path().join("report.json");
    let proof = scratch.path().join("proof.lim");
    fs::write(&report, "keep report").unwrap();
    fs::write(&proof, "keep proof").unwrap();
    let mut command = Command::new(env!("CARGO_BIN_EXE_lim"));
    command.env("PATH", "").args([
        "--check-lean-export",
        input.to_str().unwrap(),
        "Audit.identity.theorem",
        "--proof-work",
        "1",
        "--report",
        report.to_str().unwrap(),
        "--emit-proof",
        proof.to_str().unwrap(),
    ]);
    let (status, _, _) = support::run(&mut command, Duration::from_secs(15), 65536).unwrap();
    assert!(!status.success());
    assert_eq!(fs::read_to_string(report).unwrap(), "keep report");
    assert_eq!(fs::read_to_string(proof).unwrap(), "keep proof");
}

#[test]
fn cli_lsp_context_roundtrips_nondefault_budget_and_omits_defaults() {
    use lim::lsp_context::LspContext;
    let scratch = support::Scratch::new("proof-budget-lsp");
    fs::write(
        scratch.path().join("main.lim"),
        "(#fn main () #u64 (#return 0u64))",
    )
    .unwrap();
    let config = scratch.path().join("settings.lsp");
    for _ in 0..2 {
        let mut command = Command::new(env!("CARGO_BIN_EXE_lim"));
        command.current_dir(scratch.path()).env("PATH", "").args([
            "--check",
            "main.lim",
            "--proof-work",
            "1000000",
            "--proof-phase-bytes",
            "128",
            "--proof-total-bytes",
            "256",
            "--write-lsp-config",
            "settings.lsp",
        ]);
        let (status, _, stderr) =
            support::run(&mut command, Duration::from_secs(15), 65536).unwrap();
        assert!(status.success(), "{}", String::from_utf8_lossy(&stderr));
    }
    let contents = fs::read_to_string(&config).unwrap();
    assert_eq!(contents.matches("[[context]]").count(), 1);
    assert!(contents.contains("proof-work = 1000000"));
    let context = LspContext::read(&config).unwrap();
    assert_eq!(
        context.config.proof_budget(),
        ProofBudget::new(1_000_000, 128, 256).unwrap()
    );
    fs::write(
        &config,
        "schema-version = 2\n[[context]]\nentry = \"main.lim\"\ntarget = \"x86_64-sysv\"\n",
    )
    .unwrap();
    assert_eq!(
        LspContext::read(&config).unwrap().config.proof_budget(),
        ProofBudget::default()
    );
    let malformed = fs::read_to_string(&config).unwrap() + "proof-work = 1\nproof-work = 2\n";
    fs::write(&config, malformed).unwrap();
    assert!(LspContext::read(&config).is_err());
}

#[test]
fn native_checking_enforces_each_counter_independently() {
    let scratch = support::Scratch::new("proof-budget-native-limits");
    for (budget, cause) in [
        (
            ProofBudget::new(1, 64 << 20, 256 << 20).unwrap(),
            "work units",
        ),
        (
            ProofBudget::new(200_000, 1, 256 << 20).unwrap(),
            "allocation limit",
        ),
        (
            ProofBudget::new(200_000, 64 << 20, 1).unwrap(),
            "cumulative",
        ),
    ] {
        let mut config = CompileConfig::default();
        config.set_proof_budget(budget);
        let error = lim::check_theorem_details_from_path_with_config(
            NATIVE,
            &scratch.path().join("native.lim"),
            &config,
            "reflexivity",
        )
        .unwrap_err();
        assert_eq!(error.code, lim::DiagnosticCode::Proof);
        assert!(error.message.contains(cause), "{}", error.message);
    }
}

#[test]
fn malformed_budget_flags_preserve_all_existing_outputs() {
    let scratch = support::Scratch::new("proof-budget-invalid-flags");
    let input = scratch.path().join("identity.ndjson");
    fs::write(&input, IDENTITY).unwrap();
    let report = scratch.path().join("report.json");
    fs::write(&report, "report sentinel").unwrap();
    let proof = scratch.path().join("proof.lim");
    fs::write(&proof, "proof sentinel").unwrap();
    for options in [
        vec!["--proof-work", "1", "--proof-work", "2"],
        vec!["--proof-phase-bytes", "-1"],
        vec!["--proof-total-bytes", "１２"],
        vec!["--proof-work", "100000001"],
        vec!["--proof-work"],
    ] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_lim"));
        command
            .env("PATH", "")
            .args([
                "--check-lean-export",
                input.to_str().unwrap(),
                "Audit.identity.theorem",
                "--report",
                report.to_str().unwrap(),
                "--emit-proof",
                proof.to_str().unwrap(),
            ])
            .args(options);
        let (status, out, _) = support::run(&mut command, Duration::from_secs(15), 65536).unwrap();
        assert!(!status.success());
        assert!(out.is_empty());
        assert_eq!(fs::read_to_string(&report).unwrap(), "report sentinel");
        assert_eq!(fs::read_to_string(&proof).unwrap(), "proof sentinel");
    }
}

#[test]
fn lsp_budget_validation_and_default_serialization_are_explicit() {
    use lim::lsp_context::LspContext;
    let scratch = support::Scratch::new("proof-budget-lsp-invalid");
    let file = scratch.path().join("settings.lsp");
    let source = scratch.path().join("source.lim");
    fs::write(&source, "(#fn main () #u64 (#return 0u64))").unwrap();
    let context = LspContext {
        entry: source,
        target: lim::TargetDescription::X86_64_SYSTEM_V,
        config: CompileConfig::default(),
    };
    context.write(&file).unwrap();
    let original = fs::read_to_string(&file).unwrap();
    assert!(!original.contains("proof-work"));
    for invalid in [
        "proof-work = 0",
        "proof-work = +1",
        "proof-work = １２",
        "proof-total-bytes = 999999999999999999999999999999",
        "proof-phase-bytes = 1073741825",
    ] {
        fs::write(&file, format!("{original}{invalid}\n")).unwrap();
        assert!(LspContext::read(&file).is_err(), "accepted {invalid}");
    }
}
