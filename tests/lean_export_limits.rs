use lim::{LeanExportLimits, LeanFoundationPolicy, ProofBudget};
use std::io::{self, BufRead, Read};

const IDENTITY: &str = include_str!("fixtures/lean_export/identity.ndjson");
const TARGET: &str = "Audit.identity.theorem";

fn limits() -> LeanExportLimits {
    LeanExportLimits {
        max_bytes: 1 << 20,
        max_names: 100,
        max_name_bytes: 1 << 16,
        max_levels: 100,
        max_expressions: 100,
        max_declarations: 100,
        max_dependencies: 100,
        max_dependency_bytes: 1 << 16,
        max_payload_bytes: 1 << 16,
        max_scratch_bytes: 128 * 1024 * 1024,
    }
}

struct PanicReader;
impl Read for PanicReader {
    fn read(&mut self, _: &mut [u8]) -> io::Result<usize> {
        panic!("reader must not be touched")
    }
}
impl BufRead for PanicReader {
    fn fill_buf(&mut self) -> io::Result<&[u8]> {
        panic!("reader must not be touched")
    }
    fn consume(&mut self, _: usize) {}
}

#[test]
fn selected_limits_are_reported_and_checked_at_exact_boundaries() {
    let exact = LeanExportLimits {
        max_bytes: IDENTITY.len() as u64,
        max_names: 5,
        // name_record adds canonical key length plus display length for each
        // of the four names: 19 + 39 + 57 + 11 = 126 bytes.
        max_name_bytes: 126,
        max_levels: 2,
        max_expressions: 20,
        max_declarations: 2,
        max_dependencies: 1,
        // Dependency and primitive payload counters have exact accumulated
        // costs that are deliberately left at their safe defaults here.
        max_dependency_bytes: LeanExportLimits::default().max_dependency_bytes,
        max_payload_bytes: LeanExportLimits::default().max_payload_bytes,
        max_scratch_bytes: 128 * 1024 * 1024,
    };
    let report = lim::check_lean_export_with_limits(
        IDENTITY.as_bytes(),
        TARGET,
        LeanFoundationPolicy::Constructive,
        ProofBudget::default(),
        exact,
    )
    .unwrap();
    assert_eq!(report.limits, exact);
    assert_eq!(report.declarations.len(), 2);
    let too_few_name_bytes = lim::check_lean_export_with_limits(
        IDENTITY.as_bytes(),
        TARGET,
        LeanFoundationPolicy::Constructive,
        ProofBudget::default(),
        LeanExportLimits {
            max_name_bytes: 56,
            ..exact
        },
    )
    .unwrap_err();
    assert!(too_few_name_bytes.message.contains("name byte"));
    let receipt = lim::check_lean_export_receipt_with_limits(
        IDENTITY.as_bytes(),
        TARGET,
        LeanFoundationPolicy::Constructive,
        ProofBudget::default(),
        exact,
    )
    .unwrap();
    assert_eq!(receipt.limits(), exact);
    assert!(lim::check_lean_export_with_limits(
        IDENTITY.as_bytes(),
        TARGET,
        LeanFoundationPolicy::Constructive,
        ProofBudget::default(),
        LeanExportLimits {
            max_bytes: exact.max_bytes - 1,
            ..exact
        },
    )
    .is_err());
    assert_eq!(
        lim::check_lean_export(IDENTITY.as_bytes(), TARGET)
            .unwrap()
            .limits,
        LeanExportLimits::default()
    );
}

#[test]
fn invalid_limits_fail_before_reading_and_limits_do_not_grant_axioms_or_budget() {
    let bad = LeanExportLimits {
        max_names: 0,
        ..limits()
    };
    let error = lim::check_lean_export_with_limits(
        PanicReader,
        TARGET,
        LeanFoundationPolicy::Constructive,
        ProofBudget::default(),
        bad,
    )
    .unwrap_err();
    assert!(error.message.contains("name count"));
    let foundation = include_str!("fixtures/lean_export_foundations/foundations.ndjson");
    assert!(lim::check_lean_export_with_limits(
        foundation.as_bytes(),
        "BasisProbe.quotientRelated",
        LeanFoundationPolicy::Constructive,
        ProofBudget::default(),
        LeanExportLimits::default()
    )
    .unwrap_err()
    .message
    .contains("axiom"));
    let budget = ProofBudget::new(1, 1, 1).unwrap();
    assert!(lim::check_lean_export_with_limits(
        IDENTITY.as_bytes(),
        TARGET,
        LeanFoundationPolicy::Constructive,
        budget,
        limits()
    )
    .is_err());
}

#[test]
fn target_does_not_skip_trailing_records_or_cumulative_count_limits() {
    let mut trailing = IDENTITY.to_owned();
    trailing.push_str("{\"str\":{\"pre\":0,\"str\":\"after\"},\"in\":5}\n");
    let error = lim::check_lean_export_with_limits(
        trailing.as_bytes(),
        TARGET,
        LeanFoundationPolicy::Constructive,
        ProofBudget::default(),
        LeanExportLimits {
            max_names: 5,
            ..limits()
        },
    )
    .unwrap_err();
    assert!(error.message.contains("name"), "{error}");
    let mut malformed = IDENTITY.to_owned();
    malformed.push_str("not-json\n");
    assert!(lim::check_lean_export_with_limits(
        malformed.as_bytes(),
        TARGET,
        LeanFoundationPolicy::Constructive,
        ProofBudget::default(),
        limits()
    )
    .is_err());
}

#[test]
fn receipt_translation_config_and_materialized_json_match() {
    let selected = limits();
    let expected = lim::translate_lean_export_with_limits(
        IDENTITY.as_bytes(),
        TARGET,
        LeanFoundationPolicy::Constructive,
        ProofBudget::default(),
        selected,
    )
    .unwrap();
    let actual = lim::translate_lean_export_receipt_with_limits(
        IDENTITY.as_bytes(),
        TARGET,
        LeanFoundationPolicy::Constructive,
        ProofBudget::default(),
        selected,
    )
    .unwrap();
    assert_eq!(expected.source, actual.source);
    assert_eq!(expected.target, actual.target);
    assert_eq!(actual.receipt.limits(), selected);
    let mut streamed = Vec::new();
    actual.receipt.write_json(&mut streamed).unwrap();
    assert!(String::from_utf8_lossy(&streamed).contains("\"export_limits\""));
    assert!(String::from_utf8_lossy(&streamed).contains("\"max_bytes\":1048576"));
    let report = actual.receipt.into_report().unwrap();
    assert_eq!(report.limits, selected);
    assert_eq!(streamed, report.render_json().as_bytes());
    let artifact = lim::translate_lean_export_artifact_with_limits(
        IDENTITY.as_bytes(),
        TARGET,
        LeanFoundationPolicy::Constructive,
        ProofBudget::default(),
        selected,
    )
    .unwrap();
    assert_eq!(artifact.receipt.limits(), selected);
}

fn many_checked_declarations(count: usize) -> String {
    let mut rows: Vec<String> = IDENTITY.lines().map(str::to_owned).collect();
    let theorem = rows.pop().unwrap();
    for i in 0..count {
        let id = i + 5;
        rows.push(format!(
            "{{\"str\":{{\"pre\":0,\"str\":\"alias{i}\"}},\"in\":{id}}}"
        ));
    }
    let mut input = rows.join("\n");
    input.push('\n');
    for i in 0..count {
        let id = i + 5;
        // The alias has the same proposition and proof term as the checked identity theorem.
        input.push_str(&format!("{{\"thm\":{{\"name\":{id},\"levelParams\":[],\"type\":12,\"value\":19,\"all\":[{id}]}}}}\n"));
    }
    input.push_str(&theorem);
    input.push('\n');
    input
}

#[test]
fn each_cumulative_limit_rejects_crossing_its_selected_boundary() {
    let defaults = LeanExportLimits::default();
    let extra = many_checked_declarations(1);
    for (selected, input, expected) in [
        (
            LeanExportLimits {
                max_bytes: IDENTITY.len() as u64 - 1,
                ..defaults
            },
            IDENTITY,
            "total byte",
        ),
        (
            LeanExportLimits {
                max_names: 4,
                ..defaults
            },
            IDENTITY,
            "name",
        ),
        (
            LeanExportLimits {
                max_name_bytes: 125,
                ..defaults
            },
            IDENTITY,
            "name byte",
        ),
        (
            LeanExportLimits {
                max_levels: 1,
                ..defaults
            },
            IDENTITY,
            "universe",
        ),
        (
            LeanExportLimits {
                max_expressions: 19,
                ..defaults
            },
            IDENTITY,
            "expression",
        ),
        (
            LeanExportLimits {
                max_declarations: 1,
                ..defaults
            },
            IDENTITY,
            "declaration",
        ),
        (
            LeanExportLimits {
                max_dependencies: 1,
                ..defaults
            },
            extra.as_str(),
            "dependency manifest",
        ),
        (
            LeanExportLimits {
                max_dependency_bytes: 56,
                ..defaults
            },
            IDENTITY,
            "dependency manifest",
        ),
        (
            LeanExportLimits {
                max_payload_bytes: 1,
                ..defaults
            },
            IDENTITY,
            "primitive payload",
        ),
    ] {
        let error = lim::check_lean_export_receipt_with_limits(
            input.as_bytes(),
            TARGET,
            LeanFoundationPolicy::Constructive,
            ProofBudget::default(),
            selected,
        )
        .unwrap_err();
        assert!(
            error.message.contains(expected),
            "expected {expected}: {error}"
        );
    }
}

#[test]
fn selected_declaration_limit_allows_more_than_default_only_after_kernel_checks() {
    let input = many_checked_declarations(4095);
    let raised = LeanExportLimits {
        max_bytes: input.len() as u64 + 1,
        max_names: 5_000,
        max_name_bytes: 1 << 20,
        max_levels: 100,
        max_expressions: 100,
        max_declarations: 5_000,
        max_dependencies: 5_000,
        max_dependency_bytes: 1 << 20,
        max_payload_bytes: 1 << 20,
        max_scratch_bytes: 128 * 1024 * 1024,
    };
    let err = lim::check_lean_export_with_limits(
        input.as_bytes(),
        TARGET,
        LeanFoundationPolicy::Constructive,
        ProofBudget::default(),
        LeanExportLimits::default(),
    )
    .unwrap_err();
    assert!(err.message.contains("declaration"), "{err}");
    let generous_budget = ProofBudget::new(100_000_000, 1 << 30, 64 << 30).unwrap();
    let report = lim::check_lean_export_with_limits(
        input.as_bytes(),
        TARGET,
        LeanFoundationPolicy::Constructive,
        generous_budget,
        raised,
    )
    .unwrap();
    assert_eq!(report.declarations.len(), 4097);
    assert!(report.axioms.is_empty());
    assert!(report.target_axioms.is_empty());
}

#[test]
fn cli_validates_export_flags_and_does_not_publish_on_failure() {
    let scratch = std::env::temp_dir().join(format!("lim-export-limits-{}", std::process::id()));
    std::fs::create_dir_all(&scratch).unwrap();
    let input = scratch.join("identity.ndjson");
    std::fs::write(&input, IDENTITY).unwrap();
    let output = scratch.join("report.json");
    let run = |args: &[&str]| {
        std::process::Command::new(env!("CARGO_BIN_EXE_lim"))
            .arg("--check-lean-export")
            .arg(&input)
            .arg(TARGET)
            .args(args)
            .output()
            .unwrap()
    };
    for args in [
        vec!["--export-bytes", "1", "--export-bytes", "2"],
        vec!["--export-bytes"],
        vec!["--export-bytes", "bad"],
        vec!["--export-names", "0"],
        vec!["--proof-work", "10", "--emit-proof"],
        vec!["--emit-proof", "--export-bytes", "100"],
    ] {
        let result = run(&args);
        assert!(!result.status.success(), "accepted {args:?}");
    }
    let result = run(&["--report", output.to_str().unwrap(), "--export-bytes", "1"]);
    assert!(!result.status.success());
    assert!(!output.exists(), "failed export published a report");
    let ok = run(&[
        "--report",
        output.to_str().unwrap(),
        "--export-bytes",
        "1048576",
    ]);
    assert!(
        ok.status.success(),
        "{}",
        String::from_utf8_lossy(&ok.stderr)
    );
    assert!(output.exists());
    let mixed = run(&[
        "--report",
        scratch.join("mixed.json").to_str().unwrap(),
        "--proof-work",
        "1000000",
        "--export-bytes",
        "1048576",
    ]);
    assert!(
        mixed.status.success(),
        "{}",
        String::from_utf8_lossy(&mixed.stderr)
    );
    std::fs::remove_dir_all(scratch).unwrap();
}
