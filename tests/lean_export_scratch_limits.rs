use lim::{LeanExportLimits, LeanFoundationPolicy, NativeProofLimits, ProofBudget};
use std::{
    fs::File,
    io::{self, BufRead, BufReader, BufWriter, Read, Write},
    process::Command,
};

const IDENTITY: &[u8] = include_bytes!("fixtures/lean_export/identity.ndjson");
const TARGET: &str = "Audit.identity.theorem";
const MIB: u64 = 1024 * 1024;

struct Scratch(std::path::PathBuf);

impl Scratch {
    fn new() -> Self {
        static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
        let path = std::env::temp_dir().join(format!(
            "lim-export-scratch-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
        ));
        std::fs::create_dir(&path).unwrap();
        Self(path)
    }

    fn path(&self) -> &std::path::Path {
        &self.0
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

struct PanicReader;
impl Read for PanicReader {
    fn read(&mut self, _: &mut [u8]) -> io::Result<usize> {
        panic!("invalid scratch profile must be rejected before reading")
    }
}
impl BufRead for PanicReader {
    fn fill_buf(&mut self) -> io::Result<&[u8]> {
        panic!("invalid scratch profile must be rejected before reading")
    }
    fn consume(&mut self, _: usize) {}
}

fn raw_limits(scratch: u64) -> LeanExportLimits {
    LeanExportLimits {
        max_bytes: 128 * MIB,
        max_names: 6_000,
        max_name_bytes: (192 * MIB) as usize,
        max_scratch_bytes: scratch,
        ..LeanExportLimits::default()
    }
}

fn write_large_export(path: &std::path::Path) -> u64 {
    let file = File::create(path).unwrap();
    let mut out = BufWriter::new(file);
    out.write_all(IDENTITY).unwrap();
    let mut name = vec![b'n'; 16_000];
    for id in 5..5_005 {
        // Change only the final four ASCII bytes in the one reused long name
        // buffer. Every name record is streamed directly to disk.
        let suffix = format!("{id:04}");
        name[15_996..].copy_from_slice(suffix.as_bytes());
        out.write_all(b"{\"str\":{\"pre\":0,\"str\":\"").unwrap();
        out.write_all(&name).unwrap();
        writeln!(out, "\"}},\"in\":{id}}}").unwrap();
    }
    writeln!(
        out,
        "{{\"thm\":{{\"name\":5004,\"levelParams\":[],\"type\":12,\"value\":19,\"all\":[5004]}}}}"
    )
    .unwrap();
    out.flush().unwrap();
    std::fs::metadata(path).unwrap().len()
}

#[test]
fn streamed_name_table_spills_with_independent_scratch_budget() {
    let scratch = Scratch::new();
    let path = scratch.path().join("large-identity.ndjson");
    let input_bytes = write_large_export(&path);
    assert!(input_bytes < 128 * MIB);

    let too_small = lim::check_lean_export_receipt_with_limits(
        BufReader::new(File::open(&path).unwrap()),
        TARGET,
        LeanFoundationPolicy::Constructive,
        ProofBudget::default(),
        raw_limits(128 * MIB),
    )
    .unwrap_err();
    assert!(
        too_small
            .message
            .to_lowercase()
            .contains("scratch byte limit"),
        "{too_small}"
    );

    for scratch_bytes in [192 * MIB, 256 * MIB] {
        let selected = raw_limits(scratch_bytes);
        let receipt = lim::check_lean_export_receipt_with_limits(
            BufReader::new(File::open(&path).unwrap()),
            TARGET,
            LeanFoundationPolicy::Constructive,
            ProofBudget::default(),
            selected,
        )
        .unwrap();
        assert_eq!(receipt.limits(), selected);
        assert_eq!(receipt.declaration_count(), 3);
        let mut json = Vec::new();
        receipt.write_json(&mut json).unwrap();
        assert_eq!(json.iter().filter(|&&b| b == b'\n').count(), 0);
        assert!(String::from_utf8_lossy(&json).contains("\"axioms\":[]"));
        let report = receipt.into_report().unwrap();
        assert_eq!(report.bytes, input_bytes);
        assert_eq!(report.declarations.len(), 3);
        assert_eq!(report.declarations[2].name.len(), 16_000);
    }
}

#[test]
fn scratch_validation_precedes_input_and_small_identity_needs_no_spill() {
    let raw_zero = LeanExportLimits {
        max_scratch_bytes: 0,
        ..LeanExportLimits::default()
    };
    let err = lim::check_lean_export_with_limits(
        PanicReader,
        TARGET,
        LeanFoundationPolicy::Constructive,
        ProofBudget::default(),
        raw_zero,
    )
    .unwrap_err();
    assert!(err.message.contains("scratch"));
    let raw_overflow = LeanExportLimits {
        max_scratch_bytes: u64::MAX,
        ..LeanExportLimits::default()
    };
    assert!(lim::check_lean_export_with_limits(
        PanicReader,
        TARGET,
        LeanFoundationPolicy::Constructive,
        ProofBudget::default(),
        raw_overflow,
    )
    .unwrap_err()
    .message
    .contains("scratch"));

    let native_zero = NativeProofLimits {
        max_scratch_bytes: 0,
        ..NativeProofLimits::default()
    };
    let err = lim::translate_lean_export_with_profiles(
        PanicReader,
        TARGET,
        LeanFoundationPolicy::Constructive,
        ProofBudget::default(),
        LeanExportLimits::default(),
        native_zero,
    )
    .unwrap_err();
    assert!(err.message.contains("scratch"));
    let native_overflow = NativeProofLimits {
        max_scratch_bytes: u64::MAX,
        ..NativeProofLimits::default()
    };
    assert!(lim::translate_lean_export_with_profiles(
        PanicReader,
        TARGET,
        LeanFoundationPolicy::Constructive,
        ProofBudget::default(),
        LeanExportLimits::default(),
        native_overflow,
    )
    .unwrap_err()
    .message
    .contains("scratch"));

    let selected = raw_limits(1);
    let report = lim::check_lean_export_with_limits(
        IDENTITY,
        TARGET,
        LeanFoundationPolicy::Constructive,
        ProofBudget::default(),
        selected,
    )
    .unwrap();
    assert_eq!(report.declarations.len(), 2);
}

#[test]
fn cli_reports_both_scratch_profiles_and_rejects_bad_flags_before_publication() {
    let scratch = Scratch::new();
    let input = scratch.path().join("identity.ndjson");
    let report = scratch.path().join("receipt.json");
    let proof = scratch.path().join("identity.lim");
    std::fs::write(&input, IDENTITY).unwrap();
    let run = |extra: &[&str]| {
        let mut command = Command::new(env!("CARGO_BIN_EXE_lim"));
        command.args(["--check-lean-export", input.to_str().unwrap(), TARGET]);
        command.args(extra);
        command.output().unwrap()
    };
    let output = run(&[
        "--report",
        report.to_str().unwrap(),
        "--emit-proof",
        proof.to_str().unwrap(),
        "--export-scratch-bytes",
        "1048576",
        "--native-proof-scratch-bytes",
        "2097152",
    ]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let json = std::fs::read_to_string(&report).unwrap();
    assert!(json.contains("\"max_scratch_bytes\":1048576"));
    assert!(json.contains("\"max_scratch_bytes\":2097152"));

    for options in [
        vec!["--export-scratch-bytes", "0"],
        vec!["--export-scratch-bytes", "1", "--export-scratch-bytes", "2"],
        vec!["--native-proof-scratch-bytes", "18446744073709551616"],
        vec!["--native-proof-scratch-bytes"],
    ] {
        std::fs::write(&report, b"old report").unwrap();
        let mut args = options;
        args.extend(["--report", report.to_str().unwrap()]);
        let output = run(&args);
        assert!(!output.status.success());
        assert!(output.stdout.is_empty());
        assert_eq!(std::fs::read(&report).unwrap(), b"old report");
    }
}
