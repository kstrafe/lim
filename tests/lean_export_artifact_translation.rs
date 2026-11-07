use lim::{LeanFoundationPolicy, ProofBudget};
use std::io::{self, Read, Write};

const IDENTITY: &[u8] = include_bytes!("fixtures/lean_export/identity.ndjson");
const QUOTIENT: &[u8] = include_bytes!("fixtures/lean_export_quotient/quotient.ndjson");
const FOUNDATIONS: &[u8] = include_bytes!("fixtures/lean_export_foundations/foundations.ndjson");
const NESTED_POLY: &[u8] = include_bytes!("fixtures/lean_export/real-nested-poly.ndjson");
const GCD_CLOSED: &[u8] = include_bytes!("fixtures/lean_export_gcd_closed/gcd-closed.ndjson");

fn budget() -> ProofBudget {
    ProofBudget::default()
}

fn assert_matches_receipt(
    input: &[u8],
    target: &str,
    policy: LeanFoundationPolicy,
    b: ProofBudget,
) {
    let old = lim::translate_lean_export_receipt_with_budget(
        io::BufReader::new(input),
        target,
        policy,
        b,
    )
    .unwrap();
    let artifact = lim::translate_lean_export_artifact_with_budget(
        io::BufReader::new(input),
        target,
        policy,
        b,
    )
    .unwrap();

    assert_eq!(artifact.target, old.target);
    let mut actual_report = Vec::new();
    let mut expected_report = Vec::new();
    artifact.receipt.write_json(&mut actual_report).unwrap();
    old.receipt.write_json(&mut expected_report).unwrap();
    assert_eq!(actual_report, expected_report);
    assert_eq!(artifact.source_len(), old.source.len());
    let mut source = Vec::new();
    artifact.write_source(&mut source).unwrap();
    assert_eq!(source, old.source.as_bytes());
}

#[test]
fn fixture_artifacts_match_receipt_translation() {
    assert_matches_receipt(
        IDENTITY,
        "Audit.identity.theorem",
        LeanFoundationPolicy::Constructive,
        budget(),
    );
    assert_matches_receipt(
        QUOTIENT,
        "QuotientSource.inductionReflexive",
        LeanFoundationPolicy::Constructive,
        budget(),
    );
    assert_matches_receipt(
        FOUNDATIONS,
        "BasisProbe.quotientRelated",
        LeanFoundationPolicy::Lean4,
        budget(),
    );
    assert_matches_receipt(
        NESTED_POLY,
        "ReplaySource.polyNested",
        LeanFoundationPolicy::Constructive,
        budget(),
    );
    assert_matches_receipt(
        GCD_CLOSED,
        "GcdProbe.closed",
        LeanFoundationPolicy::Constructive,
        budget(),
    );
}

#[test]
fn artifact_reads_to_full_eof_and_rejects_late_malformed_rows() {
    let mut input = IDENTITY.to_vec();
    input.extend_from_slice(b"{not json}\n");
    let error = lim::translate_lean_export_artifact_with_budget(
        io::BufReader::new(input.as_slice()),
        "Audit.identity.theorem",
        LeanFoundationPolicy::Constructive,
        budget(),
    )
    .unwrap_err();
    assert_eq!(
        error.message,
        lim::translate_lean_export_receipt_with_budget(
            io::BufReader::new(input.as_slice()),
            "Audit.identity.theorem",
            LeanFoundationPolicy::Constructive,
            budget(),
        )
        .unwrap_err()
        .message
    );

    let mut read = FailsAfterBytes {
        bytes: IDENTITY,
        sent: 0,
    };
    let error = lim::translate_lean_export_artifact_with_budget(
        io::BufReader::with_capacity(128, &mut read),
        "Audit.identity.theorem",
        LeanFoundationPolicy::Constructive,
        budget(),
    )
    .unwrap_err();
    assert!(
        error.message.contains("injected EOF read failure"),
        "{error}"
    );
    assert_eq!(read.sent, IDENTITY.len());
}

struct FailsAfterBytes<'a> {
    bytes: &'a [u8],
    sent: usize,
}

impl Read for FailsAfterBytes<'_> {
    fn read(&mut self, out: &mut [u8]) -> io::Result<usize> {
        if self.sent == self.bytes.len() {
            return Err(io::Error::new(
                io::ErrorKind::Other,
                "injected EOF read failure",
            ));
        }
        let count = out.len().min(self.bytes.len() - self.sent);
        out[..count].copy_from_slice(&self.bytes[self.sent..self.sent + count]);
        self.sent += count;
        Ok(count)
    }
}

#[test]
fn wrong_target_and_default_budget_refusals_match_receipt_api() {
    for (input, target, policy, b) in [
        (
            IDENTITY,
            "Missing.theorem",
            LeanFoundationPolicy::Constructive,
            budget(),
        ),
        (
            IDENTITY,
            "Audit.identity.theorem",
            LeanFoundationPolicy::Constructive,
            ProofBudget::new(1, budget().phase_bytes(), budget().total_bytes()).unwrap(),
        ),
        (
            IDENTITY,
            "Audit.identity.theorem",
            LeanFoundationPolicy::Constructive,
            ProofBudget::new(budget().work(), 1, budget().total_bytes()).unwrap(),
        ),
        (
            IDENTITY,
            "Audit.identity.theorem",
            LeanFoundationPolicy::Constructive,
            ProofBudget::new(budget().work(), budget().phase_bytes(), 1).unwrap(),
        ),
    ] {
        let old = lim::translate_lean_export_receipt_with_budget(
            io::BufReader::new(input),
            target,
            policy,
            b,
        )
        .unwrap_err();
        let new = lim::translate_lean_export_artifact_with_budget(
            io::BufReader::new(input),
            target,
            policy,
            b,
        )
        .unwrap_err();
        assert_eq!(new.line, old.line);
        assert_eq!(new.message, old.message);
    }
}

struct FailsOnWrite;

impl Write for FailsOnWrite {
    fn write(&mut self, _: &[u8]) -> io::Result<usize> {
        Err(io::Error::new(io::ErrorKind::BrokenPipe, "sink failed"))
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

#[test]
fn source_sink_failure_propagates_and_artifact_remains_reusable() {
    let artifact = lim::translate_lean_export_artifact_with_budget(
        io::BufReader::new(IDENTITY),
        "Audit.identity.theorem",
        LeanFoundationPolicy::Constructive,
        budget(),
    )
    .unwrap();
    let expected = lim::translate_lean_export_receipt_with_budget(
        io::BufReader::new(IDENTITY),
        "Audit.identity.theorem",
        LeanFoundationPolicy::Constructive,
        budget(),
    )
    .unwrap()
    .source;

    let error = artifact.write_source(&mut FailsOnWrite).unwrap_err();
    assert_eq!(error.kind(), io::ErrorKind::BrokenPipe);
    assert_eq!(error.to_string(), "sink failed");
    let mut after_failure = Vec::new();
    artifact.write_source(&mut after_failure).unwrap();
    assert_eq!(after_failure, expected.as_bytes());
}
