use lim::{
    check_lean_export, check_lean_export_receipt_with_budget, check_lean_export_with_policy,
    LeanFoundationPolicy, ProofBudget,
};
use std::io::{self, BufRead, Read, Write};

const IDENTITY: &str = include_str!("fixtures/lean_export/identity.ndjson");
const TARGET: &str = "Audit.identity.theorem";

fn budget() -> ProofBudget {
    ProofBudget::default()
}

fn receipt(input: &str, target: &str) -> lim::LeanExportReceipt {
    check_lean_export_receipt_with_budget(
        io::BufReader::new(input.as_bytes()),
        target,
        LeanFoundationPolicy::Constructive,
        budget(),
    )
    .unwrap()
}

fn synthetic_large_identity() -> String {
    let mut rows: Vec<String> = IDENTITY.lines().map(str::to_owned).collect();
    let theorem = rows.pop().unwrap().to_owned();
    let long_name = "N".repeat(12_000);
    let extra = 90usize;
    for offset in 0..extra {
        let name_id = 5 + offset;
        rows.push(format!(
            "{{\"str\":{{\"pre\":0,\"str\":\"{long_name}{offset}\"}},\"in\":{name_id}}}"
        ));
    }
    let mut input = rows.join("\n");
    input.push('\n');
    for offset in 0..extra {
        let name_id = 5 + offset;
        let id = format!("{{\"thm\":{{\"name\":{name_id},\"levelParams\":[],\"type\":12,\"value\":19,\"all\":[{name_id}]}}}}");
        input.push_str(&id);
        input.push('\n');
    }
    input.push_str(&theorem);
    input.push('\n');
    input
}

#[test]
fn receipt_json_and_materialized_report_are_byte_identical() {
    for (input, target) in [
        (IDENTITY, TARGET),
        (
            include_str!("fixtures/lean_export_quotient/quotient.ndjson"),
            "QuotientSource.inductionReflexive",
        ),
    ] {
        let report = check_lean_export(input.as_bytes(), target).unwrap();
        let receipt = receipt(input, target);
        let mut direct = Vec::new();
        receipt.write_json(&mut direct).unwrap();
        assert_eq!(direct, report.render_json().as_bytes());
        let mut materialized = Vec::new();
        receipt
            .into_report()
            .unwrap()
            .write_json(&mut materialized)
            .unwrap();
        assert_eq!(materialized, direct);
    }
}

#[test]
fn target_selector_accepts_canonical_identity_and_distinguishes_quoted_names() {
    let canonical = "$lean:s5:Audits8:identitys7:theorem";
    for target in [TARGET, canonical] {
        let r = check_lean_export_receipt_with_budget(
            IDENTITY.as_bytes(),
            target,
            LeanFoundationPolicy::Constructive,
            budget(),
        )
        .unwrap();
        assert_eq!(r.declaration_count(), 2);
    }

    // A literal dot in a single component stays quoted in the display name;
    // it cannot collide with the hierarchical selector.
    let mut alias = IDENTITY.to_owned();
    alias.push_str("{\"in\":5,\"str\":{\"pre\":0,\"str\":\"Audit.identity.theorem\"}}\n");
    alias.push_str(
        "{\"thm\":{\"name\":5,\"levelParams\":[],\"type\":12,\"value\":19,\"all\":[5]}}\n",
    );
    for target in [TARGET.to_owned(), format!("\"{TARGET}\"")] {
        let report = receipt(&alias, &target).into_report().unwrap();
        assert_eq!(report.target, target);
        assert_eq!(report.declarations.len(), 3);
    }
}

#[test]
fn large_receipt_spills_and_still_matches_eager_json_and_materialization() {
    let input = synthetic_large_identity();
    let report = check_lean_export(input.as_bytes(), TARGET).unwrap();
    let r = receipt(&input, TARGET);
    assert_eq!(r.declaration_count(), 92);
    let mut streamed = Vec::new();
    r.write_json(&mut streamed).unwrap();
    assert!(
        streamed.len() > (1 << 20),
        "fixture did not cross the spill threshold"
    );
    assert_eq!(streamed, report.render_json().as_bytes());
    let materialized = r.into_report().unwrap();
    assert_eq!(materialized.declarations.len(), 92);
    assert_eq!(materialized.render_json().as_bytes(), streamed);
}

#[test]
fn receipt_exposes_verified_summary_and_target_axioms() {
    let r = receipt(IDENTITY, TARGET);
    assert_eq!(r.declaration_count(), 2);
    assert!(r.axioms().is_empty());
    assert!(r.target_axioms().is_empty());
}

struct FailingWriter {
    bytes: Vec<u8>,
    limit: usize,
}
impl Write for FailingWriter {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        if self.bytes.len() == self.limit {
            return Err(io::Error::new(io::ErrorKind::BrokenPipe, "injected"));
        }
        let n = buf.len().min(5).min(self.limit - self.bytes.len());
        self.bytes.extend_from_slice(&buf[..n]);
        Ok(n)
    }
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

#[test]
fn receipt_writer_handles_short_writes_propagates_errors_and_remains_reusable() {
    let r = receipt(IDENTITY, TARGET);
    let mut expected = Vec::new();
    r.write_json(&mut expected).unwrap();
    let mut short = FailingWriter {
        bytes: Vec::new(),
        limit: usize::MAX,
    };
    r.write_json(&mut short).unwrap();
    assert_eq!(short.bytes, expected);
    for limit in [0, 1, 73, expected.len() - 1] {
        let mut writer = FailingWriter {
            bytes: Vec::new(),
            limit,
        };
        assert_eq!(
            r.write_json(&mut writer).unwrap_err().kind(),
            io::ErrorKind::BrokenPipe
        );
        assert_eq!(writer.bytes, expected[..limit]);
        let mut retry = Vec::new();
        r.write_json(&mut retry).unwrap();
        assert_eq!(retry, expected);
    }
}

#[test]
fn receipt_rejects_bad_trailing_input_axioms_and_bad_targets() {
    let malformed_after_target = format!("{IDENTITY}{{not json}}\n");
    for (input, target, expected) in [
        (
            malformed_after_target.as_str(),
            TARGET,
            "invalid export JSON",
        ),
        (IDENTITY, "Audit.identity.missing", "missing or ambiguous"),
        (IDENTITY, "Audit.identity", "not a theorem"),
    ] {
        let error = check_lean_export_receipt_with_budget(
            input.as_bytes(),
            target,
            LeanFoundationPolicy::Constructive,
            budget(),
        )
        .unwrap_err();
        assert!(error.message.contains(expected), "{error}");
    }
    const FOUNDATIONS: &str = include_str!("fixtures/lean_export_foundations/foundations.ndjson");
    let error = check_lean_export_receipt_with_budget(
        FOUNDATIONS.as_bytes(),
        "BasisProbe.quotientRelated",
        LeanFoundationPolicy::Constructive,
        budget(),
    )
    .unwrap_err();
    assert!(error.message.contains("axioms"), "{error}");
}

#[test]
fn lean4_receipt_axiom_summary_matches_checked_report() {
    const FOUNDATIONS: &str = include_str!("fixtures/lean_export_foundations/foundations.ndjson");
    let target = "BasisProbe.quotientRelated";
    let expected =
        check_lean_export_with_policy(FOUNDATIONS.as_bytes(), target, LeanFoundationPolicy::Lean4)
            .unwrap();
    let r = check_lean_export_receipt_with_budget(
        FOUNDATIONS.as_bytes(),
        target,
        LeanFoundationPolicy::Lean4,
        budget(),
    )
    .unwrap();
    assert_eq!(r.axioms(), ["Classical.choice", "Quot.sound", "propext"]);
    assert_eq!(r.target_axioms(), ["Quot.sound"]);
    let mut json = Vec::new();
    r.write_json(&mut json).unwrap();
    assert_eq!(json, expected.render_json().as_bytes());
}

#[test]
fn malformed_record_after_spilled_inventory_fails_before_receipt_is_returned() {
    let mut input = synthetic_large_identity();
    input.push_str("{not json}\n");
    let error = check_lean_export_receipt_with_budget(
        input.as_bytes(),
        TARGET,
        LeanFoundationPolicy::Constructive,
        budget(),
    )
    .unwrap_err();
    assert!(error.message.contains("invalid export JSON"), "{error}");
}

#[test]
fn duplicate_name_after_name_table_paging_is_rejected() {
    let mut input = IDENTITY.to_owned();
    for index in 0..2048 {
        input.push_str(&format!(
            "{{\"in\":{},\"str\":{{\"pre\":1,\"str\":\"entry{index:04}{}\"}}}}\n",
            5 + index,
            "x".repeat(500)
        ));
    }
    input.push_str("{\"in\":2053,\"str\":{\"pre\":1,\"str\":\"entry0512");
    input.push_str(&"x".repeat(500));
    input.push_str("\"}}\n");
    let error = check_lean_export_receipt_with_budget(
        input.as_bytes(),
        TARGET,
        LeanFoundationPolicy::Constructive,
        budget(),
    )
    .unwrap_err();
    assert!(
        error.message.contains("duplicate interned export name"),
        "{error}"
    );
}

// Keep the buffered-reader trait exercised with fragmented input, since receipt
// verification must consume and validate the complete stream before returning.
struct OneByte<R>(R);
impl<R: Read> Read for OneByte<R> {
    fn read(&mut self, b: &mut [u8]) -> io::Result<usize> {
        let n = b.len().min(1);
        self.0.read(&mut b[..n])
    }
}
impl<R: BufRead> BufRead for OneByte<R> {
    fn fill_buf(&mut self) -> io::Result<&[u8]> {
        let b = self.0.fill_buf()?;
        Ok(&b[..b.len().min(1)])
    }
    fn consume(&mut self, n: usize) {
        self.0.consume(n)
    }
}

#[test]
fn receipt_accepts_fragmented_streams() {
    let r = check_lean_export_receipt_with_budget(
        OneByte(IDENTITY.as_bytes()),
        TARGET,
        LeanFoundationPolicy::Constructive,
        budget(),
    )
    .unwrap();
    assert_eq!(r.declaration_count(), 2);
}
