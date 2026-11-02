//! Native export retains source expressions without expanding unused records.
use lim::{
    check_lean_export_with_budget, translate_lean_export_with_budget, LeanFoundationPolicy,
    ProofBudget,
};

const RAW: &str = include_str!("fixtures/lean_export/identity.ndjson");
const TARGET: &str = "Audit.identity.theorem";

fn budget() -> ProofBudget {
    ProofBudget::new(1_000_000, 128 << 20, 1 << 30).unwrap()
}

fn append_unused_bvars(raw: &str, count: usize) -> String {
    let mut result = String::with_capacity(raw.len() + count * 24);
    result.push_str(raw);
    for index in 20..20 + count {
        result.push_str(&format!("{{\"bvar\":0,\"ie\":{index}}}\n"));
    }
    result
}

#[test]
fn native_storage_spills_without_changing_the_recovered_proof_or_report() {
    let budget = budget();
    let raw_report = check_lean_export_with_budget(
        RAW.as_bytes(),
        TARGET,
        LeanFoundationPolicy::Constructive,
        budget,
    )
    .unwrap();
    let native = translate_lean_export_with_budget(
        RAW.as_bytes(),
        TARGET,
        LeanFoundationPolicy::Constructive,
        budget,
    )
    .unwrap();
    assert_eq!(native.report.render_json(), raw_report.render_json());
    assert_eq!(raw_report.declarations.len(), 2);
    assert_eq!(
        raw_report.declarations[0].sha256,
        "623a885e24045bd70520481e7e1d013f945e3b163922f1773e47dddbf5ff491c"
    );
    assert_eq!(
        raw_report.declarations[1].sha256,
        "ad05e4153b542ea6dcd88e4a92d0a8e42ad2d757bdbc19552e3229a979c974ec"
    );

    let padded = append_unused_bvars(RAW, 190_000);
    assert!(padded.len() > 2 * 1024 * 1024);
    let padded_report = check_lean_export_with_budget(
        padded.as_bytes(),
        TARGET,
        LeanFoundationPolicy::Constructive,
        budget,
    )
    .unwrap();
    let padded_native = translate_lean_export_with_budget(
        padded.as_bytes(),
        TARGET,
        LeanFoundationPolicy::Constructive,
        budget,
    )
    .unwrap();

    let original_header = format!("; Input SHA-256: {}", raw_report.input_sha256);
    let padded_header = format!("; Input SHA-256: {}", padded_report.input_sha256);
    assert_eq!(native.source.matches(&original_header).count(), 1);
    assert_eq!(padded_native.source.matches(&padded_header).count(), 1);
    assert_eq!(
        padded_native
            .source
            .replacen(&padded_header, &original_header, 1),
        native.source
    );
    assert_eq!(padded_report.declarations, raw_report.declarations);
    assert_eq!(padded_native.report.declarations, raw_report.declarations);
    assert_eq!(
        padded_native.report.render_json(),
        padded_report.render_json()
    );
    assert_ne!(padded_report.input_sha256, raw_report.input_sha256);
    assert_eq!(
        padded_native.report.input_sha256,
        padded_report.input_sha256
    );

    let parsed = lim::parse_program(&padded_native.source).unwrap();
    lim::check_types(&parsed).unwrap();
}

#[test]
fn invalid_trailing_records_fail_before_native_proof_output() {
    let invalid = format!("{RAW}{{\"ie\":21,\"bvar\":0}}\n");
    assert!(check_lean_export_with_budget(
        invalid.as_bytes(),
        TARGET,
        LeanFoundationPolicy::Constructive,
        budget(),
    )
    .is_err());
    assert!(translate_lean_export_with_budget(
        invalid.as_bytes(),
        TARGET,
        LeanFoundationPolicy::Constructive,
        budget(),
    )
    .is_err());
}
