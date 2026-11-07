use lim::{parse_program, translate_lean_export_with_budget, LeanFoundationPolicy, ProofBudget};
const IDENTITY: &str = include_str!("fixtures/lean_export/identity.ndjson");
const QUOTIENT: &str = include_str!("fixtures/lean_export_quotient/quotient.ndjson");
const FOUNDATIONS: &str = include_str!("fixtures/lean_export_foundations/foundations.ndjson");

fn budget() -> ProofBudget {
    ProofBudget::default()
}

fn compare(input: &str, target: &str, policy: LeanFoundationPolicy) {
    let expected =
        translate_lean_export_with_budget(input.as_bytes(), target, policy, budget()).unwrap();
    let actual = lim::translate_lean_export_receipt_with_budget(
        std::io::BufReader::new(input.as_bytes()),
        target,
        policy,
        budget(),
    )
    .unwrap();
    assert_eq!(actual.source, expected.source);
    assert_eq!(actual.target, expected.target);
    assert_eq!(
        actual.receipt.declaration_count(),
        expected.report.declarations.len()
    );
    let mut json = Vec::new();
    actual.receipt.write_json(&mut json).unwrap();
    assert_eq!(json, expected.report.render_json().as_bytes());
    let mut materialized = Vec::new();
    actual
        .receipt
        .into_report()
        .unwrap()
        .write_json(&mut materialized)
        .unwrap();
    assert_eq!(materialized, json);
    let program = parse_program(&actual.source).unwrap();
    lim::check_types(&program).unwrap();
    let path = if target.starts_with("QuotientSource.") {
        "theorems/lean_replay/quotient.lim"
    } else if target.starts_with("BasisProbe.") {
        "theorems/lean_replay/foundations.lim"
    } else {
        "theorems/lean_replay/identity.lim"
    };
    lim::check_theorem_from_path_with_config(
        &actual.source,
        &std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(path),
        &lim::CompileConfig::default(),
        &actual.target,
    )
    .unwrap();
}

#[test]
fn identity_and_genuine_foundation_and_quotient_translations_match() {
    compare(
        IDENTITY,
        "Audit.identity.theorem",
        LeanFoundationPolicy::Constructive,
    );
    compare(
        QUOTIENT,
        "QuotientSource.inductionReflexive",
        LeanFoundationPolicy::Constructive,
    );
    compare(
        FOUNDATIONS,
        "BasisProbe.quotientRelated",
        LeanFoundationPolicy::Lean4,
    );
}

fn synthetic_large_identity() -> String {
    let mut rows: Vec<String> = IDENTITY.lines().map(str::to_owned).collect();
    let theorem = rows.pop().unwrap();
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
        input.push_str(&format!(
            "{{\"thm\":{{\"name\":{name_id},\"levelParams\":[],\"type\":12,\"value\":19,\"all\":[{name_id}]}}}}\n"
        ));
    }
    input.push_str(&theorem);
    input.push('\n');
    input
}

#[test]
fn long_name_inventory_spills_and_matches_both_translation_paths() {
    let input = synthetic_large_identity();
    let expected = translate_lean_export_with_budget(
        input.as_bytes(),
        "Audit.identity.theorem",
        LeanFoundationPolicy::Constructive,
        budget(),
    )
    .unwrap();
    assert!(expected.source.len() < 8 * 1024 * 1024);
    let actual = lim::translate_lean_export_receipt_with_budget(
        input.as_bytes(),
        "Audit.identity.theorem",
        LeanFoundationPolicy::Constructive,
        budget(),
    )
    .unwrap();
    assert_eq!(actual.source, expected.source);
    assert_eq!(actual.target, expected.target);
    assert_eq!(actual.receipt.declaration_count(), 92);
    let mut receipt = Vec::new();
    actual.receipt.write_json(&mut receipt).unwrap();
    assert_eq!(receipt, expected.report.render_json().as_bytes());
    assert!(
        receipt.len() > 1 << 20,
        "fixture did not trigger metadata spilling"
    );
    let mut report = Vec::new();
    actual
        .receipt
        .into_report()
        .unwrap()
        .write_json(&mut report)
        .unwrap();
    assert_eq!(report, receipt);
}

#[test]
fn malformed_trailing_input_and_duplicate_selected_theorem_match_rejection() {
    let mut duplicate = IDENTITY.to_owned();
    duplicate.push_str(IDENTITY.lines().last().unwrap());
    duplicate.push('\n');
    for input in [format!("{IDENTITY}{{not json}}\n"), duplicate] {
        let eager = translate_lean_export_with_budget(
            input.as_bytes(),
            "Audit.identity.theorem",
            LeanFoundationPolicy::Constructive,
            budget(),
        )
        .unwrap_err();
        let receipt = lim::translate_lean_export_receipt_with_budget(
            input.as_bytes(),
            "Audit.identity.theorem",
            LeanFoundationPolicy::Constructive,
            budget(),
        )
        .unwrap_err();
        assert_eq!(receipt.message, eager.message);
    }
}
