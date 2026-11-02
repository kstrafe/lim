//! Pinned single-target replay for Lean's generic `Nat.gcd_self` theorem.
mod support;

use lim::{
    check_lean_export_with_budget,
    lsp::json::{self, Json},
    translate_lean_export_with_budget, CompileConfig, LeanFoundationPolicy, ProofBudget,
};
use std::{collections::BTreeMap, fs, process::Command, time::Duration};

const TARGET: &str = "GcdSelfSource.self";
const NATIVE_TARGET: &str = "lean-334-GcdSelfSource-self";
const POLICY: LeanFoundationPolicy = LeanFoundationPolicy::Lean4;
const AXIOMS: &[&str] = &["Quot.sound", "propext"];
const FOUNDATIONS: &[&str] = &["quotient-computation-v1"];

fn budget() -> ProofBudget {
    ProofBudget::new(1_000_000, 134_217_728, 1_073_741_824).unwrap()
}

fn artifacts() -> (String, String) {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    (
        fs::read_to_string(root.join("tests/fixtures/lean_export_gcd_self/gcd-self.ndjson"))
            .unwrap(),
        fs::read_to_string(root.join("theorems/lean_replay/gcd-self.lim")).unwrap(),
    )
}

fn rows(source: &str) -> Vec<Json> {
    source
        .lines()
        .map(|line| json::parse(line).unwrap())
        .collect()
}

fn object(value: &mut Json) -> &mut BTreeMap<String, Json> {
    let Json::Object(fields) = value else {
        panic!("expected JSON object")
    };
    fields
}

fn field<'a>(value: &'a mut Json, name: &str) -> &'a mut Json {
    object(value).get_mut(name).unwrap()
}

fn render(data: &[Json]) -> String {
    data.iter().map(Json::render).collect::<Vec<_>>().join("\n") + "\n"
}

fn checked_config() -> CompileConfig {
    let mut config = CompileConfig::default();
    config.set_proof_budget(budget());
    config
}

#[test]
fn explicit_budget_replays_and_independently_checks_exact_native_translation() {
    let (raw, native) = artifacts();
    let budget = budget();
    let constructive = check_lean_export_with_budget(
        raw.as_bytes(),
        TARGET,
        LeanFoundationPolicy::Constructive,
        budget,
    )
    .unwrap_err();
    assert!(
        constructive.message.contains("not authorized"),
        "{}",
        constructive.message
    );

    let default_budget = ProofBudget::default();
    let default_failure =
        check_lean_export_with_budget(raw.as_bytes(), TARGET, POLICY, default_budget).unwrap_err();
    assert!(
        default_failure.message.contains("resource limit"),
        "{}",
        default_failure.message
    );

    let report = check_lean_export_with_budget(raw.as_bytes(), TARGET, POLICY, budget).unwrap();
    assert_eq!(report.target, TARGET);
    assert_eq!(report.declarations.len(), 335);
    assert_eq!(report.budget, budget);
    assert_eq!(report.axioms, AXIOMS);
    assert_eq!(report.target_axioms, AXIOMS);
    assert_eq!(report.foundations, FOUNDATIONS);

    let translated =
        translate_lean_export_with_budget(raw.as_bytes(), TARGET, POLICY, budget).unwrap();
    assert_eq!(translated.target, NATIVE_TARGET);
    assert!(translated.source == native, "native translation differs");
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let native_path = root.join("theorems/lean_replay/gcd-self.lim");
    let checked = lim::check_theorem_details_from_path_with_config(
        &native,
        &native_path,
        &checked_config(),
        NATIVE_TARGET,
    )
    .unwrap();
    assert_eq!(checked.budget, budget);
    assert_eq!(checked.foundations, AXIOMS);
    let default_native = lim::check_theorem_details_from_path_with_config(
        &native,
        &native_path,
        &CompileConfig::default(),
        NATIVE_TARGET,
    )
    .unwrap_err();
    assert!(
        default_native.message.contains("resource limit"),
        "{}",
        default_native.message
    );
}

#[test]
fn cli_reports_exact_raw_and_native_audit_lines_with_empty_path() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let raw_path = root.join("tests/fixtures/lean_export_gcd_self/gcd-self.ndjson");
    let native_path = root.join("theorems/lean_replay/gcd-self.lim");
    let raw_path = raw_path.to_str().unwrap();
    let native_path = native_path.to_str().unwrap();
    let budget_args = [
        "--proof-work",
        "1000000",
        "--proof-phase-bytes",
        "134217728",
        "--proof-total-bytes",
        "1073741824",
    ];

    let mut command = Command::new(env!("CARGO_BIN_EXE_lim"));
    command.env("PATH", "").args([
        "--check-lean-export",
        raw_path,
        TARGET,
        "--lean-foundations",
        budget_args[0],
        budget_args[1],
        budget_args[2],
        budget_args[3],
        budget_args[4],
        budget_args[5],
    ]);
    let (status, stdout, stderr) =
        support::run(&mut command, Duration::from_secs(60), 65536).unwrap();
    assert!(status.success(), "{}", String::from_utf8_lossy(&stderr));
    let output = String::from_utf8(stdout).unwrap();
    assert_eq!(
        output.lines().collect::<Vec<_>>(),
        [
            format!("checked Lean export theorem {TARGET} (335 declarations)"),
            "proof budget: work=1000000 phase-bytes=134217728 total-bytes=1073741824".into(),
            "declared Lean axioms: Quot.sound, propext".into(),
            "target logical foundations: Quot.sound, propext".into(),
        ]
    );

    let mut command = Command::new(env!("CARGO_BIN_EXE_lim"));
    command.env("PATH", "").args([
        "--check-theorem",
        native_path,
        NATIVE_TARGET,
        budget_args[0],
        budget_args[1],
        budget_args[2],
        budget_args[3],
        budget_args[4],
        budget_args[5],
    ]);
    let (status, stdout, stderr) =
        support::run(&mut command, Duration::from_secs(60), 65536).unwrap();
    assert!(status.success(), "{}", String::from_utf8_lossy(&stderr));
    let output = String::from_utf8(stdout).unwrap();
    assert_eq!(
        output.lines().collect::<Vec<_>>(),
        [
            format!("checked theorem {NATIVE_TARGET}"),
            "proof budget: work=1000000 phase-bytes=134217728 total-bytes=1073741824".into(),
            "logical foundations: Quot.sound, propext".into(),
        ]
    );
}

#[test]
fn helper_name_component_renaming_keeps_selected_closure_and_fixed_axioms() {
    let (raw, _) = artifacts();
    let budget = budget();
    let mut data = rows(&raw);
    let mut renamed = 0;
    for row in &mut data {
        let Some(name) = object(row).get_mut("str") else {
            continue;
        };
        let part = object(name).get_mut("str").unwrap();
        let replacement = match part.string().unwrap() {
            "gcd" => Some("renamedGcd".to_owned()),
            "_unary" => Some("renamedUnary".to_owned()),
            "modCore" => Some("renamedModCore".to_owned()),
            "fuel_congr" => Some("renamedFuelCongr".to_owned()),
            "fix" => Some("ordinaryFix".to_owned()),
            "casesOn" => Some("ordinaryCasesOn".to_owned()),
            name if name.starts_with("gcd.") => Some(format!("renamed{name}")),
            name if name.starts_with("_unary.") => Some(format!("renamed{name}")),
            name if name.starts_with("modCore.") => Some(format!("renamed{name}")),
            name if name.starts_with("fuel_congr.") => Some(format!("renamed{name}")),
            _ => None,
        };
        if let Some(replacement) = replacement {
            *part = Json::String(replacement);
            renamed += 1;
        }
    }
    assert!(renamed > 0);
    let report =
        check_lean_export_with_budget(render(&data).as_bytes(), TARGET, POLICY, budget).unwrap();
    assert_eq!(report.target_axioms, AXIOMS);
    assert_eq!(report.foundations, FOUNDATIONS);
}

#[test]
fn corrupted_private_modcore_helper_and_target_proof_fail_at_checked_rows() {
    let (raw, _) = artifacts();
    let budget = budget();
    let report = check_lean_export_with_budget(raw.as_bytes(), TARGET, POLICY, budget).unwrap();
    let mut data = rows(&raw);
    let helper = report
        .declarations
        .iter()
        .find(|declaration| declaration.name.contains("Nat.modCore.go.fuel_congr._f"))
        .expect("checked private modCore fuel_congr helper");
    let target_declaration = report
        .declarations
        .iter()
        .find(|d| d.name == TARGET)
        .unwrap();
    for declaration in [helper, target_declaration] {
        let at = declaration.line - 1;
        let earlier_sort = data[..at]
            .iter()
            .find_map(|row| {
                row.get("sort")
                    .and_then(Json::integer)
                    .map(|_| row.get("ie").unwrap().clone())
            })
            .expect("earlier sort expression");
        let payload_key = if data[at].get("def").is_some() {
            "def"
        } else {
            "thm"
        };
        object(field(&mut data[at], payload_key)).insert("value".into(), earlier_sort);
        let error = check_lean_export_with_budget(render(&data).as_bytes(), TARGET, POLICY, budget)
            .unwrap_err();
        assert_eq!(error.line, declaration.line);
        assert!(error.message.contains("type mismatch"), "{}", error.message);
        assert!(
            !error.message.contains("resource limit"),
            "{}",
            error.message
        );
        // Restore the clean export before corrupting the next independently selected row.
        data = rows(&raw);
    }
}

#[test]
fn corrupted_native_target_proof_is_selected_by_ast_span_and_rejected_after_prefix() {
    let (raw, native) = artifacts();
    let translated =
        translate_lean_export_with_budget(raw.as_bytes(), TARGET, POLICY, budget()).unwrap();
    let theorem = lim::parse(&native)
        .unwrap()
        .into_iter()
        .find(|node| {
            matches!(&node.expr, lim::Expr::List(items)
            if matches!(items.get(1), Some(lim::Expr::Symbol(name)) if name == NATIVE_TARGET))
        })
        .expect("native target theorem node");
    let proof = theorem
        .children
        .iter()
        .find(|node| {
            matches!(&node.expr, lim::Expr::List(items)
            if matches!(items.first(), Some(lim::Expr::Symbol(keyword)) if keyword == "#proof"))
        })
        .expect("native proof clause");
    let span = proof.children[1].span;
    lim::check_types(
        &lim::parse_program_with_config(&native[..theorem.span.start], &checked_config()).unwrap(),
    )
    .unwrap();
    let mut corrupted = native.clone();
    corrupted.replace_range(span.start..span.end, "#pt-prop");
    let path =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("theorems/lean_replay/gcd-self.lim");
    let error = lim::check_theorem_details_from_path_with_config(
        &corrupted,
        &path,
        &checked_config(),
        &translated.target,
    )
    .unwrap_err();
    assert!(error.message.contains("type mismatch"), "{}", error.message);
    assert!(
        !error.message.contains("resource limit"),
        "{}",
        error.message
    );
}
