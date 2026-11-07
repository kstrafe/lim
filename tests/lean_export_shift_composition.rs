//! Pinned natural right-shift composition proof and manifest-backed replay checks.
use lim::{
    check_lean_export_with_budget,
    lsp::json::{self, Json},
    translate_lean_export_with_budget, LeanFoundationPolicy, ProofBudget,
};
use std::collections::BTreeMap;

const RAW: &str = include_str!("fixtures/lean_export_shift_composition/shift-composition.ndjson");
const NATIVE: &str = include_str!("../theorems/lean_replay/shift-composition.lim");
const MANIFEST: &str = include_str!("fixtures/lean_export_shift_composition/provenance.json");
const POLICY: LeanFoundationPolicy = LeanFoundationPolicy::Lean4;
const TARGET: &str = "ShiftCompositionProbe.general";

fn budget() -> ProofBudget {
    ProofBudget::new(20_000_000, 1 << 30, 4 << 30).unwrap()
}

fn manifest() -> Json {
    json::parse(MANIFEST).unwrap()
}

fn declaration(name: &str) -> Json {
    manifest()
        .get("declarations")
        .unwrap()
        .array()
        .unwrap()
        .iter()
        .find(|item| item.get("name").and_then(Json::string) == Some(name))
        .unwrap()
        .clone()
}

fn native_name(name: &str) -> String {
    declaration(name)
        .get("native_name")
        .unwrap()
        .string()
        .unwrap()
        .to_owned()
}

fn inventory(key: &str) -> Vec<String> {
    manifest()
        .get(key)
        .unwrap()
        .array()
        .unwrap()
        .iter()
        .map(|value| value.string().unwrap().to_owned())
        .collect()
}

#[test]
fn raw_and_native_replays_match_manifest_closures() {
    let parsed = manifest();
    assert_eq!(
        parsed
            .get("targets")
            .unwrap()
            .array()
            .unwrap()
            .iter()
            .map(|value| value.string().unwrap())
            .collect::<Vec<_>>(),
        [TARGET]
    );
    let mut config = lim::CompileConfig::default();
    config.set_proof_budget(budget());
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("theorems/lean_replay/shift-composition.lim");
    let report = check_lean_export_with_budget(RAW.as_bytes(), TARGET, POLICY, budget()).unwrap();
    assert_eq!(report.target, TARGET);
    assert_eq!(report.budget, budget());
    assert_eq!(
        report.declarations.len(),
        parsed.get("declarations").unwrap().array().unwrap().len()
    );
    assert_eq!(report.axioms, inventory("axioms"));
    assert_eq!(
        report.target_axioms,
        parsed
            .get("target_inventories")
            .unwrap()
            .get(TARGET)
            .unwrap()
            .array()
            .unwrap()
            .iter()
            .map(|value| value.string().unwrap().to_owned())
            .collect::<Vec<_>>()
    );
    assert_eq!(report.foundations, inventory("foundations"));

    let translated =
        translate_lean_export_with_budget(RAW.as_bytes(), TARGET, POLICY, budget()).unwrap();
    let native = native_name(TARGET);
    assert_eq!(translated.target, native);
    assert_eq!(translated.source.as_bytes(), NATIVE.as_bytes());
    let checked =
        lim::check_theorem_details_from_path_with_config(NATIVE, &path, &config, &native).unwrap();
    assert_eq!(checked.budget, budget());
    assert_eq!(checked.foundations, report.target_axioms);
}

#[test]
fn constructive_replay_rejects_the_explicit_propext_axiom() {
    let error = check_lean_export_with_budget(
        RAW.as_bytes(),
        TARGET,
        LeanFoundationPolicy::Constructive,
        budget(),
    )
    .unwrap_err();
    assert!(
        error.message.contains("not authorized"),
        "{}",
        error.message
    );
}

fn object(value: &mut Json) -> &mut BTreeMap<String, Json> {
    let Json::Object(value) = value else {
        panic!("expected object")
    };
    value
}

#[test]
fn replacing_only_evidence_is_a_type_mismatch_in_raw_and_native_replay() {
    let mut rows: Vec<Json> = RAW.lines().map(|line| json::parse(line).unwrap()).collect();
    let theorem = rows
        .iter_mut()
        .rev()
        .find_map(|row| object(row).get_mut("thm"))
        .unwrap();
    let statement = theorem.get("type").unwrap().clone();
    object(theorem).insert("value".into(), statement);
    let altered = rows.iter().map(Json::render).collect::<Vec<_>>().join("\n") + "\n";
    let error =
        check_lean_export_with_budget(altered.as_bytes(), TARGET, POLICY, budget()).unwrap_err();
    assert!(error.message.contains("type mismatch"), "{}", error.message);
    assert!(
        !error.message.contains("resource limit"),
        "{}",
        error.message
    );

    let native = native_name(TARGET);
    let marker = format!("(#theorem {native}\n");
    assert_eq!(NATIVE.matches(&marker).count(), 1);
    let target_at = NATIVE.find(&marker).unwrap();
    let proof_at = target_at + NATIVE[target_at..].find("(#proof").unwrap();
    let altered = format!("{}(#proof (#pt-numeral 0)))\n", &NATIVE[..proof_at]);
    let mut config = lim::CompileConfig::default();
    config.set_proof_budget(budget());
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("theorems/lean_replay/shift-composition.lim");
    let error = lim::check_theorem_details_from_path_with_config(&altered, &path, &config, &native)
        .unwrap_err();
    assert!(error.message.contains("type mismatch"), "{}", error.message);
    assert!(
        !error.message.contains("resource limit"),
        "{}",
        error.message
    );
}

#[test]
fn renaming_composition_workers_preserves_the_unbounded_proof() {
    let mut rows: Vec<Json> = RAW.lines().map(|line| json::parse(line).unwrap()).collect();
    let mut changed = 0;
    for row in &mut rows {
        let Some(part) = object(row).get_mut("str") else {
            continue;
        };
        let Some(value) = object(part).get_mut("str") else {
            continue;
        };
        let replacement = match value.string().unwrap() {
            "shiftRight_add" => Some("ordinaryComposition"),
            "_f" => Some("ordinaryStep"),
            _ => None,
        };
        if let Some(replacement) = replacement {
            *value = Json::String(replacement.into());
            changed += 1;
        }
    }
    assert!(changed > 0);
    let altered = rows.iter().map(Json::render).collect::<Vec<_>>().join("\n") + "\n";
    let report =
        check_lean_export_with_budget(altered.as_bytes(), TARGET, POLICY, budget()).unwrap();
    assert_eq!(report.target_axioms, ["propext"]);
}
