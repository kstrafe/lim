//! Pinned right-shift evaluator proofs and checks that names do not authorize them.
use lim::{
    check_lean_export_with_budget,
    lsp::json::{self, Json},
    translate_lean_export_with_budget, LeanFoundationPolicy, ProofBudget,
};
use std::collections::BTreeMap;

const RAW: &str = include_str!("fixtures/lean_export_right_shift/shift-right.ndjson");
const NATIVE: &str = include_str!("../theorems/lean_replay/shift-right.lim");
const MANIFEST: &str = include_str!("fixtures/lean_export_right_shift/provenance.json");
const POLICY: LeanFoundationPolicy = LeanFoundationPolicy::Constructive;
const TARGETS: [&str; 4] = [
    "ShiftRightProbe.small",
    "ShiftRightProbe.zero",
    "ShiftRightProbe.large",
    "ShiftRightProbe.boundary",
];
const LARGE_LITERAL: &str = "18446744073709551616";

fn budget() -> ProofBudget {
    ProofBudget::new(1_000_000, 128 << 20, 1 << 30).unwrap()
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
fn render(data: &[Json]) -> String {
    data.iter().map(Json::render).collect::<Vec<_>>().join("\n") + "\n"
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
fn target_axioms(target: &str) -> Vec<String> {
    manifest()
        .get("target_inventories")
        .unwrap()
        .get(target)
        .unwrap()
        .array()
        .unwrap()
        .iter()
        .map(|v| v.string().unwrap().to_owned())
        .collect()
}
fn native_name(target: &str) -> String {
    declaration(target)
        .get("native_name")
        .unwrap()
        .string()
        .unwrap()
        .to_owned()
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
        TARGETS
    );
    let mut upstream_modules: Vec<_> = parsed
        .get("upstream_sources")
        .unwrap()
        .array()
        .unwrap()
        .iter()
        .map(|source| source.get("source").unwrap().string().unwrap())
        .collect();
    upstream_modules.sort_unstable();
    assert_eq!(
        upstream_modules,
        [
            "src/Init/Data/Nat/Bitwise/Basic.lean",
            "src/Init/Prelude.lean"
        ]
    );
    let mut config = lim::CompileConfig::default();
    config.set_proof_budget(budget());
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("theorems/lean_replay/shift-right.lim");
    for target in TARGETS {
        let report =
            check_lean_export_with_budget(RAW.as_bytes(), target, POLICY, budget()).unwrap();
        assert_eq!(report.target, target);
        assert_eq!(report.budget, budget());
        let count = parsed.get("declarations").unwrap().array().unwrap().len();
        assert_eq!(report.declarations.len(), count);
        let all_axioms: Vec<String> = parsed
            .get("axioms")
            .unwrap()
            .array()
            .unwrap()
            .iter()
            .map(|v| v.string().unwrap().to_owned())
            .collect();
        assert_eq!(report.axioms, all_axioms);
        assert_eq!(report.target_axioms, target_axioms(target));
        assert_eq!(
            report.foundations,
            parsed
                .get("foundations")
                .unwrap()
                .array()
                .unwrap()
                .iter()
                .map(|v| v.string().unwrap().to_owned())
                .collect::<Vec<_>>()
        );
        let translated =
            translate_lean_export_with_budget(RAW.as_bytes(), target, POLICY, budget()).unwrap();
        assert_eq!(translated.target, native_name(target));
        assert!(NATIVE.contains(&format!("(#theorem {}\n", translated.target)));
        if target == TARGETS[3] {
            assert_eq!(translated.source, NATIVE);
        }
        let checked = lim::check_theorem_details_from_path_with_config(
            NATIVE,
            &path,
            &config,
            &translated.target,
        )
        .unwrap();
        assert_eq!(checked.budget, budget());
        assert_eq!(checked.foundations, target_axioms(target));
    }
}

#[test]
fn altered_right_shift_result_is_a_type_mismatch_in_raw_and_native_proofs() {
    let original = rows(RAW);
    let literal_at = original
        .iter()
        .position(|row| row.get("natVal").and_then(Json::string) == Some(LARGE_LITERAL))
        .expect("large natVal");
    let mut corrupted = original;
    object(&mut corrupted[literal_at]).insert("natVal".into(), Json::String("0".into()));
    for target in TARGETS {
        let error =
            check_lean_export_with_budget(render(&corrupted).as_bytes(), target, POLICY, budget())
                .unwrap_err();
        assert!(error.message.contains("type mismatch"), "{}", error.message);
        assert!(
            !error.message.contains("resource limit"),
            "{}",
            error.message
        );
    }

    let mut config = lim::CompileConfig::default();
    config.set_proof_budget(budget());
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("theorems/lean_replay/shift-right.lim");
    let marker = format!("(#theorem {}", native_name(TARGETS[2]));
    let (prefix, tail) = NATIVE.split_once(&marker).unwrap();
    let altered = tail.replacen(LARGE_LITERAL, "0", 1);
    assert_ne!(altered, tail);
    let bad_source = format!("{prefix}{marker}{altered}");
    for target in TARGETS {
        let bad = lim::check_theorem_details_from_path_with_config(
            &bad_source,
            &path,
            &config,
            &native_name(target),
        )
        .unwrap_err();
        assert!(bad.message.contains("type mismatch"), "{}", bad.message);
        assert!(!bad.message.contains("resource limit"), "{}", bad.message);
    }
}

#[test]
fn renaming_shift_right_declaration_components_preserves_checked_targets() {
    let mut data = rows(RAW);
    let mut changed = 0;
    for row in &mut data {
        let Some(part) = object(row).get_mut("str") else {
            continue;
        };
        let Some(value) = object(part).get_mut("str") else {
            continue;
        };
        let replacement = match value.string().unwrap() {
            "shiftRight" => Some("renamedShiftRight".to_owned()),
            name if name.starts_with("shiftRight.") => {
                Some(format!("renamedShiftRight{}", &name[10..]))
            }
            "shiftRight_eq" => Some("renamedShiftRight_eq".to_owned()),
            name if name.starts_with("shiftRight_eq.") => {
                Some(format!("renamedShiftRight_eq{}", &name[14..]))
            }
            "_f" => Some("ordinaryFunctionStep".to_owned()),
            _ => None,
        };
        if let Some(replacement) = replacement {
            *value = Json::String(replacement);
            changed += 1;
        }
    }
    assert!(changed > 0);
    let renamed = render(&data);
    for target in TARGETS {
        let report =
            check_lean_export_with_budget(renamed.as_bytes(), target, POLICY, budget()).unwrap();
        assert_eq!(report.target, target);
        assert!(report.axioms.is_empty());
        assert_eq!(report.target_axioms, target_axioms(target));
    }
}
