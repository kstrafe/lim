//! Pinned bitwise evaluator proofs and checks that names do not authorize them.
use lim::{
    check_lean_export_with_budget,
    lsp::json::{self, Json},
    translate_lean_export_with_budget, LeanFoundationPolicy, ProofBudget,
};
use std::collections::BTreeMap;

const RAW: &str = include_str!("fixtures/lean_export_bitwise/bitwise.ndjson");
const NATIVE: &str = include_str!("../theorems/lean_replay/bitwise.lim");
const MANIFEST: &str = include_str!("fixtures/lean_export_bitwise/provenance.json");
const POLICY: LeanFoundationPolicy = LeanFoundationPolicy::Lean4;
const TARGETS: [&str; 3] = [
    "BitwiseProbe.and_small",
    "BitwiseProbe.or_small",
    "BitwiseProbe.xor_small",
];

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
    let mut config = lim::CompileConfig::default();
    config.set_proof_budget(budget());
    let path =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("theorems/lean_replay/bitwise.lim");
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
        if target == TARGETS[2] {
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
fn constructive_policy_rejects_manifest_axioms() {
    let result = lim::check_lean_export_with_budget(
        RAW.as_bytes(),
        TARGETS[0],
        LeanFoundationPolicy::Constructive,
        budget(),
    );
    assert!(result.unwrap_err().message.contains("not authorized"));
}

#[test]
fn altered_natural_literal_is_a_type_mismatch_in_raw_and_native_proofs() {
    let original = rows(RAW);
    let literal_at = original
        .iter()
        .position(|row| row.get("natVal").and_then(Json::string) == Some("9"))
        .expect("natVal 9");
    let mut corrupted = original;
    object(&mut corrupted[literal_at]).insert("natVal".into(), Json::String("8".into()));
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
    let path =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("theorems/lean_replay/bitwise.lim");
    let marker = format!("(#theorem {}", native_name(TARGETS[0]));
    let (prefix, tail) = NATIVE.split_once(&marker).unwrap();
    let altered = tail.replacen("\"9\"", "\"8\"", 1);
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
fn renaming_bitwise_declaration_components_preserves_checked_targets() {
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
            "bitwise" => Some("renamedBits".to_owned()),
            "land" => Some("renamedLand".to_owned()),
            "lor" => Some("renamedLor".to_owned()),
            "xor" => Some("renamedXor".to_owned()),
            "_unary" => Some("renamedUnary".to_owned()),
            name if name.starts_with("bitwise.") => Some(format!("renamedBits{}", &name[7..])),
            name if name.starts_with("land.") => Some(format!("renamedLand{}", &name[4..])),
            name if name.starts_with("lor.") => Some(format!("renamedLor{}", &name[3..])),
            name if name.starts_with("xor.") => Some(format!("renamedXor{}", &name[3..])),
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
        assert_eq!(report.target_axioms, target_axioms(target));
    }
}
