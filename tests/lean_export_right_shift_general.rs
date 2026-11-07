//! Manifest-backed replay checks for the unbounded natural-number right-shift theorem.
use lim::{
    check_lean_export_with_budget,
    lsp::json::{self, Json},
    translate_lean_export_with_budget, LeanFoundationPolicy, ProofBudget,
};
use std::collections::BTreeMap;

const RAW: &str =
    include_str!("fixtures/lean_export_right_shift_general/shift-right-general.ndjson");
const NATIVE: &str = include_str!("../theorems/lean_replay/shift-right-general.lim");
const MANIFEST: &str = include_str!("fixtures/lean_export_right_shift_general/provenance.json");
const SOURCE: &str = include_str!("fixtures/lean_export_right_shift_general/Source.lean");
const POLICY: LeanFoundationPolicy = LeanFoundationPolicy::Lean4;
const TARGETS: [&str; 4] = [
    "ShiftRightProbe.small",
    "ShiftRightProbe.zero",
    "ShiftRightProbe.large",
    "ShiftRightProbe.general",
];
const GENERAL: &str = TARGETS[3];

fn budget() -> ProofBudget {
    ProofBudget::new(20_000_000, 1 << 30, 4 << 30).unwrap()
}

fn manifest() -> Json {
    json::parse(MANIFEST).unwrap()
}

fn rows(source: &str) -> Vec<Json> {
    source
        .lines()
        .map(|line| json::parse(line).unwrap())
        .collect()
}

fn render(data: &[Json]) -> String {
    data.iter().map(Json::render).collect::<Vec<_>>().join("\n") + "\n"
}

fn object(value: &mut Json) -> &mut BTreeMap<String, Json> {
    let Json::Object(fields) = value else {
        panic!("expected JSON object")
    };
    fields
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

fn strings(value: &Json) -> Vec<String> {
    value
        .array()
        .unwrap()
        .iter()
        .map(|item| item.string().unwrap().to_owned())
        .collect()
}

fn target_axioms(target: &str) -> Vec<String> {
    strings(
        manifest()
            .get("target_inventories")
            .unwrap()
            .get(target)
            .unwrap(),
    )
}

#[test]
fn raw_native_and_manifest_correspond_for_all_four_targets() {
    assert!(SOURCE.contains(
        "theorem general (a b : Nat) : Nat.shiftRight a b = a / 2 ^ b := Nat.shiftRight_eq_div_pow a b"
    ));
    assert_eq!(
        strings(manifest().get("targets").unwrap()),
        TARGETS.map(str::to_owned)
    );
    assert_eq!(
        manifest().get("schema").unwrap().string(),
        Some("lim-lean-right-shift-general-fixture-v1")
    );
    assert_eq!(
        manifest()
            .get("source")
            .unwrap()
            .get("sha256")
            .unwrap()
            .string(),
        Some("81c83b07c334557351d29ae89cfecd90443ce760ab88506a0b68c37900ca5948")
    );
    let parsed = manifest();
    let owners = parsed
        .get("declarations")
        .unwrap()
        .array()
        .unwrap()
        .iter()
        .map(|item| item.get("module").unwrap().string().unwrap())
        .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(
        owners,
        [
            "Init.Core",
            "Init.Data.Nat.Basic",
            "Init.Data.Nat.Bitwise.Basic",
            "Init.Data.Nat.Div.Basic",
            "Init.Prelude",
            "Init.SimpLemmas",
            "Init.WF",
            "Source"
        ]
        .into_iter()
        .collect()
    );
    assert_eq!(
        manifest()
            .get("proof_budget")
            .unwrap()
            .get("work_per_phase")
            .unwrap()
            .render(),
        "20000000"
    );
    assert_eq!(
        manifest()
            .get("proof_budget")
            .unwrap()
            .get("transformation_bytes_per_phase")
            .unwrap()
            .render(),
        "1073741824"
    );
    assert_eq!(
        manifest()
            .get("proof_budget")
            .unwrap()
            .get("transformation_bytes_total")
            .unwrap()
            .render(),
        "4294967296"
    );

    let mut config = lim::CompileConfig::default();
    config.set_proof_budget(budget());
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("theorems/lean_replay/shift-right-general.lim");
    for target in TARGETS {
        let report =
            check_lean_export_with_budget(RAW.as_bytes(), target, POLICY, budget()).unwrap();
        assert_eq!(report.target, target);
        assert_eq!(report.budget, budget());
        assert_eq!(
            report.input_sha256,
            "7ad6811faecc66bf68855d87ebf7b94faa3b4599f7c3ebfdcaa5576f2d9eaa33"
        );
        assert_eq!(
            report.declarations.len(),
            manifest()
                .get("declarations")
                .unwrap()
                .array()
                .unwrap()
                .len()
        );
        assert_eq!(report.declarations.len(), 489);
        assert_eq!(report.axioms, ["propext"]);
        assert_eq!(report.target_axioms, target_axioms(target));
        assert_eq!(
            report.target_axioms,
            if target == GENERAL {
                vec!["propext".to_owned()]
            } else {
                vec![]
            }
        );
        assert!(report.foundations.is_empty());

        let translated =
            translate_lean_export_with_budget(RAW.as_bytes(), target, POLICY, budget()).unwrap();
        let native = native_name(target);
        assert_eq!(
            manifest()
                .get("native")
                .unwrap()
                .get("targets")
                .unwrap()
                .get(target)
                .unwrap()
                .string(),
            Some(native.as_str())
        );
        assert_eq!(translated.target, native);
        assert!(NATIVE.contains(&format!("(#theorem {native}\n")));
        if target == GENERAL {
            assert_eq!(translated.source, NATIVE);
        }
        let checked =
            lim::check_theorem_details_from_path_with_config(NATIVE, &path, &config, &native)
                .unwrap();
        assert_eq!(checked.budget, budget());
        assert_eq!(checked.foundations, target_axioms(target));
    }
    assert_eq!(
        manifest()
            .get("export")
            .unwrap()
            .get("sha256")
            .unwrap()
            .string(),
        Some("7ad6811faecc66bf68855d87ebf7b94faa3b4599f7c3ebfdcaa5576f2d9eaa33")
    );
    assert_eq!(
        manifest()
            .get("native")
            .unwrap()
            .get("sha256")
            .unwrap()
            .string(),
        Some("a6c613deaa9ccbc2e598711e9864aa5c824d4ec0ba5fe3440578ac16275f5379")
    );
}

#[test]
fn constructive_replay_rejects_general_target_propext() {
    let error = check_lean_export_with_budget(
        RAW.as_bytes(),
        GENERAL,
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

#[test]
fn altered_general_initializer_and_native_proof_are_type_mismatches() {
    let mut data = rows(RAW);
    let theorem = data
        .iter_mut()
        .rev()
        .find_map(|row| object(row).get_mut("thm"))
        .unwrap();
    let statement = theorem.get("type").unwrap().clone();
    object(theorem).insert("value".into(), statement);
    let altered = render(&data);
    let error =
        check_lean_export_with_budget(altered.as_bytes(), GENERAL, POLICY, budget()).unwrap_err();
    assert!(error.message.contains("type mismatch"), "{}", error.message);
    assert!(
        !error.message.contains("resource limit"),
        "{}",
        error.message
    );

    let native = native_name(GENERAL);
    let marker = format!("(#theorem {native}\n");
    assert_eq!(NATIVE.matches(&marker).count(), 1);
    let target_at = NATIVE.find(&marker).unwrap();
    let proof_at = target_at + NATIVE[target_at..].find("(#proof").unwrap();
    let altered = format!("{}(#proof (#pt-numeral 0)))\n", &NATIVE[..proof_at]);
    let mut config = lim::CompileConfig::default();
    config.set_proof_budget(budget());
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("theorems/lean_replay/shift-right-general.lim");
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
fn renaming_division_and_shift_workers_preserves_general_proof() {
    let mut data = rows(RAW);
    let mut changed = 0;
    let mut private_workers = 0;
    for row in &mut data {
        let Some(part) = object(row).get_mut("str") else {
            continue;
        };
        let Some(value) = object(part).get_mut("str") else {
            continue;
        };
        let name = value.string().unwrap();
        let replacement = if name == "div" {
            Some("renamedDivisionWorker".to_owned())
        } else if name.starts_with("div.") {
            Some(format!("renamedDivisionWorker{}", &name[3..]))
        } else if name == "shiftRight" {
            Some("renamedShiftWorker".to_owned())
        } else if name.starts_with("shiftRight.") {
            Some(format!("renamedShiftWorker{}", &name[10..]))
        } else if name == "shiftRight_eq_div_pow" {
            Some("renamedShiftDivisionBridge".to_owned())
        } else if name == "_f" {
            private_workers += 1;
            Some("ordinaryWorkerStep".to_owned())
        } else {
            None
        };
        if let Some(replacement) = replacement {
            *value = Json::String(replacement);
            changed += 1;
        }
    }
    assert!(changed > 0, "expected to rename an exported private worker");
    assert!(
        private_workers > 0,
        "expected to rename a private proof worker"
    );
    let altered = render(&data);
    let report =
        check_lean_export_with_budget(altered.as_bytes(), GENERAL, POLICY, budget()).unwrap();
    assert_eq!(report.target_axioms, ["propext"]);
}
