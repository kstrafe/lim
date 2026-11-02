//! Actual generic subtraction induction proofs, checked without a name rule.
use lim::lsp::json::{self, Json};
use std::collections::BTreeMap;

const FIXTURE: &str =
    include_str!("fixtures/lean_export_subtraction_bridge/subtraction-bridge.ndjson");
const MANIFEST: &str = include_str!("fixtures/lean_export_subtraction_bridge/provenance.json");
const NATIVE: &str = include_str!("../theorems/lean_replay/subtraction-bridge.lim");
const TARGETS: &[&str] = &[
    "SubtractionBridgeSource.successorCancellation",
    "SubtractionBridgeSource.doubleCancellation",
    "SubtractionBridgeSource.mappedCancellation",
];

fn native_name(original: &str) -> String {
    json::parse(MANIFEST)
        .unwrap()
        .get("declarations")
        .unwrap()
        .array()
        .unwrap()
        .iter()
        .find(|d| d.get("name").and_then(Json::string) == Some(original))
        .unwrap()
        .get("native_name")
        .unwrap()
        .string()
        .unwrap()
        .to_owned()
}

#[test]
fn actual_generic_subtraction_proofs_have_empty_assumption_inventories() {
    for target in TARGETS {
        let report = lim::check_lean_export(FIXTURE.as_bytes(), target).unwrap();
        assert_eq!(&report.target, target);
        assert!(report.axioms.is_empty());
        assert!(report.target_axioms.is_empty());
        assert!(report.foundations.is_empty());
    }
}

#[test]
fn exact_native_translation_independently_checks_all_generic_targets() {
    let target = TARGETS.last().unwrap();
    let translated = lim::translate_lean_export(FIXTURE.as_bytes(), target).unwrap();
    assert_eq!(translated.source, NATIVE);
    assert_eq!(translated.target, native_name(target));
    lim::check_types(&lim::parse_program(NATIVE).unwrap()).unwrap();
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("theorems/lean_replay/subtraction-bridge.lim");
    for original in TARGETS {
        let report = lim::check_theorem_details_from_path_with_config(
            NATIVE,
            &path,
            &lim::CompileConfig::default(),
            &native_name(original),
        )
        .unwrap();
        assert!(report.foundations.is_empty());
    }
}

fn rows() -> Vec<Json> {
    FIXTURE
        .lines()
        .map(|row| json::parse(row).unwrap())
        .collect()
}
fn object(value: &mut Json) -> &mut BTreeMap<String, Json> {
    let Json::Object(fields) = value else {
        panic!("fixture object")
    };
    fields
}
fn render(rows: &[Json]) -> String {
    rows.iter().map(Json::render).collect::<Vec<_>>().join("\n") + "\n"
}

#[test]
fn standard_operation_and_theorem_names_carry_no_computation_authority() {
    let mut data = rows();
    let mut changed = 0;
    for row in &mut data {
        let Some(name) = object(row).get_mut("str") else {
            continue;
        };
        let part = object(name).get_mut("str").unwrap();
        let replacement = match part.string().unwrap() {
            "sub" => "ordinaryRepeatedStep",
            "pred" => "ordinaryPrecedingValue",
            "succ_sub_succ_eq_sub" => "ordinaryInductionProof",
            _ => continue,
        };
        *part = Json::String(replacement.into());
        changed += 1;
    }
    assert!(changed >= 3);
    let report = lim::check_lean_export(render(&data).as_bytes(), TARGETS.last().unwrap()).unwrap();
    assert!(report.axioms.is_empty() && report.foundations.is_empty());
    assert!(report
        .declarations
        .iter()
        .any(|d| d.name == "Nat.ordinaryInductionProof"));
}

#[test]
fn corrupted_standard_and_user_proofs_fail_after_valid_dependency_prefixes() {
    let report = lim::check_lean_export(FIXTURE.as_bytes(), TARGETS.last().unwrap()).unwrap();
    for name in ["Nat.succ_sub_succ_eq_sub", TARGETS[2]] {
        let ordinal = report
            .declarations
            .iter()
            .position(|d| d.name == name)
            .unwrap();
        let declaration = &report.declarations[ordinal];
        let previous = report.declarations[..ordinal]
            .iter()
            .rev()
            .find(|d| d.kind == "theorem")
            .unwrap();
        let mut data = rows();
        let at = declaration.line - 1;
        lim::check_lean_export(render(&data[..at]).as_bytes(), &previous.name).unwrap();
        let invalid = data[..at]
            .iter()
            .find(|row| row.get("sort").is_some())
            .unwrap()
            .get("ie")
            .unwrap()
            .clone();
        object(object(&mut data[at]).get_mut("thm").unwrap()).insert("value".into(), invalid);
        let why =
            lim::check_lean_export(render(&data).as_bytes(), TARGETS.last().unwrap()).unwrap_err();
        assert_eq!(why.line, declaration.line);
        assert!(why.message.contains(name), "{why}");
        assert!(why.message.contains("type mismatch"), "{why}");
        assert!(!why.message.contains("resource limit"), "{why}");
    }
}

fn declaration(source: &str, name: &str) -> lim::SpannedExpr {
    lim::parse(source)
        .unwrap()
        .into_iter()
        .find(|node| {
            matches!(
                &node.expr, lim::Expr::List(items)
                    if matches!(items.get(1), Some(lim::Expr::Symbol(actual)) if actual == name)
            )
        })
        .unwrap()
}

#[test]
fn a_well_typed_changed_predecessor_does_not_prove_successor_cancellation() {
    let nat = native_name("Nat");
    let pred = declaration(NATIVE, &native_name("Nat.pred"));
    let span = pred.children[4].span;
    let mut source = NATIVE.to_owned();
    source.replace_range(
        span.start..span.end,
        &format!("(#pt-lambda ((x (#pt-use {nat} ()))) x)"),
    );
    let lemma = native_name("Nat.succ_sub_succ_eq_sub");
    let at = declaration(&source, &lemma).span.start;
    lim::check_types(&lim::parse_program(&source[..at]).unwrap()).unwrap();
    let why = lim::check_types(&lim::parse_program(&source).unwrap()).unwrap_err();
    assert!(why.contains(&lemma), "{why}");
    assert!(why.contains("type mismatch"), "{why}");
    assert!(!why.contains("resource limit"), "{why}");
}
