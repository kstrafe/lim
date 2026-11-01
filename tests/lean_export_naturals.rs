//! Real pinned natural-literal exports, independently rechecked native output.
use lim::{
    check_lean_export,
    lsp::json::{self, Json},
    translate_lean_export,
};
use std::collections::BTreeMap;

const FIXTURE: &str = include_str!("fixtures/lean_export_naturals/naturals.ndjson");
const NATIVE: &str = include_str!("../theorems/lean_replay/naturals.lim");
const TARGET: &str = "NaturalSource.largerSuccessor";
const TARGETS: &[(&str, &str)] = &[
    ("NaturalSource.reflexive", "lean-14-NaturalSource-reflexive"),
    ("NaturalSource.successor", "lean-15-NaturalSource-successor"),
    (
        "NaturalSource.predecessorComputes",
        "lean-24-NaturalSource-predecessorComputes",
    ),
    (
        "NaturalSource.constructorDiscriminates",
        "lean-26-NaturalSource-constructorDiscriminates",
    ),
    (TARGET, "lean-28-NaturalSource-largerSuccessor"),
];
fn rows(source: &str) -> Vec<Json> {
    source
        .lines()
        .map(|row| json::parse(row).unwrap())
        .collect()
}
fn object(value: &mut Json) -> &mut BTreeMap<String, Json> {
    match value {
        Json::Object(value) => value,
        _ => panic!("fixture object"),
    }
}
fn render(rows: &[Json]) -> String {
    rows.iter().map(Json::render).collect::<Vec<_>>().join("\n") + "\n"
}
fn rejects(data: &[Json], message: &str) {
    let why = check_lean_export(render(data).as_bytes(), TARGET).unwrap_err();
    assert!(why.message.contains(message), "expected {message}: {why}");
    assert!(!why.message.contains("resource limit"), "{why}");
}

#[test]
fn genuine_large_literal_proofs_replay_without_truncation_or_axioms() {
    for (original, _) in TARGETS {
        let report = check_lean_export(FIXTURE.as_bytes(), original).unwrap();
        assert_eq!(report.declarations.len(), 29);
        assert_eq!(&report.target, original);
        assert!(report.foundations.is_empty());
        let receipt = json::parse(&report.render_json()).unwrap();
        assert!(receipt.get("axioms").unwrap().array().unwrap().is_empty());
    }
}

#[test]
fn translation_is_exact_compact_and_independently_checks_all_five_targets() {
    let translated = translate_lean_export(FIXTURE.as_bytes(), TARGET).unwrap();
    assert_eq!(translated.source, NATIVE);
    assert_eq!(translated.target, TARGETS.last().unwrap().1);
    assert!(NATIVE.contains("#pt-nat-literal lean-3-Nat \"184467440737095516160\""));
    assert!(NATIVE.len() < 24 * 1024);
    lim::check_types(&lim::parse_program(NATIVE).unwrap()).unwrap();
    for (_, native) in TARGETS {
        lim::check_theorem_from_path_with_config(
            NATIVE,
            &std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("theorems/lean_replay/naturals.lim"),
            &lim::CompileConfig::default(),
            native,
        )
        .unwrap();
    }
}

#[test]
fn corrupting_a_large_successor_result_is_rejected_by_the_kernel() {
    let mut data = rows(FIXTURE);
    let row = data
        .iter_mut()
        .find(|row| row.get("natVal").and_then(Json::string) == Some("184467440737095516161"))
        .unwrap();
    object(row).insert(
        "natVal".into(),
        Json::String("184467440737095516162".into()),
    );
    rejects(&data, "type mismatch");
}

#[test]
fn malformed_and_oversized_export_literals_are_not_accepted_as_abbreviations() {
    for (literal, expected) in [
        ("01".into(), "canonical unsigned decimal"),
        ("-1".into(), "canonical unsigned decimal"),
        ("9".repeat(4097), "digit limit"),
    ] {
        let mut data = rows(FIXTURE);
        let row = data
            .iter_mut()
            .find(|row| row.get("natVal").and_then(Json::string) == Some("184467440737095516160"))
            .unwrap();
        object(row).insert("natVal".into(), Json::String(literal));
        rejects(&data, expected);
    }
}

fn append_literal(data: &mut Vec<Json>, literal: &str) {
    let next = data.iter().filter(|row| row.get("ie").is_some()).count();
    data.push(Json::Object(BTreeMap::from([
        ("ie".into(), Json::Number(next.to_string())),
        ("natVal".into(), Json::String(literal.into())),
    ])));
}

#[test]
fn maximum_length_unused_literals_are_bounded_and_checked_after_the_target() {
    let mut data = rows(FIXTURE);
    append_literal(&mut data, &"9".repeat(4096));
    check_lean_export(render(&data).as_bytes(), TARGET).unwrap();
    append_literal(&mut data, "-1");
    rejects(&data, "canonical unsigned decimal");
}

#[test]
fn unused_large_literals_still_require_the_independently_checked_standard_nat() {
    let input = include_str!("fixtures/lean_export/identity.ndjson");
    let mut data = rows(input);
    append_literal(&mut data, "184467440737095516160");
    let why = check_lean_export(render(&data).as_bytes(), "Audit.identity.theorem").unwrap_err();
    assert!(why.message.contains("checked standard Nat"), "{why}");
}

#[test]
fn arbitrary_successor_names_cannot_rebind_the_export_standard_nat() {
    let mut data = rows(FIXTURE);
    let segment = data
        .iter_mut()
        .find_map(|row| {
            let segment = object(row).get_mut("str")?;
            (segment.get("str").and_then(Json::string) == Some("succ")).then_some(segment)
        })
        .unwrap();
    object(segment).insert("str".into(), Json::String("fake".into()));
    rejects(&data, "standard checked Nat signature");
}
