//! Genuine Unicode string proofs and hostile literal-helper contracts.
use lim::{
    check_lean_export_with_budget,
    lsp::json::{self, Json},
    translate_lean_export_with_budget, CompileConfig, LeanFoundationPolicy, ProofBudget,
};
use std::{collections::BTreeMap, path::Path};

const RAW: &str = include_str!("fixtures/lean_export_strings/strings.ndjson");
const NATIVE: &str = include_str!("../theorems/lean_replay/strings.lim");
const MANIFEST: &str = include_str!("fixtures/lean_export_strings/provenance.json");
const TARGETS: &[(&str, &str)] = &[
    (
        "StringLiteralProbe.empty",
        "lean-373-StringLiteralProbe-empty",
    ),
    (
        "StringLiteralProbe.ascii",
        "lean-374-StringLiteralProbe-ascii",
    ),
    (
        "StringLiteralProbe.unicode",
        "lean-375-StringLiteralProbe-unicode",
    ),
    ("StringLiteralProbe.nul", "lean-376-StringLiteralProbe-nul"),
    (
        "StringLiteralProbe.balanced",
        "lean-377-StringLiteralProbe-balanced",
    ),
];
fn budget() -> ProofBudget {
    ProofBudget::new(1_000_000, 128 << 20, 1 << 30).unwrap()
}
fn rows() -> Vec<Json> {
    RAW.lines().map(|row| json::parse(row).unwrap()).collect()
}
fn object(value: &mut Json) -> &mut BTreeMap<String, Json> {
    let Json::Object(fields) = value else {
        panic!("fixture object")
    };
    fields
}
fn number(value: usize) -> Json {
    Json::Number(value.to_string())
}
fn id(value: &Json) -> usize {
    value.integer().unwrap().try_into().unwrap()
}
fn render(rows: &[Json]) -> String {
    rows.iter().map(Json::render).collect::<Vec<_>>().join("\n") + "\n"
}
fn declaration(name: &str) -> Json {
    let manifest = json::parse(MANIFEST).unwrap();
    manifest
        .get("declarations")
        .unwrap()
        .array()
        .unwrap()
        .iter()
        .find(|item| item.get("name").and_then(Json::string) == Some(name))
        .unwrap()
        .clone()
}
fn check(source: &str, target: &str) -> Result<lim::LeanExportReport, lim::LeanExportError> {
    check_lean_export_with_budget(
        source.as_bytes(),
        target,
        LeanFoundationPolicy::Constructive,
        budget(),
    )
}
fn first_literal(rows: &[Json]) -> usize {
    rows.iter()
        .position(|row| row.get("strVal").is_some())
        .unwrap()
}

#[test]
fn genuine_raw_and_native_targets_have_exact_empty_assumption_inventories() {
    let mut config = CompileConfig::default();
    config.set_proof_budget(budget());
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("theorems/lean_replay/strings.lim");
    for (original, native) in TARGETS {
        let report = check(RAW, original).unwrap();
        assert_eq!(report.target, *original);
        assert_eq!(report.declarations.len(), 378);
        assert_eq!(report.budget, budget());
        assert!(
            report.axioms.is_empty()
                && report.target_axioms.is_empty()
                && report.foundations.is_empty()
        );
        let checked =
            lim::check_theorem_details_from_path_with_config(NATIVE, &path, &config, native)
                .unwrap();
        assert_eq!(checked.budget, budget());
        assert!(checked.foundations.is_empty());
    }
}

#[test]
fn native_translation_is_exact_and_uses_ordinary_balanced_lambdas() {
    let translated = translate_lean_export_with_budget(
        RAW.as_bytes(),
        TARGETS[4].0,
        LeanFoundationPolicy::Constructive,
        budget(),
    )
    .unwrap();
    assert!(
        translated.source == NATIVE,
        "native string translation changed"
    );
    assert_eq!(translated.target, TARGETS[4].1);
    let balanced = NATIVE
        .split("(#theorem lean-377-StringLiteralProbe-balanced")
        .nth(1)
        .unwrap();
    assert!(balanced.contains("#pt-lambda"));
    assert!(!NATIVE.contains("#pt-string"));
    let failure = check_lean_export_with_budget(
        RAW.as_bytes(),
        TARGETS[0].0,
        LeanFoundationPolicy::Constructive,
        ProofBudget::default(),
    )
    .unwrap_err();
    assert!(
        failure.message.contains("Char.ofNat._proof_2")
            && failure.message.contains("resource limit")
    );
}

#[test]
fn a_checked_same_named_data_value_cannot_impersonate_the_character_function() {
    let mut data = rows();
    let helper = declaration("Char.ofNat");
    let line = id(helper.get("line").unwrap()) - 1;
    let mut names = vec![String::new()];
    for row in &data[..=line] {
        if let Some(index) = row.get("in") {
            assert_eq!(id(index), names.len());
            let part = row.get("str").or_else(|| row.get("num")).unwrap();
            let prefix = &names[id(part.get("pre").unwrap())];
            let segment = part
                .get("str")
                .and_then(Json::string)
                .map(str::to_owned)
                .unwrap_or_else(|| format!("[{}]", part.get("i").unwrap().render()));
            names.push(if prefix.is_empty() {
                segment
            } else {
                format!("{prefix}.{segment}")
            });
        }
    }
    let nat = names.iter().position(|name| name == "Nat").unwrap();
    let nat_type = data[..line]
        .iter()
        .find(|row| {
            row.get("const").is_some_and(|value| {
                id(value.get("name").unwrap()) == nat
                    && value.get("us").unwrap().array().unwrap().is_empty()
            })
        })
        .map(|row| id(row.get("ie").unwrap()))
        .unwrap();
    let zero = data[..line]
        .iter()
        .find(|row| row.get("natVal").and_then(Json::string) == Some("0"))
        .map(|row| id(row.get("ie").unwrap()))
        .unwrap();
    let definition = object(object(&mut data[line]).get_mut("def").unwrap());
    definition.insert("type".into(), number(nat_type));
    definition.insert("value".into(), number(zero));

    // The replacement itself is a valid checked Nat definition. Only the
    // literal contract rejects its use as Char.ofNat at the next record.
    let manifest = json::parse(MANIFEST).unwrap();
    let previous = manifest
        .get("declarations")
        .unwrap()
        .array()
        .unwrap()
        .iter()
        .rev()
        .find(|item| {
            item.get("kind").and_then(Json::string) == Some("theorem")
                && id(item.get("line").unwrap()) < line + 1
        })
        .unwrap();
    check(
        &render(&data[..=line]),
        previous.get("identity").unwrap().string().unwrap(),
    )
    .unwrap();
    let failure = check(&render(&data), TARGETS[0].0).unwrap_err();
    assert_eq!(failure.line, first_literal(&data) + 1);
    assert!(
        failure.message.contains("invalid string literal helper"),
        "{}",
        failure.message
    );
    assert!(!failure.message.contains("resource limit"));
}

#[test]
fn helper_universe_arity_and_canonical_identity_are_checked_before_literals() {
    let original = rows();
    let helper_line = id(declaration("Char.ofNat").get("line").unwrap()) - 1;
    let name_id = id(original[helper_line]
        .get("def")
        .unwrap()
        .get("name")
        .unwrap());
    for rename in [false, true] {
        let mut data = original.clone();
        if rename {
            let name = data
                .iter_mut()
                .find(|row| row.get("in").is_some_and(|value| id(value) == name_id))
                .unwrap();
            let part = object(object(name).get_mut("str").unwrap());
            part.insert("str".into(), Json::String("renamedOfNat".into()));
        } else {
            let definition = object(object(&mut data[helper_line]).get_mut("def").unwrap());
            definition.insert("levelParams".into(), Json::Array(vec![number(name_id)]));
        }
        let failure = check(&render(&data), TARGETS[0].0).unwrap_err();
        assert_eq!(
            failure.line,
            first_literal(&data) + 1,
            "{}",
            failure.message
        );
        assert!(
            failure.message.contains("string literal"),
            "{}",
            failure.message
        );
        assert!(!failure.message.contains("resource limit"));
    }
}

#[test]
fn invalid_later_literal_and_evidence_cannot_hide_behind_an_earlier_target() {
    let original = rows();
    let ascii = id(declaration(TARGETS[1].0).get("line").unwrap()) - 1;
    let zero = original[..ascii]
        .iter()
        .find(|row| row.get("natVal").and_then(Json::string) == Some("0"))
        .map(|row| id(row.get("ie").unwrap()))
        .unwrap();
    let mut invalid_proof = original.clone();
    object(object(&mut invalid_proof[ascii]).get_mut("thm").unwrap())
        .insert("value".into(), number(zero));
    let failure = check(&render(&invalid_proof), TARGETS[0].0).unwrap_err();
    assert_eq!(failure.line, ascii + 1);
    assert!(
        failure.message.contains("type mismatch"),
        "{}",
        failure.message
    );
    let mut invalid_literal = original;
    let index = invalid_literal
        .iter()
        .position(|row| row.get("strVal").and_then(Json::string) == Some("A"))
        .unwrap();
    object(&mut invalid_literal[index]).insert("strVal".into(), Json::String("x".repeat(4097)));
    let failure = check(&render(&invalid_literal), TARGETS[0].0).unwrap_err();
    assert_eq!(failure.line, index + 1);
    assert!(failure.message.contains("string literal byte limit"));
}

#[test]
fn altered_literal_control_reports_a_completed_type_mismatch() {
    let mut data = rows();
    let literal = data
        .iter_mut()
        .find(|row| row.get("strVal").and_then(Json::string) == Some("A"))
        .unwrap();
    object(literal).insert("strVal".into(), Json::String("B".into()));
    let failure = check(&render(&data), TARGETS[0].0).unwrap_err();
    assert_eq!(
        failure.line,
        id(declaration(TARGETS[1].0).get("line").unwrap())
    );
    assert!(
        failure.message.contains("type mismatch"),
        "{}",
        failure.message
    );
    assert!(!failure.message.contains("resource limit"));
}

#[test]
fn altered_native_ascii_evidence_reports_a_type_mismatch_for_earlier_targets_too() {
    let marker = "(#theorem lean-374-StringLiteralProbe-ascii";
    let (prefix, remainder) = NATIVE.split_once(marker).unwrap();
    let literal = "(#pt-nat-literal lean-10-Nat \"65\")";
    assert!(remainder.contains(literal));
    let invalid = format!(
        "{prefix}{marker}{}",
        remainder.replacen(literal, "(#pt-nat-literal lean-10-Nat \"66\")", 1)
    );
    let mut config = CompileConfig::default();
    config.set_proof_budget(budget());
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("theorems/lean_replay/strings.lim");
    for (_, target) in &TARGETS[..2] {
        let failure =
            lim::check_theorem_details_from_path_with_config(&invalid, &path, &config, target)
                .unwrap_err();
        assert!(
            failure.message.contains("type mismatch"),
            "{}",
            failure.message
        );
        assert!(!failure.message.contains("resource limit"));
    }
}

#[test]
fn unused_expanded_literals_are_accounted_before_eager_or_compact_retention() {
    let mut data = rows();
    let next = data
        .iter()
        .filter_map(|row| row.get("ie"))
        .map(id)
        .max()
        .unwrap()
        + 1;
    let original_lines = data.len();
    for offset in 0..100 {
        data.push(Json::Object(
            [
                ("ie".into(), number(next + offset)),
                ("strVal".into(), Json::String("x".repeat(4096))),
            ]
            .into_iter()
            .collect(),
        ));
    }
    let source = render(&data);
    let compact = check(&source, TARGETS[0].0).unwrap_err();
    let eager = match translate_lean_export_with_budget(
        source.as_bytes(),
        TARGETS[0].0,
        LeanFoundationPolicy::Constructive,
        budget(),
    ) {
        Err(error) => error,
        Ok(_) => panic!("unused literals bypassed the eager source payload limit"),
    };
    assert_eq!(compact, eager);
    assert!(compact.line > original_lines);
    assert!(
        compact.message.contains("primitive payload limit"),
        "{}",
        compact.message
    );
}
