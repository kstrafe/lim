//! Genuine pinned standard arithmetic, including its course-of-values model.
use lim::lsp::json::{self, Json};
use lim::{check_lean_export, translate_lean_export};
use std::collections::BTreeMap;

const FIXTURE: &str = include_str!("fixtures/lean_export_arithmetic/arithmetic.ndjson");
const NATIVE: &str = include_str!("../theorems/lean_replay/arithmetic.lim");
const TARGET: &str = "ArithmeticSource.nested";
const TARGETS: &[(&str, &str)] = &[
    (
        "ArithmeticSource.addition",
        "lean-26-ArithmeticSource-addition",
    ),
    (
        "ArithmeticSource.multiplication",
        "lean-30-ArithmeticSource-multiplication",
    ),
    (
        "ArithmeticSource.zeroProduct",
        "lean-31-ArithmeticSource-zeroProduct",
    ),
    (
        "ArithmeticSource.zeroRight",
        "lean-32-ArithmeticSource-zeroRight",
    ),
    (TARGET, "lean-33-ArithmeticSource-nested"),
];
fn rows() -> Vec<Json> {
    FIXTURE
        .lines()
        .map(|line| json::parse(line).unwrap())
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
fn rejected_source(source: &str) {
    let why = lim::check_types(&lim::parse_program(source).unwrap()).unwrap_err();
    assert!(why.contains("type mismatch"), "{why}");
    assert!(!why.contains("resource limit"), "{why}");
}

#[test]
fn actual_standard_add_and_mul_replay_with_empty_axiom_inventories() {
    for (original, _) in TARGETS {
        let report = check_lean_export(FIXTURE.as_bytes(), original).unwrap();
        assert_eq!(report.declarations.len(), 34);
        assert_eq!(&report.target, original);
        assert!(report.axioms.is_empty());
        assert!(report.target_axioms.is_empty());
        assert!(report.foundations.is_empty());
    }
}

#[test]
fn exact_native_translation_independently_checks_every_target() {
    let translated = translate_lean_export(FIXTURE.as_bytes(), TARGET).unwrap();
    assert_eq!(translated.source, NATIVE);
    assert_eq!(translated.target, TARGETS.last().unwrap().1);
    assert!(NATIVE.contains("Nat-brecOn-go"));
    assert!(NATIVE.len() < 40 * 1024);
    lim::check_types(&lim::parse_program(NATIVE).unwrap()).unwrap();
    for (_, name) in TARGETS {
        let checked = lim::check_theorem_details_from_path_with_config(
            NATIVE,
            &std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("theorems/lean_replay/arithmetic.lim"),
            &lim::CompileConfig::default(),
            name,
        )
        .unwrap();
        assert!(checked.foundations.is_empty());
    }
}

#[test]
fn changing_any_large_result_is_rejected_by_the_normal_checker() {
    for (before, after) in [
        (
            "340282366920938463647842048168863727616",
            "340282366920938463647842048168863727617",
        ),
        (
            "18446744073709551616000000000000000000000",
            "18446744073709551616000000000000000000001",
        ),
        (
            "18446744073709551616000000000000000000007",
            "18446744073709551616000000000000000000008",
        ),
    ] {
        let mut rows = rows();
        let row = rows
            .iter_mut()
            .find(|row| row.get("natVal").and_then(Json::string) == Some(before))
            .unwrap();
        object(row).insert("natVal".into(), Json::String(after.into()));
        let why = check_lean_export(render(&rows).as_bytes(), TARGET).unwrap_err();
        assert!(why.message.contains("type mismatch"), "{why}");
        assert!(!why.message.contains("resource limit"), "{why}");
    }
}

#[test]
fn names_and_provenance_comments_do_not_authorize_arithmetic() {
    let source = NATIVE
        .lines()
        .filter(|line| !line.starts_with(';'))
        .collect::<Vec<_>>()
        .join("\n")
        .replace("Nat-add", "unrelated-operation")
        .replace("Nat-mul", "other-operation")
        .replace("PProd", "Another-record")
        .replace("Nat", "Tally");
    lim::check_types(&lim::parse_program(&source).unwrap()).unwrap();
}

#[test]
fn a_well_typed_changed_standard_addition_body_is_not_the_original_operation() {
    let original =
        "(#pt-app (#pt-use lean-5-Nat-succ ()) (#pt-app (#pt-project lean-10-PProd 0 v5) v3))";
    assert!(NATIVE.contains(original));
    for changed in ["(#pt-app (#pt-project lean-10-PProd 0 v5) v3)",
        "(#pt-app (#pt-use lean-5-Nat-succ ()) (#pt-app (#pt-use lean-5-Nat-succ ()) (#pt-app (#pt-project lean-10-PProd 0 v5) v3)))"] {
        let source = NATIVE.replacen(original, changed, 1);
        let prefix = source.split("(#theorem lean-26-ArithmeticSource-addition").next().unwrap();
        lim::check_types(&lim::parse_program(prefix).unwrap()).unwrap();
        rejected_source(&source);
    }
}

#[test]
fn opaque_standard_names_do_not_expose_their_initializers() {
    let original = "(#math-definition lean-19-Nat-add";
    assert!(NATIVE.contains(original));
    let source = NATIVE.replacen(original, "(#math-opaque lean-19-Nat-add", 1);
    let prefix = source
        .split("(#theorem lean-26-ArithmeticSource-addition")
        .next()
        .unwrap();
    lim::check_types(&lim::parse_program(prefix).unwrap()).unwrap();
    rejected_source(&source);
}

#[test]
fn a_standard_name_does_not_bypass_the_provided_signature() {
    let mut rows = rows();
    let prop = rows
        .iter()
        .find(|row| row.get("sort").and_then(Json::integer) == Some(0))
        .unwrap()
        .get("ie")
        .unwrap()
        .clone();
    let name = rows
        .iter()
        .find(|row| {
            row.get("str")
                .and_then(|v| v.get("str"))
                .and_then(Json::string)
                == Some("add")
        })
        .unwrap()
        .get("in")
        .unwrap()
        .clone();
    let record = rows
        .iter_mut()
        .find_map(|row| {
            let record = object(row).get_mut("def")?;
            (record.get("name") == Some(&name)).then_some(record)
        })
        .unwrap();
    object(record).insert("type".into(), prop);
    let why = check_lean_export(render(&rows).as_bytes(), TARGET).unwrap_err();
    assert!(why.message.contains("type mismatch"), "{why}");
    assert!(!why.message.contains("resource limit"), "{why}");
}

#[test]
fn earlier_successful_arithmetic_does_not_skip_a_late_duplicate_record() {
    let mut rows = rows();
    rows.push(
        rows.iter()
            .find(|row| row.get("def").is_some())
            .unwrap()
            .clone(),
    );
    let why = check_lean_export(render(&rows).as_bytes(), "ArithmeticSource.addition").unwrap_err();
    assert!(why.message.contains("duplicate"), "{why}");
}
