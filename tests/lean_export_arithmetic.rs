//! Genuine pinned standard arithmetic, including its course-of-values model.
use lim::lsp::json::{self, Json};
use lim::{check_lean_export, translate_lean_export};
use std::collections::BTreeMap;

const FIXTURE: &str = include_str!("fixtures/lean_export_arithmetic/arithmetic.ndjson");
const NATIVE: &str = include_str!("../theorems/lean_replay/arithmetic.lim");
const TARGET: &str = "ArithmeticSource.nestedSubtraction";
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
    ("ArithmeticSource.nested", "lean-33-ArithmeticSource-nested"),
    ("ArithmeticSource.power", "lean-39-ArithmeticSource-power"),
    (
        "ArithmeticSource.zeroBase",
        "lean-40-ArithmeticSource-zeroBase",
    ),
    (
        "ArithmeticSource.zeroExponent",
        "lean-41-ArithmeticSource-zeroExponent",
    ),
    (
        "ArithmeticSource.oneBase",
        "lean-42-ArithmeticSource-oneBase",
    ),
    (
        "ArithmeticSource.nestedPower",
        "lean-43-ArithmeticSource-nestedPower",
    ),
    (
        "ArithmeticSource.affineGrowth",
        "lean-45-ArithmeticSource-affineGrowth",
    ),
    (
        "ArithmeticSource.subtraction",
        "lean-49-ArithmeticSource-subtraction",
    ),
    (
        "ArithmeticSource.subtractToZero",
        "lean-50-ArithmeticSource-subtractToZero",
    ),
    (
        "ArithmeticSource.subtractSelf",
        "lean-51-ArithmeticSource-subtractSelf",
    ),
    (
        "ArithmeticSource.zeroMinus",
        "lean-52-ArithmeticSource-zeroMinus",
    ),
    (
        "ArithmeticSource.subtractZero",
        "lean-53-ArithmeticSource-subtractZero",
    ),
    (TARGET, "lean-54-ArithmeticSource-nestedSubtraction"),
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
fn actual_standard_arithmetic_replays_with_empty_axiom_inventories() {
    for (original, _) in TARGETS {
        let report = check_lean_export(FIXTURE.as_bytes(), original).unwrap();
        assert_eq!(report.declarations.len(), 55);
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
    assert!(NATIVE.len() < 96 * 1024);
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

fn shift_expression_ids(value: &mut Json, start: i64) {
    match value {
        Json::Object(fields) => {
            for (key, value) in fields {
                if matches!(
                    key.as_str(),
                    "ie" | "type" | "value" | "body" | "fn" | "arg" | "expr" | "rhs" | "struct"
                ) {
                    if let Some(id) = value.integer().filter(|id| *id >= start) {
                        *value = Json::Number((id + 2).to_string());
                    }
                }
                shift_expression_ids(value, start);
            }
        }
        Json::Array(items) => {
            for item in items {
                shift_expression_ids(item, start);
            }
        }
        _ => {}
    }
}

/// Copy only this theorem's Eq right endpoint. The 2^128 literal is also an
/// earlier addition input, so changing its shared row would test that earlier
/// theorem instead of reaching the power obligation.
fn with_expected_endpoint(target: &str, decimal: &str) -> (Vec<Json>, usize) {
    let mut data = rows();
    let name = data
        .iter()
        .find(|row| {
            row.get("str")
                .and_then(|v| v.get("str"))
                .and_then(Json::string)
                == Some(target)
        })
        .unwrap()
        .get("in")
        .unwrap()
        .clone();
    let at = data
        .iter()
        .position(|row| row.get("thm").and_then(|v| v.get("name")) == Some(&name))
        .unwrap();
    let next = data[..at]
        .iter()
        .filter(|row| row.get("ie").is_some())
        .count() as i64;
    let ty = data[at].get("thm").unwrap().get("type").unwrap();
    let root = data[..at]
        .iter()
        .find(|row| row.get("ie") == Some(ty))
        .unwrap();
    let function = root.get("app").unwrap().get("fn").unwrap().clone();
    for row in &mut data[at..] {
        shift_expression_ids(row, next);
    }
    object(object(&mut data[at]).get_mut("thm").unwrap())
        .insert("type".into(), Json::Number((next + 1).to_string()));
    data.insert(
        at,
        Json::Object(BTreeMap::from([
            ("ie".into(), Json::Number(next.to_string())),
            ("natVal".into(), Json::String(decimal.into())),
        ])),
    );
    data.insert(
        at + 1,
        Json::Object(BTreeMap::from([
            ("ie".into(), Json::Number((next + 1).to_string())),
            (
                "app".into(),
                Json::Object(BTreeMap::from([
                    ("fn".into(), function),
                    ("arg".into(), Json::Number(next.to_string())),
                ])),
            ),
        ])),
    );
    (data, at + 2)
}

#[test]
fn false_endpoints_are_rejected_at_the_actual_arithmetic_obligation() {
    // Positive control validates every shifted ID and the direct Nat endpoint.
    let (data, _) = with_expected_endpoint("power", "340282366920938463463374607431768211456");
    check_lean_export(render(&data).as_bytes(), TARGET).unwrap();
    for (target, wrong) in [
        ("power", "340282366920938463463374607431768211457"),
        ("zeroBase", "1"),
        ("oneBase", "0"),
        ("affineGrowth", "340282366920938463463374607431768211454"),
        ("subtraction", "340282366920938463444927863358058659841"),
        ("subtractToZero", "1"),
        ("subtractSelf", "1"),
        ("zeroMinus", "1"),
        (
            "nestedSubtraction",
            "340282366920938463444927863358058659848",
        ),
    ] {
        let (data, at) = with_expected_endpoint(target, wrong);
        check_lean_export(render(&data[..at]).as_bytes(), "ArithmeticSource.nested").unwrap();
        let why = check_lean_export(render(&data).as_bytes(), TARGET).unwrap_err();
        assert!(
            why.message.contains(&format!("ArithmeticSource.{target}")),
            "{why}"
        );
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
        .replace("Nat-pow", "different-operation")
        .replace("Nat-pred", "a-preceding-operation")
        .replace("Nat-sub", "a-decreasing-operation")
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
fn a_well_typed_changed_power_step_does_not_authorize_the_original_result() {
    let original = "(#pt-app (#pt-use lean-29-Nat-mul ()) (#pt-project lean-10-PProd 0 v4) v0)";
    assert!(NATIVE.contains(original));
    let changed = "(#pt-app (#pt-use lean-19-Nat-add ()) (#pt-project lean-10-PProd 0 v4) v0)";
    let source = NATIVE.replacen(original, changed, 1);
    let prefix = source
        .split("(#theorem lean-39-ArithmeticSource-power")
        .next()
        .unwrap();
    lim::check_types(&lim::parse_program(prefix).unwrap()).unwrap();
    let why = lim::check_types(&lim::parse_program(&source).unwrap()).unwrap_err();
    assert!(why.contains("lean-39-ArithmeticSource-power"), "{why}");
    assert!(why.contains("type mismatch"), "{why}");
    assert!(!why.contains("resource limit"), "{why}");
}

#[test]
fn a_well_typed_changed_subtraction_step_is_not_the_original_operation() {
    let original =
        "(#pt-app (#pt-use lean-46-Nat-pred ()) (#pt-app (#pt-project lean-10-PProd 0 v5) v3))";
    assert!(NATIVE.contains(original));
    let changed = "(#pt-app (#pt-project lean-10-PProd 0 v5) v3)";
    let source = NATIVE.replacen(original, changed, 1);
    let prefix = source
        .split("(#theorem lean-49-ArithmeticSource-subtraction")
        .next()
        .unwrap();
    lim::check_types(&lim::parse_program(prefix).unwrap()).unwrap();
    let why = lim::check_types(&lim::parse_program(&source).unwrap()).unwrap_err();
    assert!(
        why.contains("lean-49-ArithmeticSource-subtraction"),
        "{why}"
    );
    assert!(why.contains("type mismatch"), "{why}");
    assert!(!why.contains("resource limit"), "{why}");
}

#[test]
fn opaque_standard_names_do_not_expose_their_initializers() {
    for (function, theorem) in [
        ("lean-19-Nat-add", "lean-26-ArithmeticSource-addition"),
        ("lean-38-Nat-pow", "lean-39-ArithmeticSource-power"),
        ("lean-48-Nat-sub", "lean-49-ArithmeticSource-subtraction"),
    ] {
        let original = format!("(#math-definition {function}");
        assert!(NATIVE.contains(&original));
        let source = NATIVE.replacen(&original, &format!("(#math-opaque {function}"), 1);
        let prefix = source
            .split(&format!("(#theorem {theorem}"))
            .next()
            .unwrap();
        lim::check_types(&lim::parse_program(prefix).unwrap()).unwrap();
        rejected_source(&source);
    }
}

#[test]
fn a_standard_name_does_not_bypass_the_provided_signature() {
    for operation in ["add", "pow", "pred", "sub"] {
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
                    == Some(operation)
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
        assert!(why.message.contains(&format!("Nat.{operation}")), "{why}");
        assert!(why.message.contains("type mismatch"), "{why}");
        assert!(!why.message.contains("resource limit"), "{why}");
    }
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
