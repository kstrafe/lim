//! Genuine pinned quotient computations and hostile primitive-package records.
use lim::{
    check_lean_export,
    lsp::json::{self, Json},
    translate_lean_export,
};
use std::collections::{BTreeMap, BTreeSet};

const FIXTURE: &str = include_str!("fixtures/lean_export_quotient/quotient.ndjson");
const NATIVE: &str = include_str!("../theorems/lean_replay/quotient.lim");
const TARGET: &str = "QuotientSource.inductionReflexive";

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
fn array(value: &mut Json) -> &mut Vec<Json> {
    match value {
        Json::Array(value) => value,
        _ => panic!("fixture array"),
    }
}
fn field<'a>(value: &'a mut Json, name: &str) -> &'a mut Json {
    object(value).get_mut(name).unwrap()
}
fn number(value: usize) -> Json {
    Json::Number(value.to_string())
}
fn index(value: &Json) -> usize {
    value.integer().unwrap() as usize
}
fn quotient(rows: &mut [Json], ordinal: usize) -> &mut Json {
    rows.iter_mut()
        .filter_map(|row| object(row).get_mut("quot"))
        .nth(ordinal)
        .unwrap()
}
fn expression(rows: &[Json], id: usize) -> &Json {
    rows.iter()
        .find(|row| row.get("ie").and_then(Json::integer) == Some(id as i64))
        .unwrap()
}
fn expression_mut(rows: &mut [Json], id: usize) -> &mut Json {
    rows.iter_mut()
        .find(|row| row.get("ie").and_then(Json::integer) == Some(id as i64))
        .unwrap()
}
fn render(rows: &[Json]) -> String {
    rows.iter().map(Json::render).collect::<Vec<_>>().join("\n") + "\n"
}
fn rejects(rows: &[Json], message: &str) {
    let error = check_lean_export(render(rows).as_bytes(), TARGET).unwrap_err();
    assert!(
        error.message.contains(message),
        "expected {message}: {error}"
    );
    assert!(!error.message.contains("resource limit"), "{error}");
}
fn positions(rows: &[Json]) -> Vec<usize> {
    rows.iter()
        .enumerate()
        .filter_map(|(i, row)| row.get("quot").map(|_| i))
        .collect()
}

#[test]
fn genuine_lift_induction_and_overapplied_lift_replay_without_axioms() {
    for target in [
        "QuotientSource.liftComputes",
        "QuotientSource.extraArgumentComputes",
        TARGET,
    ] {
        let report = check_lean_export(FIXTURE.as_bytes(), target).unwrap();
        assert_eq!(report.target, target);
        assert_eq!(report.declarations.len(), 24);
        assert_eq!(report.foundations, ["quotient-computation-v1"]);
        let receipt = json::parse(&report.render_json()).unwrap();
        assert!(receipt.get("axioms").unwrap().array().unwrap().is_empty());
        assert_eq!(
            receipt.get("foundations").unwrap().array().unwrap(),
            &[Json::String("quotient-computation-v1".into())]
        );
        for (name, kind) in [
            ("Quot", "quotient-type"),
            ("Quot.mk", "quotient-ctor"),
            ("Quot.lift", "quotient-lift"),
            ("Quot.ind", "quotient-ind"),
        ] {
            assert!(report
                .declarations
                .iter()
                .any(|d| d.name == name && d.kind == kind));
        }
        let known: BTreeSet<_> = report
            .declarations
            .iter()
            .map(|d| d.identity.as_str())
            .collect();
        for declaration in &report.declarations {
            assert!(declaration
                .dependencies
                .iter()
                .all(|d| known.contains(d.as_str())));
        }
    }
}

#[test]
fn genuine_quotient_translation_reproduces_native_source_and_checks_normally() {
    let translated = translate_lean_export(FIXTURE.as_bytes(), TARGET).unwrap();
    assert_eq!(translated.source, NATIVE);
    assert_eq!(
        translated.target,
        "lean-23-QuotientSource-inductionReflexive"
    );
    assert!(NATIVE.contains("Checked primitive foundations: [\"quotient-computation-v1\"]"));
    for form in [
        "#pt-quot",
        "#pt-quot-make",
        "#pt-quot-lift",
        "#pt-quot-induct",
        "#pt-induct lean-0-Eq",
    ] {
        assert!(NATIVE.contains(form), "missing checked wrapper {form}");
    }
    let program = lim::parse_program(NATIVE).unwrap();
    lim::check_types(&program).unwrap();
    for target in [
        "lean-19-QuotientSource-liftComputes",
        "lean-22-QuotientSource-extraArgumentComputes",
        translated.target.as_str(),
    ] {
        lim::check_theorem_from_path_with_config(
            NATIVE,
            &std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("theorems/lean_replay/quotient.lim"),
            &lim::CompileConfig::default(),
            target,
        )
        .unwrap();
    }
}

#[test]
fn quotient_kinds_names_universes_and_exact_schema_are_checked() {
    for ordinal in 0..4 {
        let mut data = rows();
        *field(quotient(&mut data, ordinal), "kind") = Json::String("sound".into());
        rejects(&data, "pinned identities");
        let mut data = rows();
        *field(quotient(&mut data, ordinal), "name") = number(1); // Eq, already interned.
        rejects(&data, "pinned identities");
        let mut data = rows();
        array(field(quotient(&mut data, ordinal), "levelParams")).pop();
        rejects(&data, "universe parameter count");
        let mut data = rows();
        object(quotient(&mut data, ordinal)).insert("trusted".into(), Json::Bool(true));
        rejects(&data, "exactly these fields");
    }
}

#[test]
fn quoted_dotted_names_cannot_impersonate_primitive_quotient_identities() {
    let mut data = rows();
    let id = index(quotient(&mut data, 1).get("name").unwrap());
    let name = data
        .iter_mut()
        .find(|row| row.get("in").and_then(Json::integer) == Some(id as i64))
        .unwrap();
    let segment = field(name, "str");
    *field(segment, "pre") = number(0);
    *field(segment, "str") = Json::String("Quot.mk".into());
    rejects(&data, "pinned identities");
}

#[test]
fn quotient_package_order_duplicates_and_missing_first_member_fail() {
    let mut data = rows();
    let at = positions(&data);
    // Gather the package after its primitive tables so swapping its members
    // tests the package rule rather than a forward reference in the name table.
    let suffix = data.split_off(at[3] + 1);
    let mut package = Vec::new();
    data.retain(|row| {
        if row.get("quot").is_some() {
            package.push(row.clone());
            false
        } else {
            true
        }
    });
    let mut control = data.clone();
    control.extend(package.clone());
    control.extend(suffix.clone());
    check_lean_export(render(&control).as_bytes(), TARGET).unwrap();
    package.swap(0, 1);
    data.extend(package);
    data.extend(suffix);
    rejects(&data, "package order");
    let mut data = rows();
    let at = positions(&data);
    let duplicate = data[at[3]].clone();
    data.insert(at[3] + 1, duplicate);
    rejects(&data, "duplicate quotient package");
    let mut data = rows();
    data.remove(positions(&data)[0]);
    rejects(&data, "package order");
}

#[test]
fn unfinished_quotient_package_cannot_be_accepted_at_eof() {
    for ordinal in 0..3 {
        let mut data = rows();
        data.truncate(positions(&data)[ordinal] + 1);
        rejects(&data, "incomplete checked quotient package");
    }
}

#[test]
fn ordinary_declaration_cannot_interleave_quotient_package_members() {
    let mut data = rows();
    let declaration = data
        .iter()
        .find(|row| row.get("def").is_some())
        .unwrap()
        .clone();
    data.insert(positions(&data)[0] + 1, declaration);
    rejects(&data, "must finish before other declarations");
}

#[test]
fn all_four_primitive_signatures_must_match_fixed_schemas() {
    for ordinal in 0..4 {
        let mut data = rows();
        // Prop is a checked sort, closed under every quotient universe scope,
        // but it is not any of the four fixed primitive signatures.
        let prop = data
            .iter()
            .find(|row| row.get("sort").and_then(Json::integer) == Some(0))
            .unwrap()
            .get("ie")
            .unwrap()
            .clone();
        *field(quotient(&mut data, ordinal), "type") = prop;
        rejects(&data, "signature differs");
    }
}

#[test]
fn a_vacuous_lift_respect_proof_cannot_replace_the_required_equality() {
    let mut data = rows();
    let mut id = index(quotient(&mut data, 2).get("type").unwrap());
    for _ in 0..4 {
        id = index(
            expression(&data, id)
                .get("forallE")
                .unwrap()
                .get("body")
                .unwrap(),
        );
    }
    id = index(
        expression(&data, id)
            .get("forallE")
            .unwrap()
            .get("type")
            .unwrap(),
    );
    for _ in 0..3 {
        id = index(
            expression(&data, id)
                .get("forallE")
                .unwrap()
                .get("body")
                .unwrap(),
        );
    }
    // Eq B (f left) (f right) -> Eq B (f left) (f left).
    let previous = index(expression(&data, id).get("app").unwrap().get("fn").unwrap());
    let left = expression(&data, previous)
        .get("app")
        .unwrap()
        .get("arg")
        .unwrap()
        .clone();
    *field(field(expression_mut(&mut data, id), "app"), "arg") = left;
    rejects(&data, "signature differs");
}

#[test]
fn quotient_induction_cannot_be_widened_from_propositions_to_data() {
    let mut data = rows();
    let mut id = index(quotient(&mut data, 3).get("type").unwrap());
    for _ in 0..2 {
        id = index(
            expression(&data, id)
                .get("forallE")
                .unwrap()
                .get("body")
                .unwrap(),
        );
    }
    id = index(
        expression(&data, id)
            .get("forallE")
            .unwrap()
            .get("type")
            .unwrap(),
    );
    let level_one = data
        .iter()
        .find(|row| row.get("succ").and_then(Json::integer) == Some(0))
        .unwrap()
        .get("il")
        .unwrap();
    let type_expr = data
        .iter()
        .find(|row| row.get("sort") == Some(level_one))
        .unwrap()
        .get("ie")
        .unwrap()
        .clone();
    *field(field(expression_mut(&mut data, id), "forallE"), "body") = type_expr;
    rejects(&data, "signature differs");
}

#[test]
fn an_impostor_equality_constructor_cannot_authorize_quotient_computation() {
    let mut data = rows();
    // Every constructor/reference shares the interned name: the resulting
    // inductive block is valid, but it declares Eq.fake instead of Eq.refl.
    let name = data
        .iter_mut()
        .find(|row| {
            row.get("str")
                .and_then(|s| s.get("str"))
                .and_then(Json::string)
                == Some("refl")
        })
        .unwrap();
    *field(field(name, "str"), "str") = Json::String("fake".into());
    rejects(&data, "standard checked Eq/refl shape");
}

// Insert a fresh expression before Quot while preserving every table reference.
fn shift_expression_ids(value: &mut Json, start: usize) {
    match value {
        Json::Object(fields) => {
            for (key, value) in fields {
                if matches!(
                    key.as_str(),
                    "ie" | "type" | "value" | "body" | "fn" | "arg" | "expr" | "e" | "rhs"
                ) {
                    if let Some(id) = value.integer() {
                        if id as usize >= start {
                            *value = number(id as usize + 1);
                        }
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
fn signature_let(valid: bool) -> Vec<Json> {
    let mut data = rows();
    let at = positions(&data)[0];
    let next = data[..at]
        .iter()
        .filter(|row| row.get("ie").is_some())
        .count();
    let original = quotient(&mut data, 0).get("type").unwrap().clone();
    let prop = data[..at]
        .iter()
        .find(|row| row.get("sort").and_then(Json::integer) == Some(0))
        .unwrap()
        .get("ie")
        .unwrap()
        .clone();
    let one = data[..at]
        .iter()
        .find(|row| row.get("succ").and_then(Json::integer) == Some(0))
        .unwrap()
        .get("il")
        .unwrap();
    let type_expr = data[..at]
        .iter()
        .find(|row| row.get("sort") == Some(one))
        .unwrap()
        .get("ie")
        .unwrap()
        .clone();
    for row in &mut data[at..] {
        shift_expression_ids(row, next);
    }
    *field(quotient(&mut data, 0), "type") = number(next);
    let wrapper = Json::Object(BTreeMap::from([
        ("ie".into(), number(next)),
        (
            "letE".into(),
            Json::Object(BTreeMap::from([
                ("name".into(), number(0)),
                ("type".into(), if valid { type_expr } else { prop.clone() }),
                ("value".into(), prop),
                ("body".into(), original),
                ("nondep".into(), Json::Bool(false)),
            ])),
        ),
    ]));
    data.insert(at, wrapper);
    data
}

#[test]
fn convertible_signature_lets_are_checked_before_zeta_erases_their_values() {
    // Positive control proves that the edit preserves reference ordering/scope.
    check_lean_export(render(&signature_let(true)).as_bytes(), TARGET).unwrap();
    rejects(&signature_let(false), "type mismatch");
}

#[test]
fn axioms_and_malformed_records_after_the_target_remain_unauthorized() {
    for name in ["Quot.sound", "Classical.choice", "propext"] {
        let mut data = rows();
        let id = data.iter().filter(|row| row.get("in").is_some()).count() + 1;
        data.push(
            json::parse(&format!(
                "{{\"in\":{id},\"str\":{{\"pre\":0,\"str\":\"{name}\"}}}}"
            ))
            .unwrap(),
        );
        data.push(
            json::parse(&format!(
                "{{\"axiom\":{{\"name\":{id},\"levelParams\":[],\"type\":3}}}}"
            ))
            .unwrap(),
        );
        rejects(&data, "axioms are not authorized");
    }
    let mut data = rows();
    data.push(json::parse("{\"unknown\":{}}").unwrap());
    rejects(&data, "unsupported export record");
}
