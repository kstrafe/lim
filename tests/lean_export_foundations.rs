//! Genuine pinned axiom records require explicit policy and checked adapters.
use lim::{
    check_lean_export, check_lean_export_with_policy,
    lsp::json::{self, Json},
    translate_lean_export_with_policy, LeanFoundationPolicy,
};
use std::collections::BTreeMap;

const FIXTURE: &str = include_str!("fixtures/lean_export_foundations/foundations.ndjson");
const NATIVE: &str = include_str!("../theorems/lean_replay/foundations.lim");
const TARGET: &str = "BasisProbe.quotientRelated";
const POLICY: LeanFoundationPolicy = LeanFoundationPolicy::Lean4;
const AXIOMS: &[&str] = &["Classical.choice", "Quot.sound", "propext"];
fn rows() -> Vec<Json> {
    FIXTURE
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
fn field<'a>(value: &'a mut Json, key: &str) -> &'a mut Json {
    object(value).get_mut(key).unwrap()
}
fn number(value: usize) -> Json {
    Json::Number(value.to_string())
}
fn axiom(data: &mut [Json], ordinal: usize) -> &mut Json {
    data.iter_mut()
        .filter_map(|row| object(row).get_mut("axiom"))
        .nth(ordinal)
        .unwrap()
}
fn render(data: &[Json]) -> String {
    data.iter().map(Json::render).collect::<Vec<_>>().join("\n") + "\n"
}
fn rejects(data: &[Json], expected: &str) {
    let why = check_lean_export_with_policy(render(data).as_bytes(), TARGET, POLICY).unwrap_err();
    assert!(why.message.contains(expected), "expected {expected}: {why}");
    assert!(!why.message.contains("resource limit"), "{why}");
}

#[test]
fn genuine_axioms_require_opt_in_and_have_target_specific_closures() {
    for (target, basis) in [
        ("BasisProbe.choiceReflexive", vec!["Classical.choice"]),
        ("BasisProbe.propositionEquality", vec!["propext"]),
        (TARGET, vec!["Quot.sound"]),
        ("BasisProbe.pick._proof_1", vec![]),
    ] {
        assert!(check_lean_export(FIXTURE.as_bytes(), target)
            .unwrap_err()
            .message
            .contains("not authorized"));
        let report = check_lean_export_with_policy(FIXTURE.as_bytes(), target, POLICY).unwrap();
        assert_eq!(report.declarations.len(), 34);
        assert_eq!(report.axioms, AXIOMS);
        assert_eq!(report.target_axioms, basis);
        assert_eq!(
            report
                .declarations
                .iter()
                .filter(|d| d.kind == "axiom")
                .count(),
            3
        );
    }
}

#[test]
fn genuine_translation_is_exact_and_every_native_target_has_the_same_basis() {
    let translated = translate_lean_export_with_policy(FIXTURE.as_bytes(), TARGET, POLICY).unwrap();
    assert!(
        translated.source == NATIVE,
        "committed native artifact differs"
    );
    assert_eq!(translated.target, "lean-33-BasisProbe-quotientRelated");
    assert!(NATIVE.contains("#pt-foundation-choice"));
    assert!(NATIVE.contains("#pt-foundation-propext"));
    assert!(NATIVE.contains("#pt-foundation-quot-sound"));
    assert!(NATIVE.contains("#pt-eq-elim"));
    assert!(NATIVE.contains("#math-opaque lean-10-Classical-choice"));
    assert!(NATIVE.contains("#math-opaque lean-23-propext"));
    assert!(NATIVE.contains("#math-opaque lean-32-Quot-sound"));
    for (name, basis) in [
        ("lean-19-BasisProbe-choiceReflexive", "Classical.choice"),
        ("lean-24-BasisProbe-propositionEquality", "propext"),
        (translated.target.as_str(), "Quot.sound"),
    ] {
        let checked = lim::check_theorem_details_from_path_with_config(
            NATIVE,
            &std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("theorems/lean_replay/foundations.lim"),
            &lim::CompileConfig::default(),
            name,
        )
        .unwrap();
        assert_eq!(checked.foundations, [basis]);
    }
}

#[test]
fn native_inventory_is_derived_from_terms_instead_of_comment_claims() {
    let source = NATIVE
        .lines()
        .filter(|line| !line.starts_with(';'))
        .collect::<Vec<_>>()
        .join("\n");
    let checked = lim::check_theorem_details_from_path_with_config(
        &source,
        &std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("theorems/lean_replay/foundations.lim"),
        &lim::CompileConfig::default(),
        "lean-33-BasisProbe-quotientRelated",
    )
    .unwrap();
    assert_eq!(checked.foundations, ["Quot.sound"]);
}

#[test]
fn fixed_axioms_cannot_be_selected_as_theorems() {
    for name in AXIOMS {
        let why = check_lean_export_with_policy(FIXTURE.as_bytes(), name, POLICY).unwrap_err();
        assert!(why.message.contains("not a theorem"), "{why}");
    }
}

#[test]
fn changed_names_unsafe_flags_extra_fields_and_universe_counts_are_rejected() {
    for ordinal in 0..3 {
        let mut data = rows();
        *field(axiom(&mut data, ordinal), "name") = number(1);
        rejects(&data, "only the three pinned");
        let mut data = rows();
        *field(axiom(&mut data, ordinal), "isUnsafe") = Json::Bool(true);
        rejects(&data, "unsafe axiom");
        let mut data = rows();
        object(axiom(&mut data, ordinal)).insert("value".into(), number(0));
        rejects(&data, "exactly these fields");
        let mut data = rows();
        *field(axiom(&mut data, ordinal), "levelParams") = if ordinal == 1 {
            Json::Array(vec![number(11)])
        } else {
            Json::Array(vec![])
        };
        rejects(&data, "universe parameter count");
    }
}

#[test]
fn all_provided_signatures_are_compared_to_fixed_schemas() {
    for ordinal in 0..3 {
        let mut data = rows();
        let prop = data
            .iter()
            .find(|row| row.get("sort").and_then(Json::integer) == Some(0))
            .unwrap()
            .get("ie")
            .unwrap()
            .clone();
        *field(axiom(&mut data, ordinal), "type") = prop;
        rejects(&data, "signature differs");
    }
}

#[test]
fn weakening_any_axiom_evidence_to_an_arbitrary_proposition_is_rejected() {
    for (ordinal, binders) in [(0, 2), (1, 3), (2, 5)] {
        let mut data = rows();
        let mut id = axiom(&mut data, ordinal)
            .get("type")
            .and_then(Json::integer)
            .unwrap();
        for _ in 1..binders {
            id = data
                .iter()
                .find(|row| row.get("ie").and_then(Json::integer) == Some(id))
                .unwrap()
                .get("forallE")
                .unwrap()
                .get("body")
                .and_then(Json::integer)
                .unwrap();
        }
        let prop = data
            .iter()
            .find(|row| row.get("sort").and_then(Json::integer) == Some(0))
            .unwrap()
            .get("ie")
            .unwrap()
            .clone();
        let binder = data
            .iter_mut()
            .find(|row| row.get("ie").and_then(Json::integer) == Some(id))
            .unwrap();
        *field(field(binder, "forallE"), "type") = prop;
        rejects(&data, "signature differs");
    }
}

#[test]
fn same_spelling_in_one_name_component_does_not_authorize_a_hierarchical_axiom() {
    let mut data = rows();
    let id = axiom(&mut data, 0)
        .get("name")
        .and_then(Json::integer)
        .unwrap();
    let name = data
        .iter_mut()
        .find(|row| row.get("in").and_then(Json::integer) == Some(id))
        .unwrap();
    let segment = field(name, "str");
    *field(segment, "pre") = number(0);
    *field(segment, "str") = Json::String("Classical.choice".into());
    rejects(&data, "only the three pinned");
}

#[test]
fn standard_equality_nonempty_and_iff_constructor_shapes_are_required() {
    for (parent, label) in [("Nonempty", "intro"), ("Iff", "intro"), ("Eq", "refl")] {
        let mut data = rows();
        let parent_id = data
            .iter()
            .find(|row| {
                row.get("str").is_some_and(|s| {
                    s.get("pre").and_then(Json::integer) == Some(0)
                        && s.get("str").and_then(Json::string) == Some(parent)
                })
            })
            .unwrap()
            .get("in")
            .and_then(Json::integer)
            .unwrap();
        let name = data
            .iter_mut()
            .find(|row| {
                row.get("str").is_some_and(|s| {
                    s.get("pre").and_then(Json::integer) == Some(parent_id)
                        && s.get("str").and_then(Json::string) == Some(label)
                })
            })
            .unwrap();
        *field(field(name, "str"), "str") = Json::String("counterfeit".into());
        rejects(&data, "standard checked");
    }
}

#[test]
fn quotient_soundness_requires_the_complete_checked_computation_package() {
    let mut data = rows();
    data.retain(|row| row.get("quot").is_none());
    rejects(&data, "complete checked Quot package");
}

#[test]
fn late_unknown_axioms_and_duplicates_never_turn_into_additional_assumptions() {
    let mut data = rows();
    let next = data.iter().filter(|row| row.get("in").is_some()).count() + 1;
    data.push(
        json::parse(&format!(
            "{{\"in\":{next},\"str\":{{\"pre\":0,\"str\":\"untrusted\"}}}}"
        ))
        .unwrap(),
    );
    data.push(
        json::parse(&format!(
            "{{\"axiom\":{{\"name\":{next},\"levelParams\":[],\"type\":3,\"isUnsafe\":false}}}}"
        ))
        .unwrap(),
    );
    rejects(&data, "only the three pinned");
    let mut data = rows();
    let duplicate = Json::Object(BTreeMap::from([(
        "axiom".into(),
        axiom(&mut data, 0).clone(),
    )]));
    data.push(duplicate);
    rejects(&data, "duplicate");
}

#[test]
fn choosing_an_earlier_target_does_not_skip_later_bad_axioms() {
    let mut data = rows();
    *field(axiom(&mut data, 2), "isUnsafe") = Json::Bool(true);
    let why = check_lean_export_with_policy(
        render(&data).as_bytes(),
        "BasisProbe.choiceReflexive",
        POLICY,
    )
    .unwrap_err();
    assert!(why.message.contains("unsafe axiom"), "{why}");
}

fn shift_ids(value: &mut Json, start: usize) {
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
                shift_ids(value, start);
            }
        }
        Json::Array(items) => {
            for item in items {
                shift_ids(item, start);
            }
        }
        _ => {}
    }
}
fn signature_let(valid: bool) -> Vec<Json> {
    let mut data = rows();
    let at = data
        .iter()
        .position(|row| row.get("axiom").is_some())
        .unwrap();
    let next = data[..at]
        .iter()
        .filter(|row| row.get("ie").is_some())
        .count();
    let original = axiom(&mut data, 0).get("type").unwrap().clone();
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
    let ty = data[..at]
        .iter()
        .find(|row| row.get("sort") == Some(one))
        .unwrap()
        .get("ie")
        .unwrap()
        .clone();
    for row in &mut data[at..] {
        shift_ids(row, next);
    }
    *field(axiom(&mut data, 0), "type") = number(next);
    data.insert(
        at,
        Json::Object(BTreeMap::from([
            ("ie".into(), number(next)),
            (
                "letE".into(),
                Json::Object(BTreeMap::from([
                    ("name".into(), number(0)),
                    ("type".into(), if valid { ty } else { prop.clone() }),
                    ("value".into(), prop),
                    ("body".into(), original),
                    ("nondep".into(), Json::Bool(false)),
                ])),
            ),
        ])),
    );
    data
}

#[test]
fn erased_signature_values_are_checked_before_zeta_conversion() {
    check_lean_export_with_policy(render(&signature_let(true)).as_bytes(), TARGET, POLICY).unwrap();
    rejects(&signature_let(false), "type mismatch");
}
