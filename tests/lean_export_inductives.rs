use lim::{
    check_lean_export,
    lsp::json::{self, Json},
};
use std::collections::BTreeMap;

const FIXTURE: &str = include_str!("fixtures/lean_export/inductives.ndjson");
const TARGET: &str = "Replay.doubleTwo";
fn rows() -> Vec<Json> {
    FIXTURE
        .lines()
        .map(|line| json::parse(line).unwrap())
        .collect()
}
fn object(value: &mut Json) -> &mut BTreeMap<String, Json> {
    if let Json::Object(value) = value {
        value
    } else {
        panic!("fixture object")
    }
}
fn array(value: &mut Json) -> &mut Vec<Json> {
    if let Json::Array(value) = value {
        value
    } else {
        panic!("fixture array")
    }
}
fn field<'a>(value: &'a mut Json, key: &str) -> &'a mut Json {
    object(value).get_mut(key).unwrap()
}
fn block(rows: &mut [Json], number: usize) -> &mut Json {
    rows.iter_mut()
        .filter_map(|row| object(row).get_mut("inductive"))
        .nth(number)
        .unwrap()
}
fn render(rows: &[Json]) -> String {
    rows.iter().map(Json::render).collect::<Vec<_>>().join("\n") + "\n"
}
fn number(value: usize) -> Json {
    Json::Number(value.to_string())
}
fn rejects(rows: &[Json], expected: &str) {
    let input = render(rows);
    let error = check_lean_export(input.as_bytes(), TARGET).unwrap_err();
    assert!(
        error.message.contains(expected),
        "expected {expected}: {error}"
    );
    assert!(!error.message.contains("resource limit"), "{error}");
}

#[test]
fn imported_nat_equality_and_dependent_record_computations_are_replayed() {
    for target in [TARGET, "Replay.transport", "Replay.projection"] {
        let report = check_lean_export(FIXTURE.as_bytes(), target).unwrap();
        assert_eq!(report.declarations.len(), 15);
        assert_eq!(report.target, target);
        assert!(report
            .declarations
            .iter()
            .any(|decl| decl.name == "Nat.rec" && decl.kind == "recursor"));
        assert!(report
            .declarations
            .iter()
            .any(|decl| decl.name == "Eq.rec" && decl.kind == "recursor"));
    }
}

#[test]
fn imported_mutual_recursors_adapt_fields_before_hypotheses_without_changing_types() {
    let source = include_str!("fixtures/lean_export/mutual.ndjson");
    let report = check_lean_export(source.as_bytes(), "Replay.mutualDepth").unwrap();
    assert_eq!(report.declarations.len(), 25);
    for name in ["Tree.rec", "Forest.rec"] {
        assert!(report
            .declarations
            .iter()
            .any(|decl| decl.name == name && decl.kind == "recursor"));
    }
}

#[test]
fn redundant_export_flags_never_supply_a_typing_or_computation_rule() {
    let mut data = rows();
    *field(&mut array(field(block(&mut data, 0), "types"))[0], "isRec") = Json::Bool(false);
    *field(
        &mut array(field(block(&mut data, 1), "types"))[0],
        "isReflexive",
    ) = Json::Bool(true);
    check_lean_export(render(&data).as_bytes(), TARGET).unwrap();
    // The K flag is checked against the constructor shape, not installed.
    *field(&mut array(field(block(&mut data, 0), "recs"))[0], "k") = Json::Bool(true);
    rejects(&data, "K flag");
}

#[test]
fn forged_constructor_and_recursor_metadata_are_rejected() {
    let mut data = rows();
    *field(
        &mut array(field(block(&mut data, 0), "ctors"))[1],
        "numFields",
    ) = number(0);
    rejects(&data, "constructor return");
    let mut data = rows();
    array(field(block(&mut data, 0), "ctors")).swap(0, 1);
    rejects(&data, "every constructor");
    let mut data = rows();
    array(field(
        &mut array(field(block(&mut data, 0), "recs"))[0],
        "rules",
    ))
    .pop();
    rejects(&data, "every constructor");
    let mut data = rows();
    *field(
        &mut array(field(block(&mut data, 0), "recs"))[0],
        "numMotives",
    ) = number(2);
    rejects(&data, "telescope counts");
    let mut data = rows();
    *field(
        &mut array(field(block(&mut data, 0), "types"))[0],
        "numNested",
    ) = number(1);
    rejects(&data, "nested count");
}

#[test]
fn invalid_recursor_rhs_cannot_replace_a_checked_reduction_rule() {
    let mut data = rows();
    let mut expr = field(
        &mut array(field(
            &mut array(field(block(&mut data, 0), "recs"))[0],
            "rules",
        ))[1],
        "rhs",
    )
    .integer()
    .unwrap() as usize;
    loop {
        let node = data
            .iter()
            .find(|node| node.get("ie").and_then(Json::integer) == Some(expr as i64))
            .unwrap();
        if let Some(body) = node
            .get("lam")
            .and_then(|lam| lam.get("body"))
            .and_then(Json::integer)
        {
            expr = body as usize;
        } else {
            break;
        }
    }
    let node = data
        .iter_mut()
        .find(|node| node.get("ie").and_then(Json::integer) == Some(expr as i64))
        .unwrap();
    *node = Json::Object(BTreeMap::from([
        ("bvar".into(), number(2)),
        ("ie".into(), number(expr)),
    ]));
    // The supplied rule now returns the zero case at a successor index.
    rejects(&data, "kernel type mismatch");
}

#[test]
fn peeling_a_constructor_telescope_cannot_erase_an_ill_typed_let() {
    let mut data = rows();
    let at = data
        .iter()
        .enumerate()
        .filter(|(_, node)| node.get("inductive").is_some())
        .nth(2)
        .unwrap()
        .0;
    let nat_name = data
        .iter()
        .find_map(|node| {
            node.get("inductive")
                .and_then(|block| block.get("types"))
                .and_then(Json::array)
                .map(|types| types[0].get("name").unwrap().clone())
        })
        .unwrap();
    let nat_expr = data[..at]
        .iter()
        .find(|node| node.get("const").and_then(|c| c.get("name")) == Some(&nat_name))
        .unwrap()
        .get("ie")
        .unwrap()
        .clone();
    let type_expr = data[1..at]
        .iter()
        .find(|node| node.get("sort").is_some())
        .unwrap()
        .get("ie")
        .unwrap()
        .clone();
    let original = field(&mut array(field(block(&mut data, 2), "ctors"))[0], "type").clone();
    let next = data[..at]
        .iter()
        .filter(|node| node.get("ie").is_some())
        .count();
    *field(&mut array(field(block(&mut data, 2), "ctors"))[0], "type") = number(next);
    data.truncate(at + 1);
    let wrapper = Json::Object(BTreeMap::from([
        (
            "letE".into(),
            Json::Object(BTreeMap::from([
                ("name".into(), number(0)),
                ("type".into(), nat_expr),
                ("value".into(), type_expr),
                ("body".into(), original),
                ("nondep".into(), Json::Bool(false)),
            ])),
        ),
        ("ie".into(), number(next)),
    ]));
    data.insert(at, wrapper);
    rejects(&data, "kernel type mismatch");
}

#[test]
fn ordinary_literals_cannot_rebind_the_standard_nat_by_its_printed_name() {
    let mut data = rows();
    let nat = block(&mut data, 0);
    // Renaming the zero constructor makes it a different family signature.
    let name = field(&mut array(field(nat, "ctors"))[0], "name")
        .integer()
        .unwrap();
    let node = data
        .iter_mut()
        .find(|node| node.get("in").and_then(Json::integer) == Some(name))
        .unwrap();
    *field(field(node, "str"), "str") = Json::String("notZero".into());
    // Compact literals retain the nominal family reference. The final audit
    // must still reject a family whose standard constructor was renamed.
    rejects(&data, "standard checked Nat signature");
}

#[test]
fn export_record_hashes_include_primitive_tables_and_prior_declarations() {
    let original = check_lean_export(FIXTURE.as_bytes(), TARGET).unwrap();
    let changed = FIXTURE.replacen(
        "\"binderInfo\":\"default\"",
        "\"binderInfo\":\"implicit\"",
        1,
    );
    let report = check_lean_export(changed.as_bytes(), TARGET).unwrap();
    assert_ne!(original.input_sha256, report.input_sha256);
    assert_eq!(original.declarations.len(), report.declarations.len());
    for (original, changed) in original.declarations.iter().zip(&report.declarations) {
        assert_eq!(original.identity, changed.identity);
        assert_ne!(original.sha256, changed.sha256);
    }
}
