//! Genuine pinned natural division composition, checked from bodies without a name rule.
use lim::lsp::json::{self, Json};
use std::collections::BTreeMap;

const FIXTURE: &str =
    include_str!("fixtures/lean_export_division_composition/division-composition.ndjson");
const MANIFEST: &str = include_str!("fixtures/lean_export_division_composition/provenance.json");
const NATIVE: &str = include_str!("../theorems/lean_replay/division-composition.lim");
const TARGETS: &[&str] = &[
    "DivisionCompositionSource.small",
    "DivisionCompositionSource.dividend",
    "DivisionCompositionSource.divisor",
    "DivisionCompositionSource.both",
    "DivisionCompositionSource.equal",
    "DivisionCompositionSource.below",
    "DivisionCompositionSource.zero",
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
fn actual_division_proofs_have_empty_assumption_inventories() {
    for target in TARGETS {
        let report = lim::check_lean_export(FIXTURE.as_bytes(), target).unwrap();
        assert_eq!(&report.target, target);
        assert!(report.axioms.is_empty());
        assert!(report.target_axioms.is_empty());
        assert!(report.foundations.is_empty());
    }
}

#[test]
fn exact_native_translation_independently_checks_all_division_targets() {
    let target = TARGETS.last().unwrap();
    let translated = lim::translate_lean_export(FIXTURE.as_bytes(), target).unwrap();
    assert_eq!(translated.source.as_bytes(), NATIVE.as_bytes());
    assert_eq!(translated.target, native_name(target));
    lim::check_types(&lim::parse_program(NATIVE).unwrap()).unwrap();
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("theorems/lean_replay/division-composition.lim");
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
fn standard_division_and_worker_names_carry_no_computation_authority() {
    let mut data = rows();
    let mut divisions = 0;
    for row in &mut data {
        let Some(name) = object(row).get_mut("str") else {
            continue;
        };
        let part = object(name).get_mut("str").unwrap();
        let replacement = match part.string().unwrap() {
            "div" => {
                divisions += 1;
                "ordinaryQuotient".to_owned()
            }
            // A private worker can contain the dot inside a single string
            // component, rather than using separate "div" and "go" components.
            "div.go" => "ordinaryQuotientWorker".to_owned(),
            "go" => "ordinaryWorker".to_owned(),
            part if part.starts_with("div.") => {
                format!("ordinaryPiece{}", &part[4..])
            }
            _ => continue,
        };
        *part = Json::String(replacement);
    }
    assert!(divisions > 0, "the actual Nat.div name must be renamed");
    let renamed = render(&data);
    for target in TARGETS {
        let report = lim::check_lean_export(renamed.as_bytes(), target).unwrap();
        assert!(report.axioms.is_empty());
        assert!(report.target_axioms.is_empty());
        assert!(report.foundations.is_empty());
        assert!(report
            .declarations
            .iter()
            .any(|d| d.name == "Nat.ordinaryQuotient"));
    }
}

#[test]
fn corrupted_composition_proofs_fail_after_valid_standard_dependency_prefixes() {
    let report = lim::check_lean_export(FIXTURE.as_bytes(), TARGETS.last().unwrap()).unwrap();
    // Check a standard dependency prefix before replacing each user proof
    // reference, preserving the theorem type. Include the first target.
    for target in TARGETS {
        let ordinal = report
            .declarations
            .iter()
            .position(|d| d.name == *target)
            .unwrap();
        let declaration = &report.declarations[ordinal];
        let previous = report.declarations[..ordinal]
            .iter()
            .rev()
            .find(|d| d.kind == "theorem" && !d.name.starts_with("DivisionCompositionSource."))
            .unwrap();
        let mut data = rows();
        let at = declaration.line - 1;
        lim::check_lean_export(render(&data[..previous.line]).as_bytes(), &previous.name).unwrap();
        let invalid = data[..at]
            .iter()
            .find(|row| row.get("sort").and_then(Json::integer) == Some(0))
            .unwrap()
            .get("ie")
            .unwrap()
            .clone();
        object(object(&mut data[at]).get_mut("thm").unwrap()).insert("value".into(), invalid);
        let why =
            lim::check_lean_export(render(&data).as_bytes(), TARGETS.last().unwrap()).unwrap_err();
        assert_eq!(why.line, declaration.line);
        assert!(why.message.contains(*target), "{why}");
        assert!(why.message.contains("type mismatch"), "{why}");
        assert!(!why.message.contains("resource limit"), "{why}");
        assert!(!why.message.contains("work limit"), "{why}");
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
fn a_well_typed_changed_division_body_does_not_prove_computed_small() {
    let nat = native_name("Nat");
    let zero = native_name("Nat.zero");
    let div = declaration(NATIVE, &native_name("Nat.div"));
    let span = div.children[4].span;
    let mut source = NATIVE.to_owned();
    // Constant zero still has type Nat -> Nat -> Nat. The prefix contains
    // only standard dependencies; the first user theorem, 2^6 / 2^3 = 8,
    // must fail.
    source.replace_range(
        span.start..span.end,
        &format!(
            "(#pt-lambda ((x (#pt-use {nat} ())) (y (#pt-use {nat} ()))) (#pt-use {zero} ()))"
        ),
    );
    let target = native_name("DivisionCompositionSource.small");
    let at = declaration(&source, &target).span.start;
    lim::check_types(&lim::parse_program(&source[..at]).unwrap()).unwrap();
    let why = lim::check_types(&lim::parse_program(&source).unwrap()).unwrap_err();
    assert!(why.contains(&target), "{why}");
    assert!(why.contains("type mismatch"), "{why}");
    assert!(!why.contains("resource limit"), "{why}");
    assert!(!why.contains("work limit"), "{why}");
}
