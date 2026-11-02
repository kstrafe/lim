//! Genuine pinned generic discrimination proofs and their native replays.
use lim::lsp::json::{self, Json};
use lim::{check_lean_export, translate_lean_export};
use std::collections::BTreeMap;

const FIXTURE: &str = include_str!("fixtures/lean_export_discrimination/discrimination.ndjson");
const PROVENANCE: &str = include_str!("fixtures/lean_export_discrimination/provenance.json");
const NATIVE: &str = include_str!("../theorems/lean_replay/discrimination.lim");
const TARGETS: &[&str] = &[
    "DiscriminationSource.zeroNotSuccessor",
    "DiscriminationSource.successorInjective",
    "DiscriminationSource.booleanDiscrimination",
    "DiscriminationSource.selfBooleanDiscrimination",
    "DiscriminationSource.mappedDiscrimination",
];

fn native_target(original: &str) -> String {
    let provenance = json::parse(PROVENANCE).unwrap();
    provenance
        .get("declarations")
        .and_then(Json::array)
        .unwrap()
        .iter()
        .find(|declaration| declaration.get("name").and_then(Json::string) == Some(original))
        .and_then(|declaration| declaration.get("native_name"))
        .and_then(Json::string)
        .unwrap_or_else(|| panic!("missing provenance mapping for {original}"))
        .to_owned()
}

#[test]
fn original_export_checks_all_five_generic_targets_without_foundations() {
    for target in TARGETS {
        let report = check_lean_export(FIXTURE.as_bytes(), target).unwrap();
        assert_eq!(report.target, *target);
        assert!(report.axioms.is_empty());
        assert!(report.target_axioms.is_empty());
        assert!(report.foundations.is_empty());
    }
}

#[test]
fn translated_native_artifact_checks_each_provenance_mapped_target() {
    let original = TARGETS.last().unwrap();
    let translated = translate_lean_export(FIXTURE.as_bytes(), original).unwrap();
    assert_eq!(translated.source, NATIVE);
    assert_eq!(translated.target, native_target(original));
    lim::check_types(&lim::parse_program(NATIVE).unwrap()).unwrap();
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("theorems/lean_replay/discrimination.lim");
    for target in TARGETS {
        let checked = lim::check_theorem_details_from_path_with_config(
            NATIVE,
            &path,
            &lim::CompileConfig::default(),
            &native_target(target),
        )
        .unwrap();
        assert!(checked.foundations.is_empty());
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
        panic!("expected fixture object");
    };
    fields
}

fn render(rows: &[Json]) -> String {
    rows.iter().map(Json::render).collect::<Vec<_>>().join("\n") + "\n"
}

#[test]
fn renaming_standard_comparison_and_private_helpers_does_not_authorize_reduction() {
    let mut data = rows();
    let mut renamed = 0;
    for row in &mut data {
        let Some(name) = object(row).get_mut("str") else {
            continue;
        };
        let part = object(name).get_mut("str").unwrap();
        let replacement = match part.string().unwrap() {
            "beq" => "ordinaryEqualityTest",
            "noConfusion_of_Nat" => "ordinaryEqualityBridge",
            "aux" => "ordinaryPrivateHelper",
            _ => continue,
        };
        *part = Json::String(replacement.into());
        renamed += 1;
    }
    assert_eq!(renamed, 4);
    let report = check_lean_export(render(&data).as_bytes(), TARGETS.last().unwrap()).unwrap();
    assert!(report.axioms.is_empty() && report.foundations.is_empty());
    assert!(report
        .declarations
        .iter()
        .any(|d| d.name == "Nat.ordinaryEqualityTest"));
}

#[test]
fn a_forged_generic_proof_fails_at_its_declaration_after_valid_dependencies() {
    let mut data = rows();
    let name = data
        .iter()
        .find(|row| {
            row.get("str")
                .and_then(|n| n.get("str"))
                .and_then(Json::string)
                == Some("mappedDiscrimination")
        })
        .unwrap()
        .get("in")
        .unwrap()
        .clone();
    let at = data
        .iter()
        .position(|row| row.get("thm").and_then(|t| t.get("name")) == Some(&name))
        .unwrap();
    let zero = data[..at]
        .iter()
        .find(|row| row.get("natVal").and_then(Json::string) == Some("0"))
        .unwrap()
        .get("ie")
        .unwrap()
        .clone();
    check_lean_export(render(&data[..at]).as_bytes(), TARGETS[3]).unwrap();
    object(object(&mut data[at]).get_mut("thm").unwrap()).insert("value".into(), zero);
    let why = check_lean_export(render(&data).as_bytes(), TARGETS.last().unwrap()).unwrap_err();
    assert!(
        why.message
            .contains("DiscriminationSource.mappedDiscrimination"),
        "{why}"
    );
    assert!(why.message.contains("type mismatch"), "{why}");
    assert!(!why.message.contains("resource limit"), "{why}");
    assert_eq!(why.line, at + 1);
}

#[test]
fn corrupt_private_helper_body_is_checked_before_any_public_bridge() {
    let report = check_lean_export(FIXTURE.as_bytes(), TARGETS.last().unwrap()).unwrap();
    let helper = report
        .declarations
        .iter()
        .find(|declaration| declaration.name.ends_with(".noConfusion_of_Nat.aux._f"))
        .unwrap();
    let mut data = rows();
    let at = helper.line - 1;
    let zero = data[..at]
        .iter()
        .find(|row| row.get("natVal").and_then(Json::string) == Some("0"))
        .unwrap()
        .get("ie")
        .unwrap()
        .clone();
    check_lean_export(render(&data[..at]).as_bytes(), TARGETS[1]).unwrap();
    object(object(&mut data[at]).get_mut("def").unwrap()).insert("value".into(), zero);
    let why = check_lean_export(render(&data).as_bytes(), TARGETS.last().unwrap()).unwrap_err();
    assert_eq!(why.line, helper.line);
    assert!(why.message.contains(&helper.name), "{why}");
    assert!(why.message.contains("type mismatch"), "{why}");
    assert!(!why.message.contains("resource limit"), "{why}");
}

#[test]
fn native_reflexivity_does_not_prove_distinct_naturals_equal() {
    let false_claim = format!(
        "{NATIVE}\n(#theorem false-claim\n\
         (#universes) (#parameters)\n\
         (#statement (#pt-eq (#pt-use lean-0-Nat ())\n\
          (#pt-nat-literal lean-0-Nat \"0\") (#pt-nat-literal lean-0-Nat \"1\")))\n\
         (#proof (#pt-refl (#pt-use lean-0-Nat ()) (#pt-nat-literal lean-0-Nat \"0\"))))\n"
    );
    let error = lim::check_types(&lim::parse_program(&false_claim).unwrap()).unwrap_err();
    assert!(error.contains("type mismatch"), "{error}");
    assert!(!error.contains("resource limit"), "{error}");
}
