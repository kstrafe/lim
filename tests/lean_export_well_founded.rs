//! Pinned generic equation for Lean's well-founded natural recursion.
mod support;
use lim::{
    check_lean_export, check_lean_export_with_policy,
    lsp::json::{self, Json},
    translate_lean_export_with_policy, LeanFoundationPolicy,
};
use std::{collections::BTreeMap, fs};

const TARGET: &str = "WellFoundedProbe.equation";
const POLICY: LeanFoundationPolicy = LeanFoundationPolicy::Lean4;

fn artifacts() -> (String, String) {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    (
        fs::read_to_string(
            root.join("tests/fixtures/lean_export_well_founded/well-founded.ndjson"),
        )
        .expect("generated raw fixture"),
        fs::read_to_string(root.join("theorems/lean_replay/well-founded.lim"))
            .expect("generated native fixture"),
    )
}

fn rows(raw: &str) -> Vec<Json> {
    raw.lines().map(|line| json::parse(line).unwrap()).collect()
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
fn pinned_corpus_requires_explicit_foundation_policy_and_maps_exactly() {
    let (raw, native) = artifacts();
    let default_error = check_lean_export(raw.as_bytes(), TARGET).unwrap_err();
    assert!(
        default_error.message.contains("not authorized"),
        "{default_error}"
    );
    let report = check_lean_export_with_policy(raw.as_bytes(), TARGET, POLICY).unwrap();
    assert_eq!(report.declarations.len(), 141);
    assert_eq!(report.axioms, ["Quot.sound"]);
    assert_eq!(report.target_axioms, ["Quot.sound"]);
    assert_eq!(report.foundations, ["quotient-computation-v1"]);
    let translated = translate_lean_export_with_policy(raw.as_bytes(), TARGET, POLICY).unwrap();
    assert_eq!(translated.source, native);
    let native_report = lim::check_theorem_details_from_path_with_config(
        &native,
        &std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("theorems/lean_replay/well-founded.lim"),
        &lim::CompileConfig::default(),
        &translated.target,
    )
    .unwrap();
    assert_eq!(native_report.foundations, ["Quot.sound"]);
}

#[test]
fn cli_checks_raw_and_native_without_external_path_tools() {
    use std::{process::Command, time::Duration};
    let (raw, native) = artifacts();
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let raw_path = root.join("tests/fixtures/lean_export_well_founded/well-founded.ndjson");
    let native_path = root.join("theorems/lean_replay/well-founded.lim");
    let manifest: Json = json::parse(
        &fs::read_to_string(root.join("tests/fixtures/lean_export_well_founded/provenance.json"))
            .expect("generated provenance"),
    )
    .unwrap();
    let native_target = manifest
        .get("native")
        .unwrap()
        .get("targets")
        .unwrap()
        .get(TARGET)
        .unwrap()
        .string()
        .unwrap();
    assert!(!raw.is_empty() && !native.is_empty());
    let mut command = Command::new(env!("CARGO_BIN_EXE_lim"));
    command
        .env("PATH", "")
        .args(["--check-lean-export", raw_path.to_str().unwrap(), TARGET]);
    let (status, stdout, _) = support::run(&mut command, Duration::from_secs(30), 65536).unwrap();
    assert!(!status.success());
    assert!(stdout.is_empty());
    let mut command = Command::new(env!("CARGO_BIN_EXE_lim"));
    command.env("PATH", "").args([
        "--check-lean-export",
        raw_path.to_str().unwrap(),
        TARGET,
        "--lean-foundations",
    ]);
    let (status, stdout, stderr) =
        support::run(&mut command, Duration::from_secs(30), 65536).unwrap();
    assert!(status.success(), "{}", String::from_utf8_lossy(&stderr));
    assert!(String::from_utf8(stdout)
        .unwrap()
        .contains("141 declarations"));
    let mut command = Command::new(env!("CARGO_BIN_EXE_lim"));
    command.env("PATH", "").args([
        "--check-theorem",
        native_path.to_str().unwrap(),
        native_target,
    ]);
    let (status, stdout, stderr) =
        support::run(&mut command, Duration::from_secs(30), 65536).unwrap();
    assert!(status.success(), "{}", String::from_utf8_lossy(&stderr));
    assert!(String::from_utf8(stdout)
        .unwrap()
        .contains("logical foundations: Quot.sound"));
}

#[test]
fn helper_names_are_not_authority_and_fixed_axiom_identity_is_checked() {
    let (raw, _) = artifacts();
    let mut data = rows(&raw);
    let mut count = 0;
    for row in &mut data {
        let Some(name) = object(row).get_mut("str") else {
            continue;
        };
        let part = object(name).get_mut("str").unwrap();
        let replacement = match part.string().unwrap() {
            "WellFounded" => "RenamedRecursion".to_owned(),
            "fix" => "ordinaryFix".to_owned(),
            "fix_eq" => "ordinaryFixEquation".to_owned(),
            "eager" => "ordinaryEager".to_owned(),
            "go" => "ordinaryWorker".to_owned(),
            part if part.starts_with("fix.") => format!("ordinaryFixPart{}", &part[4..]),
            part if part.starts_with("go.") => format!("ordinaryWorkerPart{}", &part[3..]),
            _ => continue,
        };
        *part = Json::String(replacement.into());
        count += 1;
    }
    assert!(count > 0);
    let renamed = render(&data);
    let report = check_lean_export_with_policy(renamed.as_bytes(), TARGET, POLICY).unwrap();
    assert_eq!(report.target_axioms, ["Quot.sound"]);

    let mut changed = rows(&raw);
    let row = changed
        .iter_mut()
        .find(|row| row.get("axiom").is_some())
        .unwrap();
    let axiom = object(row).get_mut("axiom").unwrap();
    object(axiom).insert("name".into(), Json::Number("0".into()));
    assert!(check_lean_export_with_policy(render(&changed).as_bytes(), TARGET, POLICY).is_err());
}

#[test]
fn corrupted_final_proof_is_rejected_after_the_valid_prefix() {
    let (raw, _) = artifacts();
    let original = check_lean_export_with_policy(raw.as_bytes(), TARGET, POLICY).unwrap();
    let mut data = rows(&raw);
    let target = original
        .declarations
        .iter()
        .find(|d| d.name == TARGET)
        .unwrap();
    let at = target.line - 1;
    let invalid = data[..at]
        .iter()
        .find_map(|row| {
            row.get("sort")
                .and_then(Json::integer)
                .map(|_| row.get("ie").unwrap().clone())
        })
        .unwrap();
    object(object(&mut data[at]).get_mut("thm").unwrap()).insert("value".into(), invalid);
    let error =
        check_lean_export_with_policy(render(&data).as_bytes(), TARGET, POLICY).unwrap_err();
    assert_eq!(error.line, target.line);
    assert!(error.message.contains("type mismatch"), "{error}");
}

#[test]
fn corrupted_native_proof_is_rejected_after_checked_dependencies() {
    let (_, native) = artifacts();
    let translated =
        translate_lean_export_with_policy(artifacts().0.as_bytes(), TARGET, POLICY).unwrap();
    let node = lim::parse(&native)
        .unwrap()
        .into_iter()
        .find(|node| {
            matches!(&node.expr, lim::Expr::List(items)
            if matches!(items.get(1), Some(lim::Expr::Symbol(name)) if name == &translated.target))
        })
        .unwrap();
    let proof_clause = node
        .children
        .iter()
        .find(|child| {
            matches!(&child.expr, lim::Expr::List(items)
            if matches!(items.first(), Some(lim::Expr::Symbol(keyword)) if keyword == "#proof"))
        })
        .unwrap();
    let proof = proof_clause.children[1].span;
    lim::check_types(&lim::parse_program(&native[..node.span.start]).unwrap()).unwrap();
    let mut changed = native;
    changed.replace_range(proof.start..proof.end, "#pt-prop");
    let why = lim::check_theorem_details_from_path_with_config(
        &changed,
        &std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("theorems/lean_replay/well-founded.lim"),
        &lim::CompileConfig::default(),
        &translated.target,
    )
    .unwrap_err();
    assert!(why.message.contains("type mismatch"), "{}", why.message);
    assert!(!why.message.contains("resource limit"), "{}", why.message);
}
