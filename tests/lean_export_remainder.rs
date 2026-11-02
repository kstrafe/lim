//! Genuine pinned natural remainders, including unbounded zero controls.
mod support;

use lim::lsp::json::{self, Json};
use std::{collections::BTreeMap, process::Command, time::Duration};

const FIXTURE: &str = include_str!("fixtures/lean_export_remainder/remainder.ndjson");
const MANIFEST: &str = include_str!("fixtures/lean_export_remainder/provenance.json");
const NATIVE: &str = include_str!("../theorems/lean_replay/remainder.lim");
const TARGETS: &[&str] = &[
    "RemainderSource.zero",
    "RemainderSource.hugeZero",
    "RemainderSource.below",
    "RemainderSource.equal",
    "RemainderSource.exact",
    "RemainderSource.withRemainder",
    "RemainderSource.large",
    "RemainderSource.largeEqualPowers",
    "RemainderSource.computed",
    "RemainderSource.computedEqualPowers",
    "RemainderSource.computedBelow",
    "RemainderSource.computedZero",
    "RemainderSource.zeroLeft",
    "RemainderSource.zeroDivisor",
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
fn actual_remainder_proofs_have_empty_assumption_inventories() {
    for target in TARGETS {
        let report = lim::check_lean_export(FIXTURE.as_bytes(), target).unwrap();
        assert_eq!(&report.target, target);
        assert!(report.axioms.is_empty());
        assert!(report.target_axioms.is_empty());
        assert!(report.foundations.is_empty());
    }
}

#[test]
fn exact_native_translation_independently_checks_all_remainder_targets() {
    let target = TARGETS.last().unwrap();
    let translated = lim::translate_lean_export(FIXTURE.as_bytes(), target).unwrap();
    assert_eq!(translated.source.as_bytes(), NATIVE.as_bytes());
    assert_eq!(translated.target, native_name(target));
    lim::check_types(&lim::parse_program(NATIVE).unwrap()).unwrap();
    let path =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("theorems/lean_replay/remainder.lim");
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

#[test]
fn independent_cli_checks_all_raw_and_native_remainder_targets() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let raw = root.join("tests/fixtures/lean_export_remainder/remainder.ndjson");
    let native = root.join("theorems/lean_replay/remainder.lim");
    let manifest = json::parse(MANIFEST).unwrap();
    let declarations = manifest.get("declarations").unwrap().array().unwrap().len();
    for target in TARGETS {
        let (status, stdout, stderr) = support::run(
            Command::new(env!("CARGO_BIN_EXE_lim"))
                .env("PATH", "")
                .args(["--check-lean-export", raw.to_str().unwrap(), target]),
            Duration::from_secs(60),
            1024 * 1024,
        )
        .unwrap();
        assert!(status.success(), "{}", String::from_utf8_lossy(&stderr));
        assert_eq!(
            String::from_utf8(stdout).unwrap(),
            format!("checked Lean export theorem {target} ({declarations} declarations)\n")
        );
        assert!(stderr.is_empty(), "{}", String::from_utf8_lossy(&stderr));

        let name = native_name(target);
        let (status, stdout, stderr) = support::run(
            Command::new(env!("CARGO_BIN_EXE_lim"))
                .env("PATH", "")
                .args(["--check-theorem", native.to_str().unwrap(), &name]),
            Duration::from_secs(60),
            1024 * 1024,
        )
        .unwrap();
        assert!(status.success(), "{}", String::from_utf8_lossy(&stderr));
        assert_eq!(
            String::from_utf8(stdout).unwrap(),
            format!("checked theorem {name}\n")
        );
        assert!(stderr.is_empty(), "{}", String::from_utf8_lossy(&stderr));
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
fn standard_remainder_and_worker_names_carry_no_computation_authority() {
    let mut data = rows();
    let mut remainders = 0;
    let mut cores = 0;
    for row in &mut data {
        let Some(name) = object(row).get_mut("str") else {
            continue;
        };
        let part = object(name).get_mut("str").unwrap();
        let replacement = match part.string().unwrap() {
            "mod" => {
                remainders += 1;
                "ordinaryRemainder".to_owned()
            }
            "modCore" => {
                cores += 1;
                "ordinaryRemainderCore".to_owned()
            }
            // Private workers can keep the dot in a single string component.
            "mod.go" => "ordinaryRemainderWorker".to_owned(),
            "modCore.go" => "ordinaryRemainderCoreWorker".to_owned(),
            "go" => "ordinaryWorker".to_owned(),
            part if part.starts_with("mod.") => {
                format!("ordinaryRemainderPiece{}", &part[4..])
            }
            part if part.starts_with("modCore.") => {
                format!("ordinaryRemainderCorePiece{}", &part[8..])
            }
            _ => continue,
        };
        *part = Json::String(replacement);
    }
    assert!(remainders > 0, "the actual Nat.mod name must be renamed");
    let renamed = render(&data);
    for target in TARGETS {
        let report = lim::check_lean_export(renamed.as_bytes(), target).unwrap();
        assert!(report.axioms.is_empty());
        assert!(report.target_axioms.is_empty());
        assert!(report.foundations.is_empty());
        assert!(report
            .declarations
            .iter()
            .any(|d| d.name == "Nat.ordinaryRemainder"));
        if cores > 0 {
            assert!(report
                .declarations
                .iter()
                .any(|d| d.name == "Nat.ordinaryRemainderCore"));
        }
    }
}

#[test]
fn corrupted_user_proofs_fail_after_valid_dependency_prefixes() {
    let report = lim::check_lean_export(FIXTURE.as_bytes(), TARGETS.last().unwrap()).unwrap();
    // Every target after the first has a genuine earlier user theorem for the
    // prefix control. Change only its proof reference, preserving its type.
    for target in TARGETS.iter().skip(1) {
        let ordinal = report
            .declarations
            .iter()
            .position(|d| d.name == *target)
            .unwrap();
        let declaration = &report.declarations[ordinal];
        let previous = report.declarations[..ordinal]
            .iter()
            .rev()
            .find(|d| d.kind == "theorem")
            .unwrap();
        let mut data = rows();
        let at = declaration.line - 1;
        lim::check_lean_export(render(&data[..at]).as_bytes(), &previous.name).unwrap();
        // Sort 0 is closed, including under the generic targets' binders.
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
fn a_well_typed_changed_remainder_body_does_not_prove_huge_zero() {
    let nat = native_name("Nat");
    let zero = native_name("Nat.zero");
    let remainder = declaration(NATIVE, &native_name("Nat.mod"));
    let span = remainder.children[4].span;
    let mut source = NATIVE.to_owned();
    // Constant zero still has type Nat -> Nat -> Nat. The first user theorem,
    // 0 % 0 = 0, remains true. The next, huge % 0 = huge, must fail.
    source.replace_range(
        span.start..span.end,
        &format!(
            "(#pt-lambda ((x (#pt-use {nat} ())) (y (#pt-use {nat} ()))) (#pt-use {zero} ()))"
        ),
    );
    let target = native_name("RemainderSource.hugeZero");
    let at = declaration(&source, &target).span.start;
    lim::check_types(&lim::parse_program(&source[..at]).unwrap()).unwrap();
    let why = lim::check_types(&lim::parse_program(&source).unwrap()).unwrap_err();
    assert!(why.contains(&target), "{why}");
    assert!(why.contains("type mismatch"), "{why}");
    assert!(!why.contains("resource limit"), "{why}");
    assert!(!why.contains("work limit"), "{why}");
}
