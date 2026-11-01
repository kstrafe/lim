use std::io::Cursor;

use lim::lsp::json::{self, Json};

const PROVENANCE: &str = include_str!("fixtures/lean_export/real-provenance.json");

fn json(text: &str) -> Json {
    json::parse(text).expect("fixture JSON is valid")
}

fn fixture_entry<'a>(manifest: &'a Json, file: &str) -> &'a Json {
    manifest
        .get("fixtures")
        .and_then(Json::array)
        .unwrap()
        .iter()
        .find(|entry| entry.get("file").and_then(Json::string) == Some(file))
        .unwrap_or_else(|| panic!("manifest entry missing for {file}"))
}

fn assert_checked_fixture(source: &str, filename: &str, target: &str, count: usize) {
    let manifest = json(PROVENANCE);
    let entry = fixture_entry(&manifest, filename);
    assert_eq!(
        entry.get("expected").and_then(Json::string),
        Some("checked")
    );

    let report = lim::check_lean_export(Cursor::new(source.as_bytes()), target)
        .unwrap_or_else(|error| panic!("{filename} should replay: {error}"));
    assert_eq!(report.target, target);
    assert_eq!(report.declarations.len(), count);
    assert_eq!(
        report.input_sha256,
        entry.get("sha256").and_then(Json::string).unwrap()
    );

    let manifest_declarations = entry.get("declarations").and_then(Json::array).unwrap();
    assert_eq!(manifest_declarations.len(), report.declarations.len());
    let checked = report
        .declarations
        .iter()
        .map(|declaration| declaration.identity.as_str())
        .collect::<std::collections::BTreeSet<_>>();
    for (actual, expected) in report.declarations.iter().zip(manifest_declarations) {
        assert_eq!(
            actual.name,
            expected.get("name").and_then(Json::string).unwrap()
        );
        assert_eq!(
            actual.kind,
            expected.get("kind").and_then(Json::string).unwrap()
        );
        for dependency in &actual.dependencies {
            assert!(
                checked.contains(dependency.as_str()),
                "{} depends on unchecked member {dependency}",
                actual.name
            );
        }
    }

    let receipt = json(&report.render_json());
    assert_eq!(
        receipt.get("axioms").and_then(Json::array).unwrap().len(),
        0
    );
    assert_eq!(
        receipt.get("lean_version").and_then(Json::string),
        Some("4.33.1")
    );
    assert_eq!(
        receipt.get("lean_githash").and_then(Json::string),
        Some("819816b2e0a3bf405af45ae5c7af2491d8f5bee6")
    );
    assert_eq!(
        receipt.get("format_version").and_then(Json::string),
        Some("3.1.0")
    );

    for declaration in manifest_declarations {
        let project = declaration.get("project").and_then(Json::string).unwrap();
        let module = declaration.get("module").and_then(Json::string).unwrap();
        assert!(
            (project == "lim-fixture" && module == "Source")
                || (project == "lean4" && module.starts_with("Init.")),
            "unexpected provenance {project}/{module}"
        );
        assert!(declaration
            .get("source")
            .and_then(Json::string)
            .is_some_and(|source| !source.is_empty()));
        let source_hash = declaration
            .get("source_sha256")
            .and_then(Json::string)
            .unwrap();
        assert_eq!(source_hash.len(), 64);
        assert!(source_hash.bytes().all(|byte| byte.is_ascii_hexdigit()));
    }
}

#[test]
fn replays_pinned_real_lean_exports_with_provenance() {
    assert_checked_fixture(
        include_str!("fixtures/lean_export/real-identity.ndjson"),
        "real-identity.ndjson",
        "ReplaySource.identityProof",
        2,
    );
    assert_checked_fixture(
        include_str!("fixtures/lean_export/real-inductives.ndjson"),
        "real-inductives.ndjson",
        "ReplaySource.doubleTwo",
        10,
    );
    assert_checked_fixture(
        include_str!("fixtures/lean_export/real-projection.ndjson"),
        "real-projection.ndjson",
        "ReplaySource.projection",
        18,
    );
    assert_checked_fixture(
        include_str!("fixtures/lean_export/real-mutual.ndjson"),
        "real-mutual.ndjson",
        "ReplaySource.mutualDepth",
        35,
    );
}

#[test]
fn nested_inductive_fails_at_the_unsupported_inductive_record() {
    let source = include_str!("fixtures/lean_export/real-nested.ndjson");
    let error = lim::check_lean_export(Cursor::new(source.as_bytes()), "ReplaySource.nestedLeaf")
        .expect_err("nested inductive fixture is intentionally unsupported");
    assert_eq!(
        error.message,
        "nested inductive export replay is not implemented"
    );
    assert!(source
        .lines()
        .nth(error.line.saturating_sub(1))
        .is_some_and(|line| line.contains("\"inductive\"")));
    assert!(!error.message.to_lowercase().contains("resource limit"));
    assert!(!error.message.to_lowercase().contains("resource exhaustion"));
}

#[test]
fn rejects_a_semantically_corrupted_mutual_recursor() {
    let source = include_str!("fixtures/lean_export/real-mutual.ndjson");
    let mut changed = false;
    let mutated = source
        .lines()
        .map(|line| {
            if !changed && line.contains("\"inductive\"") && line.contains("\"numMotives\":2") {
                changed = true;
                line.replacen("\"numMotives\":2", "\"numMotives\":3", 1)
            } else {
                line.to_owned()
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
        + "\n";
    assert!(changed, "mutual recursor record was not found");
    // Keep the altered record syntactically valid JSON so the checker must
    // reject its recursor semantics rather than its transport or schema.
    for line in mutated.lines() {
        json(line);
    }
    let error = lim::check_lean_export(Cursor::new(mutated.as_bytes()), "ReplaySource.mutualDepth")
        .expect_err("corrupt mutual recursor must fail kernel replay");
    assert!(!error.message.to_lowercase().contains("resource limit"));
    assert!(!error.message.to_lowercase().contains("invalid export json"));
}
