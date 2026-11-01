//! Integrity checks for the committed outputs of the real pinned producer.
//! Provenance remains audit data; every accepted theorem is replayed separately.
use super::*;

const MANIFEST: &str = include_str!("../../../tests/fixtures/lean_export/real-provenance.json");
const SOURCE: &[u8] = include_bytes!("../../../tests/fixtures/lean_export/Source.lean");
const CHECKS: &[u8] = include_bytes!("../../../tests/fixtures/lean_export/NestedChecks.lean");
const ORIGINS: &[u8] = include_bytes!("../../../scripts/lean-export-origins.lean");
const LEAN_LICENSE: &[u8] = include_bytes!("../../../tests/fixtures/lean_export/LEAN-LICENSE.txt");
const EXPORTER_LICENSE: &[u8] =
    include_bytes!("../../../tests/fixtures/lean_export/EXPORTER-LICENSE.txt");
const EXPORTS: [(&str, &[u8]); 5] = [
    (
        "real-identity.ndjson",
        include_bytes!("../../../tests/fixtures/lean_export/real-identity.ndjson"),
    ),
    (
        "real-inductives.ndjson",
        include_bytes!("../../../tests/fixtures/lean_export/real-inductives.ndjson"),
    ),
    (
        "real-projection.ndjson",
        include_bytes!("../../../tests/fixtures/lean_export/real-projection.ndjson"),
    ),
    (
        "real-mutual.ndjson",
        include_bytes!("../../../tests/fixtures/lean_export/real-mutual.ndjson"),
    ),
    (
        "real-nested.ndjson",
        include_bytes!("../../../tests/fixtures/lean_export/real-nested.ndjson"),
    ),
];

fn digest(bytes: &[u8]) -> String {
    let mut digest = hash::Sha256::new();
    digest.update(bytes);
    hash::hex(&digest.finish())
}
fn field<'a>(value: &'a Json, name: &str) -> &'a Json {
    value
        .get(name)
        .unwrap_or_else(|| panic!("missing manifest field {name}"))
}
fn text<'a>(value: &'a Json, name: &str) -> &'a str {
    field(value, name).string().unwrap()
}

#[test]
fn real_fixture_bytes_sources_origin_reader_and_licenses_match_the_manifest() {
    let manifest = crate::lsp::json::parse(MANIFEST).unwrap();
    assert_eq!(text(&manifest, "schema"), "lim-lean-fixtures-v1");
    assert_eq!(
        text(field(&manifest, "fixture_source"), "sha256"),
        digest(SOURCE)
    );
    assert_eq!(
        text(field(&manifest, "origin_reader"), "sha256"),
        digest(ORIGINS)
    );
    assert_eq!(
        text(field(&manifest, "producer_checks"), "sha256"),
        digest(CHECKS)
    );
    let projects = field(&manifest, "projects").array().unwrap();
    for (id, bytes) in [("lean4", LEAN_LICENSE), ("lean4export", EXPORTER_LICENSE)] {
        let project = projects
            .iter()
            .find(|project| text(project, "id") == id)
            .unwrap();
        assert_eq!(text(project, "license_sha256"), digest(bytes));
        assert_eq!(text(project, "license"), "Apache-2.0");
    }
    let fixtures = field(&manifest, "fixtures").array().unwrap();
    assert_eq!(fixtures.len(), EXPORTS.len());
    for (name, bytes) in EXPORTS {
        let entry = fixtures
            .iter()
            .find(|entry| text(entry, "file") == name)
            .unwrap();
        assert_eq!(text(entry, "sha256"), digest(bytes), "{name}");
        assert_eq!(field(entry, "bytes").integer(), Some(bytes.len() as i64));
    }
}

#[test]
fn every_fixture_declaration_keeps_its_original_source_hash_and_license_notice() {
    let manifest = crate::lsp::json::parse(MANIFEST).unwrap();
    let sources = field(&manifest, "upstream_sources").array().unwrap();
    assert!(!sources.is_empty());
    let revision = text(&manifest, "lean_revision");
    for source in sources {
        assert_eq!(text(source, "license"), "Apache-2.0");
        assert!(text(source, "notice").contains("Copyright"));
        assert!(text(source, "url").contains(revision));
        assert!(text(source, "url").ends_with(text(source, "source")));
    }
    for fixture in field(&manifest, "fixtures").array().unwrap() {
        for declaration in field(fixture, "declarations").array().unwrap() {
            match text(declaration, "project") {
                "lim-fixture" => {
                    assert_eq!(text(declaration, "source"), "Source.lean");
                    assert_eq!(text(declaration, "source_sha256"), digest(SOURCE));
                }
                "lean4" => {
                    let source = sources
                        .iter()
                        .find(|source| text(source, "source") == text(declaration, "source"))
                        .unwrap();
                    assert_eq!(text(declaration, "source_sha256"), text(source, "sha256"));
                }
                other => panic!("unrecorded source project {other}"),
            }
        }
    }
}
