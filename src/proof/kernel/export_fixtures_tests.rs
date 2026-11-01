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
const EXPORTS: [(&str, &[u8]); 9] = [
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
    (
        "real-nested-poly.ndjson",
        include_bytes!("../../../tests/fixtures/lean_export/real-nested-poly.ndjson"),
    ),
    (
        "real-nested-indexed.ndjson",
        include_bytes!("../../../tests/fixtures/lean_export/real-nested-indexed.ndjson"),
    ),
    (
        "real-nested-deep.ndjson",
        include_bytes!("../../../tests/fixtures/lean_export/real-nested-deep.ndjson"),
    ),
    (
        "real-nested-sigma.ndjson",
        include_bytes!("../../../tests/fixtures/lean_export/real-nested-sigma.ndjson"),
    ),
];

fn digest(bytes: &[u8]) -> String {
    let mut digest = hash::Sha256::new();
    digest.update(bytes);
    hash::hex(&digest.finish())
}

#[test]
fn native_proof_artifacts_reproduce_the_checked_genuine_exports() {
    let manifest_bytes = include_bytes!("../../../theorems/lean_replay/manifest.json");
    let manifest = crate::lsp::json::parse(std::str::from_utf8(manifest_bytes).unwrap()).unwrap();
    assert_eq!(
        field(&manifest, "schema").string(),
        Some("lim-lean-native-translations-v1")
    );
    assert_eq!(
        field(&manifest, "provenance_sha256").string(),
        Some(digest(MANIFEST.as_bytes()).as_str())
    );
    let entries = field(&manifest, "translations").array().unwrap();
    assert_eq!(entries.len(), EXPORTS.len());
    for (input_name, input) in EXPORTS {
        let entry = entries
            .iter()
            .find(|entry| {
                field(entry, "input")
                    .string()
                    .unwrap()
                    .ends_with(input_name)
            })
            .unwrap();
        let native = std::fs::read(
            std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("theorems/lean_replay")
                .join(field(entry, "file").string().unwrap()),
        )
        .unwrap();
        assert_eq!(
            field(entry, "sha256").string(),
            Some(digest(&native).as_str())
        );
        assert_eq!(field(entry, "bytes").integer(), Some(native.len() as i64));
        let translated =
            translate_lean_export(input, field(entry, "original_target").string().unwrap())
                .unwrap();
        assert_eq!(native, translated.source.as_bytes());
        assert_eq!(
            field(entry, "native_target").string(),
            Some(translated.target.as_str())
        );
        assert_eq!(
            field(entry, "input_sha256").string(),
            Some(translated.report.input_sha256.as_str())
        );
        let mappings = field(entry, "declarations").array().unwrap();
        assert_eq!(mappings.len(), translated.report.declarations.len());
        let program = crate::parse_program(&translated.source).unwrap();
        for ((mapping, original), item) in mappings
            .iter()
            .zip(&translated.report.declarations)
            .zip(&program.items)
        {
            let crate::Item::Proof { name, .. } = item else {
                panic!("nonproof item in translated artifact")
            };
            assert_eq!(
                field(mapping, "identity").string(),
                Some(original.identity.as_str())
            );
            assert_eq!(
                field(mapping, "sha256").string(),
                Some(original.sha256.as_str())
            );
            assert_eq!(field(mapping, "native_name").string(), Some(name.as_str()));
        }
    }
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

#[test]
fn genuine_quotient_fixture_retains_checked_mapping_hashes_and_attribution() {
    let manifest = crate::lsp::json::parse(include_str!(
        "../../../tests/fixtures/lean_export_quotient/provenance.json"
    ))
    .unwrap();
    assert_eq!(text(&manifest, "schema"), "lim-lean-quotient-fixture-v1");
    assert_eq!(text(&manifest, "lean_revision"), LEAN_EXPORT_GITHASH);
    assert_eq!(text(&manifest, "exporter_revision"), EXPORTER_REVISION);
    assert!(field(&manifest, "axioms").array().unwrap().is_empty());
    assert_eq!(
        field(&manifest, "foundations").array().unwrap(),
        &[text_json("quotient-computation-v1")]
    );
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    for key in ["source", "producer", "origin_reader", "export", "native"] {
        let record = field(&manifest, key);
        let bytes = std::fs::read(root.join(text(record, "file"))).unwrap();
        assert_eq!(text(record, "sha256"), digest(&bytes), "{key}");
        if let Some(size) = record.get("bytes") {
            assert_eq!(size.integer(), Some(bytes.len() as i64));
        }
    }
    for license in field(&manifest, "licenses").array().unwrap() {
        let bytes = std::fs::read(root.join(text(license, "file"))).unwrap();
        assert_eq!(text(license, "license"), "Apache-2.0");
        assert_eq!(text(license, "sha256"), digest(&bytes));
    }
    let input = include_bytes!("../../../tests/fixtures/lean_export_quotient/quotient.ndjson");
    let report = check_lean_export(input.as_slice(), "QuotientSource.inductionReflexive").unwrap();
    assert_eq!(
        text(field(&manifest, "export"), "sha256"),
        report.input_sha256
    );
    let mappings = field(&manifest, "declarations").array().unwrap();
    assert_eq!(mappings.len(), report.declarations.len());
    let native =
        crate::parse_program(include_str!("../../../theorems/lean_replay/quotient.lim")).unwrap();
    assert_eq!(native.items.len(), mappings.len());
    let upstream = field(&manifest, "upstream_sources").array().unwrap();
    assert_eq!(upstream.len(), 1);
    assert_eq!(text(&upstream[0], "license"), "Apache-2.0");
    assert!(text(&upstream[0], "notice").contains("Copyright"));
    assert!(text(&upstream[0], "url").contains(LEAN_EXPORT_GITHASH));
    let mut target_count = 0;
    for ((mapping, declaration), item) in
        mappings.iter().zip(&report.declarations).zip(&native.items)
    {
        let crate::Item::Proof { name, .. } = item else {
            panic!("nonproof native item")
        };
        assert_eq!(text(mapping, "native_name"), name);
        assert_eq!(text(mapping, "identity"), declaration.identity);
        assert_eq!(text(mapping, "name"), declaration.name);
        assert_eq!(text(mapping, "kind"), declaration.kind);
        assert_eq!(text(mapping, "sha256"), declaration.sha256);
        assert_eq!(
            field(mapping, "line").integer(),
            Some(declaration.line as i64)
        );
        assert_eq!(
            field(mapping, "dependencies").array().unwrap(),
            &declaration
                .dependencies
                .iter()
                .map(|name| text_json(name))
                .collect::<Vec<_>>()
        );
        match text(mapping, "project") {
            "lim-fixture" => {
                assert_eq!(text(mapping, "module"), "Source");
                assert_eq!(
                    text(mapping, "source"),
                    text(field(&manifest, "source"), "file")
                );
                assert_eq!(
                    text(mapping, "source_sha256"),
                    text(field(&manifest, "source"), "sha256")
                );
            }
            "lean4" => {
                assert_eq!(text(mapping, "module"), "Init.Prelude");
                assert_eq!(text(mapping, "source"), text(&upstream[0], "source"));
                assert_eq!(text(mapping, "source_sha256"), text(&upstream[0], "sha256"));
            }
            other => panic!("unrecorded quotient source project {other}"),
        }
        if let Some(target) = field(field(&manifest, "native"), "targets").get(&declaration.name) {
            assert_eq!(target.string(), Some(name.as_str()));
            assert_eq!(declaration.kind, "theorem");
            target_count += 1;
        }
    }
    assert_eq!(target_count, 3);
}
