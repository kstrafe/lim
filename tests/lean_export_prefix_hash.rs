use lim::check_lean_export;

const FIXTURE: &str = include_str!("fixtures/lean_export/identity.ndjson");
const TARGET: &str = "Audit.identity.theorem";

const DEFINITION_PREFIX_SHA256: &str =
    "623a885e24045bd70520481e7e1d013f945e3b163922f1773e47dddbf5ff491c";
const THEOREM_PREFIX_SHA256: &str =
    "ad05e4153b542ea6dcd88e4a92d0a8e42ad2d757bdbc19552e3229a979c974ec";
const FIXTURE_SHA256: &str = THEOREM_PREFIX_SHA256;

#[test]
fn declaration_prefix_hashes_ignore_trailing_primitive_records() {
    let report = check_lean_export(FIXTURE.as_bytes(), TARGET).unwrap();

    assert_eq!(report.declarations.len(), 2);
    assert_eq!(report.declarations[0].line, 27);
    assert_eq!(report.declarations[0].sha256, DEFINITION_PREFIX_SHA256);
    assert_eq!(report.declarations[1].line, 28);
    assert_eq!(report.declarations[1].sha256, THEOREM_PREFIX_SHA256);
    assert_eq!(report.input_sha256, FIXTURE_SHA256);

    let with_unused_primitive = format!("{FIXTURE}{{\"ie\":20,\"bvar\":0}}\n");
    let appended = check_lean_export(with_unused_primitive.as_bytes(), TARGET).unwrap();

    assert_eq!(
        appended.declarations[0].sha256,
        report.declarations[0].sha256
    );
    assert_eq!(
        appended.declarations[1].sha256,
        report.declarations[1].sha256
    );
    assert_eq!(
        appended.input_sha256,
        "07fd062f3c1575c7be24ae8c8d53c96c7cedbdf609eb59aa9ab3782c3fe761f5"
    );
    assert_ne!(appended.input_sha256, report.input_sha256);
}

#[test]
fn inserted_unused_name_changes_only_later_declaration_prefix() {
    const INSERTED_THEOREM_PREFIX_SHA256: &str =
        "79cc10296b2d226a2a0b5113d0c5456f0633a65474d0727c6df8ba49ee081347";

    let definition = "{\"def\":{\"name\":2,\"levelParams\":[4],\"type\":4,\"value\":7,\"hints\":\"abbrev\",\"safety\":\"safe\",\"all\":[2]}}\n";
    assert_eq!(FIXTURE.matches(definition).count(), 1);
    let with_name = FIXTURE.replacen(
        definition,
        &format!("{definition}{{\"str\":{{\"pre\":0,\"str\":\"PrefixProbe\"}},\"in\":5}}\n"),
        1,
    );
    let inserted = check_lean_export(with_name.as_bytes(), TARGET).unwrap();

    assert_eq!(inserted.declarations.len(), 2);
    assert_eq!(inserted.declarations[0].line, 27);
    assert_eq!(inserted.declarations[0].sha256, DEFINITION_PREFIX_SHA256);
    assert_eq!(inserted.declarations[1].line, 29);
    assert_eq!(
        inserted.declarations[1].sha256,
        INSERTED_THEOREM_PREFIX_SHA256
    );
    assert_eq!(inserted.input_sha256, INSERTED_THEOREM_PREFIX_SHA256);
}
