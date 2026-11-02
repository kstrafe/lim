//! Whole-reader coverage for names that genuinely exceed the spill threshold.
//! These extend a small protocol fixture, not the upstream FLT proof corpus.
use lim::{check_lean_export, translate_lean_export};
use std::fmt::Write;

const FIXTURE: &str = include_str!("fixtures/lean_export/identity.ndjson");
const COMPONENT_BYTES: usize = 512;

fn component(index: usize) -> String {
    let mut value = format!("entry{index}");
    value.extend(std::iter::repeat_n('x', COMPONENT_BYTES - value.len()));
    value
}
fn append_name(source: &mut String, id: usize, component: &str) {
    writeln!(
        source,
        r#"{{"in":{id},"str":{{"pre":1,"str":"{component}"}}}}"#
    )
    .unwrap();
}
fn source_with_names(count: usize) -> String {
    let mut source = FIXTURE.to_owned();
    for index in 0..count {
        append_name(&mut source, 5 + index, &component(index));
    }
    source
}
fn append_theorem(source: &mut String, name: usize) {
    writeln!(
        source,
        r#"{{"thm":{{"name":{name},"levelParams":[],"type":12,"value":19,"all":[{name}]}}}}"#
    )
    .unwrap();
}

#[test]
fn old_name_pages_resolve_when_a_later_theorem_and_native_translation_use_them() {
    let mut source = source_with_names(2048);
    let middle = 1024;
    let target = format!("Audit.{}", component(middle));
    append_theorem(&mut source, 5 + middle);
    let raw = check_lean_export(source.as_bytes(), &target).unwrap();
    let native = translate_lean_export(source.as_bytes(), &target).unwrap();
    assert_eq!(raw.render_json(), native.report.render_json());
    assert_eq!(raw.target, target);
    assert_eq!(raw.declarations.len(), 3);
    assert!(raw.axioms.is_empty());
    assert!(raw.target_axioms.is_empty());
    assert!(native.source.contains(&native.target));
}

#[test]
fn duplicate_keys_after_the_selected_theorem_are_rejected_after_real_paging() {
    let mut source = source_with_names(2048);
    append_name(&mut source, 5 + 2048, &component(512));
    let error = check_lean_export(source.as_bytes(), "Audit.identity.theorem").unwrap_err();
    assert_eq!(error.line, source.lines().count());
    assert!(
        error.message.contains("duplicate interned export name"),
        "{}",
        error.message
    );
}

#[test]
fn cumulative_name_payload_limit_is_enforced_on_both_sides_of_its_boundary() {
    // Independently count the fixture's four expanded key/display pairs.
    let fixture_payload = [
        ("$lean:s5:Audit", "Audit"),
        ("$lean:s5:Audits8:identity", "Audit.identity"),
        (
            "$lean:s5:Audits8:identitys7:theorem",
            "Audit.identity.theorem",
        ),
        ("$lean:s1:u", "u"),
    ]
    .iter()
    .map(|(key, display)| key.len() + display.len())
    .sum::<usize>();
    // Parent key + segment header + component, and display parent + dot.
    let per_name =
        "$lean:s5:Audit".len() + "s512:".len() + COMPONENT_BYTES + "Audit.".len() + COMPONENT_BYTES;
    let valid_count = ((16 << 20) - fixture_payload) / per_name;
    let mut source = source_with_names(valid_count);
    assert!(check_lean_export(source.as_bytes(), "Audit.identity.theorem").is_ok());
    append_name(&mut source, 5 + valid_count, &component(valid_count));
    let error = check_lean_export(source.as_bytes(), "Audit.identity.theorem").unwrap_err();
    assert_eq!(error.line, source.lines().count());
    assert!(
        error.message.contains("export name byte limit exceeded"),
        "{}",
        error.message
    );
}
