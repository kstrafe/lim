//! Whole-reader coverage of universe paging, scope and explicit instantiation.
//! These extend a protocol fixture, not the complete upstream proof corpus.
use lim::{check_lean_export, translate_lean_export};
use std::fmt::Write;

const FIXTURE: &str = include_str!("fixtures/lean_export/identity.ndjson");
const LEVEL_COUNT: usize = 4096;
const PARAMETER_NAME: usize = 5 + LEVEL_COUNT / 2;
const LATE_NAME: usize = 5 + LEVEL_COUNT;
const THEOREM_NAME: usize = LATE_NAME + 1;
const TARGET: &str = r#"Audit."late-theorem""#;

fn source() -> String {
    let mut source = FIXTURE.to_owned();
    for index in 0..LEVEL_COUNT {
        let parameter = format!("v{index:04}{}", "x".repeat(251));
        let name = 5 + index;
        let id = 2 + index;
        writeln!(
            source,
            r#"{{"in":{name},"str":{{"pre":0,"str":"{parameter}"}}}}"#
        )
        .unwrap();
        writeln!(source, r#"{{"il":{id},"param":{name}}}"#).unwrap();
    }
    writeln!(
        source,
        r#"{{"in":{LATE_NAME},"str":{{"pre":1,"str":"late"}}}}"#
    )
    .unwrap();
    // The middle page is cold when this fresh sort first materializes. Build
    // an ordinary polymorphic identity at that level, then instantiate it in
    // a closed proof. Existing fixture nodes 3/6 are its open Pi/lambda tails.
    let middle = 2 + LEVEL_COUNT / 2;
    writeln!(source, r#"{{"ie":20,"sort":{middle}}}"#).unwrap();
    for row in [
        r#"{"ie":21,"forallE":{"name":0,"type":20,"body":3,"binderInfo":"implicit"}}"#,
        r#"{"ie":22,"lam":{"name":0,"type":20,"body":6,"binderInfo":"implicit"}}"#,
    ] {
        writeln!(source, "{row}").unwrap();
    }
    writeln!(source, r#"{{"def":{{"name":{LATE_NAME},"levelParams":[{PARAMETER_NAME}],"type":21,"value":22,"hints":"abbrev","safety":"safe","all":[{LATE_NAME}]}}}}"#).unwrap();
    writeln!(
        source,
        r#"{{"ie":23,"const":{{"name":{LATE_NAME},"us":[0]}}}}"#
    )
    .unwrap();
    for row in [
        r#"{"ie":24,"app":{"fn":23,"arg":14}}"#,
        r#"{"ie":25,"app":{"fn":24,"arg":16}}"#,
        r#"{"ie":26,"lam":{"name":0,"type":9,"body":25,"binderInfo":"default"}}"#,
        r#"{"ie":27,"lam":{"name":0,"type":8,"body":26,"binderInfo":"implicit"}}"#,
    ] {
        writeln!(source, "{row}").unwrap();
    }
    writeln!(
        source,
        r#"{{"in":{THEOREM_NAME},"str":{{"pre":1,"str":"late-theorem"}}}}"#
    )
    .unwrap();
    writeln!(source, r#"{{"thm":{{"name":{THEOREM_NAME},"levelParams":[],"type":12,"value":27,"all":[{THEOREM_NAME}]}}}}"#).unwrap();
    source
}

#[test]
fn cold_universe_pages_support_checked_polymorphism_and_native_correspondence() {
    let source = source();
    let raw = check_lean_export(source.as_bytes(), TARGET).unwrap();
    let native = translate_lean_export(source.as_bytes(), TARGET).unwrap();
    assert_eq!(raw.render_json(), native.report.render_json());
    assert_eq!(raw.declarations.len(), 4);
    assert!(raw.axioms.is_empty());
    assert!(raw.target_axioms.is_empty());
    assert_eq!(raw.target, TARGET);
}

#[test]
fn cached_universe_values_do_not_authorize_missing_declaration_parameters() {
    let original = source();
    let changed = original.replace(
        &format!(r#""levelParams":[{PARAMETER_NAME}]"#),
        r#""levelParams":[]"#,
    );
    assert_ne!(changed, original);
    let line = changed
        .lines()
        .position(|line| line.starts_with(&format!(r#"{{"def":{{"name":{LATE_NAME},"#)))
        .unwrap()
        + 1;
    let raw = check_lean_export(changed.as_bytes(), TARGET).unwrap_err();
    let native = translate_lean_export(changed.as_bytes(), TARGET).unwrap_err();
    for error in [raw, native] {
        assert_eq!(error.line, line);
        assert!(
            error.message.contains("undeclared universe parameter"),
            "{}",
            error.message
        );
    }
}

#[test]
fn wrong_explicit_instantiation_is_rejected_after_real_paging() {
    let source = source().replace(
        &format!(r#""name":{LATE_NAME},"us":[0]"#),
        &format!(r#""name":{LATE_NAME},"us":[]"#),
    );
    let error = check_lean_export(source.as_bytes(), TARGET).unwrap_err();
    assert_eq!(error.line, source.lines().count());
    assert!(
        error.message.contains("explicit universe argument"),
        "{}",
        error.message
    );
}

#[test]
fn an_unused_forward_universe_after_the_target_still_rejects_the_whole_input() {
    let mut source = source();
    let id = LEVEL_COUNT + 2;
    let future = id + 1;
    writeln!(source, r#"{{"il":{id},"succ":{future}}}"#).unwrap();
    let error = check_lean_export(source.as_bytes(), TARGET).unwrap_err();
    assert_eq!(error.line, source.lines().count());
    assert!(
        error.message.contains("earlier record"),
        "{}",
        error.message
    );
}
