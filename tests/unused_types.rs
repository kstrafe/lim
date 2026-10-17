mod support;

use std::{fs, process::Command, time::Duration};

fn warnings(source: &str) -> Vec<lim::Diagnostic> {
    let scratch = support::Scratch::new("unused-type-warnings");
    let (result, warnings) = lim::with_warnings(|| {
        lim::check_source_with_generated_sources(
            source,
            &scratch.path().join("main.lim"),
            &lim::CompileConfig::default(),
            &scratch.path().join("cache"),
            &scratch.path().join("generated"),
        )
    });
    result.unwrap_or_else(|error| panic!("{error:?}"));
    warnings
}

#[test]
fn unused_struct_enum_and_alias_warnings_have_exact_names_and_warning_severity() {
    let source = "(#struct UnusedStruct () ())\n(#enum UnusedEnum () (Empty))\n(#type UnusedAlias #u64)\n(#fn main () #u64 (#return 0u64))";
    let diagnostics = warnings(source);
    assert_eq!(diagnostics.len(), 3, "{diagnostics:?}");
    for (diagnostic, name) in diagnostics
        .iter()
        .zip(["UnusedStruct", "UnusedEnum", "UnusedAlias"])
    {
        assert_eq!(diagnostic.severity, lim::DiagnosticSeverity::Warning);
        assert_eq!(diagnostic.code_string(), "W8000");
        let span = diagnostic.span.unwrap();
        assert_eq!(&source[span.start..span.end], name);
        let rendered = lim::render_diagnostic(diagnostic, source, "main.lim");
        assert!(rendered.starts_with("warning[W8000]:"));
        assert!(rendered.contains(&"^".repeat(name.len())), "{rendered}");
        let json = lim::render_diagnostic_json(diagnostic, "main.lim");
        assert!(json.contains("\"severity\":\"warning\""), "{json}");
    }
}

#[test]
fn function_signatures_bodies_globals_and_transitive_types_count_as_use() {
    for source in [
        "(#type Alias Container) (#struct Container () ((element Element))) (#enum Element () (Empty)) (#fn consume (: value Alias) () (#forget value) (#return ()))",
        "(#enum Choice () (Only)) (#fn main () #u64 (#return (#match Only (#case Only 0u64))))",
        "(#struct Local () ()) (#fn main () #u64 (#let value Local (#struct-literal Local ())) (#forget value) (#return 0u64))",
        "(#struct Local () ()) (#fn main () #u64 (#return (#block (#let value Local (#struct-literal Local ())) (#forget value) 0u64)))",
        "(#type Counter #u64) (#let value Counter 1u64)",
        "(#struct Sized () ((value #u64))) (#fn main () #usize (#return (#size-of Sized)))",
    ] { assert!(warnings(source).is_empty(), "{source}"); }
}

#[test]
fn self_references_and_field_labels_do_not_hide_unused_types() {
    let source =
        "(#struct First () ((next (#ptr Second)))) (#struct Second () ((back (#ptr First))))";
    assert_eq!(warnings(source).len(), 2);
    let source = "(#struct Unused () ()) (#struct Used () ((Unused #u64))) (#fn main () #u64 (#let value Used (#struct-literal Used ((Unused 0u64)))) (#forget value) (#return 0u64))";
    let diagnostics = warnings(source);
    assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
    assert!(diagnostics[0].message.contains("'Unused'"));
}

#[test]
fn imported_generated_and_cfg_selected_types_keep_warning_origins() {
    let scratch = support::Scratch::new("unused-type-origins");
    let entry = scratch.path().join("main.lim");
    let imported = scratch.path().join("types.lim");
    fs::write(&imported, "(#struct Unused () ())").unwrap();
    let source = "(#import-external \"types.lim\" Ext-) (#gn emit () `((#type Generated #u64))) (@emit) (#cfg-if (#cfg-is #platform not-enabled) (#enum Hidden () (Absent)))";
    let mut previous = None;
    for _ in 0..2 {
        let (result, diagnostics) = lim::with_warnings(|| {
            lim::check_source_with_generated_sources(
                source,
                &entry,
                &lim::CompileConfig::default(),
                &scratch.path().join("cache"),
                &scratch.path().join("generated"),
            )
        });
        result.unwrap();
        assert_eq!(diagnostics.len(), 2, "{diagnostics:?}");
        assert_eq!(diagnostics[0].source_name.as_deref(), imported.to_str());
        assert!(diagnostics[0].message.contains("Ext-Unused"));
        assert!(!diagnostics[1].expansion_provenance.is_empty());
        if let Some(previous) = &previous {
            assert_eq!(&diagnostics, previous);
        }
        previous = Some(diagnostics);
    }
}

#[test]
fn cli_warnings_are_nonfatal_for_check_and_native_compilation() {
    let scratch = support::Scratch::new("unused-type-cli");
    let entry = scratch.path().join("main.lim");
    let binary = scratch.path().join("program");
    fs::write(
        &entry,
        "(#enum Unused () (Empty))\n(#fn main () #u64 (#return 42u64))",
    )
    .unwrap();
    for command in [
        vec!["--check".to_owned(), entry.display().to_string()],
        vec![
            entry.display().to_string(),
            "-o".into(),
            binary.display().to_string(),
        ],
    ] {
        let output = Command::new(env!("CARGO_BIN_EXE_lim"))
            .args(command)
            .arg("--diagnostic-format=json")
            .output()
            .unwrap();
        assert!(output.status.success(), "{:?}", output.stderr);
        assert!(output.stdout.is_empty());
        let text = String::from_utf8(output.stderr).unwrap();
        assert_eq!(text.lines().count(), 1, "{text}");
        assert!(text.contains("\"severity\":\"warning\""), "{text}");
        assert!(text.contains("W8000"), "{text}");
    }
    let (status, _, stderr) =
        support::run(&mut Command::new(binary), Duration::from_secs(5), 4096).unwrap();
    assert_eq!(status.code(), Some(42), "{stderr:?}");
}
