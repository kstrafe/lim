mod support;

use std::{fs, process::Command};

fn lim() -> Command {
    Command::new(env!("CARGO_BIN_EXE_lim"))
}

fn timing_stderr(output: &std::process::Output) -> String {
    String::from_utf8(output.stderr.clone()).unwrap()
}

#[test]
fn check_timings_are_opt_in_and_json_is_a_plain_object() {
    let scratch = support::Scratch::new("timings-check");
    let source = scratch.path().join("main.lim");
    fs::write(&source, "(#fn main () #u64 (#return 0u64))").unwrap();

    let default = lim().arg("--check").arg(&source).output().unwrap();
    assert!(default.status.success());
    assert!(default.stderr.is_empty());

    let timed = lim()
        .arg("--check")
        .arg(&source)
        .arg("--timings")
        .arg("--diagnostic-format=json")
        .output()
        .unwrap();
    assert!(timed.status.success());
    let stderr = timing_stderr(&timed);
    assert!(stderr.starts_with("{\"timings\":["), "{stderr}");
    assert!(stderr.ends_with("]}\n"), "{stderr}");
    for stage in [
        "input_read",
        "prepare_imports_parse_cfg",
        "expansion",
        "materialize_generated_sources",
        "semantic_validate",
        "total",
    ] {
        assert!(
            stderr.contains(&format!("\"stage\":\"{stage}\"")),
            "{stderr}"
        );
    }
}

#[test]
fn assembly_and_binary_commands_report_emission_and_native_stages() {
    let scratch = support::Scratch::new("timings-outputs");
    let source = scratch.path().join("main.lim");
    fs::write(&source, "(#fn main () #u64 (#return 0u64))").unwrap();

    let assembly = scratch.path().join("main.s");
    let emitted = lim()
        .arg("--emit-asm")
        .arg(&source)
        .arg(&assembly)
        .arg("--timings")
        .output()
        .unwrap();
    assert!(emitted.status.success(), "{}", timing_stderr(&emitted));
    assert!(assembly.is_file());
    let assembly_timings = timing_stderr(&emitted);
    assert!(assembly_timings.contains("native_emission"));
    assert!(assembly_timings.contains("output_write"));

    let binary = scratch.path().join("program");
    let compiled = lim()
        .arg(&source)
        .arg("-o")
        .arg(&binary)
        .arg("--timings")
        .output()
        .unwrap();
    assert!(compiled.status.success(), "{}", timing_stderr(&compiled));
    assert!(binary.is_file());
    let binary_timings = timing_stderr(&compiled);
    for stage in [
        "native_emission",
        "native_assembly",
        "native_link",
        "output_write",
    ] {
        assert!(binary_timings.contains(stage), "{binary_timings}");
    }
}

#[test]
fn failed_compile_reports_reached_stages_in_json_mode() {
    let scratch = support::Scratch::new("timings-failure");
    let source = scratch.path().join("bad.lim");
    fs::write(&source, "(#fn main (").unwrap();
    let output = lim()
        .arg("--check")
        .arg(&source)
        .arg("--timings")
        .arg("--diagnostic-format=json")
        .output()
        .unwrap();
    assert!(!output.status.success());
    let stderr = timing_stderr(&output);
    let lines: Vec<_> = stderr.lines().collect();
    assert_eq!(lines.len(), 2, "{stderr}");
    assert!(lines[0].starts_with("{\"schema_version\":"), "{stderr}");
    assert!(lines[1].starts_with("{\"timings\":["), "{stderr}");
    assert!(lines[1].contains("prepare_imports_parse_cfg"), "{stderr}");
    assert!(!lines[1].contains("semantic_validate"), "{stderr}");
}

#[test]
fn timings_are_rejected_for_non_compiler_commands() {
    let output = lim()
        .arg("--stack-usage")
        .arg("unused.lim")
        .arg("--timings")
        .output()
        .unwrap();
    assert!(!output.status.success());
    let stderr = timing_stderr(&output);
    assert!(stderr.contains("--timings is supported"), "{stderr}");
    assert!(!stderr.contains("timing total"), "{stderr}");
}
