mod support;

use lim::{check_theorem_from_path_with_config, CompileConfig, DiagnosticCode};
use std::{
    fs,
    process::{Command, ExitStatus},
    time::Duration,
};

fn run(scratch: &support::Scratch, arguments: &[&str]) -> (ExitStatus, String, String) {
    let (status, stdout, stderr) = support::run(
        Command::new(env!("CARGO_BIN_EXE_lim"))
            .current_dir(scratch.path())
            // Checking a theorem must not require a linker or an external prover.
            .env("PATH", "")
            .args(arguments),
        Duration::from_secs(20),
        1024 * 1024,
    )
    .unwrap();
    (
        status,
        String::from_utf8(stdout).unwrap(),
        String::from_utf8(stderr).unwrap(),
    )
}

fn write(scratch: &support::Scratch, relative: &str, source: &str) {
    let path = scratch.path().join(relative);
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, source).unwrap();
}

#[test]
fn api_checks_program_theorems_and_keeps_whole_program_validation() {
    let scratch = support::Scratch::new("check-program-theorem-api");
    let path = scratch.path().join("main.lim");
    let source = "(#theorem selected (#proof-for-all ((value #u8))
        (#proof-eq (#u8::add-wrap value 0u8) value)))";
    write(&scratch, "main.lim", source);
    let name =
        check_theorem_from_path_with_config(source, &path, &CompileConfig::default(), "selected")
            .unwrap();
    assert_eq!(name, "selected");

    let invalid = format!("{source}\n(#theorem broken false)");
    write(&scratch, "main.lim", &invalid);
    let error =
        check_theorem_from_path_with_config(&invalid, &path, &CompileConfig::default(), "selected")
            .unwrap_err();
    assert_eq!(error.code, DiagnosticCode::ProofCounterexample);
    assert!(error.message.contains("disproved"), "{}", error.message);
}

#[test]
fn missing_and_false_theorems_fail_without_a_success_line() {
    for (source, name, expected) in [
        ("(#theorem actual true)", "missing", "unknown theorem"),
        ("(#theorem broken false)", "broken", "disproved"),
    ] {
        let scratch = support::Scratch::new("check-theorem-failure");
        write(&scratch, "main.lim", source);
        let (status, stdout, stderr) = run(&scratch, &["--check-theorem", "main.lim", name]);
        assert!(!status.success(), "{source}");
        assert!(stdout.is_empty());
        assert!(stderr.contains(expected), "{stderr}");
    }
}

#[test]
fn cfg_and_target_flags_are_shared_with_check_in_either_option_order() {
    let scratch = support::Scratch::new("check-theorem-cfg-target");
    write(
        &scratch,
        "main.lim",
        "(#cfg-if
      (#cfg-and (#cfg-is #feature enabled) (#cfg-is #arch aarch64))
      (#theorem configured true) (#cfg-else (#theorem configured false)))",
    );
    for flags in [
        ["--cfg", "feature=enabled", "--target", "aarch64-linux"],
        ["--target", "aarch64-linux", "--cfg", "feature=enabled"],
    ] {
        let mut arguments = vec!["--check-theorem", "main.lim", "configured"];
        arguments.extend(flags);
        let (status, stdout, stderr) = run(&scratch, &arguments);
        assert!(status.success(), "{stderr}");
        assert_eq!(stdout, "checked theorem configured\n");
    }
}

#[test]
fn explicit_cfg_overrides_survive_target_application() {
    let scratch = support::Scratch::new("check-theorem-target-override");
    write(
        &scratch,
        "main.lim",
        "(#cfg-if
      (#cfg-and (#cfg-is #arch x86_64) (#cfg-is #target aarch64-unknown-linux-gnu))
      (#theorem configured true) (#cfg-else (#theorem configured false)))",
    );
    let (status, stdout, stderr) = run(
        &scratch,
        &[
            "--check-theorem",
            "main.lim",
            "configured",
            "--cfg",
            "arch=x86_64",
            "--target",
            "aarch64-linux",
        ],
    );
    assert!(status.success(), "{stderr}");
    assert_eq!(stdout, "checked theorem configured\n");
}

#[test]
fn module_paths_project_defaults_and_explicit_targets_are_honored() {
    let scratch = support::Scratch::new("check-theorem-project");
    write(&scratch, "lim.project", "schema-version = 1\nname = \"theorem-test\"\nsource-root = \"src\"\nmodule-path = \"modules\"\ntarget = \"aarch64-linux\"\n");
    write(
        &scratch,
        "modules/selected.lim",
        "(#cfg-if (#cfg-is #arch aarch64)
          (#theorem module-proof true)
          (#cfg-else (#theorem module-proof false)))",
    );
    write(
        &scratch,
        "src/main.lim",
        "(#alias configured = //modules/selected.lim::module-proof)",
    );
    let (status, stdout, stderr) =
        run(&scratch, &["--check-theorem", "src/main.lim", "configured"]);
    assert!(status.success(), "{stderr}");
    assert_eq!(stdout, "checked theorem configured\n");
    let (status, stdout, _) = run(
        &scratch,
        &[
            "--check-theorem",
            "src/main.lim",
            "configured",
            "--target",
            "x86_64-sysv",
        ],
    );
    assert!(!status.success());
    assert!(stdout.is_empty());

    write(
        &scratch,
        "standalone.lim",
        "(#alias selected = ./modules/selected.lim::module-proof)",
    );
    let (status, stdout, stderr) = run(
        &scratch,
        &[
            "--check-theorem",
            "standalone.lim",
            "selected",
            "--module-path",
            "modules",
        ],
    );
    assert!(status.success(), "{stderr}");
    assert_eq!(stdout, "checked theorem selected\n");
}

#[test]
fn timing_json_keeps_success_stdout_separate_and_has_no_native_emission_stages() {
    let scratch = support::Scratch::new("check-theorem-timings");
    write(&scratch, "main.lim", "(#theorem reflexivity true)");
    let (status, stdout, stderr) = run(
        &scratch,
        &[
            "--timings",
            "--diagnostic-format=json",
            "--check-theorem",
            "main.lim",
            "reflexivity",
        ],
    );
    assert!(status.success(), "{stderr}");
    assert_eq!(stdout, "{\"schema_version\":1,\"category\":\"proof\",\"theorem\":\"reflexivity\",\"proof_outcome\":\"proved\"}\n");
    let lines = stderr.lines().collect::<Vec<_>>();
    assert_eq!(lines.len(), 1, "{stderr}");
    assert!(lines[0].starts_with("{\"timings\":["), "{stderr}");
    for stage in ["input_read", "semantic_validate", "total"] {
        assert!(stderr.contains(stage), "{stderr}");
    }
    for stage in [
        "native_emission",
        "native_assembly",
        "native_link",
        "output_write",
    ] {
        assert!(!stderr.contains(stage), "{stderr}");
    }
}

#[test]
fn invalid_flag_arguments_and_misordered_positionals_are_rejected() {
    let scratch = support::Scratch::new("check-theorem-arguments");
    write(&scratch, "main.lim", "(#theorem valid true)");
    for arguments in [
        vec!["--check-theorem"],
        vec!["--check-theorem", "main.lim"],
        vec![
            "--check-theorem",
            "--cfg",
            "feature=enabled",
            "main.lim",
            "valid",
        ],
        vec![
            "--check-theorem",
            "main.lim",
            "--cfg",
            "feature=enabled",
            "valid",
        ],
        vec!["--check-theorem", "main.lim", ""],
        vec!["--check-theorem", "main.lim", "valid", "extra"],
        vec!["--check-theorem", "main.lim", "valid", "--cfg"],
        vec!["--check-theorem", "main.lim", "valid", "--cfg", "feature"],
        vec!["--check-theorem", "main.lim", "valid", "--target"],
        vec![
            "--check-theorem",
            "main.lim",
            "valid",
            "--target",
            "--cfg",
            "feature=enabled",
        ],
        vec!["--check-theorem", "main.lim", "valid", "--module-path"],
        vec![
            "--check-theorem",
            "main.lim",
            "valid",
            "--module-path",
            "--target",
            "aarch64-linux",
        ],
        vec!["--check-theorem", "main.lim", "valid", "-o", "out"],
        vec!["--check-theorem", "main.lim", "valid", "--unknown"],
    ] {
        let mut args = arguments.clone();
        args.push("--diagnostic-format=json");
        let (status, stdout, stderr) = run(&scratch, &args);
        assert!(!status.success(), "accepted {arguments:?}");
        assert!(stdout.is_empty(), "{arguments:?}: {stdout}");
        assert!(
            stderr.contains("\"code\":\"E7000\""),
            "{arguments:?}: {stderr}"
        );
    }
}
