mod support;

use lim::{check_theorem_from_path_with_config, CompileConfig, DiagnosticCode};
use std::{
    fs,
    process::{Command, ExitStatus},
    time::Duration,
};

const REFLEXIVITY: &str = "(#theorem reflexivity
  (#universes u)
  (#parameters (#parameter a (#pt-type u)) (#parameter value a))
  (#statement (#pt-eq a value value))
  (#proof (#pt-refl a value)))";

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
fn generic_and_procedural_theorems_have_an_exact_success_line_and_no_native_output() {
    for (source, name) in [
        (REFLEXIVITY, "reflexivity"),
        (
            "(#fn pure () #u64 (#return 42u64))
          (#theorem no-io (#proof-no-effects pure (#proof-io)))",
            "no-io",
        ),
    ] {
        let scratch = support::Scratch::new("check-theorem-success");
        write(&scratch, "main.lim", source);
        let (status, stdout, stderr) = run(&scratch, &["--check-theorem", "main.lim", name]);
        assert!(status.success(), "{stderr}");
        assert_eq!(stdout, format!("checked theorem {name}\n"));
        assert!(stderr.is_empty(), "{stderr}");
        for artifact in ["main", "main.s", ".lim"] {
            assert!(
                !scratch.path().join(artifact).exists(),
                "unexpected artifact {artifact}"
            );
        }
        assert_eq!(
            fs::read_to_string(scratch.path().join("main.lim")).unwrap(),
            source
        );
    }
}

#[test]
fn public_api_returns_the_actual_root_or_alias_identity() {
    let scratch = support::Scratch::new("check-theorem-api");
    let path = scratch.path().join("main.lim");
    let config = CompileConfig::default();
    assert_eq!(
        check_theorem_from_path_with_config(REFLEXIVITY, &path, &config, "reflexivity").unwrap(),
        "reflexivity"
    );
    write(
        &scratch,
        "math/lib.lim",
        &format!("(#export reflexivity)\n{REFLEXIVITY}"),
    );
    let source = "(#alias imported = ./math/lib.lim::reflexivity)";
    let canonical =
        check_theorem_from_path_with_config(source, &path, &config, "imported").unwrap();
    assert!(
        canonical.ends_with("math/lib.lim::reflexivity"),
        "{canonical}"
    );
    assert_eq!(
        check_theorem_from_path_with_config(source, &path, &config, &canonical).unwrap(),
        canonical
    );
}

#[test]
fn cli_selects_an_exported_mathematical_theorem_through_an_alias() {
    let scratch = support::Scratch::new("check-theorem-alias");
    write(
        &scratch,
        "math/lib.lim",
        &format!("(#export reflexivity)\n{REFLEXIVITY}"),
    );
    write(
        &scratch,
        "main.lim",
        "(#alias imported = ./math/lib.lim::reflexivity)",
    );
    let (status, stdout, stderr) = run(&scratch, &["--check-theorem", "main.lim", "imported"]);
    assert!(status.success(), "{stderr}");
    assert_eq!(stdout, "checked theorem imported\n");
}

#[test]
fn a_private_theorem_cannot_be_selected_through_a_forbidden_alias() {
    let scratch = support::Scratch::new("check-theorem-private");
    write(
        &scratch,
        "math/lib.lim",
        &format!("(#export)\n{REFLEXIVITY}"),
    );
    write(
        &scratch,
        "main.lim",
        "(#alias stolen = ./math/lib.lim::reflexivity)",
    );
    let (status, stdout, stderr) = run(
        &scratch,
        &[
            "--check-theorem",
            "main.lim",
            "stolen",
            "--diagnostic-format=json",
        ],
    );
    assert!(!status.success());
    assert!(stdout.is_empty());
    assert!(stderr.contains("private"), "{stderr}");
}

#[test]
fn the_selector_cannot_guess_an_unexported_theorem_canonical_path() {
    let scratch = support::Scratch::new("check-theorem-private-selector");
    write(
        &scratch,
        "math/lib.lim",
        &format!("(#export visible)\n(#theorem visible true)\n{REFLEXIVITY}"),
    );
    let source = "(#alias allowed = ./math/lib.lim::visible)";
    let path = scratch.path().join("main.lim");
    let hidden = format!(
        "{}::reflexivity",
        scratch.path().join("math/lib.lim").display()
    );
    let error =
        check_theorem_from_path_with_config(source, &path, &CompileConfig::default(), &hidden)
            .unwrap_err();
    assert_eq!(error.code, DiagnosticCode::Proof);
    assert!(error.message.contains("unknown theorem"), "{error:?}");
}

#[test]
fn missing_and_false_theorems_fail_without_a_success_line() {
    for (source, name, expected) in [
        ("(#theorem actual true)", "missing", "unknown theorem"),
        ("(#theorem broken false)", "broken", "disproved"),
        (
            "(#theorem broken (#universes) (#parameters)
          (#statement (#pt-eq #pt-nat #pt-zero (#pt-succ #pt-zero)))
          (#proof (#pt-refl #pt-nat #pt-zero)))",
            "broken",
            "E4400",
        ),
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
fn mathematical_definitions_inductives_and_functions_are_not_theorems() {
    for (source, name) in [
        ("(#math-definition zero () #pt-nat #pt-zero)", "zero"),
        (
            "(#math-inductive box () () (#pt-type 0) ((pack ())))",
            "box",
        ),
        ("(#fn value () #u64 (#return 42u64))", "value"),
    ] {
        let scratch = support::Scratch::new("check-theorem-kind");
        write(&scratch, "main.lim", source);
        let (status, stdout, stderr) = run(
            &scratch,
            &[
                "--check-theorem",
                "main.lim",
                name,
                "--diagnostic-format=json",
            ],
        );
        assert!(!status.success(), "{source}");
        assert!(stdout.is_empty());
        assert!(stderr.contains("\"code\":\"E4400\""), "{stderr}");
        assert!(stderr.contains("theorem"), "{stderr}");
    }
}

#[test]
fn selection_still_checks_all_other_proof_and_runtime_obligations() {
    for other in [
        "(#theorem unrelated false)",
        "(#theorem unrelated (#universes) (#parameters)
          (#statement #pt-false) (#proof #pt-zero))",
        "(#fn invalid () #u64 (#return false))",
    ] {
        let source = format!("(#theorem selected true)\n{other}");
        let scratch = support::Scratch::new("check-theorem-all-obligations");
        write(&scratch, "main.lim", &source);
        let (status, stdout, stderr) = run(&scratch, &["--check-theorem", "main.lim", "selected"]);
        assert!(!status.success(), "ignored obligation: {other}");
        assert!(stdout.is_empty());
        assert!(!stderr.is_empty());
    }
}

#[test]
fn selection_does_not_bypass_invalid_imported_obligations() {
    let scratch = support::Scratch::new("check-theorem-import-obligation");
    write(
        &scratch,
        "math/lib.lim",
        "(#export visible)
      (#theorem visible true) (#theorem private-failure false)",
    );
    write(
        &scratch,
        "main.lim",
        "(#alias chosen = ./math/lib.lim::visible)",
    );
    let (status, stdout, stderr) = run(&scratch, &["--check-theorem", "main.lim", "chosen"]);
    assert!(!status.success());
    assert!(stdout.is_empty());
    assert!(stderr.contains("private-failure"), "{stderr}");
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
    write(&scratch, "main.lim", REFLEXIVITY);
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
    assert_eq!(stdout, "checked theorem reflexivity\n");
    let lines = stderr.lines().collect::<Vec<_>>();
    assert_eq!(lines.len(), 1, "{stderr}");
    assert!(lines[0].starts_with("{\"timings\":["), "{stderr}");
    for stage in [
        "input_read",
        "prepare_imports_parse_cfg",
        "expansion",
        "semantic_validate",
        "total",
    ] {
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
fn failure_json_has_e4400_precise_source_positions_and_a_separate_timing_record() {
    for (source, selected) in [
        ("(#theorem broken false)", "false"),
        (
            "(#theorem broken (#universes) (#parameters)
          (#statement (#pt-eq #pt-nat #pt-zero (#pt-succ #pt-zero)))
          (#proof (#pt-refl #pt-nat #pt-zero)))",
            "whole-declaration",
        ),
    ] {
        let scratch = support::Scratch::new("check-theorem-json-position");
        write(&scratch, "main.lim", source);
        let (status, stdout, stderr) = run(
            &scratch,
            &[
                "--check-theorem",
                "main.lim",
                "broken",
                "--diagnostic-format=json",
                "--timings",
            ],
        );
        assert!(!status.success());
        assert!(stdout.is_empty());
        let lines = stderr.lines().collect::<Vec<_>>();
        assert_eq!(lines.len(), 2, "{stderr}");
        assert!(lines[0].contains("\"code\":\"E4400\""), "{stderr}");
        assert!(lines[0].contains("\"category\":\"proof\""), "{stderr}");
        let (start, end) = if selected == "false" {
            let start = source.find("false").unwrap();
            (start, start + "false".len())
        } else {
            (0, source.len())
        };
        assert!(
            lines[0].contains(&format!("\"byte_start\":{start}")),
            "{stderr}"
        );
        assert!(
            lines[0].contains(&format!("\"byte_end\":{end}")),
            "{stderr}"
        );
        assert!(lines[1].starts_with("{\"timings\":["), "{stderr}");
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

#[test]
fn checking_theorem_does_not_require_native_backend_representability() {
    let scratch = support::Scratch::new("check-theorem-no-codegen");
    write(
        &scratch,
        "main.lim",
        "(#fn wide-result () #i128 (#return 1i128))
      (#theorem valid true)",
    );
    let (status, stdout, stderr) = run(
        &scratch,
        &[
            "--check-theorem",
            "main.lim",
            "valid",
            "--target",
            "aarch64-linux",
        ],
    );
    assert!(status.success(), "{stderr}");
    assert_eq!(stdout, "checked theorem valid\n");
}

#[test]
fn fermats_last_theorem_statement_is_checked_as_a_definition_never_as_a_proved_theorem() {
    let scratch = support::Scratch::new("check-theorem-fermat-statement");
    write(
        &scratch,
        "fermat_statement.lim",
        include_str!("../theorems/fermat_statement.lim"),
    );
    let (status, stdout, stderr) = run(&scratch, &["--check", "fermat_statement.lim"]);
    assert!(status.success(), "{stderr}");
    assert!(stdout.is_empty());
    let (status, stdout, stderr) = run(
        &scratch,
        &[
            "--check-theorem",
            "fermat_statement.lim",
            "fermats-last-theorem-statement",
            "--diagnostic-format=json",
        ],
    );
    assert!(!status.success());
    assert!(stdout.is_empty());
    assert!(stderr.contains("\"code\":\"E4400\""), "{stderr}");
    assert!(stderr.contains("definition"), "{stderr}");
    assert!(!scratch.path().join("fermat_statement").exists());
}
