mod support;

use std::{fs, path::PathBuf, process::Command, time::Duration};

const SOURCE: &str = "#gn first () `((#type First #u64))\n#gn second () `((#type Second #u64))\n#generate first; #generate second\n#fn main () #u64 (#return 0u64)\n";

fn run(arguments: &[&str]) -> (bool, String, String) {
    let (status, stdout, stderr) = support::run(
        Command::new(env!("CARGO_BIN_EXE_lim")).args(arguments),
        Duration::from_secs(30),
        64 * 1024,
    )
    .unwrap();
    (
        status.success(),
        String::from_utf8(stdout).unwrap(),
        String::from_utf8(stderr).unwrap(),
    )
}

#[test]
fn locates_points_and_overlapping_ranges_without_native_output() {
    let scratch = support::Scratch::new("locate-command");
    let input = scratch.path().join("ns:foo-bar.lim");
    fs::write(&input, SOURCE).unwrap();
    let entry = input.to_str().unwrap();
    for (suffix, expected) in [
        ("3", 2),
        ("3-4", 2),
        ("3:2", 1),
        ("3:4-3:6", 1),
        ("3:14-3:20", 2),
        ("3:17", 0),
        ("3:1-3:17", 1),
        ("4", 0),
    ] {
        let selection = format!("{entry}:{suffix}");
        let (success, stdout, stderr) = run(&[entry, "--locate-generated", &selection]);
        assert!(success, "{suffix}: {stderr}");
        assert!(stderr.is_empty(), "{stderr}");
        let paths: Vec<_> = stdout
            .lines()
            .map(|line| {
                assert!(line.starts_with("direct #generate "), "{line}");
                PathBuf::from(line.split_once(" -> ").unwrap().1)
            })
            .collect();
        assert_eq!(paths.len(), expected, "{suffix}: {stdout}");
        for path in &paths {
            assert!(path.is_file(), "{}", path.display());
            assert!(path.starts_with(scratch.path().join(".lim")));
            assert!(fs::read_to_string(path).unwrap().contains("#type"));
        }
    }
    assert_eq!(fs::read_to_string(&input).unwrap(), SOURCE);
    assert!(!input.with_extension("").exists());
    assert!(!input.with_extension("s").exists());
}

#[test]
fn imported_selection_uses_cfg_target_module_paths_and_writes_lsp_context() {
    let scratch = support::Scratch::new("locate-command-config");
    let modules = scratch.path().join("modules");
    fs::create_dir(&modules).unwrap();
    let selected = modules.join("selected.lim");
    fs::write(
        &selected,
        "#cfg-if (#cfg-is #feature enabled) (#gn first () `((#type First #u64)))\n#generate first\n",
    )
    .unwrap();
    let input = scratch.path().join("main.lim");
    fs::write(
        &input,
        "#alias First = ./modules/selected.lim::First\n#fn main () First (#return 0u64)\n",
    )
    .unwrap();
    let context = scratch.path().join("context.lsp");
    let selection = format!("{}:2", selected.display());
    let (success, stdout, stderr) = run(&[
        input.to_str().unwrap(),
        "--locate-generated",
        &selection,
        "--cfg",
        "feature=enabled",
        "--target",
        "aarch64-linux",
        "--module-path",
        modules.to_str().unwrap(),
        "--write-lsp-config",
        context.to_str().unwrap(),
    ]);
    assert!(success, "{stderr}");
    assert_eq!(stdout.lines().count(), 1, "{stdout}");
    let context = lim::lsp_context::LspContext::read(&context).unwrap();
    assert_eq!(context.entry, input);
    assert_eq!(context.target, lim::TargetDescription::AARCH64_LINUX);
    let path = stdout.trim().split_once(" -> ").unwrap().1;
    assert!(fs::read_to_string(path).unwrap().contains("First"));
    assert!(!input.with_extension("").exists());
}

#[test]
fn rejects_bad_selections_and_options_with_json_cli_diagnostics() {
    let scratch = support::Scratch::new("locate-command-errors");
    let input = scratch.path().join("main.lim");
    fs::write(&input, SOURCE).unwrap();
    let entry = input.to_str().unwrap();
    for suffix in ["0", "500", "3:0", "3:500", "4-3", "3:8-3:2", "1:1-500:1"] {
        let selection = format!("{entry}:{suffix}");
        let (success, stdout, stderr) = run(&[
            entry,
            "--locate-generated",
            &selection,
            "--diagnostic-format=json",
        ]);
        assert!(!success, "{suffix}");
        assert!(stdout.is_empty());
        assert!(stderr.contains("\"category\":\"cli\""), "{stderr}");
    }
    for arguments in [
        vec![entry, "--locate-generated"],
        vec![entry, "--locate-generated", "missing.lim:1"],
        vec![
            entry,
            "--locate-generated",
            "main.lim:1",
            "--locate-generated",
            "main.lim:2",
        ],
        vec![entry, "--locate-generated", "main.lim:1", "--cfg", "bad"],
    ] {
        let (success, stdout, stderr) = run(&arguments);
        assert!(!success);
        assert!(stdout.is_empty());
        assert!(!stderr.is_empty());
    }
}

#[test]
fn reports_current_entry_errors_even_when_selection_has_no_invocation() {
    let scratch = support::Scratch::new("locate-command-diagnostic");
    let input = scratch.path().join("main.lim");
    fs::write(&input, "#fn main () #u64 (#return missing)\n").unwrap();
    let selection = format!("{}:1:1", input.display());
    let (success, stdout, stderr) = run(&[
        input.to_str().unwrap(),
        "--locate-generated",
        &selection,
        "--diagnostic-format=json",
    ]);
    assert!(!success);
    assert!(stdout.is_empty());
    assert!(stderr.contains("\"category\":\"type\""), "{stderr}");
    assert!(!input.with_extension("").exists());
}

#[test]
fn distinguishes_selected_output_from_nested_generators_on_cold_and_warm_runs() {
    let scratch = support::Scratch::new("locate-command-nested-labels");
    let input = scratch.path().join("main.lim");
    fs::write(
        &input,
        "#gn inner () `((#type Value #u64))\n#gn outer () `((#generate inner))\n#generate outer\n#generate inner\n",
    )
    .unwrap();
    let selection = format!("{}:3", input.display());
    let arguments = [input.to_str().unwrap(), "--locate-generated", &selection];
    let (success, cold, stderr) = run(&arguments);
    assert!(success, "{stderr}");
    let lines = cold.lines().collect::<Vec<_>>();
    assert_eq!(lines.len(), 2, "{cold}");
    assert!(lines[0].starts_with("direct #generate outer -> "), "{cold}");
    assert!(lines[1].starts_with("nested #generate inner -> "), "{cold}");
    for line in &lines {
        assert!(std::path::Path::new(line.split_once(" -> ").unwrap().1).is_file());
    }
    let (success, warm, stderr) = run(&arguments);
    assert!(success, "{stderr}");
    assert_eq!(cold, warm);

    let selection = format!("{}:4", input.display());
    let (success, stdout, stderr) =
        run(&[input.to_str().unwrap(), "--locate-generated", &selection]);
    assert!(success, "{stderr}");
    assert_eq!(stdout.lines().count(), 1, "{stdout}");
    assert!(stdout.starts_with("direct #generate inner -> "), "{stdout}");

    let selection = format!("{}:3-4", input.display());
    let (success, stdout, stderr) =
        run(&[input.to_str().unwrap(), "--locate-generated", &selection]);
    assert!(success, "{stderr}");
    assert_eq!(stdout.lines().count(), 2, "{stdout}");
    assert!(
        stdout
            .lines()
            .all(|line| line.starts_with("direct #generate ")),
        "{stdout}"
    );
}
