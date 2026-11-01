mod support;

use std::{fs, process::Command, time::Duration};

const FIXTURE: &str = include_str!("fixtures/lean_export/real-identity.ndjson");
const TARGET: &str = "ReplaySource.identityProof";
const TIMEOUT: Duration = Duration::from_secs(10);
const OUTPUT_LIMIT: usize = 1024 * 1024;

fn cli(args: &[&str], empty_path: bool) -> (std::process::ExitStatus, Vec<u8>, Vec<u8>) {
    let mut command = Command::new(env!("CARGO_BIN_EXE_lim"));
    command.args(args);
    if empty_path {
        command.env("PATH", "");
    }
    support::run(&mut command, TIMEOUT, OUTPUT_LIMIT).unwrap()
}

fn export_args(input: &std::path::Path, options: &[&str]) -> Vec<String> {
    let mut args = vec![
        "--check-lean-export".to_owned(),
        input.display().to_string(),
        TARGET.to_owned(),
    ];
    args.extend(options.iter().map(|value| (*value).to_owned()));
    args
}

#[test]
fn emits_checked_source_report_in_either_option_order_and_checks_native_target() {
    let scratch = support::Scratch::new("lean-export-source-cli");
    let input = scratch.path().join("real-identity.ndjson");
    fs::write(&input, FIXTURE).unwrap();

    for (index, report_first) in [false, true].into_iter().enumerate() {
        let proof = scratch
            .path()
            .join(if index == 0 { "one.lim" } else { "two.lim" });
        let report = scratch
            .path()
            .join(if index == 0 { "one.json" } else { "two.json" });
        let mut options = Vec::new();
        if report_first {
            options.extend(["--report".to_owned(), report.display().to_string()]);
            options.extend(["--emit-proof".to_owned(), proof.display().to_string()]);
        } else {
            options.extend(["--emit-proof".to_owned(), proof.display().to_string()]);
            options.extend(["--report".to_owned(), report.display().to_string()]);
        }
        if index == 0 {
            options.push("--timings".to_owned());
        }
        let args = export_args(
            &input,
            &options.iter().map(String::as_str).collect::<Vec<_>>(),
        );
        let args = args.iter().map(String::as_str).collect::<Vec<_>>();
        let (status, stdout, stderr) = cli(&args, true);
        assert!(status.success(), "{}", String::from_utf8_lossy(&stderr));
        let stdout = String::from_utf8(stdout).unwrap();
        let lines = stdout.lines().collect::<Vec<_>>();
        assert_eq!(lines.len(), 2, "{stdout}");
        assert!(lines[0].starts_with("checked Lean export theorem ReplaySource.identityProof ("));
        let (native_target, reported_path) = lines[1]
            .strip_prefix("emitted native theorem ")
            .and_then(|line| line.split_once(" to "))
            .expect("emission success line includes native target and path");
        assert_eq!(reported_path, proof.display().to_string());
        assert!(!fs::read_to_string(&proof).unwrap().is_empty());
        assert!(fs::read_to_string(report)
            .unwrap()
            .contains("\"axioms\":[]"));
        if index == 0 {
            assert!(String::from_utf8_lossy(&stderr).contains("lean_export_replay"));
        }

        let (status, _, stderr) = cli(
            &["--check-theorem", proof.to_str().unwrap(), native_target],
            true,
        );
        assert!(status.success(), "{}", String::from_utf8_lossy(&stderr));
    }
}

#[test]
fn rejects_duplicate_empty_dangling_and_unknown_options() {
    let scratch = support::Scratch::new("lean-export-source-options");
    let input = scratch.path().join("input.ndjson");
    fs::write(&input, FIXTURE).unwrap();
    let input = input.to_str().unwrap();
    for args in [
        vec![
            "--check-lean-export",
            input,
            TARGET,
            "--report",
            "a",
            "--report",
            "b",
        ],
        vec![
            "--check-lean-export",
            input,
            TARGET,
            "--emit-proof",
            "a",
            "--emit-proof",
            "b",
        ],
        vec!["--check-lean-export", input, TARGET, "--report"],
        vec!["--check-lean-export", input, TARGET, "--emit-proof"],
        vec!["--check-lean-export", input, TARGET, "--report", ""],
        vec!["--check-lean-export", input, TARGET, "--emit-proof", ""],
        vec!["--check-lean-export", input, TARGET, "--unknown", "a"],
    ] {
        let (status, stdout, _) = cli(&args, true);
        assert!(!status.success(), "accepted {args:?}");
        assert!(stdout.is_empty(), "unexpected output for {args:?}");
    }
}

#[test]
fn rejects_input_and_output_pair_collisions_including_hard_links() {
    let scratch = support::Scratch::new("lean-export-source-collisions");
    let input = scratch.path().join("input.ndjson");
    fs::write(&input, FIXTURE).unwrap();

    let input_text = input.to_str().unwrap();
    for output in [
        input_text.to_owned(),
        scratch
            .path()
            .join(".")
            .join("input.ndjson")
            .display()
            .to_string(),
    ] {
        let (status, _, _) = cli(
            &[
                "--check-lean-export",
                input_text,
                TARGET,
                "--emit-proof",
                &output,
            ],
            true,
        );
        assert!(!status.success(), "accepted input collision {output}");
    }

    let input_link = scratch.path().join("input-link.ndjson");
    fs::hard_link(&input, &input_link).unwrap();
    let link_text = input_link.to_str().unwrap();
    let (status, _, _) = cli(
        &[
            "--check-lean-export",
            input_text,
            TARGET,
            "--report",
            link_text,
        ],
        true,
    );
    assert!(!status.success(), "accepted hard-link input collision");

    let same = scratch.path().join("same.lim");
    let alternate = scratch.path().join(".").join("same.lim");
    let (status, _, _) = cli(
        &[
            "--check-lean-export",
            input_text,
            TARGET,
            "--emit-proof",
            same.to_str().unwrap(),
            "--report",
            alternate.to_str().unwrap(),
        ],
        true,
    );
    assert!(!status.success(), "accepted identical new output paths");
    assert!(!same.exists());

    let first = scratch.path().join("first.lim");
    let second = scratch.path().join("second.json");
    fs::write(&first, "existing output").unwrap();
    fs::hard_link(&first, &second).unwrap();
    let (status, _, _) = cli(
        &[
            "--check-lean-export",
            input_text,
            TARGET,
            "--emit-proof",
            first.to_str().unwrap(),
            "--report",
            second.to_str().unwrap(),
        ],
        true,
    );
    assert!(
        !status.success(),
        "accepted hard-linked proof/report outputs"
    );
    assert_eq!(fs::read(&first).unwrap(), b"existing output");
}

#[test]
fn failed_replay_leaves_existing_proof_and_report_outputs_unchanged() {
    let scratch = support::Scratch::new("lean-export-source-atomic-failure");
    let input = scratch.path().join("input.ndjson");
    let proof = scratch.path().join("existing.lim");
    let report = scratch.path().join("existing.json");
    for invalid in [
        format!("{FIXTURE}{{bad json}}\n"),
        FIXTURE.replace("\"safety\":\"safe\"", "\"safety\":\"unsafe\""),
        FIXTURE.replace("\"value\":13", "\"value\":7"),
    ] {
        fs::write(&input, invalid).unwrap();
        fs::write(&proof, "old proof").unwrap();
        fs::write(&report, "old report").unwrap();
        let (status, stdout, _) = cli(
            &[
                "--check-lean-export",
                input.to_str().unwrap(),
                TARGET,
                "--emit-proof",
                proof.to_str().unwrap(),
                "--report",
                report.to_str().unwrap(),
            ],
            true,
        );
        assert!(!status.success());
        assert!(stdout.is_empty());
        assert_eq!(fs::read(&proof).unwrap(), b"old proof");
        assert_eq!(fs::read(&report).unwrap(), b"old report");
    }
}

#[test]
fn a_translation_resource_failure_does_not_publish_outputs() {
    let original = include_str!("fixtures/lean_export/identity.ndjson");
    let levels = (2..=201)
        .map(|index| format!("{{\"succ\":{},\"il\":{index}}}\n", index - 1))
        .collect::<String>();
    let input = original.replace("{\"param\":4,\"il\":1}\n",&format!("{{\"param\":4,\"il\":1}}\n{levels}"))
        .replace("{\"sort\":1,\"ie\":0}","{\"sort\":201,\"ie\":0}")
        .replace("{\"def\":",concat!(
            "{\"lam\":{\"name\":0,\"type\":9,\"body\":16,\"binderInfo\":\"default\"},\"ie\":20}\n",
            "{\"lam\":{\"name\":0,\"type\":8,\"body\":20,\"binderInfo\":\"implicit\"},\"ie\":21}\n{\"def\":"))
        .replace("\"type\":12,\"value\":19","\"type\":12,\"value\":21");
    let target = "Audit.identity.theorem";
    lim::check_lean_export(input.as_bytes(), target).unwrap();
    assert!(lim::translate_lean_export(input.as_bytes(), target)
        .unwrap_err()
        .message
        .contains("source expression depth limit"));
    let scratch = support::Scratch::new("lean-source-translation-limit");
    let path = scratch.path().join("input.ndjson");
    let proof = scratch.path().join("proof.lim");
    let report = scratch.path().join("receipt.json");
    fs::write(&path, input).unwrap();
    fs::write(&proof, "old proof").unwrap();
    fs::write(&report, "old receipt").unwrap();
    let (status, stdout, stderr) = cli(
        &[
            "--check-lean-export",
            path.to_str().unwrap(),
            target,
            "--emit-proof",
            proof.to_str().unwrap(),
            "--report",
            report.to_str().unwrap(),
        ],
        true,
    );
    assert!(!status.success());
    assert!(stdout.is_empty());
    assert!(String::from_utf8_lossy(&stderr).contains("source expression depth limit"));
    assert_eq!(fs::read(proof).unwrap(), b"old proof");
    assert_eq!(fs::read(report).unwrap(), b"old receipt");
}
