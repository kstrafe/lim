mod support;

use lim::lsp::json::{self, Json};
use std::{fs, process::Command, time::Duration};

const FIXTURE: &str = include_str!("fixtures/lean_export_foundations/foundations.ndjson");
const TARGET: &str = "BasisProbe.quotientRelated";
const TIMEOUT: Duration = Duration::from_secs(10);
const OUTPUT_LIMIT: usize = 1024 * 1024;

fn cli(args: &[&str]) -> (std::process::ExitStatus, Vec<u8>, Vec<u8>) {
    let mut command = Command::new(env!("CARGO_BIN_EXE_lim"));
    command.args(args).env("PATH", "");
    support::run(&mut command, TIMEOUT, OUTPUT_LIMIT).unwrap()
}

fn json(path: &std::path::Path) -> Json {
    json::parse(&fs::read_to_string(path).unwrap()).expect("valid receipt JSON")
}

fn strings(value: &Json) -> Vec<&str> {
    value
        .array()
        .unwrap()
        .iter()
        .map(|v| v.string().unwrap())
        .collect()
}

#[test]
fn pinned_replay_reports_declared_and_target_axioms_and_emits_auditable_proof() {
    let scratch = support::Scratch::new("lean-foundations-cli");
    let input = scratch.path().join("foundations.ndjson");
    fs::write(&input, FIXTURE).unwrap();

    let (status, stdout, _) = cli(&["--check-lean-export", input.to_str().unwrap(), TARGET]);
    assert!(!status.success());
    assert!(stdout.is_empty());

    let proof = scratch.path().join("proof.lim");
    let receipt = scratch.path().join("receipt.json");
    let (status, stdout, stderr) = cli(&[
        "--check-lean-export",
        input.to_str().unwrap(),
        TARGET,
        "--report",
        receipt.to_str().unwrap(),
        "--lean-foundations",
        "--emit-proof",
        proof.to_str().unwrap(),
    ]);
    assert!(status.success(), "{}", String::from_utf8_lossy(&stderr));
    let stdout = String::from_utf8(stdout).unwrap();
    assert!(stdout.contains("declared Lean axioms:"), "{stdout}");
    assert!(
        stdout.contains("target logical foundations: Quot.sound"),
        "{stdout}"
    );
    assert_eq!(
        strings(json(&receipt).get("axioms").unwrap()),
        ["Classical.choice", "Quot.sound", "propext"]
    );
    assert_eq!(
        strings(json(&receipt).get("target_axioms").unwrap()),
        ["Quot.sound"]
    );

    let source = fs::read_to_string(&proof).unwrap();
    let target = source
        .lines()
        .find_map(|line| line.strip_prefix("; Native theorem: "))
        .expect("emitted source identifies its native theorem");
    assert!(
        source.contains("Target logical foundations: [\"Quot.sound\"]"),
        "{source}"
    );
    let (status, stdout, stderr) = cli(&["--check-theorem", proof.to_str().unwrap(), target]);
    assert!(status.success(), "{}", String::from_utf8_lossy(&stderr));
    assert!(String::from_utf8(stdout)
        .unwrap()
        .contains("logical foundations: Quot.sound"));
}

#[test]
fn flag_order_duplicates_and_invalid_options_are_checked() {
    let scratch = support::Scratch::new("lean-foundations-options");
    let input = scratch.path().join("input.ndjson");
    fs::write(&input, FIXTURE).unwrap();
    let input = input.to_str().unwrap();
    for (index, report_first) in [false, true].into_iter().enumerate() {
        let report = scratch.path().join(format!("order-{index}.json"));
        let proof = scratch.path().join(format!("order-{index}.lim"));
        let mut args = vec!["--check-lean-export", input, TARGET];
        if report_first {
            args.extend([
                "--lean-foundations",
                "--report",
                report.to_str().unwrap(),
                "--emit-proof",
                proof.to_str().unwrap(),
            ]);
        } else {
            args.extend([
                "--emit-proof",
                proof.to_str().unwrap(),
                "--lean-foundations",
                "--report",
                report.to_str().unwrap(),
            ]);
        }
        let (status, _, stderr) = cli(&args);
        assert!(status.success(), "{}", String::from_utf8_lossy(&stderr));
    }
    for options in [
        vec!["--lean-foundations", "--lean-foundations"],
        vec!["--lean-foundations=true"],
        vec!["--lean-foundations", "value"],
        vec!["--unknown"],
    ] {
        let mut args = vec!["--check-lean-export", input, TARGET];
        args.extend(options.iter().copied());
        let (status, stdout, _) = cli(&args);
        assert!(!status.success(), "accepted {options:?}");
        assert!(stdout.is_empty());
    }
}

#[test]
fn corrupted_axiom_metadata_preserves_existing_outputs() {
    let scratch = support::Scratch::new("lean-foundations-corrupt");
    let input = scratch.path().join("input.ndjson");
    let proof = scratch.path().join("existing.lim");
    let receipt = scratch.path().join("existing.json");
    for field in ["isUnsafe", "type"] {
        let mut rows = FIXTURE
            .lines()
            .map(|row| json::parse(row).unwrap())
            .collect::<Vec<_>>();
        let row = rows
            .iter_mut()
            .filter_map(|row| match row {
                Json::Object(data) => data.get_mut("axiom"),
                _ => None,
            })
            .nth(1)
            .unwrap();
        let Json::Object(data) = row else {
            panic!("axiom object")
        };
        data.insert(
            field.into(),
            if field == "isUnsafe" {
                Json::Bool(true)
            } else {
                Json::Number("3".into())
            },
        );
        fs::write(
            &input,
            rows.iter().map(Json::render).collect::<Vec<_>>().join("\n") + "\n",
        )
        .unwrap();
        fs::write(&proof, "preserve proof").unwrap();
        fs::write(&receipt, "preserve receipt").unwrap();
        let (status, stdout, _) = cli(&[
            "--check-lean-export",
            input.to_str().unwrap(),
            "BasisProbe.choiceReflexive",
            "--lean-foundations",
            "--emit-proof",
            proof.to_str().unwrap(),
            "--report",
            receipt.to_str().unwrap(),
        ]);
        assert!(!status.success());
        assert!(stdout.is_empty());
        assert_eq!(fs::read(&proof).unwrap(), b"preserve proof");
        assert_eq!(fs::read(&receipt).unwrap(), b"preserve receipt");
    }
}

#[test]
fn replay_only_uses_the_explicit_policy_and_default_refusal_preserves_outputs() {
    let scratch = support::Scratch::new("lean-foundations-replay-only");
    let input = scratch.path().join("input.ndjson");
    let report = scratch.path().join("report.json");
    let proof = scratch.path().join("proof.lim");
    fs::write(&input, FIXTURE).unwrap();
    fs::write(&report, "existing report").unwrap();
    fs::write(&proof, "existing proof").unwrap();
    let (status, stdout, _) = cli(&[
        "--check-lean-export",
        input.to_str().unwrap(),
        TARGET,
        "--report",
        report.to_str().unwrap(),
        "--emit-proof",
        proof.to_str().unwrap(),
    ]);
    assert!(!status.success());
    assert!(stdout.is_empty());
    assert_eq!(fs::read(&report).unwrap(), b"existing report");
    assert_eq!(fs::read(&proof).unwrap(), b"existing proof");
    let (status, stdout, stderr) = cli(&[
        "--check-lean-export",
        input.to_str().unwrap(),
        TARGET,
        "--lean-foundations",
        "--report",
        report.to_str().unwrap(),
    ]);
    assert!(status.success(), "{}", String::from_utf8_lossy(&stderr));
    assert!(String::from_utf8(stdout)
        .unwrap()
        .contains("target logical foundations: Quot.sound"));
    assert_eq!(
        strings(json(&report).get("target_axioms").unwrap()),
        ["Quot.sound"]
    );
    assert_eq!(fs::read(&proof).unwrap(), b"existing proof");
    let (status, stdout, stderr) = cli(&[
        "--check-lean-export",
        input.to_str().unwrap(),
        "BasisProbe.pick._proof_1",
        "--lean-foundations",
    ]);
    assert!(status.success(), "{}", String::from_utf8_lossy(&stderr));
    assert!(String::from_utf8(stdout)
        .unwrap()
        .contains("target logical foundations: none"));
}
