mod support;

use lim::check_lean_export;
use std::{
    fs,
    io::{BufRead, Read},
    process::Command,
    time::Duration,
};

const FIXTURE: &str = include_str!("fixtures/lean_export/identity.ndjson");
const INPUT_SHA256: &str = "ad05e4153b542ea6dcd88e4a92d0a8e42ad2d757bdbc19552e3229a979c974ec";
const TARGET: &str = "Audit.identity.theorem";

struct SmallChunks<R> {
    inner: R,
    size: usize,
}

impl<R: Read> Read for SmallChunks<R> {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        let limit = buf.len().min(self.size);
        self.inner.read(&mut buf[..limit])
    }
}

impl<R: BufRead> BufRead for SmallChunks<R> {
    fn fill_buf(&mut self) -> std::io::Result<&[u8]> {
        let available = self.inner.fill_buf()?;
        let limit = available.len().min(self.size);
        Ok(&available[..limit])
    }
    fn consume(&mut self, amount: usize) {
        self.inner.consume(amount)
    }
}

#[test]
fn api_replays_identity_fixture_with_one_byte_reads_and_receipt_fields() {
    let report = check_lean_export(
        SmallChunks {
            inner: FIXTURE.as_bytes(),
            size: 1,
        },
        TARGET,
    )
    .unwrap();

    assert_eq!(report.target, TARGET);
    assert_eq!(report.declarations.len(), 2);
    assert_eq!(report.records, 28);
    assert_eq!(report.bytes, FIXTURE.len() as u64);
    assert_eq!(report.input_sha256, INPUT_SHA256);
    assert_eq!(report.declarations[0].name, "Audit.identity");
    assert_eq!(report.declarations[0].kind, "definition");
    assert_eq!(report.declarations[1].name, TARGET);
    assert_eq!(report.declarations[1].kind, "theorem");
    assert_eq!(
        report.declarations[1].dependencies,
        vec!["$lean:s5:Audits8:identity".to_owned()]
    );

    let receipt = report.render_json();
    for expected in [
        "\"target\":\"Audit.identity.theorem\"",
        &format!("\"input_sha256\":\"{INPUT_SHA256}\""),
        "\"bytes\":1352",
        "\"records\":28",
        "\"axioms\":[]",
    ] {
        assert!(
            receipt.contains(expected),
            "missing {expected} in {receipt}"
        );
    }
}

#[test]
fn api_reads_the_fixture_through_a_small_buffered_stream() {
    let report = check_lean_export(
        std::io::BufReader::with_capacity(1, FIXTURE.as_bytes()),
        TARGET,
    )
    .unwrap();
    assert_eq!(report.input_sha256, INPUT_SHA256);
    assert_eq!(report.declarations.len(), 2);
}

fn changed(from: &str, to: &str) -> String {
    assert_eq!(FIXTURE.matches(from).count(), 1, "mutation anchor: {from}");
    FIXTURE.replacen(from, to, 1)
}

#[test]
fn api_rejects_malformed_or_unauthorized_export_records() {
    let axiom = "{\"axiom\":{\"name\":2,\"levelParams\":[],\"type\":0,\"isUnsafe\":false}}\n";
    let cases = [
        (
            changed(
                "{\"str\":{\"pre\":0,\"str\":\"Audit\"},\"in\":1}",
                "{\"str\":{\"pre\":1,\"str\":\"Audit\"},\"in\":1}",
            ),
            "earlier record",
        ),
        (
            changed(
                "\"format\":{\"version\":\"3.1.0\"}",
                "\"format\":{\"version\":\"3.0.0\"}",
            ),
            "metadata",
        ),
        (
            changed("\"safety\":\"safe\"", "\"safety\":\"unsafe\""),
            "unsafe",
        ),
        (
            format!(
                "{}\n{axiom}{}\n",
                FIXTURE.lines().next().unwrap(),
                FIXTURE.lines().skip(1).collect::<Vec<_>>().join("\n")
            ),
            "axioms",
        ),
        (FIXTURE.to_owned(), "missing or ambiguous"),
        (FIXTURE.to_owned(), "not a theorem"),
        (format!("{FIXTURE}{{bad json}}\n"), "invalid export JSON"),
    ];

    for (index, (input, expected)) in cases.into_iter().enumerate() {
        let target = match index {
            4 => "Audit.identity.missing",
            5 => "Audit.identity",
            _ => TARGET,
        };
        let error = check_lean_export(input.as_bytes(), target).unwrap_err();
        assert!(error.message.contains(expected), "case {index}: {error}");
    }

    let duplicate_field = changed(
        "\"exporter\":{\"name\":\"lean4export\",\"version\":\"3.1.0\"}",
        "\"exporter\":{\"name\":\"lean4export\",\"version\":\"3.1.0\",\"extra\":0}",
    );
    assert!(check_lean_export(duplicate_field.as_bytes(), TARGET).is_err());

    let duplicate_id = FIXTURE.replacen(
        "{\"str\":{\"pre\":1,\"str\":\"identity\"},\"in\":2}\n",
        "{\"str\":{\"pre\":1,\"str\":\"identity\"},\"in\":1}\n{\"str\":{\"pre\":1,\"str\":\"identity\"},\"in\":2}\n",
        1,
    );
    let error = check_lean_export(duplicate_id.as_bytes(), TARGET).unwrap_err();
    assert!(error.message.contains("contiguous"), "{error}");
}

#[test]
fn cli_prints_the_exact_success_line_and_writes_the_json_report() {
    let scratch = support::Scratch::new("lean-export-cli");
    let input = scratch.path().join("identity.ndjson");
    let report = scratch.path().join("report.json");
    fs::write(&input, FIXTURE).unwrap();
    let (status, stdout, stderr) = support::run(
        Command::new(env!("CARGO_BIN_EXE_lim")).args([
            "--check-lean-export",
            input.to_str().unwrap(),
            TARGET,
            "--report",
            report.to_str().unwrap(),
        ]),
        Duration::from_secs(20),
        1024 * 1024,
    )
    .unwrap();
    assert!(status.success(), "{}", String::from_utf8_lossy(&stderr));
    assert_eq!(
        String::from_utf8(stdout).unwrap(),
        format!("checked Lean export theorem {TARGET} (2 declarations)\n")
    );
    assert!(stderr.is_empty());
    let receipt = fs::read_to_string(report).unwrap();
    assert!(receipt.contains(&format!("\"input_sha256\":\"{INPUT_SHA256}\"")));
}

#[test]
fn cli_failure_has_no_success_stdout_or_report_file() {
    let scratch = support::Scratch::new("lean-export-cli-invalid");
    let input = scratch.path().join("invalid.ndjson");
    let report = scratch.path().join("report.json");
    fs::write(
        &input,
        changed("\"safety\":\"safe\"", "\"safety\":\"unsafe\""),
    )
    .unwrap();
    let (status, stdout, stderr) = support::run(
        Command::new(env!("CARGO_BIN_EXE_lim")).args([
            "--check-lean-export",
            input.to_str().unwrap(),
            TARGET,
            "--report",
            report.to_str().unwrap(),
        ]),
        Duration::from_secs(20),
        1024 * 1024,
    )
    .unwrap();
    assert!(!status.success());
    assert!(stdout.is_empty());
    assert!(String::from_utf8_lossy(&stderr).contains("unsafe"));
    assert!(!report.exists());
}

#[test]
fn cli_reports_replay_timings_and_structured_errors() {
    let scratch = support::Scratch::new("lean-export-options");
    let input = scratch.path().join("identity.ndjson");
    fs::write(&input, FIXTURE).unwrap();
    let (status, stdout, stderr) = support::run(
        Command::new(env!("CARGO_BIN_EXE_lim")).args([
            "--check-lean-export",
            input.to_str().unwrap(),
            TARGET,
            "--timings",
        ]),
        Duration::from_secs(20),
        1024 * 1024,
    )
    .unwrap();
    assert!(status.success(), "{}", String::from_utf8_lossy(&stderr));
    assert!(!stdout.is_empty());
    assert!(String::from_utf8_lossy(&stderr).contains("lean_export_replay"));
    let (status, stdout, stderr) = support::run(
        Command::new(env!("CARGO_BIN_EXE_lim")).args([
            "--check-lean-export",
            input.to_str().unwrap(),
            "missing",
            "--diagnostic-format=json",
        ]),
        Duration::from_secs(20),
        1024 * 1024,
    )
    .unwrap();
    assert!(!status.success());
    assert!(stdout.is_empty());
    let diagnostic = lim::lsp::json::parse(std::str::from_utf8(&stderr).unwrap()).unwrap();
    assert!(diagnostic
        .get("message")
        .unwrap()
        .string()
        .unwrap()
        .contains("missing or ambiguous"));
}

#[test]
fn invalid_targets_and_report_destinations_cannot_publish_success() {
    let scratch = support::Scratch::new("lean-export-publication");
    let input = scratch.path().join("identity.ndjson");
    let report = scratch.path().join("receipt.json");
    fs::write(&input, FIXTURE).unwrap();
    fs::write(&report, "previous receipt").unwrap();
    for (target, destination) in [("missing", report.as_path()), (TARGET, scratch.path())] {
        let (status, stdout, stderr) = support::run(
            Command::new(env!("CARGO_BIN_EXE_lim")).args([
                "--check-lean-export",
                input.to_str().unwrap(),
                target,
                "--report",
                destination.to_str().unwrap(),
            ]),
            Duration::from_secs(20),
            1024 * 1024,
        )
        .unwrap();
        assert!(!status.success());
        assert!(stdout.is_empty());
        assert!(!stderr.is_empty());
        assert_eq!(fs::read_to_string(&report).unwrap(), "previous receipt");
        assert_eq!(fs::read_to_string(&input).unwrap(), FIXTURE);
    }
}

#[test]
fn structured_names_preserve_string_boundaries_and_numeric_components() {
    let additions = [
        "{\"str\":{\"pre\":0,\"str\":\"Audit.identity\"},\"in\":5}",
        "{\"num\":{\"pre\":1,\"i\":1},\"in\":6}",
        "{\"str\":{\"pre\":1,\"str\":\"[1]\"},\"in\":7}",
    ];
    let mut input = FIXTURE.to_owned();
    for row in additions {
        input.push_str(row);
        input.push('\n');
    }
    for name in 5..=7 {
        input.push_str(&format!("{{\"def\":{{\"name\":{name},\"levelParams\":[4],\"type\":4,\"value\":7,\"hints\":\"abbrev\",\"safety\":\"safe\",\"all\":[{name}]}}}}\n"));
    }
    let report = check_lean_export(input.as_bytes(), TARGET).unwrap();
    let identities = report
        .declarations
        .iter()
        .map(|decl| &decl.identity)
        .collect::<std::collections::HashSet<_>>();
    assert_eq!(identities.len(), 5);
    assert_ne!(report.declarations[0].name, report.declarations[2].name);
    assert_ne!(report.declarations[3].name, report.declarations[4].name);
}

#[test]
fn duplicate_json_keys_and_forward_expression_references_fail_before_replay() {
    let bad = changed(
        "\"format\":{\"version\":\"3.1.0\"}",
        "\"format\":{\"version\":\"3.1.0\"},\"format\":{\"version\":\"3.1.0\"}",
    );
    assert!(check_lean_export(bad.as_bytes(), TARGET)
        .unwrap_err()
        .message
        .contains("JSON"));
    let bad = changed(
        "{\"bvar\":0,\"ie\":1}",
        "{\"app\":{\"fn\":1,\"arg\":0},\"ie\":1}",
    );
    assert!(check_lean_export(bad.as_bytes(), TARGET)
        .unwrap_err()
        .message
        .contains("earlier record"));
}

#[test]
fn an_unbounded_input_line_is_stopped_before_unbounded_allocation() {
    let header = FIXTURE.lines().next().unwrap().to_owned() + "\n";
    let stream = std::io::Cursor::new(header.into_bytes()).chain(std::io::repeat(b' '));
    let input = std::io::BufReader::with_capacity(64, stream);
    let error = check_lean_export(input, TARGET).unwrap_err();
    assert_eq!(error.line, 2);
    assert!(error.message.contains("line byte limit"), "{error}");
}

#[test]
fn unused_deep_expression_graphs_are_rejected_without_recursive_cleanup_overflow() {
    let mut input = FIXTURE.to_owned();
    for id in 20..=300 {
        input.push_str(&format!(
            "{{\"app\":{{\"fn\":{},\"arg\":0}},\"ie\":{id}}}\n",
            id - 1
        ));
    }
    let error = check_lean_export(input.as_bytes(), TARGET).unwrap_err();
    assert!(error.message.contains("expression depth limit"), "{error}");
}

#[test]
fn an_input_read_error_after_the_target_still_rejects_the_export() {
    struct BrokenTail;
    impl Read for BrokenTail {
        fn read(&mut self, _: &mut [u8]) -> std::io::Result<usize> {
            Err(std::io::Error::other("test read failure"))
        }
    }
    let input = std::io::BufReader::new(std::io::Cursor::new(FIXTURE.as_bytes()).chain(BrokenTail));
    let error = check_lean_export(input, TARGET).unwrap_err();
    assert_eq!(error.line, 29);
    assert!(error.message.contains("test read failure"), "{error}");
}

#[cfg(unix)]
#[test]
fn cli_report_cannot_overwrite_a_hard_link_to_its_input() {
    let scratch = support::Scratch::new("lean-export-hardlink");
    let input = scratch.path().join("proof.ndjson");
    let output = scratch.path().join("receipt.json");
    fs::write(&input, FIXTURE).unwrap();
    fs::hard_link(&input, &output).unwrap();
    let (status, stdout, stderr) = support::run(
        Command::new(env!("CARGO_BIN_EXE_lim")).args([
            "--check-lean-export",
            input.to_str().unwrap(),
            TARGET,
            "--report",
            output.to_str().unwrap(),
        ]),
        Duration::from_secs(20),
        1024 * 1024,
    )
    .unwrap();
    assert!(!status.success());
    assert!(stdout.is_empty());
    assert!(!stderr.is_empty());
    assert_eq!(fs::read_to_string(input).unwrap(), FIXTURE);
    assert_eq!(fs::read_to_string(output).unwrap(), FIXTURE);
}

#[test]
fn previously_checked_syntax_is_rechecked_under_each_declarations_universes() {
    // Both roots are still owned by the checked polymorphic definition. Reusing
    // their syntax cannot carry that declaration's universe authorization.
    let source = format!("{FIXTURE}\
{{\"in\":5,\"str\":{{\"pre\":1,\"str\":\"badScope\"}}}}\n\
{{\"def\":{{\"name\":5,\"levelParams\":[],\"type\":4,\"value\":7,\"hints\":\"abbrev\",\"safety\":\"safe\",\"all\":[5]}}}}\n");
    let error = check_lean_export(source.as_bytes(), TARGET).unwrap_err();
    assert_eq!(error.line, FIXTURE.lines().count() + 2);
    assert!(
        error.message.contains("undeclared universe"),
        "{}",
        error.message
    );
}

#[test]
fn a_previous_theorem_body_is_rechecked_against_a_changed_statement() {
    let source = format!(
        "{FIXTURE}\
{{\"in\":5,\"str\":{{\"pre\":1,\"str\":\"badType\"}}}}\n\
{{\"ie\":20,\"forallE\":{{\"name\":0,\"type\":8,\"body\":9,\"binderInfo\":\"default\"}}}}\n\
{{\"thm\":{{\"name\":5,\"levelParams\":[],\"type\":20,\"value\":19,\"all\":[5]}}}}\n"
    );
    let error = check_lean_export(source.as_bytes(), TARGET).unwrap_err();
    assert_eq!(error.line, FIXTURE.lines().count() + 3);
    assert!(error.message.contains("type mismatch"), "{}", error.message);
    assert!(
        !error.message.contains("resource limit"),
        "{}",
        error.message
    );
}

#[test]
fn an_unused_natural_literal_still_requires_the_checked_standard_family() {
    let source = format!("{FIXTURE}{{\"ie\":20,\"natVal\":\"0\"}}\n");
    let error = check_lean_export(source.as_bytes(), TARGET).unwrap_err();
    assert!(
        error.message.contains("Nat literals require"),
        "{}",
        error.message
    );
}

#[test]
fn long_metadata_chains_keep_backward_ids_without_deep_materialization() {
    let mut source = FIXTURE.to_owned();
    for id in 20..4116 {
        source.push_str(&format!(
            "{{\"ie\":{id},\"mdata\":{{\"expr\":{},\"data\":{{}}}}}}\n",
            id - 1
        ));
    }
    source.push_str("{\"in\":5,\"str\":{\"pre\":1,\"str\":\"aliasProof\"}}\n");
    source.push_str(
        "{\"thm\":{\"name\":5,\"levelParams\":[],\"type\":12,\"value\":4115,\"all\":[5]}}\n",
    );
    let report = check_lean_export(source.as_bytes(), "Audit.aliasProof").unwrap();
    assert_eq!(report.declarations.len(), 3);
    assert!(report.axioms.is_empty());
    let translated = lim::translate_lean_export(source.as_bytes(), "Audit.aliasProof").unwrap();
    assert_eq!(translated.report.input_sha256, report.input_sha256);
}
