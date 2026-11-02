use lim::{check_lean_export, lsp::json::Json, LeanExportReport};
use std::{
    collections::BTreeMap,
    io::{self, Write},
};

fn text(value: &str) -> Json {
    Json::String(value.to_owned())
}
fn number(value: impl ToString) -> Json {
    Json::Number(value.to_string())
}
fn strings(values: &[String]) -> Json {
    Json::Array(values.iter().map(|value| text(value)).collect())
}
fn object(values: impl IntoIterator<Item = (&'static str, Json)>) -> Json {
    Json::Object(
        values
            .into_iter()
            .map(|(key, value)| (key.to_owned(), value))
            .collect::<BTreeMap<_, _>>(),
    )
}

// The previous general-purpose JSON tree renderer is an independent reference
// for schema contents, key order, escaping and decimal representations.
fn reference(report: &LeanExportReport) -> String {
    object([
        ("schema", text("lim-lean-replay-v1")),
        (
            "proof_budget",
            object([
                ("work_per_phase", number(report.budget.work())),
                (
                    "transformation_bytes_per_phase",
                    number(report.budget.phase_bytes()),
                ),
                (
                    "transformation_bytes_total",
                    number(report.budget.total_bytes()),
                ),
            ]),
        ),
        ("target", text(&report.target)),
        ("input_sha256", text(&report.input_sha256)),
        ("bytes", number(report.bytes)),
        ("records", number(report.records)),
        ("lean_version", text("4.33.1")),
        (
            "lean_githash",
            text("819816b2e0a3bf405af45ae5c7af2491d8f5bee6"),
        ),
        ("format_version", text("3.1.0")),
        (
            "exporter_revision",
            text("15f6055e299ad5b89345e533cc2192f4cc00f659"),
        ),
        (
            "declaration_hash_scope",
            text("export-prefix-through-record"),
        ),
        ("axioms", strings(&report.axioms)),
        ("target_axioms", strings(&report.target_axioms)),
        ("foundations", strings(&report.foundations)),
        (
            "declarations",
            Json::Array(
                report
                    .declarations
                    .iter()
                    .map(|declaration| {
                        object([
                            ("name", text(&declaration.name)),
                            ("identity", text(&declaration.identity)),
                            ("kind", text(&declaration.kind)),
                            ("line", number(declaration.line)),
                            ("sha256", text(&declaration.sha256)),
                            ("dependencies", strings(&declaration.dependencies)),
                        ])
                    })
                    .collect(),
            ),
        ),
    ])
    .render()
}

fn report() -> LeanExportReport {
    check_lean_export(
        include_bytes!("fixtures/lean_export/identity.ndjson").as_slice(),
        "Audit.identity.theorem",
    )
    .unwrap()
}

struct Chunks {
    bytes: Vec<u8>,
    fail_after: Option<usize>,
    errors: usize,
}
impl Write for Chunks {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        if self
            .fail_after
            .is_some_and(|limit| self.bytes.len() >= limit)
        {
            self.errors += 1;
            return Err(io::Error::new(io::ErrorKind::BrokenPipe, "injected"));
        }
        let count = bytes.len().min(3).min(
            self.fail_after
                .map_or(usize::MAX, |limit| limit - self.bytes.len()),
        );
        self.bytes.extend_from_slice(&bytes[..count]);
        Ok(count)
    }
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

#[test]
fn streamed_receipts_match_the_previous_json_tree_byte_for_byte() {
    let original = report();
    let mut changed = original.clone();
    changed.target = "target\n\"é🦀\\\0".into();
    changed.axioms = vec!["quoted\"axiom".into()];
    changed.target_axioms = vec!["\u{1f}basis".into()];
    changed.foundations = vec!["é-foundation".into()];
    changed.declarations[0].name = "name\r\t\u{8}".into();
    changed.declarations[0]
        .dependencies
        .push("line\nbreak\\dependency".into());
    changed.bytes = u64::MAX;
    changed.records = u64::MAX;
    changed.budget = lim::ProofBudget::new(1, 2, 3).unwrap();
    let mut empty = original.clone();
    empty.declarations.clear();
    for report in [original, changed, empty] {
        let expected = reference(&report);
        assert_eq!(report.render_json(), expected);
        let mut writer = Chunks {
            bytes: Vec::new(),
            fail_after: None,
            errors: 0,
        };
        report.write_json(&mut writer).unwrap();
        assert_eq!(writer.bytes, expected.as_bytes());
        assert_eq!(writer.errors, 0);
    }
}

#[test]
fn streamed_receipts_propagate_writer_errors_without_continuing() {
    let report = report();
    let expected = reference(&report);
    for limit in [0, 1, 73, expected.len() - 1] {
        let mut writer = Chunks {
            bytes: Vec::new(),
            fail_after: Some(limit),
            errors: 0,
        };
        assert_eq!(
            report.write_json(&mut writer).unwrap_err().kind(),
            io::ErrorKind::BrokenPipe
        );
        assert_eq!(writer.errors, 1);
        assert_eq!(writer.bytes, expected.as_bytes()[..limit]);
    }
}
