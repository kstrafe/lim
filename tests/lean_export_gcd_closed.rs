//! Original closed `Nat.gcd 84 30 = 6 := rfl`, replayed without axioms.
mod support;

use lim::{
    check_lean_export_with_budget,
    lsp::json::{self, Json},
    translate_lean_export_with_budget, CompileConfig, Expr, LeanExportReport, LeanFoundationPolicy,
    ProofBudget, SpannedExpr,
};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
    process::Command,
    sync::OnceLock,
    time::Duration,
};

const TARGET: &str = "GcdProbe.closed";
const NATIVE_TARGET: &str = "lean-250-GcdProbe-closed";
const RAW_PATH: &str = "tests/fixtures/lean_export_gcd_closed/gcd-closed.ndjson";
const NATIVE_PATH: &str = "theorems/lean_replay/gcd-closed.lim";
const SHA256: &str = "76980f212b359452b3390ad0a75b8f10cd96998fc2d2839bb35348d792c19604";
const POLICY: LeanFoundationPolicy = LeanFoundationPolicy::Constructive;

fn budget() -> ProofBudget {
    ProofBudget::new(20_000_000, 1_073_741_824, 2_147_483_648).unwrap()
}

fn config(budget: ProofBudget) -> CompileConfig {
    let mut config = CompileConfig::default();
    config.set_proof_budget(budget);
    config
}

fn path(relative: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(relative)
}

struct Fixture {
    raw: String,
    native: String,
    provenance: Json,
    report: LeanExportReport,
}

fn fixture() -> &'static Fixture {
    static FIXTURE: OnceLock<Fixture> = OnceLock::new();
    FIXTURE.get_or_init(|| {
        // Runtime reads allow the fixture producer to land independently.
        let raw = fs::read_to_string(path(RAW_PATH)).expect("original closed GCD export");
        let native = fs::read_to_string(path(NATIVE_PATH)).expect("closed GCD native translation");
        let provenance = json::parse(
            &fs::read_to_string(path(
                "tests/fixtures/lean_export_gcd_closed/provenance.json",
            ))
            .expect("closed GCD provenance"),
        )
        .unwrap();
        let report =
            check_lean_export_with_budget(raw.as_bytes(), TARGET, POLICY, budget()).unwrap();
        Fixture {
            raw,
            native,
            provenance,
            report,
        }
    })
}

fn rows(source: &str) -> Vec<Json> {
    source
        .lines()
        .map(|line| json::parse(line).unwrap())
        .collect()
}

fn object(value: &mut Json) -> &mut BTreeMap<String, Json> {
    let Json::Object(fields) = value else {
        panic!("expected JSON object")
    };
    fields
}

fn field<'a>(value: &'a mut Json, name: &str) -> &'a mut Json {
    object(value).get_mut(name).unwrap()
}

fn render(data: &[Json]) -> String {
    data.iter().map(Json::render).collect::<Vec<_>>().join("\n") + "\n"
}

fn assert_empty_inventories(report: &Json) {
    for key in ["axioms", "target_axioms", "foundations"] {
        assert!(
            report.get(key).and_then(Json::array).unwrap().is_empty(),
            "{key}"
        );
    }
}

fn assert_type_mismatch(message: &str) {
    assert!(message.contains("type mismatch"), "{message}");
    assert!(!message.contains("resource limit"), "{message}");
    assert!(!message.contains("work limit"), "{message}");
}

fn named_node<'a>(nodes: &'a [SpannedExpr], name: &str) -> &'a SpannedExpr {
    nodes
        .iter()
        .find(|node| {
            matches!(&node.expr, Expr::List(items)
            if matches!(items.get(1), Some(Expr::Symbol(found)) if found == name))
        })
        .unwrap_or_else(|| panic!("missing native declaration {name}"))
}

fn has_head(node: &SpannedExpr, head: &str) -> bool {
    matches!(&node.expr, Expr::List(items)
        if matches!(items.first(), Some(Expr::Symbol(found)) if found == head))
}

fn clause<'a>(node: &'a SpannedExpr, head: &str) -> &'a SpannedExpr {
    node.children
        .iter()
        .find(|child| has_head(child, head))
        .unwrap()
}

#[test]
fn original_export_provenance_and_exact_native_translation_are_axiom_free() {
    let f = fixture();
    let report = &f.report;
    assert_eq!(report.target, TARGET);
    assert_eq!(report.budget, budget());
    assert_eq!(report.bytes, 450_075);
    assert_eq!(report.records, 8_342);
    assert_eq!(report.declarations.len(), 251);
    assert_eq!(report.input_sha256, SHA256);
    assert!(report.axioms.is_empty());
    assert!(report.target_axioms.is_empty());
    assert!(report.foundations.is_empty());

    let provenance = &f.provenance;
    assert_empty_inventories(provenance);
    assert_eq!(
        provenance.get("schema").and_then(Json::string),
        Some("lim-lean-gcd-closed-fixture-v1")
    );
    assert_eq!(
        provenance
            .get("source")
            .unwrap()
            .get("sha256")
            .and_then(Json::string),
        Some("3e81aa542e780a7bc92ed70de4eddb61ee231bc88719b3cc18688190ed7d3560")
    );
    let export = provenance.get("export").unwrap();
    assert_eq!(export.get("file").and_then(Json::string), Some(RAW_PATH));
    assert_eq!(export.get("sha256").and_then(Json::string), Some(SHA256));
    assert_eq!(
        export.get("bytes").and_then(Json::integer),
        Some(f.raw.len() as i64)
    );
    let receipt = json::parse(&report.render_json()).unwrap();
    for key in ["lean_version", "exporter_revision", "format_version"] {
        assert_eq!(provenance.get(key), receipt.get(key), "{key}");
    }
    assert_eq!(provenance.get("lean_revision"), receipt.get("lean_githash"));
    assert_eq!(provenance.get("proof_budget"), receipt.get("proof_budget"));
    let expected = provenance
        .get("declarations")
        .and_then(Json::array)
        .unwrap();
    assert_eq!(expected.len(), report.declarations.len());
    let nodes = lim::parse(&f.native).unwrap();
    assert_eq!(nodes.len(), 251);
    for (actual, expected) in report.declarations.iter().zip(expected) {
        assert_eq!(
            expected.get("name").and_then(Json::string),
            Some(actual.name.as_str())
        );
        assert_eq!(
            expected.get("identity").and_then(Json::string),
            Some(actual.identity.as_str())
        );
        assert_eq!(
            expected.get("kind").and_then(Json::string),
            Some(actual.kind.as_str())
        );
        assert_eq!(
            expected.get("line").and_then(Json::integer),
            Some(actual.line as i64)
        );
        assert_eq!(
            expected.get("sha256").and_then(Json::string),
            Some(actual.sha256.as_str())
        );
        let dependencies = expected.get("dependencies").and_then(Json::array).unwrap();
        assert_eq!(
            dependencies
                .iter()
                .map(|v| v.string().unwrap())
                .collect::<Vec<_>>(),
            actual.dependencies
        );
        let native_name = expected.get("native_name").and_then(Json::string).unwrap();
        named_node(&nodes, native_name);
    }
    let native_manifest = provenance.get("native").unwrap();
    assert_eq!(
        native_manifest.get("file").and_then(Json::string),
        Some(NATIVE_PATH)
    );
    assert_eq!(
        native_manifest.get("bytes").and_then(Json::integer),
        Some(f.native.len() as i64)
    );
    assert_eq!(
        native_manifest
            .get("targets")
            .unwrap()
            .get(TARGET)
            .and_then(Json::string),
        Some(NATIVE_TARGET)
    );
    let target = report.declarations.last().unwrap();
    assert_eq!(target.name, TARGET);
    assert_eq!(target.sha256, SHA256);

    let translated =
        translate_lean_export_with_budget(f.raw.as_bytes(), TARGET, POLICY, budget()).unwrap();
    assert_eq!(translated.target, NATIVE_TARGET);
    assert_eq!(translated.report.declarations, report.declarations);
    assert!(
        translated.source == f.native,
        "native translation differs from original export"
    );
    let checked = lim::check_theorem_details_from_path_with_config(
        &f.native,
        &path(NATIVE_PATH),
        &config(budget()),
        NATIVE_TARGET,
    )
    .unwrap();
    assert_eq!(checked.name, NATIVE_TARGET);
    assert_eq!(checked.budget, budget());
    assert!(checked.foundations.is_empty());
}

#[test]
fn ordinary_helper_name_components_preserve_the_semantic_proof() {
    let f = fixture();
    let mut data = rows(&f.raw);
    let replacements = [
        ("gcd", "ordinaryOperation"),
        ("_unary", "packedWorker"),
        ("fix", "recursiveDriver"),
        ("go", "recursiveStep"),
    ];
    let mut counts = [0; 4];
    for row in &mut data {
        let Some(name) = object(row).get_mut("str") else {
            continue;
        };
        let part = field(name, "str");
        for (index, (old, new)) in replacements.iter().enumerate() {
            if part.string() == Some(*old) {
                *part = Json::String((*new).into());
                counts[index] += 1;
                break;
            }
        }
    }
    assert!(
        counts.iter().all(|count| *count > 0),
        "missing helper components: {counts:?}"
    );
    let renamed = render(&data);
    let report =
        check_lean_export_with_budget(renamed.as_bytes(), TARGET, POLICY, budget()).unwrap();
    assert_eq!(report.target, TARGET);
    assert_eq!(report.declarations.len(), f.report.declarations.len());
    assert_eq!(report.budget, budget());
    assert_empty_inventories(&json::parse(&report.render_json()).unwrap());
    assert!(report
        .declarations
        .iter()
        .any(|d| d.name == "Nat.ordinaryOperation.packedWorker"));
    assert!(report
        .declarations
        .iter()
        .any(|d| d.name == "WellFounded.Nat.recursiveDriver"));
}

#[test]
fn unchanged_default_budgets_check_both_axiom_free_representations() {
    let f = fixture();
    let report =
        check_lean_export_with_budget(f.raw.as_bytes(), TARGET, POLICY, ProofBudget::default())
            .unwrap();
    assert_eq!(report.budget, ProofBudget::default());
    assert_empty_inventories(&json::parse(&report.render_json()).unwrap());
    let checked = lim::check_theorem_details_from_path_with_config(
        &f.native,
        &path(NATIVE_PATH),
        &CompileConfig::default(),
        NATIVE_TARGET,
    )
    .unwrap();
    assert_eq!(checked.budget, ProofBudget::default());
    assert!(checked.foundations.is_empty());
}

#[test]
fn corrupted_raw_worker_body_and_target_proof_fail_at_selected_declarations() {
    let f = fixture();
    for name in ["Nat.gcd._unary", TARGET] {
        let declaration = f
            .report
            .declarations
            .iter()
            .find(|d| d.name == name)
            .unwrap();
        let mut data = rows(&f.raw);
        let at = declaration.line - 1;
        let wrong = data[..at]
            .iter()
            .find_map(|row| {
                (row.get("sort").and_then(Json::integer) == Some(0))
                    .then(|| row.get("ie").unwrap().clone())
            })
            .expect("existing closed Prop sort in the valid prefix");
        let key = if name == TARGET { "thm" } else { "def" };
        *field(field(&mut data[at], key), "value") = wrong;
        let error =
            check_lean_export_with_budget(render(&data).as_bytes(), TARGET, POLICY, budget())
                .unwrap_err();
        assert_eq!(error.line, declaration.line, "{error}");
        assert_type_mismatch(&error.message);
    }
}

// Resolve expression identities rather than replacing decimal text or export IDs.
fn expression<'a>(data: &'a [Json], id: &Json) -> &'a Json {
    data.iter()
        .find(|row| row.get("ie") == Some(id))
        .expect("expression identity")
}

fn application_closure(data: &[Json], id: &Json, found: &mut BTreeSet<i64>) {
    if !found.insert(id.integer().unwrap()) {
        return;
    }
    if let Some(app) = expression(data, id).get("app") {
        application_closure(data, app.get("fn").unwrap(), found);
        application_closure(data, app.get("arg").unwrap(), found);
    }
}

#[test]
fn changed_raw_closed_result_keeps_the_original_rfl_proof_and_fails_at_target() {
    let f = fixture();
    let mut data = rows(&f.raw);
    let target = f
        .report
        .declarations
        .iter()
        .find(|d| d.name == TARGET)
        .unwrap();
    let thm = data[target.line - 1].get("thm").unwrap();
    let result = expression(&data, thm.get("type").unwrap())
        .get("app")
        .unwrap()
        .get("arg")
        .unwrap();
    let mut result_ids = BTreeSet::new();
    application_closure(&data, result, &mut result_ids);
    let mut proof_ids = BTreeSet::new();
    application_closure(&data, thm.get("value").unwrap(), &mut proof_ids);
    let candidates = data
        .iter()
        .enumerate()
        .filter_map(|(index, row)| {
            let id = row.get("ie")?.integer()?;
            (result_ids.contains(&id) && row.get("natVal").and_then(Json::string) == Some("6"))
                .then_some((index, id))
        })
        .collect::<Vec<_>>();
    assert_eq!(candidates.len(), 1, "the closed equality's result literal");
    let (index, id) = candidates[0];
    assert!(
        !proof_ids.contains(&id),
        "result mutation must preserve the proof DAG"
    );
    *field(&mut data[index], "natVal") = Json::String("7".into());
    let error = check_lean_export_with_budget(render(&data).as_bytes(), TARGET, POLICY, budget())
        .unwrap_err();
    assert_eq!(error.line, target.line, "{error}");
    assert_type_mismatch(&error.message);
}

fn literal_spans(node: &SpannedExpr, spans: &mut Vec<lim::Span>) {
    if has_head(node, "#pt-nat-literal") {
        assert!(matches!(&node.children[2].expr, Expr::String(value) if value == "6"));
        spans.push(node.children[2].span);
    }
    for child in &node.children {
        literal_spans(child, spans);
    }
}

#[test]
fn native_target_mutations_are_selected_by_ast_and_fail_after_a_valid_prefix() {
    let f = fixture();
    let nodes = lim::parse(&f.native).unwrap();
    let theorem = named_node(&nodes, NATIVE_TARGET);
    assert!(has_head(theorem, "#theorem"));
    lim::check_types(
        &lim::parse_program_with_config(&f.native[..theorem.span.start], &config(budget()))
            .unwrap(),
    )
    .unwrap();
    let proof = &clause(theorem, "#proof").children[1];
    let statement = &clause(theorem, "#statement").children[1];
    assert!(has_head(statement, "#pt-app"));
    // The last equality argument is the result, including both OfNat literals.
    let result = statement.children.last().unwrap();
    let mut spans = Vec::new();
    literal_spans(result, &mut spans);
    assert_eq!(spans.len(), 2);
    let mut changed_result = f.native.clone();
    for span in spans.iter().rev() {
        changed_result.replace_range(span.start..span.end, "\"7\"");
    }
    let changed_nodes = lim::parse(&changed_result).unwrap();
    assert_eq!(
        clause(named_node(&changed_nodes, NATIVE_TARGET), "#proof").expr,
        clause(theorem, "#proof").expr
    );
    let mut changed_proof = f.native.clone();
    changed_proof.replace_range(proof.span.start..proof.span.end, "#pt-prop");
    for changed in [&changed_proof, &changed_result] {
        assert_eq!(
            &changed[..theorem.span.start],
            &f.native[..theorem.span.start]
        );
        let error = lim::check_theorem_details_from_path_with_config(
            changed,
            &path(NATIVE_PATH),
            &config(budget()),
            NATIVE_TARGET,
        )
        .unwrap_err();
        assert_eq!(error.code, lim::DiagnosticCode::Proof);
        assert!(error.message.contains(NATIVE_TARGET), "{}", error.message);
        assert_type_mismatch(&error.message);
    }
}

#[test]
fn explicit_small_work_and_transformation_limits_are_enforced() {
    let f = fixture();
    // Each dimension is lowered independently; the successful explicit budget
    // is covered above, without assuming anything about the defaults.
    for (limited, cause) in [
        (
            ProofBudget::new(1, budget().phase_bytes(), budget().total_bytes()).unwrap(),
            "work units",
        ),
        (
            ProofBudget::new(budget().work(), 1, budget().total_bytes()).unwrap(),
            "allocation limit",
        ),
        (
            ProofBudget::new(budget().work(), budget().phase_bytes(), 1).unwrap(),
            "cumulative",
        ),
    ] {
        let error =
            check_lean_export_with_budget(f.raw.as_bytes(), TARGET, POLICY, limited).unwrap_err();
        assert!(error.message.contains(cause), "{error}");
        let error = lim::check_theorem_details_from_path_with_config(
            &f.native,
            &path(NATIVE_PATH),
            &config(limited),
            NATIVE_TARGET,
        )
        .unwrap_err();
        assert_eq!(error.code, lim::DiagnosticCode::Proof);
        assert!(error.message.contains(cause), "{}", error.message);
    }
}

#[test]
fn cli_checks_with_empty_path_and_writes_an_axiom_free_json_audit() {
    let f = fixture();
    let scratch = support::Scratch::new("gcd-closed-cli");
    let audit_path = scratch.path().join("audit.json");
    let proof_path = scratch.path().join("closed.lim");
    let budget_args = [
        "--proof-work",
        "20000000",
        "--proof-phase-bytes",
        "1073741824",
        "--proof-total-bytes",
        "2147483648",
    ];
    let budget_line = "proof budget: work=20000000 phase-bytes=1073741824 total-bytes=2147483648";
    let mut command = Command::new(env!("CARGO_BIN_EXE_lim"));
    command
        .env("PATH", "")
        .arg("--check-lean-export")
        .arg(path(RAW_PATH))
        .arg(TARGET)
        .arg("--report")
        .arg(&audit_path)
        .arg("--emit-proof")
        .arg(&proof_path)
        .args(budget_args);
    let (status, stdout, stderr) =
        support::run(&mut command, Duration::from_secs(180), 65536).unwrap();
    assert!(status.success(), "{}", String::from_utf8_lossy(&stderr));
    assert!(stderr.is_empty(), "{}", String::from_utf8_lossy(&stderr));
    assert_eq!(
        String::from_utf8(stdout)
            .unwrap()
            .lines()
            .collect::<Vec<_>>(),
        [
            format!("checked Lean export theorem {TARGET} (251 declarations)"),
            budget_line.into(),
            format!(
                "emitted native theorem {NATIVE_TARGET} to {}",
                proof_path.display()
            ),
        ]
    );
    let audit = json::parse(&fs::read_to_string(&audit_path).unwrap()).unwrap();
    assert_empty_inventories(&audit);
    assert_eq!(audit, json::parse(&f.report.render_json()).unwrap());
    assert!(
        fs::read_to_string(&proof_path).unwrap() == f.native,
        "CLI native translation differs"
    );

    let mut command = Command::new(env!("CARGO_BIN_EXE_lim"));
    command
        .env("PATH", "")
        .arg("--check-theorem")
        .arg(&proof_path)
        .arg(NATIVE_TARGET)
        .args(budget_args);
    let (status, stdout, stderr) =
        support::run(&mut command, Duration::from_secs(180), 65536).unwrap();
    assert!(status.success(), "{}", String::from_utf8_lossy(&stderr));
    assert!(stderr.is_empty(), "{}", String::from_utf8_lossy(&stderr));
    assert_eq!(
        String::from_utf8(stdout)
            .unwrap()
            .lines()
            .collect::<Vec<_>>(),
        [
            format!("checked theorem {NATIVE_TARGET}"),
            budget_line.into(),
        ]
    );
}
