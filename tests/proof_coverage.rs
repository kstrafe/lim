//! Coverage warnings supplement, rather than redefine, universal contracts.
use lim::{CompileConfig, Diagnostic, DiagnosticCode, DiagnosticSeverity, ProofOutcome};
use std::path::Path;
mod support;

const IDENTITY: &str = "(#fn identity (: value #u8) #u8 (#return value))";

fn check(
    source: &str,
    path: &Path,
    name: &str,
) -> (Result<lim::CheckedTheorem, Diagnostic>, Vec<Diagnostic>) {
    lim::with_warnings(|| {
        lim::check_theorem_details_from_path_with_config(
            source,
            path,
            &CompileConfig::default(),
            name,
        )
    })
}

fn warnings(source: &str) -> Vec<Diagnostic> {
    let (result, warnings) = check(source, Path::new("coverage.lim"), "claim");
    assert_eq!(result.unwrap().outcome, ProofOutcome::Proved);
    warnings
        .into_iter()
        .filter(|warning| warning.code == DiagnosticCode::ProofVacuous)
        .collect()
}

#[test]
fn contradictory_preconditions_are_warned_without_changing_universal_logic() {
    for predicate in [
        "false",
        "(#u8::gt value 255u8)",
        "(#bool::and (#u8::lt value 10u8) (#u8::ge value 10u8))",
    ] {
        let source =
            format!("{IDENTITY}\n(#theorem claim (#proof-contract identity {predicate} false))");
        let warnings = warnings(&source);
        assert_eq!(warnings.len(), 1, "{warnings:?}");
        let warning = &warnings[0];
        assert_eq!(warning.severity, DiagnosticSeverity::Warning);
        assert_eq!(warning.proof_outcome(), None);
        assert!(warning.code.is_proof());
        assert!(warning.message.contains("precondition is unsatisfiable"));
        let span = warning.span.unwrap();
        assert_eq!(&source[span.start..span.end], predicate);
        assert!(warning
            .notes
            .iter()
            .any(|note| note.contains("no execution behavior")));
    }
}

#[test]
fn one_feasible_precondition_branch_prevents_a_vacuity_warning() {
    for predicate in [
        "true",
        "(#u8::eq value 255u8)",
        "(#if (#u8::lt value 128u8) false (#u8::eq value 200u8))",
    ] {
        let source = format!("{IDENTITY}\n(#theorem claim (#proof-contract identity {predicate} (#proof-eq (#proof-result) value)))");
        assert!(warnings(&source).is_empty());
    }
}

#[test]
fn an_infeasible_enclosing_guard_is_distinguished_from_an_impossible_precondition() {
    let source = format!(
        "{IDENTITY}\n(#theorem claim (#proof-implies false (#proof-contract identity true false)))"
    );
    let warnings = warnings(&source);
    assert_eq!(warnings.len(), 1);
    assert!(warnings[0]
        .message
        .contains("enclosing proof path is infeasible"));
    assert!(!warnings[0]
        .message
        .contains("precondition is unsatisfiable"));
}

#[test]
fn separate_source_clauses_keep_separate_precise_warnings() {
    let source = format!("{IDENTITY}\n(#theorem claim (#proof-and\n (#proof-contract identity false false)\n (#proof-contract identity false false)))");
    let warnings = warnings(&source);
    assert_eq!(warnings.len(), 2, "{warnings:?}");
    let first = warnings[0].span.unwrap();
    let second = warnings[1].span.unwrap();
    assert_ne!(first, second);
    assert_eq!(first.line, 3);
    assert_eq!(second.line, 4);
    for span in [first, second] {
        assert_eq!(&source[span.start..span.end], "false");
    }
}

#[test]
fn a_failed_theorem_discards_all_provisional_coverage_warnings() {
    for source in [
        format!("{IDENTITY} (#theorem claim (#proof-not (#proof-contract identity false false)))"),
        format!("{IDENTITY} (#theorem vacuous (#proof-contract identity false false)) (#theorem claim false)"),
        format!("{IDENTITY} (#theorem claim (#proof-and (#proof-contract identity false false) false))"),
    ] {
        let (result, warnings) = check(&source, Path::new("coverage.lim"), "claim");
        assert_eq!(result.unwrap_err().proof_outcome(), Some(ProofOutcome::Counterexample));
        assert!(warnings.is_empty(), "{warnings:?}");
    }
}

#[test]
fn negated_nonvacuous_false_contracts_do_not_report_empty_input_domains() {
    let source =
        format!("{IDENTITY} (#theorem claim (#proof-not (#proof-contract identity true false)))");
    assert!(warnings(&source).is_empty());
}

#[test]
fn aliased_module_theorems_report_the_authored_precondition() {
    let scratch = support::Scratch::new("proof-coverage-alias");
    let module = scratch.path().join("module.lim");
    let source = format!("{IDENTITY}\n(#theorem original (#proof-contract identity false false))");
    std::fs::write(&module, &source).unwrap();
    let entry = scratch.path().join("main.lim");
    let root = "(#alias claim = ./module.lim::original)";
    std::fs::write(&entry, root).unwrap();
    for _ in 0..2 {
        let (result, warnings) = check(root, &entry, "claim");
        result.unwrap();
        assert_eq!(warnings.len(), 1);
        assert_eq!(warnings[0].source_name.as_deref(), module.to_str());
        let span = warnings[0].span.unwrap();
        assert_eq!(&source[span.start..span.end], "false");
        assert_eq!(span.line, 2);
    }
}

#[test]
fn generated_coverage_warnings_are_recomputed_on_cold_and_warm_caches() {
    let scratch = support::Scratch::new("proof-coverage-generated");
    let source = "(#gn emit () `((#fn generated (: value #u8) #u8 (#return value))\n (#theorem claim (#proof-contract generated false false))))\n(#generate emit)";
    let path = scratch.path().join("main.lim");
    std::fs::write(&path, source).unwrap();
    let mut previous = None;
    for _ in 0..2 {
        let (result, warnings) = check(source, &path, "claim");
        result.unwrap();
        assert_eq!(warnings.len(), 1);
        let warning = &warnings[0];
        let span = warning.span.unwrap();
        assert_eq!(
            &warning.source_text.as_ref().unwrap()[span.start..span.end],
            "false"
        );
        assert!(warning.source_name.as_ref().unwrap().contains(".lim"));
        assert!(!warning.expansion_provenance.is_empty(), "{warning:?}");
        if let Some(previous) = previous {
            assert_eq!(warnings, previous);
        }
        previous = Some(warnings);
    }
}

#[test]
fn warning_sessions_do_not_leak_between_checks() {
    let source = format!("{IDENTITY} (#theorem claim (#proof-contract identity false false))");
    let ((inner_result, inner_warnings), outer_warnings) = lim::with_warnings(|| {
        let result = check(&source, Path::new("coverage.lim"), "claim");
        let source = format!("{IDENTITY} (#theorem claim (#proof-contract identity true true))");
        lim::check_theorem_details_from_path_with_config(
            &source,
            Path::new("coverage.lim"),
            &CompileConfig::default(),
            "claim",
        )
        .unwrap();
        result
    });
    inner_result.unwrap();
    assert_eq!(inner_warnings.len(), 1);
    assert!(outer_warnings.is_empty());
}

#[test]
fn oversized_clause_tracking_fails_closed_even_under_negation() {
    let clauses = "(#proof-contract identity false false) ".repeat(1025);
    for body in [
        format!("(#proof-and {clauses})"),
        format!("(#proof-not (#proof-and {clauses} false))"),
    ] {
        let source = format!("{IDENTITY} (#theorem claim {body})");
        let (result, warnings) = check(&source, Path::new("coverage.lim"), "claim");
        let error = result.unwrap_err();
        assert_eq!(error.proof_outcome(), Some(ProofOutcome::ResourceLimit));
        assert!(
            error.message.contains("coverage exceeds 1024"),
            "{}",
            error.message
        );
        assert!(warnings.is_empty());
    }
}

#[test]
fn diagnostic_storage_is_bounded_across_all_theorems_before_source_cloning() {
    let mut source = IDENTITY.to_owned();
    for index in 0..700 {
        source.push_str(&format!(
            "\n(#theorem claim-{index} (#proof-contract identity false false))"
        ));
    }
    source.push_str("\n(#theorem claim true)");
    let (result, warnings) = check(&source, Path::new("coverage.lim"), "claim");
    let error = result.unwrap_err();
    assert_eq!(error.proof_outcome(), Some(ProofOutcome::ResourceLimit));
    assert!(error.message.contains("16 MiB"), "{}", error.message);
    assert!(warnings.is_empty());
}
