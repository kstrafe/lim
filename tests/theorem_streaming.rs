mod support;

use lim::{check_theorem_details_from_path_with_config, CompileConfig, DiagnosticCode};
use std::{fs, path::Path};

const REFL: &str = "(#theorem reflexivity\n  (#universes u)\n  (#parameters (#parameter a (#pt-type u)) (#parameter value a))\n  (#statement (#pt-eq a value value))\n  (#proof (#pt-refl a value)))";
const BROKEN: &str = "(#theorem broken (#universes) (#parameters)
  (#statement (#pt-eq #pt-nat #pt-zero (#pt-succ #pt-zero)))
  (#proof (#pt-refl #pt-nat #pt-zero)))";
const FORCE_GENERAL: &str = "\n(#fn validation-control () #u64 (#return 0u64))";

fn check(source: &str, path: &Path, name: &str) -> Result<lim::CheckedTheorem, lim::Diagnostic> {
    check_theorem_details_from_path_with_config(source, path, &CompileConfig::default(), name)
}

fn write(scratch: &support::Scratch, relative: &str, contents: &str) -> std::path::PathBuf {
    let path = scratch.path().join(relative);
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(&path, contents).unwrap();
    path
}

#[test]
fn pure_math_selection_has_stable_result_and_checks_later_declarations() {
    let scratch = support::Scratch::new("theorem-streaming-pure");
    let path = scratch.path().join("main.lim");
    let source = format!("{REFL}\n{}", REFL.replace("reflexivity", "later"));
    let result = check(&source, &path, "reflexivity").unwrap();
    assert_eq!(result.name, "reflexivity");
    assert!(result.foundations.is_empty());
    assert_eq!(result.budget, lim::ProofBudget::default());
    assert_eq!(
        result,
        check(&format!("{source}{FORCE_GENERAL}"), &path, "reflexivity").unwrap()
    );

    let invalid = format!("{REFL}\n{BROKEN}");
    let error = check(&invalid, &path, "reflexivity").unwrap_err();
    assert_eq!(error.code, DiagnosticCode::Proof);
    let eager = check(&format!("{invalid}{FORCE_GENERAL}"), &path, "reflexivity").unwrap_err();
    assert_eq!(error.message, eager.message);
    assert_eq!(error.span, eager.span);
    assert_eq!(error.span.unwrap().start, invalid.find(BROKEN).unwrap());
}

#[test]
fn pure_source_at_the_standalone_size_limit_remains_checkable() {
    let scratch = support::Scratch::new("theorem-streaming-size-limit");
    let path = scratch.path().join("main.lim");
    for size in [8 * 1024 * 1024, 8 * 1024 * 1024 + 1] {
        let mut source = ";".to_owned();
        source.push_str(&" ".repeat(size - REFL.len() - 2));
        source.push('\n');
        source.push_str(REFL);
        assert_eq!(source.len(), size);
        assert_eq!(
            check(&source, &path, "reflexivity").unwrap().name,
            "reflexivity"
        );
    }
}

#[test]
fn selected_proof_errors_keep_precise_source_spans() {
    let scratch = support::Scratch::new("theorem-streaming-span");
    let path = scratch.path().join("main.lim");
    let source = BROKEN;
    let error = check(source, &path, "broken").unwrap_err();
    assert_eq!(error.code, DiagnosticCode::Proof);
    let span = error
        .span
        .expect("proof failure should identify its source span");
    assert_eq!((span.start, span.end), (0, source.len()));
    assert_eq!(error.source_text.as_deref(), Some(source));
}

#[test]
fn mathematical_definitions_are_not_selectable_theorems() {
    let scratch = support::Scratch::new("theorem-streaming-definition");
    let path = scratch.path().join("main.lim");
    let source = "(#math-definition zero () #pt-nat #pt-zero)";
    let error = check(source, &path, "zero").unwrap_err();
    assert_eq!(error.code, DiagnosticCode::Proof);
    assert!(error.message.contains("theorem"), "{error:?}");
}

#[test]
fn imports_and_runtime_forms_keep_general_frontend_behavior() {
    let scratch = support::Scratch::new("theorem-streaming-fallback");
    let imported = write(
        &scratch,
        "math/lib.lim",
        "(#export theorem)\n(#theorem theorem true)",
    );
    let root = scratch.path().join("main.lim");
    let source = "(#alias chosen = ./math/lib.lim::theorem)";
    let result = check(source, &root, "chosen").unwrap();
    assert!(
        result.name.ends_with("math/lib.lim::theorem"),
        "{}",
        result.name
    );
    assert!(imported.exists());

    let mixed = "(#fn value () #u64 (#return 42u64))\n(#theorem valid true)";
    assert_eq!(check(mixed, &root, "valid").unwrap().name, "valid");
    let procedural =
        "(#fn pure () #u64 (#return 42u64))\n(#theorem no-io (#proof-no-effects pure (#proof-io)))";
    assert_eq!(check(procedural, &root, "no-io").unwrap().name, "no-io");
}

#[test]
fn unresolved_names_and_reserved_authored_names_fail_through_normal_diagnostics() {
    let scratch = support::Scratch::new("theorem-streaming-names");
    let path = scratch.path().join("main.lim");
    let unknown = check(REFL, &path, "absent").unwrap_err();
    assert_eq!(unknown.code, DiagnosticCode::Proof);
    assert!(unknown.message.contains("unknown theorem"));

    let reserved = REFL.replace("reflexivity", "lim.gensym.forged");
    let error = check(&reserved, &path, "lim.gensym.forged").unwrap_err();
    assert!(error.message.contains("reserved"), "{error:?}");
}

#[test]
fn configured_budgets_and_foundation_audits_match_the_general_checker() {
    let scratch = support::Scratch::new("theorem-streaming-budget-foundations");
    let path = scratch.path().join("main.lim");
    let full = include_str!("../examples/proof_foundations.lim");
    let math = full.split("(#fn main").next().unwrap();
    for target in [
        "selected-natural-reflexive",
        "proposition-extensionality",
        "quotient-related-representatives",
    ] {
        let checked = check(math, &path, target).unwrap();
        assert!(!checked.foundations.is_empty());
        assert_eq!(checked, check(full, &path, target).unwrap());
    }
    let mut config = CompileConfig::default();
    config.set_proof_budget(lim::ProofBudget::new(1, 64 << 20, 256 << 20).unwrap());
    let error = check_theorem_details_from_path_with_config(REFL, &path, &config, "reflexivity")
        .unwrap_err();
    let eager = check_theorem_details_from_path_with_config(
        &format!("{REFL}{FORCE_GENERAL}"),
        &path,
        &config,
        "reflexivity",
    )
    .unwrap_err();
    assert_eq!(error.code, DiagnosticCode::Proof);
    assert_eq!(error.message, eager.message);
    assert_eq!(error.span, eager.span);
}

#[test]
fn primitive_spelling_and_global_config_errors_are_not_bypassed() {
    let scratch = support::Scratch::new("theorem-streaming-front-end-guards");
    let path = scratch.path().join("main.lim");
    let source = REFL.replace("value", "u64");
    let error = check(&source, &path, "reflexivity").unwrap_err();
    assert!(error.message.contains("primitive type"), "{error:?}");
    let mut config = CompileConfig::default();
    config.set("async-lowering", "invalid");
    let error = check_theorem_details_from_path_with_config(REFL, &path, &config, "reflexivity")
        .unwrap_err();
    assert!(
        error.message.contains("unknown async-lowering"),
        "{error:?}"
    );
}

#[test]
fn pure_file_uses_inventory_while_contextual_names_use_normal_resolution() {
    let scratch = support::Scratch::new("theorem-streaming-inventory");
    let path = scratch.path().join("main.lim");
    let timing = lim::TimingSession::start();
    check(REFL, &path, "reflexivity").unwrap();
    let events = timing.finish();
    assert!(events
        .iter()
        .any(|event| event.stage == "proof_source_inventory"));
    assert!(!events.iter().any(|event| event.stage == "expansion"));
    let definition = "(#export zero)\n(#math-definition zero () #pt-nat #pt-zero)";
    write(&scratch, "math/lib.lim", definition);
    let source = "(#theorem reflexivity (#universes) (#parameters)
      (#statement (#pt-eq #pt-nat (#pt-use ./math/lib.lim::zero ()) #pt-zero))
      (#proof (#pt-refl #pt-nat #pt-zero)))";
    let timing = lim::TimingSession::start();
    check(source, &path, "reflexivity").unwrap();
    assert!(timing
        .finish()
        .iter()
        .any(|event| event.stage == "expansion"));
}

#[test]
fn frontend_only_syntax_and_authored_markers_keep_general_diagnostics() {
    let scratch = support::Scratch::new("theorem-streaming-directives");
    let path = scratch.path().join("main.lim");
    for body in [
        "(#syntax-splice absent)",
        "$lim-file-import",
        "@private-name",
        "'#pt-zero",
    ] {
        let source = REFL.replace("(#pt-refl a value)", body);
        let error = check(&source, &path, "reflexivity").unwrap_err();
        let eager = check(&format!("{source}{FORCE_GENERAL}"), &path, "reflexivity").unwrap_err();
        assert_eq!(error.message, eager.message, "{body}");
        assert_eq!(error.code, eager.code, "{body}");
        assert_eq!(error.span, eager.span, "{body}");
    }
}

#[test]
fn relative_source_paths_keep_the_general_checkers_diagnostic_identity() {
    let path = Path::new("./theorem-streaming-diagnostic.lim");
    let error = check(BROKEN, path, "broken").unwrap_err();
    let eager = check(&format!("{BROKEN}{FORCE_GENERAL}"), path, "broken").unwrap_err();
    assert_eq!(error.source_name, eager.source_name);
    assert_eq!(error.span, eager.span);
    assert_eq!(error.message, eager.message);
}
