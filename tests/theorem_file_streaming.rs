mod support;

use lim::{
    check_theorem_details_from_file_with_config, check_theorem_details_from_path_with_config,
    CompileConfig, DiagnosticCode, TheoremFileError,
};
use std::{fs, path::Path};

const REFL: &str = "(#theorem reflexivity\n  (#universes u)\n  (#parameters (#parameter a (#pt-type u)) (#parameter value a))\n  (#statement (#pt-eq a value value))\n  (#proof (#pt-refl a value)))";
const BROKEN: &str = "(#theorem broken (#universes) (#parameters)\n  (#statement (#pt-eq #pt-nat #pt-zero (#pt-succ #pt-zero)))\n  (#proof (#pt-refl #pt-nat #pt-zero)))";

fn write(scratch: &support::Scratch, rel: &str, source: &str) -> std::path::PathBuf {
    let path = scratch.path().join(rel);
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(&path, source).unwrap();
    path
}

fn file_check(path: &Path, name: &str) -> Result<lim::CheckedTheorem, TheoremFileError> {
    check_theorem_details_from_file_with_config(path, &CompileConfig::default(), name)
}

#[test]
fn file_success_checks_all_declarations_and_matches_string_route() {
    let scratch = support::Scratch::new("theorem-file-success");
    // The complete declaration inventory matches the in-memory route.
    let source = format!("{REFL}\n{}", REFL.replace("reflexivity", "later"));
    let path = write(&scratch, "main.lim", &source);
    let from_file = file_check(&path, "reflexivity").unwrap();
    let from_text = check_theorem_details_from_path_with_config(
        &source,
        &path,
        &CompileConfig::default(),
        "reflexivity",
    )
    .unwrap();
    assert_eq!(from_file, from_text);
    assert_eq!(from_file.name, "reflexivity");
    assert!(from_file.foundations.is_empty());

    let foundations = include_str!("../examples/proof_foundations.lim")
        .split("(#fn main")
        .next()
        .unwrap();
    let foundation_path = write(&scratch, "foundations.lim", foundations);
    for target in ["selected-natural-reflexive", "proposition-extensionality"] {
        let from_file = file_check(&foundation_path, target).unwrap();
        let from_text = check_theorem_details_from_path_with_config(
            foundations,
            &foundation_path,
            &CompileConfig::default(),
            target,
        )
        .unwrap();
        assert_eq!(from_file, from_text);
        assert!(!from_file.foundations.is_empty());
    }

    let late_bad = format!("{REFL}\n{BROKEN}");
    let path = write(&scratch, "late-bad.lim", &late_bad);
    let file_error = file_check(&path, "reflexivity").unwrap_err();
    let text_error = check_theorem_details_from_path_with_config(
        &late_bad,
        &path,
        &CompileConfig::default(),
        "reflexivity",
    )
    .unwrap_err();
    assert_eq!(file_error.diagnostic().unwrap().message, text_error.message);
    assert_eq!(file_error.diagnostic().unwrap().span, text_error.span);
    assert_eq!(file_error.diagnostic().unwrap().code, DiagnosticCode::Proof);
}

#[test]
fn file_proof_errors_retain_global_spans_and_matching_rendered_excerpt() {
    let scratch = support::Scratch::new("theorem-file-diagnostics");
    for (label, prefix) in [
        ("unicode-tab", "; λ😀\t\t\n"),
        ("crlf", "; first\r\n; second\r\n"),
    ] {
        let source = format!("{prefix}{BROKEN}");
        let path = write(&scratch, &format!("{label}.lim"), &source);
        let file_error = file_check(&path, "broken").unwrap_err();
        let diagnostic = file_error.diagnostic().expect("proof diagnostic");
        assert!(
            diagnostic.source_text.is_none(),
            "pure math must use the file route"
        );
        let text_error = check_theorem_details_from_path_with_config(
            &source,
            &path,
            &CompileConfig::default(),
            "broken",
        )
        .unwrap_err();
        assert_eq!(diagnostic.code, text_error.code);
        assert_eq!(diagnostic.message, text_error.message);
        assert_eq!(diagnostic.span, text_error.span);
        let span = diagnostic.span.unwrap();
        assert_eq!(
            (span.start, span.end),
            (source.find(BROKEN).unwrap(), source.len())
        );
        assert_eq!(
            file_error.to_string(),
            lim::render_diagnostic(&text_error, &source, &path.display().to_string())
        );
    }
}

#[test]
fn file_contextual_alias_and_invalid_config_use_general_frontend() {
    let scratch = support::Scratch::new("theorem-file-fallback");
    write(
        &scratch,
        "math/lib.lim",
        "(#export theorem)\n(#theorem theorem true)",
    );
    let root = write(
        &scratch,
        "main.lim",
        "(#alias chosen = ./math/lib.lim::theorem)",
    );
    let alias = file_check(&root, "chosen").unwrap();
    let source = fs::read_to_string(&root).unwrap();
    let text = check_theorem_details_from_path_with_config(
        &source,
        &root,
        &CompileConfig::default(),
        "chosen",
    )
    .unwrap();
    assert_eq!(alias, text);
    assert!(alias.name.ends_with("math/lib.lim::theorem"));

    let pure = write(&scratch, "pure.lim", REFL);
    let mut config = CompileConfig::default();
    config.set("async-lowering", "invalid");
    let error =
        check_theorem_details_from_file_with_config(&pure, &config, "reflexivity").unwrap_err();
    let eager = check_theorem_details_from_path_with_config(REFL, &pure, &config, "reflexivity")
        .unwrap_err();
    let diagnostic = error.diagnostic().expect("config diagnostic");
    assert_eq!(diagnostic.message, eager.message);
    assert_eq!(diagnostic.code, eager.code);
    assert_eq!(diagnostic.span, eager.span);
    assert!(error.to_string().contains("unknown async-lowering"));
}

#[test]
fn missing_file_is_an_unpositioned_io_error() {
    let scratch = support::Scratch::new("theorem-file-missing");
    let path = scratch.path().join("absent.lim");
    let error = file_check(&path, "reflexivity").unwrap_err();
    assert!(error.diagnostic().is_none());
    assert!(!error.to_string().is_empty());
    assert!(std::error::Error::source(&error).is_none());
}

#[test]
fn file_route_preserves_forward_references_and_mutual_groups() {
    let scratch = support::Scratch::new("theorem-file-schedule");
    let source = r#"
      (#math-definition use-later () #pt-nat (#pt-use later ()))
      (#math-definition later () #pt-nat #pt-zero)
      (#math-inductive left () () (#mutual left right) (#pt-type 0)
        ((wrap ((children (#pt-recur right ()))))))
      (#math-inductive right () () (#mutual left right) (#pt-type 0)
        ((back ((children (#pt-recur left ()))))))
      (#theorem early-proof (#universes) (#parameters)
        (#statement (#pt-eq #pt-nat #pt-zero #pt-zero))
        (#proof (#pt-use later-proof ())))
      (#theorem later-proof (#universes) (#parameters)
        (#statement (#pt-eq #pt-nat #pt-zero #pt-zero))
        (#proof (#pt-refl #pt-nat #pt-zero)))
    "#;
    let path = write(&scratch, "main.lim", source);
    assert_eq!(
        file_check(&path, "early-proof").unwrap(),
        check_theorem_details_from_path_with_config(
            source,
            &path,
            &CompileConfig::default(),
            "early-proof",
        )
        .unwrap()
    );
}

#[test]
fn late_syntax_errors_preserve_general_frontend_precedence() {
    let scratch = support::Scratch::new("theorem-file-syntax");
    for (label, suffix) in [("parse", ")"), ("lex", "\"unterminated")] {
        let source = format!("{BROKEN}\n{suffix}");
        let path = write(&scratch, &format!("{label}.lim"), &source);
        let error = file_check(&path, "broken").unwrap_err();
        let expected = check_theorem_details_from_path_with_config(
            &source,
            &path,
            &CompileConfig::default(),
            "broken",
        )
        .unwrap_err();
        let diagnostic = error.diagnostic().unwrap();
        assert_eq!(diagnostic.code, expected.code);
        assert_ne!(diagnostic.code, DiagnosticCode::Proof);
        assert_eq!(diagnostic.span, expected.span);
        assert_eq!(
            error.to_string(),
            lim::render_diagnostic(&expected, &source, &path.display().to_string())
        );
    }
}

#[test]
fn invalid_utf8_after_a_valid_theorem_is_an_input_error() {
    let scratch = support::Scratch::new("theorem-file-utf8");
    let path = scratch.path().join("main.lim");
    let mut bytes = REFL.as_bytes().to_vec();
    bytes.extend_from_slice(b"\n\xff");
    fs::write(&path, bytes).unwrap();
    let error = file_check(&path, "reflexivity").unwrap_err();
    assert!(error.diagnostic().is_none());
    assert!(error.to_string().contains("UTF-8"), "{error}");
}

#[test]
fn file_inventory_checks_beyond_the_in_memory_eligibility_limit() {
    let scratch = support::Scratch::new("theorem-file-large");
    let mut source = format!("{REFL}\n");
    // Many short comments exercise bounded read-ahead rather than the
    // ordinary frontend fallback for an over-limit single form or comment.
    let comment = format!(";{}\n", "x".repeat(4094));
    while source.len() < 9 * 1024 * 1024 {
        source.push_str(&comment);
    }
    let path = write(&scratch, "main.lim", &source);
    assert_eq!(
        file_check(&path, "reflexivity").unwrap().name,
        "reflexivity"
    );
    let start = source.len();
    source.push_str(BROKEN);
    fs::write(&path, &source).unwrap();
    let error = file_check(&path, "reflexivity").unwrap_err();
    let diagnostic = error.diagnostic().unwrap();
    assert_eq!(diagnostic.code, DiagnosticCode::Proof);
    assert!(
        diagnostic.source_text.is_none(),
        "large source must stay file-backed"
    );
    assert_eq!(diagnostic.span.unwrap().start, start);
    assert!(error.to_string().contains(BROKEN.lines().next().unwrap()));

    // Also reject a bad declaration in the prefix consumed before paging.
    // Checking only the later suffix would incorrectly accept this target.
    source.truncate(start);
    source.replace_range(..REFL.len(), BROKEN);
    source.push_str(REFL);
    fs::write(&path, &source).unwrap();
    let error = file_check(&path, "reflexivity").unwrap_err();
    let diagnostic = error.diagnostic().unwrap();
    assert!(diagnostic.source_text.is_none());
    assert_eq!(diagnostic.span.unwrap().start, 0);
    assert!(diagnostic.message.contains("theorem 'broken'"));
}
