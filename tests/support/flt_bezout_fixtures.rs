//! Isolated proof probes for the constructive cubic Bezout arguments.
use lim::{check_theorem_details_from_path_with_config, CompileConfig};
use std::{
    fs,
    path::Path,
    sync::atomic::{AtomicUsize, Ordering},
};

pub fn term(name: &str, args: &[&str]) -> String {
    if args.is_empty() {
        format!("(#pt-use {name} ())")
    } else {
        format!("(#pt-app (#pt-use {name} ()) {})", args.join(" "))
    }
}
pub fn product(first: &str, second: &str) -> String {
    term("eisenstein-multiply", &[first, second])
}

pub fn fixture(statement: &str, proof: &str, valid: bool, config: &CompileConfig) {
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let directory = std::env::temp_dir().join(format!(
        "lim-flt-bezout-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir(&directory).unwrap();
    let path = directory.join("probe.lim");
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("theorems/flt");
    let terms = format!("{statement} {proof}");
    let referenced: std::collections::HashSet<&str> = terms
        .split(|c: char| c.is_whitespace() || c == '(' || c == ')')
        .collect();
    let mut source = String::new();
    for (module, names) in [
        (
            "eisenstein-defs",
            &[
                "eisenstein",
                "eisenstein-one",
                "eisenstein-zero",
                "eisenstein-lambda",
                "eisenstein-omega",
                "eisenstein-equal",
                "eisenstein-add",
                "eisenstein-multiply",
                "eisenstein-negate",
                "eisenstein-power",
                "eisenstein-coprime",
            ][..],
        ),
        ("logic-exists", &["exists"][..]),
        (
            "eisenstein-equality",
            &[
                "eisenstein-reflexive",
                "eisenstein-symmetric",
                "eisenstein-transitive",
                "eisenstein-add-congruent",
            ][..],
        ),
        (
            "eisenstein-ring",
            &["eisenstein-multiply-one", "eisenstein-multiply-zero"][..],
        ),
        (
            "eisenstein-additive-divisibility",
            &["eisenstein-zero-add"][..],
        ),
        ("eisenstein-cubic-bridge", &["eisenstein-one-unit"][..]),
        (
            "eisenstein-cubic-shifts",
            &[
                "eisenstein-omega-plus-one-unit",
                "eisenstein-omega-lambda-unit-shift",
                "eisenstein-omega-square-lambda-unit-shift",
            ][..],
        ),
        (
            "eisenstein-bezout-linear-algebra",
            &[
                "eisenstein-negative-add-inverse",
                "eisenstein-negative-add-cancel",
            ][..],
        ),
        (
            "eisenstein-bezout-linear-change",
            &[
                "eisenstein-coprime-linear-change",
                "eisenstein-coprime-from-sum-and-unit-shift",
            ][..],
        ),
        (
            "eisenstein-cubic-residual-coprime",
            &[
                "eisenstein-cubic-primary-omega-residuals-coprime",
                "eisenstein-cubic-primary-square-residuals-coprime",
                "eisenstein-cubic-rotated-residuals-coprime",
            ][..],
        ),
    ] {
        for name in names {
            if referenced.contains(name) {
                source.push_str(&format!(
                    "(#alias {name} = {}::{name})\n",
                    root.join(format!("{module}.lim")).display()
                ));
            }
        }
    }
    source.push_str(&format!("(#theorem observed-bezout (#universes) (#parameters) (#statement {statement}) (#proof {proof}))"));
    fs::write(&path, &source).unwrap();
    let result =
        check_theorem_details_from_path_with_config(&source, &path, config, "observed-bezout");
    fs::remove_dir_all(&directory).unwrap();
    if valid {
        assert!(result
            .unwrap_or_else(|error| panic!("{}", error.message))
            .foundations
            .is_empty());
    } else {
        let error = result.unwrap_err();
        assert_eq!(error.code, lim::DiagnosticCode::Proof);
        assert!(error.message.contains("mismatch"), "{}", error.message);
    }
}
