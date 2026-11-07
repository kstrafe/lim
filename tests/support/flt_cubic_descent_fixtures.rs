//! Isolated native-kernel probes for the constructive cubic descent.
use lim::{check_theorem_details_from_path_with_config, CompileConfig, DiagnosticCode};
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

pub fn fixture(statement: &str, proof: &str, valid: bool, config: &CompileConfig) {
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let directory = std::env::temp_dir().join(format!(
        "lim-flt-cubic-descent-{}-{}",
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
        ("integer-defs", &["integer-equal"][..]),
        (
            "eisenstein-defs",
            &[
                "eisenstein",
                "eisenstein-zero",
                "eisenstein-one",
                "eisenstein-omega",
                "eisenstein-lambda",
                "eisenstein-equal",
                "eisenstein-add",
                "eisenstein-negate",
                "eisenstein-multiply",
                "eisenstein-power",
                "eisenstein-unit",
                "eisenstein-divides",
            ][..],
        ),
        ("eisenstein-equality", &["eisenstein-reflexive"][..]),
        (
            "eisenstein-lambda-prime",
            &["eisenstein-lambda-not-unit"][..],
        ),
        (
            "eisenstein-unit-divisibility",
            &["eisenstein-divisor-of-unit-is-unit"][..],
        ),
        ("eisenstein-constants", &["eisenstein-omega-unit"][..]),
        ("eisenstein-divisibility", &["eisenstein-divides-zero"][..]),
        (
            "logical-connectives",
            &["conjunction", "conjunction-introduce", "disjunction"][..],
        ),
        ("logic-exists", &["exists"][..]),
        ("equality", &["substitution"][..]),
        ("../fermat_statement", &["add"][..]),
        ("natural-order", &["less-than", "less-than-successor"][..]),
        ("eisenstein-lambda-order", &["eisenstein-lambda-order"][..]),
        (
            "eisenstein-normalized-cubic-sign",
            &["eisenstein-normalized-cubic-coefficient-sign"][..],
        ),
        (
            "eisenstein-cubic-square-divisor",
            &[
                "eisenstein-square-divides-scaled-factor-cube",
                "eisenstein-square-divides-scaled-cube-from-divisor",
            ][..],
        ),
        (
            "eisenstein-cubic-signed-coefficient",
            &[
                "eisenstein-signed-cubic-absorption",
                "eisenstein-signed-coefficient-cube",
            ][..],
        ),
        (
            "eisenstein-cubic-descent-orders",
            &[
                "natural-cubic-predecessor-positive",
                "natural-cubic-predecessor-smaller",
                "eisenstein-lambda-powered-free-residual-order",
            ][..],
        ),
        ("fermat-for", &["fermat-for"][..]),
        ("fermat-three", &["fermat-for-three"][..]),
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
    source.push_str(&format!("(#theorem observed-descent (#universes) (#parameters) (#statement {statement}) (#proof {proof}))"));
    fs::write(&path, &source).unwrap();
    let result =
        check_theorem_details_from_path_with_config(&source, &path, config, "observed-descent");
    fs::remove_dir_all(&directory).unwrap();
    if valid {
        assert!(result
            .unwrap_or_else(|error| panic!("{}", error.message))
            .foundations
            .is_empty());
    } else {
        let error = result.unwrap_err();
        assert_eq!(error.code, DiagnosticCode::Proof);
        assert!(error.message.contains("mismatch"), "{}", error.message);
    }
}
