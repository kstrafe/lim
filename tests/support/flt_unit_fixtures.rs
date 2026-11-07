//! Isolated native proof probes for unit classification and congruences.
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

pub fn fixture(statement: &str, proof: &str, valid: bool, config: &CompileConfig) {
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let directory = std::env::temp_dir().join(format!(
        "lim-flt-unit-{}-{}",
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
            "integer-defs",
            &[
                "integer",
                "integer-zero",
                "integer-one",
                "integer-negate",
                "integer-of-natural",
                "integer-equal",
                "integer-divides",
            ][..],
        ),
        (
            "eisenstein-defs",
            &[
                "eisenstein",
                "eisenstein-one",
                "eisenstein-zero",
                "eisenstein-omega",
                "eisenstein-lambda",
                "eisenstein-equal",
                "eisenstein-add",
                "eisenstein-negate",
                "eisenstein-of-integer",
                "eisenstein-power",
                "eisenstein-divides",
                "eisenstein-unit",
            ][..],
        ),
        (
            "logical-connectives",
            &["disjunction", "conjunction-introduce"][..],
        ),
        ("logic-exists", &["exists"][..]),
        (
            "natural-unit-bound",
            &["natural-three-square-budget-small"][..],
        ),
        (
            "integer-unit-bound",
            &["integer-three-square-value-small"][..],
        ),
        (
            "eisenstein-norm-unit",
            &["eisenstein-unit-of-natural-norm-one"][..],
        ),
        (
            "eisenstein-unit-classification",
            &["eisenstein-standard-unit", "eisenstein-unit-classification"][..],
        ),
        (
            "eisenstein-divisibility",
            &[
                "eisenstein-divides-zero",
                "eisenstein-divides-congruent-target",
            ][..],
        ),
        (
            "eisenstein-unit-kummer",
            &[
                "eisenstein-three-divides-lambda-square",
                "integer-three-divides-eisenstein-omega",
                "eisenstein-unit-square-integer-congruence-cases",
                "eisenstein-unit-integer-congruence-one-or-negative-one",
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
    source.push_str(&format!("(#theorem observed-unit (#universes) (#parameters) (#statement {statement}) (#proof {proof}))"));
    fs::write(&path, &source).unwrap();
    let result =
        check_theorem_details_from_path_with_config(&source, &path, config, "observed-unit");
    fs::remove_dir_all(&directory).unwrap();
    if valid {
        assert!(result
            .unwrap_or_else(|error| panic!("{}", error.message))
            .foundations
            .is_empty());
    } else {
        let error = result.unwrap_err();
        assert_eq!(error.code, lim::DiagnosticCode::Proof);
        // A resource limit is not evidence that an invalid proof was rejected.
        assert!(error.message.contains("mismatch"), "{}", error.message);
    }
}
