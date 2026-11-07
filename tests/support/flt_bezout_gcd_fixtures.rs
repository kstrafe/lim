//! Isolated native proof probes for Eisenstein gcd/Bezout witnesses.
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
        "lim-flt-bezout-gcd-{}-{}",
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
        ("integer-defs", &["integer", "integer-equal"][..]),
        (
            "eisenstein-defs",
            &[
                "eisenstein",
                "eisenstein-zero",
                "eisenstein-one",
                "eisenstein-equal",
                "eisenstein-add",
                "eisenstein-negate",
                "eisenstein-multiply",
                "eisenstein-divides",
            ][..],
        ),
        ("eisenstein-norm-defs", &["eisenstein-natural-norm"][..]),
        (
            "eisenstein-divisibility",
            &["eisenstein-divides-reflexive"][..],
        ),
        (
            "eisenstein-bezout-gcd-defs",
            &[
                "eisenstein-bezout-gcd-spec",
                "eisenstein-has-bezout-gcd",
                "eisenstein-bezout-gcd-common-divisor",
            ][..],
        ),
        (
            "eisenstein-bezout-gcd-euclidean",
            &["eisenstein-bezout-gcd-euclidean-step"][..],
        ),
        (
            "eisenstein-bezout-gcd-induction",
            &["eisenstein-bezout-gcd-with-norm-exists"][..],
        ),
        (
            "eisenstein-bezout-gcd",
            &["eisenstein-bezout-gcd-exists"][..],
        ),
        (
            "eisenstein-gcd",
            &[
                "eisenstein-gcd-spec",
                "eisenstein-has-gcd",
                "eisenstein-gcd-of-bezout-certificate",
                "eisenstein-gcd-exists",
            ][..],
        ),
        ("../fermat_statement", &["add"][..]),
        (
            "logical-connectives",
            &["conjunction", "conjunction-introduce"][..],
        ),
        ("logic-exists", &["exists"][..]),
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
    source.push_str(&format!("(#theorem observed-bezout-gcd (#universes) (#parameters) (#statement {statement}) (#proof {proof}))"));
    fs::write(&path, &source).unwrap();
    let result =
        check_theorem_details_from_path_with_config(&source, &path, config, "observed-bezout-gcd");
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
