//! Isolated native proof probes for Eisenstein unit/coprime/prime certificates.
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
        "lim-flt-prime-{}-{}",
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
                "eisenstein-lambda",
                "eisenstein-equal",
                "eisenstein-add",
                "eisenstein-multiply",
                "eisenstein-unit",
                "eisenstein-coprime",
                "eisenstein-divides",
            ][..],
        ),
        ("eisenstein-norm-defs", &["eisenstein-natural-norm"][..]),
        ("eisenstein-embedding", &["eisenstein-one-nonzero"][..]),
        ("eisenstein-cubic-bridge", &["eisenstein-one-unit"][..]),
        ("eisenstein-constants", &["eisenstein-lambda-nonzero"][..]),
        (
            "eisenstein-lambda-prime",
            &["eisenstein-prime", "eisenstein-lambda-prime"][..],
        ),
        (
            "eisenstein-divisibility",
            &["eisenstein-divides-reflexive"][..],
        ),
        (
            "eisenstein-euclidean-division",
            &["eisenstein-euclidean-division-spec"][..],
        ),
        (
            "eisenstein-unit-divisibility",
            &[
                "eisenstein-unit-of-divides-one",
                "eisenstein-unit-congruent",
            ][..],
        ),
        (
            "eisenstein-coprime-factors",
            &[
                "eisenstein-coprime-divides-product",
                "eisenstein-coprime-symmetric",
            ][..],
        ),
        (
            "eisenstein-divisibility-cases",
            &[
                "eisenstein-unit-cases",
                "eisenstein-euclidean-zero-remainder-divides",
                "eisenstein-euclidean-nonzero-remainder-not-divides",
            ][..],
        ),
        (
            "eisenstein-irreducible-prime",
            &[
                "eisenstein-irreducible",
                "eisenstein-lambda-irreducible",
                "eisenstein-irreducible-prime",
                "eisenstein-prime-factorization-unit-cofactor",
            ][..],
        ),
        ("../fermat_statement", &["add"][..]),
        ("natural-order", &["less-than"][..]),
        (
            "logical-connectives",
            &["conjunction", "conjunction-introduce", "disjunction"][..],
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
    source.push_str(&format!("(#theorem observed-prime (#universes) (#parameters) (#statement {statement}) (#proof {proof}))"));
    fs::write(&path, &source).unwrap();
    let result =
        check_theorem_details_from_path_with_config(&source, &path, config, "observed-prime");
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
