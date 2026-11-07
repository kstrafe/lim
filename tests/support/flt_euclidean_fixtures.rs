//! Isolated native proof probes for Eisenstein Euclidean division.
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
        "lim-flt-euclidean-{}-{}",
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
            &["integer", "integer-of-natural", "integer-equal"][..],
        ),
        (
            "eisenstein-defs",
            &[
                "eisenstein",
                "eisenstein-zero",
                "eisenstein-one",
                "eisenstein-equal",
                "eisenstein-add",
                "eisenstein-multiply",
                "eisenstein-of-integer",
            ][..],
        ),
        (
            "eisenstein-norm-defs",
            &["eisenstein-conjugate", "eisenstein-natural-norm"][..],
        ),
        ("eisenstein-embedding", &["eisenstein-one-nonzero"][..]),
        (
            "eisenstein-coordinate-division",
            &["eisenstein-coordinate-division-spec"][..],
        ),
        (
            "eisenstein-euclidean-algebra",
            &["eisenstein-division-remainder"][..],
        ),
        (
            "eisenstein-euclidean-norm",
            &["eisenstein-remainder-natural-norm-decreases"][..],
        ),
        (
            "eisenstein-euclidean-division",
            &[
                "eisenstein-euclidean-division-spec",
                "eisenstein-has-euclidean-division",
                "eisenstein-euclidean-has-division",
                "eisenstein-euclidean-division-from-coordinates",
                "eisenstein-euclidean-division-with-norm-exists",
                "eisenstein-euclidean-division-exists",
            ][..],
        ),
        (
            "natural-product-order-reflection",
            &["natural-multiply-strict-reflect"][..],
        ),
        ("../fermat_statement", &["add"][..]),
        ("natural-order", &["less-than"][..]),
        ("natural-nonzero", &["successor-not-zero"][..]),
        ("equality", &["symmetry"][..]),
        (
            "logical-connectives",
            &["conjunction", "conjunction-introduce", "conjunction-left"][..],
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
    source.push_str(&format!("(#theorem observed-euclidean (#universes) (#parameters) (#statement {statement}) (#proof {proof}))"));
    fs::write(&path, &source).unwrap();
    let result =
        check_theorem_details_from_path_with_config(&source, &path, config, "observed-euclidean");
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
