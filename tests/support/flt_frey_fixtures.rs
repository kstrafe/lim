//! Isolated native certificates for Frey normalization; host code adds no proof authority.
use lim::{
    check_theorem_details_from_path_with_config, CompileConfig, DiagnosticCode, ProofBudget,
};
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
pub fn fixture(prelude: &str, statement: &str, proof: &str, valid: bool) {
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let directory = std::env::temp_dir().join(format!(
        "lim-flt-frey-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir(&directory).unwrap();
    let path = directory.join("probe.lim");
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("theorems/flt");
    let terms = format!("{prelude} {statement} {proof}");
    let referenced: std::collections::HashSet<&str> = terms
        .split(|c: char| c.is_whitespace() || c == '(' || c == ')')
        .collect();
    let mut source = String::new();
    for (module, names) in [
        (
            "../fermat_statement",
            &["add", "multiply", "power", "fermats-last-theorem-statement"][..],
        ),
        (
            "natural-power-products",
            &["power-product", "divides-positive-power"][..],
        ),
        (
            "fermat-power-factor-descent",
            &["power-remove-common-factor", "power-common-prime-descends"][..],
        ),
        (
            "fermat-power-primitive",
            &["natural-power-has-primitive"][..],
        ),
        (
            "fermat-power-defs",
            &[
                "natural-power-solution",
                "has-natural-primitive-power-solution",
                "has-smaller-natural-power-solution",
            ][..],
        ),
        (
            "natural-coprime",
            &[
                "coprime",
                "coprime-one-left",
                "coprime-symmetric",
                "coprime-add-left",
            ][..],
        ),
        ("natural-nonzero", &["successor-not-zero"][..]),
        ("natural-order", &["less-than", "less-than-successor"][..]),
        ("natural-discrete-order", &["zero-less-successor"][..]),
        ("natural-divisibility-defs", &["divides"][..]),
        ("natural-divisibility", &["divides-reflexive"][..]),
        ("natural-prime-two", &["prime-two"][..]),
        ("natural-prime-three", &["prime-three"][..]),
        ("natural-parity", &["odd"][..]),
        ("natural-parity-arithmetic", &["odd-even-exclusion"][..]),
        ("logic-exists", &["exists"][..]),
        ("logical-connectives", &["conjunction", "disjunction"][..]),
        (
            "integer-defs",
            &[
                "integer",
                "integer-of-natural",
                "integer-negative-natural",
                "integer-equal",
                "integer-divides",
                "integer-power",
                "integer-negate",
            ][..],
        ),
        (
            "integer-divisibility",
            &["integer-divides-negative-target"][..],
        ),
        (
            "integer-natural-bridge",
            &["integer-natural-divisibility-reflects"][..],
        ),
        ("integer-power-laws", &["integer-negative-odd-power"][..]),
        (
            "frey-even-power-packet",
            &[
                "has-integer-even-power-packet",
                "natural-primitive-power-has-even-signed-packet",
            ][..],
        ),
        (
            "frey-normalized-power-packet",
            &[
                "has-normalized-integer-power-packet",
                "natural-primitive-power-has-normalized-signed-packet",
            ][..],
        ),
        (
            "integer-mod-four-normalization",
            &[
                "integer-three-mod-four",
                "integer-not-even-mod-four-sign-cases",
                "integer-negative-one-mod-four-is-three",
            ][..],
        ),
        ("natural-four-remainders", &["less-than-four-cases"][..]),
        (
            "frey-package",
            &[
                "large-prime-positive-and-odd",
                "fermat-statement-from-frey-refutation",
            ][..],
        ),
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
    source.push_str(prelude);
    source.push_str(&format!("(#theorem observed-frey (#universes) (#parameters) (#statement {statement}) (#proof {proof}))"));
    fs::write(&path, &source).unwrap();
    let mut config = CompileConfig::default();
    let default = ProofBudget::default();
    config.set_proof_budget(
        ProofBudget::new(default.work(), default.phase_bytes(), 1024 * 1024 * 1024).unwrap(),
    );
    let result =
        check_theorem_details_from_path_with_config(&source, &path, &config, "observed-frey");
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
