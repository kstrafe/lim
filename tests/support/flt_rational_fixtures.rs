//! Native-kernel probes for exact rationals; candidate certificates carry no host authority.
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
pub fn fixture(statement: &str, proof: &str, valid: bool) {
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let directory = std::env::temp_dir().join(format!(
        "lim-flt-rational-{}-{}",
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
        ("../fermat_statement", &["add"][..]),
        ("natural-nonzero", &["successor-not-zero"][..]),
        (
            "integer-defs",
            &[
                "integer",
                "integer-equal",
                "integer-multiply",
                "integer-add",
                "integer-power",
                "integer-zero",
            ][..],
        ),
        ("integer-domain", &["integer-natural-embedding-nonzero"][..]),
        (
            "integer-divisibility-decision",
            &["integer-negative-nonzero"][..],
        ),
        (
            "integer-defs",
            &["integer-of-natural", "integer-negate"][..],
        ),
        (
            "integer-cross-products",
            &["integer-cross-product-transitive"][..],
        ),
        (
            "rational-defs",
            &[
                "rational",
                "rational-equal",
                "rational-zero",
                "rational-one",
                "rational-add",
                "rational-multiply",
                "rational-negate",
                "rational-power",
                "rational-of-integer",
            ][..],
        ),
        (
            "rational-equality",
            &[
                "rational-reflexive",
                "rational-transitive",
                "rational-zero-numerator",
                "rational-fraction-nonzero",
            ][..],
        ),
        (
            "rational-congruence",
            &["rational-add-congruent", "rational-multiply-congruent"][..],
        ),
        (
            "rational-ring",
            &[
                "rational-add-associative",
                "rational-multiply-distribute-second",
                "rational-add-inverse",
                "rational-nonzero-product",
                "rational-power-nonzero",
            ][..],
        ),
        (
            "rational-fractions",
            &[
                "rational-fraction-natural-factor-cancel",
                "rational-fraction-times-denominator",
            ][..],
        ),
        (
            "rational-embedding-laws",
            &[
                "rational-of-integer-negate",
                "rational-of-integer-power",
                "rational-natural-multiple-times-fraction",
            ][..],
        ),
        (
            "frey-rational-c4",
            &["frey-rational-model-c4", "frey-rational-curve-c4"][..],
        ),
        (
            "rational-weierstrass-defs",
            &[
                "rational-weierstrass-curve",
                "rational-weierstrass-b2",
                "rational-weierstrass-b4",
                "rational-weierstrass-b6",
                "rational-weierstrass-c4",
            ][..],
        ),
        (
            "frey-rational-curve",
            &[
                "frey-rational-model",
                "frey-rational-curve",
                "frey-rational-curve-a4-nonzero",
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
    source.push_str(&format!("(#theorem observed-rational (#universes) (#parameters) (#statement {statement}) (#proof {proof}))"));
    fs::write(&path, &source).unwrap();
    let mut config = CompileConfig::default();
    let default = ProofBudget::default();
    config.set_proof_budget(
        ProofBudget::new(default.work(), default.phase_bytes(), 1024 * 1024 * 1024).unwrap(),
    );
    let result =
        check_theorem_details_from_path_with_config(&source, &path, &config, "observed-rational");
    fs::remove_dir_all(&directory).unwrap();
    if valid {
        assert!(result
            .unwrap_or_else(|e| panic!("{}", e.message))
            .foundations
            .is_empty());
    } else {
        let e = result.unwrap_err();
        assert_eq!(e.code, DiagnosticCode::Proof);
        assert!(e.message.contains("mismatch"), "{}", e.message);
    }
}
