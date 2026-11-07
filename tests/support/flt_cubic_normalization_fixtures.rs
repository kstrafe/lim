//! Isolated native proof probes for Eisenstein finite-search/prime-factor certificates.
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
    fixture_with_prelude("", statement, proof, valid, config);
}

pub fn fixture_with_prelude(
    prelude: &str,
    statement: &str,
    proof: &str,
    valid: bool,
    config: &CompileConfig,
) {
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let directory = std::env::temp_dir().join(format!(
        "lim-flt-cubic-normalization-{}-{}",
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
            "integer-defs",
            &["integer", "integer-equal", "integer-of-natural"][..],
        ),
        ("integer-magnitude", &["integer-negative-magnitude"][..]),
        (
            "eisenstein-defs",
            &[
                "eisenstein",
                "eisenstein-zero",
                "eisenstein-one",
                "eisenstein-lambda",
                "eisenstein-equal",
                "eisenstein-multiply",
                "eisenstein-unit",
                "eisenstein-coprime",
                "eisenstein-power",
                "eisenstein-add",
                "eisenstein-divides",
            ][..],
        ),
        ("eisenstein-norm-defs", &["eisenstein-natural-norm"][..]),
        (
            "eisenstein-constants",
            &[
                "eisenstein-lambda-nonzero",
                "eisenstein-lambda-divides-three",
            ][..],
        ),
        (
            "eisenstein-lambda-prime",
            &[
                "eisenstein-prime",
                "eisenstein-lambda-not-unit",
                "eisenstein-lambda-prime",
            ][..],
        ),
        ("eisenstein-cubic-bridge", &["eisenstein-one-unit"][..]),
        (
            "eisenstein-unit-divisibility",
            &[
                "eisenstein-unit-congruent",
                "eisenstein-divisor-of-unit-is-unit",
            ][..],
        ),
        (
            "eisenstein-finite-coordinates",
            &[
                "eisenstein-has-finite-coordinates",
                "eisenstein-finite-coordinates-exist",
            ][..],
        ),
        (
            "natural-coordinate-search-bound",
            &["natural-three-square-budget-magnitude-bound"][..],
        ),
        (
            "integer-coordinate-search-bound",
            &["integer-three-square-magnitude-bound"][..],
        ),
        (
            "proposition-minimum",
            &["minimum-exists-from-proposition-cases"][..],
        ),
        ("least-witness", &["minimum", "has-minimum"][..]),
        ("decidable-order", &["natural-order-decided"][..]),
        (
            "eisenstein-finite-norm-search",
            &[
                "eisenstein-norm-property",
                "eisenstein-norm-property-exists",
                "eisenstein-coordinate-property-search",
                "eisenstein-norm-existence-to-search",
                "eisenstein-search-to-norm-existence",
            ][..],
        ),
        (
            "eisenstein-prime-divisor",
            &["eisenstein-prime-divisor-exists"][..],
        ),
        (
            "eisenstein-nonunit-factor-norm",
            &["eisenstein-nonunit-factor-norm-decreases"][..],
        ),
        ("../fermat_statement", &["add"][..]),
        ("natural-order", &["less-than", "not-less-than-self"][..]),
        ("natural-nonzero", &["successor-not-zero"][..]),
        ("equality", &["symmetry"][..]),
        (
            "logical-connectives",
            &["conjunction", "conjunction-introduce", "conjunction-left"][..],
        ),
        ("logic-exists", &["exists"][..]),
        ("eisenstein-equality", &["eisenstein-reflexive"][..]),
        (
            "eisenstein-power-divisibility",
            &["eisenstein-power-divisor"][..],
        ),
        (
            "eisenstein-prime-cube-laws",
            &[
                "eisenstein-prime-divides-power",
                "eisenstein-coprime-divisor-left",
                "eisenstein-prime-divisor-excludes-coprime-factor",
                "eisenstein-prime-divides-unit-cube-root",
            ][..],
        ),
        (
            "eisenstein-associated-cube",
            &[
                "eisenstein-associated-cube",
                "eisenstein-zero-associated-cube",
                "eisenstein-unit-associated-cube",
                "eisenstein-associated-cube-congruent",
            ][..],
        ),
        (
            "eisenstein-norm-unit",
            &["eisenstein-unit-of-natural-norm-one"][..],
        ),
        (
            "eisenstein-domain-powers",
            &["eisenstein-power-nonzero"][..],
        ),
        (
            "eisenstein-coprime-power-factor",
            &["eisenstein-coprime-extract-power"][..],
        ),
        (
            "eisenstein-cube-factor-removal",
            &["eisenstein-prime-cube-factor-removal"][..],
        ),
        (
            "eisenstein-cube-extraction-norm",
            &["eisenstein-prime-cube-quotient-norm-decreases"][..],
        ),
        (
            "eisenstein-coprime-cube",
            &[
                "eisenstein-coprime-product-associated-cube",
                "eisenstein-coprime-product-associated-cubes",
            ][..],
        ),
        (
            "eisenstein-coprime-cube-triple",
            &["eisenstein-coprime-triple-associated-cubes"][..],
        ),
        (
            "eisenstein-associated-cube-properties",
            &[
                "eisenstein-cube-root-divides-value",
                "eisenstein-nondivisor-implies-nonzero",
                "eisenstein-cube-root-nondivisor",
                "eisenstein-cube-roots-coprime",
            ][..],
        ),
        (
            "eisenstein-descent-unit-laws",
            &[
                "eisenstein-witnessed-inverse-is-unit",
                "eisenstein-units-multiply",
                "eisenstein-unit-negate",
                "eisenstein-unit-power",
            ][..],
        ),
        (
            "eisenstein-cubic-linear-algebra",
            &["eisenstein-omega-weighted-linear-sum"][..],
        ),
        (
            "eisenstein-cubic-normalizing-scales",
            &["eisenstein-normalized-cubic-units"][..],
        ),
        (
            "eisenstein-cubic-normalization-orders",
            &[
                "natural-cubic-balance-predecessor-order",
                "natural-cubic-balance-has-predecessor",
                "eisenstein-normalized-cubic-from-balanced-factors",
                "eisenstein-normalized-cubic-order-exists",
            ][..],
        ),
        (
            "eisenstein-unit-divisibility",
            &["eisenstein-unit-of-divides-one"][..],
        ),
        ("eisenstein-defs", &["eisenstein-negate"][..]),
        ("../fermat_statement", &["multiply"][..]),
        ("eisenstein-defs", &["eisenstein-omega"][..]),
        (
            "eisenstein-ring",
            &[
                "eisenstein-add-commutative",
                "eisenstein-add-inverse",
                "eisenstein-multiply-zero",
            ][..],
        ),
        (
            "eisenstein-equality",
            &["eisenstein-transitive", "eisenstein-symmetric"][..],
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
    source.push_str(prelude);
    source.push_str(&format!("(#theorem observed-normalization (#universes) (#parameters) (#statement {statement}) (#proof {proof}))"));
    fs::write(&path, &source).unwrap();
    let result = check_theorem_details_from_path_with_config(
        &source,
        &path,
        config,
        "observed-normalization",
    );
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
