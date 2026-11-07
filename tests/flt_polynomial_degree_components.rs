//! Inventory all native polynomial support, degree and domain proofs.
use lim::{check_theorem_details_from_path_with_config, CompileConfig, ProofBudget};
use std::path::Path;
fn matrix(module: &str, expected: &[&str]) {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("theorems/flt")
        .join(format!("{module}.lim"));
    let source = std::fs::read_to_string(&path).unwrap();
    let declared: Vec<_> = source
        .lines()
        .filter_map(|line| line.strip_prefix("(#theorem ")?.split_whitespace().next())
        .collect();
    assert_eq!(
        declared, expected,
        "every native theorem must be inventoried"
    );
    let target = expected.last().unwrap();
    let mut config = CompileConfig::default();
    let budget = ProofBudget::default();
    let total = if module.contains("rational") {
        2 * 1024 * 1024 * 1024
    } else {
        1024 * 1024 * 1024
    };
    config.set_proof_budget(ProofBudget::new(budget.work(), budget.phase_bytes(), total).unwrap());
    let directory =
        std::env::temp_dir().join(format!("lim-degree-matrix-{}-{module}", std::process::id()));
    std::fs::create_dir(&directory).unwrap();
    let entry = directory.join("entry.lim");
    let driver = format!(
        "(#alias checked-module-theorem = {}::{target})",
        path.display()
    );
    std::fs::write(&entry, &driver).unwrap();
    let result = check_theorem_details_from_path_with_config(
        &driver,
        &entry,
        &config,
        "checked-module-theorem",
    );
    std::fs::remove_dir_all(directory).unwrap();
    let report = result.unwrap_or_else(|e| panic!("{module}: {}", e.message));
    assert_eq!(
        report.name,
        format!("{}::{target}", path.canonicalize().unwrap().display())
    );
    assert!(report.foundations.is_empty());
}

#[test]
fn ring_polynomial_degree_x_powers() {
    matrix(
        "ring-polynomial-degree-X-powers",
        &[
            "ring-polynomial-degree-X",
            "ring-polynomial-degree-X-square",
            "ring-polynomial-degree-X-cube",
        ],
    );
}

#[test]
fn ring_polynomial_degree_certificates() {
    matrix(
        "ring-polynomial-degree-certificates",
        &[
            "ring-polynomial-degree-data-valid",
            "ring-polynomial-degree-data-agrees",
            "ring-polynomial-degree-data-zero-tag",
            "ring-polynomial-degree-data-nonzero-tag",
        ],
    );
}

#[test]
fn ring_polynomial_degree_computation() {
    matrix(
        "ring-polynomial-degree-computation",
        &["ring-polynomial-degree-compute-nil"],
    );
}

#[test]
fn ring_polynomial_degree_computed_congruence() {
    matrix(
        "ring-polynomial-degree-computed-congruence",
        &[
            "ring-polynomial-degree-data-zero-natural",
            "ring-polynomial-degree-natural-congruent",
            "ring-polynomial-degree-leading-congruent",
        ],
    );
}

#[test]
fn ring_polynomial_degree_data() {
    matrix(
        "ring-polynomial-degree-data",
        &["ring-polynomial-degree-data-zero"],
    );
}

#[test]
fn ring_polynomial_degree_dominance() {
    matrix(
        "ring-polynomial-degree-dominance",
        &[
            "ring-polynomial-degree-negate",
            "ring-polynomial-degree-add-left-dominant",
            "ring-polynomial-degree-add-right-dominant",
            "ring-polynomial-degree-subtract-left-dominant",
            "ring-polynomial-degree-subtract-right-dominant",
        ],
    );
}

#[test]
fn ring_polynomial_degree_existence() {
    matrix(
        "ring-polynomial-degree-existence",
        &[
            "ring-polynomial-degree-exists",
            "ring-polynomial-degree-computed-agrees",
            "ring-polynomial-degree-computed-valid",
        ],
    );
}

#[test]
fn ring_polynomial_degree_leading() {
    matrix(
        "ring-polynomial-degree-leading",
        &[
            "ring-polynomial-degree-nonzero",
            "ring-polynomial-degree-congruent",
            "ring-polynomial-degree-cons-zero",
            "ring-polynomial-degree-cons-successor",
            "ring-polynomial-degree-tail-zero",
            "ring-polynomial-degree-tail-successor",
        ],
    );
}

#[test]
fn ring_polynomial_degree_positive_bridge() {
    matrix(
        "ring-polynomial-degree-positive-bridge",
        &["ring-polynomial-degree-positive-natural-bridge"],
    );
}

#[test]
fn ring_polynomial_degree_powers() {
    matrix(
        "ring-polynomial-degree-powers",
        &[
            "ring-polynomial-degree-one",
            "ring-polynomial-degree-power-law",
        ],
    );
}

#[test]
fn ring_polynomial_degree_product() {
    matrix(
        "ring-polynomial-degree-product",
        &["ring-polynomial-degree-product"],
    );
}

#[test]
fn ring_polynomial_degree_product_constant_head() {
    matrix(
        "ring-polynomial-degree-product-constant-head",
        &["ring-polynomial-degree-product-constant-head"],
    );
}

#[test]
fn ring_polynomial_degree_product_indices() {
    matrix(
        "ring-polynomial-degree-product-indices",
        &[
            "ring-polynomial-degree-product-support-index",
            "ring-polynomial-degree-product-leading-index",
        ],
    );
}

#[test]
fn ring_polynomial_degree_rational_instance() {
    matrix(
        "ring-polynomial-degree-rational-instance",
        &["ring-polynomial-domain-rational-one"],
    );
}

#[test]
fn ring_polynomial_degree_residue_instance() {
    matrix(
        "ring-polynomial-degree-residue-instance",
        &["ring-polynomial-degree-residue-valid"],
    );
}

#[test]
fn ring_polynomial_degree_uniqueness() {
    matrix(
        "ring-polynomial-degree-uniqueness",
        &[
            "ring-polynomial-degree-not-below",
            "ring-polynomial-degree-unique",
        ],
    );
}

#[test]
fn ring_polynomial_degree_weierstrass() {
    matrix(
        "ring-polynomial-degree-weierstrass",
        &[
            "ring-polynomial-degree-weierstrass-linear-bound",
            "ring-polynomial-degree-weierstrass-cubic",
        ],
    );
}

#[test]
fn ring_polynomial_domain_data() {
    matrix(
        "ring-polynomial-domain-data",
        &[
            "ring-polynomial-domain-one-nonzero",
            "ring-polynomial-domain-product-nonzero",
        ],
    );
}

#[test]
fn ring_polynomial_domain_lift() {
    matrix(
        "ring-polynomial-domain-lift",
        &["ring-polynomial-domain-lift-product"],
    );
}

#[test]
fn ring_polynomial_domain_residue_instance() {
    matrix(
        "ring-polynomial-domain-residue-instance",
        &["ring-polynomial-domain-prime-residue-one"],
    );
}

#[test]
fn ring_polynomial_product_top() {
    matrix(
        "ring-polynomial-product-top",
        &["ring-polynomial-product-top"],
    );
}

#[test]
fn ring_polynomial_support_data() {
    matrix(
        "ring-polynomial-support-data",
        &[
            "ring-polynomial-support-nil",
            "ring-polynomial-support-zero-equivalent",
            "ring-polynomial-support-from-zero",
            "ring-polynomial-support-length",
        ],
    );
}

#[test]
fn ring_polynomial_support_further_operations() {
    matrix(
        "ring-polynomial-support-further-operations",
        &[
            "ring-polynomial-support-successor",
            "ring-polynomial-support-constant-product",
        ],
    );
}

#[test]
fn ring_polynomial_support_operations() {
    matrix(
        "ring-polynomial-support-operations",
        &[
            "ring-polynomial-support-add",
            "ring-polynomial-support-negate",
            "ring-polynomial-support-scale",
            "ring-polynomial-support-shift",
            "ring-polynomial-support-cons-successor",
            "ring-polynomial-support-tail",
            "ring-polynomial-support-constant",
        ],
    );
}

#[test]
fn ring_polynomial_support_strict_index() {
    matrix(
        "ring-polynomial-support-strict-index",
        &["ring-polynomial-support-after-degree"],
    );
}

#[test]
fn ring_polynomial_support_transport() {
    matrix(
        "ring-polynomial-support-transport",
        &[
            "ring-polynomial-support-congruent",
            "ring-polynomial-support-weaken",
        ],
    );
}
