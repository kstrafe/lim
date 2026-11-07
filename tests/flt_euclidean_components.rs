//! Foundation-free checks for Euclidean component theorems.
use lim::{check_theorem_details_from_path_with_config, CompileConfig, ProofBudget};
use std::path::Path;

const NATURAL_PRODUCT_ORDER_REFLECTION: &[&str] = &["natural-multiply-strict-reflect"];

const EISENSTEIN_NATURAL_NORM_TRANSPORT: &[&str] = &[
    "eisenstein-natural-norm-conjugate",
    "eisenstein-natural-norm-congruent",
    "eisenstein-natural-norm-unique",
    "eisenstein-product-conjugate-natural",
    "eisenstein-product-natural-norm-equation",
];

const EISENSTEIN_EUCLIDEAN_ALGEBRA: &[&str] = &[
    "eisenstein-division-reconstruction",
    "eisenstein-three-factor-swap-tail",
    "eisenstein-remainder-conjugate-expansion",
    "eisenstein-remainder-conjugate-from-coordinates",
];

fn euclidean_components_config() -> CompileConfig {
    let mut config = CompileConfig::default();
    let default = ProofBudget::default();
    config.set_proof_budget(
        ProofBudget::new(default.work(), default.phase_bytes(), 1024 * 1024 * 1024).unwrap(),
    );
    config
}

fn check_matrix(module: &str, targets: &[&str]) {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let path = root.join("theorems/flt").join(module);
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("failed to read {}: {error}", path.display()));
    let config = euclidean_components_config();

    for &target in targets {
        let report = check_theorem_details_from_path_with_config(&source, &path, &config, target)
            .unwrap_or_else(|error| {
                panic!(
                    "failed to check {target} in {}: {}",
                    path.display(),
                    error.message
                )
            });
        assert!(
            report.name == target || report.name.ends_with(&format!("::{target}")),
            "unexpected canonical target for {}: {}",
            path.display(),
            report.name
        );
        assert!(
            report.foundations.is_empty(),
            "foundations for {target} in {}: {:?}",
            path.display(),
            report.foundations
        );
    }
}

#[test]
fn natural_product_order_reflection_theorems_are_foundation_free() {
    check_matrix(
        "natural-product-order-reflection.lim",
        NATURAL_PRODUCT_ORDER_REFLECTION,
    );
}

#[test]
fn eisenstein_natural_norm_transport_theorems_are_foundation_free() {
    check_matrix(
        "eisenstein-natural-norm-transport.lim",
        EISENSTEIN_NATURAL_NORM_TRANSPORT,
    );
}

#[test]
fn eisenstein_euclidean_algebra_theorems_are_foundation_free() {
    check_matrix(
        "eisenstein-euclidean-algebra.lim",
        EISENSTEIN_EUCLIDEAN_ALGEBRA,
    );
}
