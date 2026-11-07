//! Foundation-free checks for Eisenstein cubic normalization components.
use lim::{check_theorem_details_from_path_with_config, CompileConfig, ProofBudget};
use std::path::Path;

const EISENSTEIN_CUBIC_NORMALIZATION: &[&str] = &[
    "eisenstein-cube-root-divides-value",
    "eisenstein-nondivisor-implies-nonzero",
    "eisenstein-cube-root-nondivisor",
    "eisenstein-cube-roots-coprime",
];
const EISENSTEIN_DESCENT_UNIT_LAWS: &[&str] = &[
    "eisenstein-witnessed-inverse-is-unit",
    "eisenstein-units-multiply",
    "eisenstein-unit-negate",
    "eisenstein-unit-power",
];
const EISENSTEIN_CUBIC_LINEAR_ALGEBRA: &[&str] = &[
    "eisenstein-add-three-pairs",
    "eisenstein-annihilating-coefficient-sum",
    "eisenstein-omega-nested-scale",
    "eisenstein-omega-square-nested-scale",
    "eisenstein-omega-weighted-linear-sum",
];
const EISENSTEIN_CUBIC_ROOT_LINEAR: &[&str] = &[
    "eisenstein-cubic-residual-linear-zero",
    "eisenstein-cubic-root-linear-zero",
];
const EISENSTEIN_CUBIC_NORMALIZATION_ALGEBRA: &[&str] = &[
    "eisenstein-multiply-swap-inner",
    "eisenstein-scale-three-sum",
    "eisenstein-three-sum-zero-solve-first",
    "eisenstein-cubic-cancel-common-lambda",
];
const EISENSTEIN_CUBIC_NORMALIZING_SCALES: &[&str] = &[
    "eisenstein-normalizing-scale-times-omega",
    "eisenstein-normalizing-scale-times-omega-square",
    "eisenstein-normalizing-scale-cancels-unit",
    "eisenstein-normalizing-scale-reorders-last",
    "eisenstein-normalizing-negative-scale-cube",
    "eisenstein-normalized-cubic-units",
];
const EISENSTEIN_NORMALIZED_CUBIC_EQUATION: &[&str] = &[
    "eisenstein-normalized-cubic-equation",
    "eisenstein-normalized-cubic-from-factor-equations",
];
const EISENSTEIN_CUBIC_NORMALIZATION_ORDERS: &[&str] = &[
    "natural-cubic-balance-predecessor-order",
    "natural-cubic-balance-has-predecessor",
    "eisenstein-normalized-cubic-from-balanced-factors",
    "eisenstein-normalized-cubic-order-exists",
];

fn cubic_normalization_config() -> CompileConfig {
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
    let config = cubic_normalization_config();

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
fn eisenstein_cubic_normalization_theorems_are_foundation_free() {
    check_matrix(
        "eisenstein-associated-cube-properties.lim",
        EISENSTEIN_CUBIC_NORMALIZATION,
    );
}

#[test]
fn eisenstein_descent_unit_laws_are_foundation_free() {
    check_matrix(
        "eisenstein-descent-unit-laws.lim",
        EISENSTEIN_DESCENT_UNIT_LAWS,
    );
}

#[test]
fn eisenstein_cubic_linear_algebra_theorems_are_foundation_free() {
    check_matrix(
        "eisenstein-cubic-linear-algebra.lim",
        EISENSTEIN_CUBIC_LINEAR_ALGEBRA,
    );
}

#[test]
fn eisenstein_cubic_root_linear_theorems_are_foundation_free() {
    check_matrix(
        "eisenstein-cubic-root-linear.lim",
        EISENSTEIN_CUBIC_ROOT_LINEAR,
    );
}

#[test]
fn eisenstein_cubic_normalization_algebra_theorems_are_foundation_free() {
    check_matrix(
        "eisenstein-cubic-normalization-algebra.lim",
        EISENSTEIN_CUBIC_NORMALIZATION_ALGEBRA,
    );
}

#[test]
fn eisenstein_cubic_normalizing_scales_are_foundation_free() {
    check_matrix(
        "eisenstein-cubic-normalizing-scales.lim",
        EISENSTEIN_CUBIC_NORMALIZING_SCALES,
    );
}

#[test]
fn eisenstein_normalized_cubic_equation_theorems_are_foundation_free() {
    check_matrix(
        "eisenstein-normalized-cubic-equation.lim",
        EISENSTEIN_NORMALIZED_CUBIC_EQUATION,
    );
}

#[test]
fn eisenstein_cubic_normalization_orders_are_foundation_free() {
    check_matrix(
        "eisenstein-cubic-normalization-orders.lim",
        EISENSTEIN_CUBIC_NORMALIZATION_ORDERS,
    );
}
