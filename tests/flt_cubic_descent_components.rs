//! Foundation-free checks for Eisenstein cubic descent residue components.
use lim::{check_theorem_details_from_path_with_config, CompileConfig, ProofBudget};
use std::path::Path;

const EISENSTEIN_WEIGHTED_RESIDUE_ALGEBRA: &[&str] = &[
    "eisenstein-divides-replace-residue",
    "eisenstein-weighted-residue-sum",
    "eisenstein-positive-signed-residue",
    "eisenstein-negative-signed-residue",
];
const EISENSTEIN_NORMALIZED_CUBIC_SIGN: &[&str] = &[
    "eisenstein-normalized-coefficient-integer-congruence",
    "eisenstein-normalized-cubic-coefficient-sign",
];
const EISENSTEIN_CUBIC_SQUARE_DIVISOR: &[&str] = &[
    "eisenstein-square-divides-scaled-factor-cube",
    "eisenstein-square-divides-scaled-cube-from-divisor",
];
const EISENSTEIN_CUBIC_DESCENT_ORDERS: &[&str] = &[
    "natural-cubic-predecessor-positive",
    "natural-cubic-predecessor-smaller",
    "eisenstein-positive-lambda-power-product-divides",
    "eisenstein-lambda-powered-free-residual-order",
    "eisenstein-lambda-powered-free-residual-nonzero",
];
const EISENSTEIN_CUBIC_SIGNED_COEFFICIENT: &[&str] = &[
    "eisenstein-signed-coefficient-cube",
    "eisenstein-signed-coefficient-product-cube",
    "eisenstein-signed-cubic-absorption",
    "eisenstein-unit-product-nondivisor",
    "eisenstein-coprime-unit-product-right",
];
const EISENSTEIN_CUBIC_DESCENT_DEFS: &[&str] = &["eisenstein-cubic-solution-has-exact-order"];
const EISENSTEIN_CUBIC_NORMALIZED_DESCENT: &[&str] = &[
    "eisenstein-normalized-cubic-smaller-ordered-solution",
    "eisenstein-normalized-cubic-has-smaller-solution",
];
const EISENSTEIN_CUBIC_PACKET_DESCENT: &[&str] = &[
    "eisenstein-cubic-root-inverse-smaller-solution",
    "eisenstein-cubic-root-witnesses-smaller-solution",
    "eisenstein-cubic-two-roots-smaller-solution",
    "eisenstein-cubic-residual-packet-has-smaller-solution",
];
const EISENSTEIN_CUBIC_SOLUTION_DESCENT: &[&str] = &[
    "eisenstein-oriented-cubic-primary-has-smaller-solution",
    "eisenstein-oriented-cubic-has-smaller-solution",
    "eisenstein-cubic-ordered-solution-has-smaller-solution",
];
const EISENSTEIN_CUBIC_DESCENT: &[&str] = &[
    "eisenstein-cubic-descent-induction-step",
    "eisenstein-cubic-no-solution-at-order",
    "eisenstein-fermat-three-general-proved",
];
const FERMAT_THREE: &[&str] = &["fermat-for-three"];

fn cubic_descent_config() -> CompileConfig {
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
    let config = cubic_descent_config();

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
fn eisenstein_weighted_residue_algebra_theorems_are_foundation_free() {
    check_matrix(
        "eisenstein-weighted-residue-algebra.lim",
        EISENSTEIN_WEIGHTED_RESIDUE_ALGEBRA,
    );
}

#[test]
fn eisenstein_normalized_cubic_sign_theorems_are_foundation_free() {
    check_matrix(
        "eisenstein-normalized-cubic-sign.lim",
        EISENSTEIN_NORMALIZED_CUBIC_SIGN,
    );
}

#[test]
fn eisenstein_cubic_square_divisor_theorems_are_foundation_free() {
    check_matrix(
        "eisenstein-cubic-square-divisor.lim",
        EISENSTEIN_CUBIC_SQUARE_DIVISOR,
    );
}

#[test]
fn eisenstein_cubic_descent_orders_theorems_are_foundation_free() {
    check_matrix(
        "eisenstein-cubic-descent-orders.lim",
        EISENSTEIN_CUBIC_DESCENT_ORDERS,
    );
}

#[test]
fn eisenstein_cubic_signed_coefficient_theorems_are_foundation_free() {
    check_matrix(
        "eisenstein-cubic-signed-coefficient.lim",
        EISENSTEIN_CUBIC_SIGNED_COEFFICIENT,
    );
}

#[test]
fn eisenstein_cubic_descent_defs_theorems_are_foundation_free() {
    check_matrix(
        "eisenstein-cubic-descent-defs.lim",
        EISENSTEIN_CUBIC_DESCENT_DEFS,
    );
}

#[test]
fn eisenstein_cubic_normalized_descent_theorems_are_foundation_free() {
    check_matrix(
        "eisenstein-cubic-normalized-descent.lim",
        EISENSTEIN_CUBIC_NORMALIZED_DESCENT,
    );
}

#[test]
fn eisenstein_cubic_packet_descent_theorems_are_foundation_free() {
    check_matrix(
        "eisenstein-cubic-packet-descent.lim",
        EISENSTEIN_CUBIC_PACKET_DESCENT,
    );
}

#[test]
fn eisenstein_cubic_solution_descent_theorems_are_foundation_free() {
    check_matrix(
        "eisenstein-cubic-solution-descent.lim",
        EISENSTEIN_CUBIC_SOLUTION_DESCENT,
    );
}

#[test]
fn eisenstein_cubic_descent_theorems_are_foundation_free() {
    check_matrix("eisenstein-cubic-descent.lim", EISENSTEIN_CUBIC_DESCENT);
}

#[test]
fn fermat_three_theorem_is_foundation_free() {
    check_matrix("fermat-three.lim", FERMAT_THREE);
}
