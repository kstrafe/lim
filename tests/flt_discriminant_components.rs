//! Foundation-free checks for the Frey discriminant components.
use lim::{check_theorem_details_from_path_with_config, CompileConfig, ProofBudget};
use std::path::Path;

const FREY_DISCRIMINANT_FACTOR: &[&str] = &[
    "frey-rational-model-b8",
    "frey-rational-model-b4-as-twice-a4",
    "frey-rational-model-discriminant-factored",
];
const FREY_DISCRIMINANT_FRACTION: &[&str] = &[
    "frey-discriminant-numerator",
    "frey-rational-model-discriminant-fraction",
    "frey-rational-model-discriminant-with-sum",
];
const FREY_DISCRIMINANT_SQUARE_CROSS: &[&str] = &["frey-discriminant-square-cross"];
const FREY_DISCRIMINANT_SQUARE_INTEGER: &[&str] = &["frey-discriminant-square-integer"];
const FREY_DISCRIMINANT_SQUARE: &[&str] = &[
    "frey-rational-discriminant-inner",
    "frey-rational-model-discriminant-square",
];
const FREY_DISCRIMINANT: &[&str] = &[
    "frey-discriminant-denominator",
    "frey-rational-curve-discriminant",
    "frey-rational-curve-discriminant-nonzero",
];
const FREY_PACKAGE_DISCRIMINANT: &[&str] = &[
    "frey-package-discriminant",
    "frey-package-discriminant-nonzero",
];
const INTEGER_POWER_SUMS: &[&str] = &["integer-power-add", "integer-power-square"];
const RATIONAL_DISCRIMINANT_ALGEBRA: &[&str] =
    &["rational-eight-twice-cube", "rational-discriminant-factor"];
const RATIONAL_FRACTION_PRODUCTS: &[&str] = &[
    "rational-fraction-square",
    "rational-fraction-times-integer",
];
const RATIONAL_POWER_LAWS: &[&str] = &[
    "rational-power-one",
    "rational-power-two",
    "rational-multiply-swap-inner",
    "rational-multiply-four-interchange",
    "rational-power-product",
    "rational-square-negative",
    "rational-two-cubed",
    "rational-eight-times-eight",
];
const RATIONAL_SIGN_LAWS: &[&str] = &[
    "rational-negate-zero",
    "rational-zero-multiply",
    "rational-one-multiply",
    "rational-zero-add",
    "rational-multiply-negative",
    "rational-multiply-negative-second",
    "rational-multiply-two-negatives",
    "rational-negate-add",
];
const WEIERSTRASS_ZERO_B6: &[&str] = &["weierstrass-discriminant-zero-b6"];
const RATIONAL_UNITS: &[&str] = &[
    "rational-positive-magnitude-reciprocal",
    "rational-negative-magnitude-reciprocal",
    "rational-nonzero-is-unit",
    "rational-unit-is-nonzero",
];
const FREY_ELLIPTIC: &[&str] = &[
    "rational-weierstrass-nonzero-discriminant-is-elliptic",
    "frey-package-is-elliptic",
];

fn discriminant_components_config() -> CompileConfig {
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
    let config = discriminant_components_config();

    for &target in targets {
        let report = check_theorem_details_from_path_with_config(&source, &path, &config, target)
            .unwrap_or_else(|error| {
                panic!(
                    "failed to check {target} in {}: {}",
                    path.display(),
                    error.message
                )
            });
        assert_eq!(
            report.name,
            format!("{}::{target}", path.canonicalize().unwrap().display()),
            "unexpected canonical target for {}",
            path.display()
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
fn frey_discriminant_factor_theorems_are_foundation_free() {
    check_matrix("frey-discriminant-factor.lim", FREY_DISCRIMINANT_FACTOR);
}

#[test]
fn frey_discriminant_fraction_theorems_are_foundation_free() {
    check_matrix("frey-discriminant-fraction.lim", FREY_DISCRIMINANT_FRACTION);
}

#[test]
fn frey_discriminant_square_cross_theorem_is_foundation_free() {
    check_matrix(
        "frey-discriminant-square-cross.lim",
        FREY_DISCRIMINANT_SQUARE_CROSS,
    );
}

#[test]
fn frey_discriminant_square_integer_theorem_is_foundation_free() {
    check_matrix(
        "frey-discriminant-square-integer.lim",
        FREY_DISCRIMINANT_SQUARE_INTEGER,
    );
}

#[test]
fn frey_discriminant_square_theorems_are_foundation_free() {
    check_matrix("frey-discriminant-square.lim", FREY_DISCRIMINANT_SQUARE);
}

#[test]
fn frey_discriminant_theorems_are_foundation_free() {
    check_matrix("frey-discriminant.lim", FREY_DISCRIMINANT);
}

#[test]
fn frey_package_discriminant_theorems_are_foundation_free() {
    check_matrix("frey-package-discriminant.lim", FREY_PACKAGE_DISCRIMINANT);
}

#[test]
fn integer_power_sum_theorems_are_foundation_free() {
    check_matrix("integer-power-sums.lim", INTEGER_POWER_SUMS);
}

#[test]
fn rational_discriminant_algebra_theorems_are_foundation_free() {
    check_matrix(
        "rational-discriminant-algebra.lim",
        RATIONAL_DISCRIMINANT_ALGEBRA,
    );
}

#[test]
fn rational_fraction_product_theorems_are_foundation_free() {
    check_matrix("rational-fraction-products.lim", RATIONAL_FRACTION_PRODUCTS);
}

#[test]
fn rational_power_law_theorems_are_foundation_free() {
    check_matrix("rational-power-laws.lim", RATIONAL_POWER_LAWS);
}

#[test]
fn rational_sign_law_theorems_are_foundation_free() {
    check_matrix("rational-sign-laws.lim", RATIONAL_SIGN_LAWS);
}

#[test]
fn weierstrass_zero_b6_theorem_is_foundation_free() {
    check_matrix("weierstrass-zero-b6.lim", WEIERSTRASS_ZERO_B6);
}

#[test]
fn rational_unit_theorems_are_foundation_free() {
    check_matrix("rational-units.lim", RATIONAL_UNITS);
}

#[test]
fn frey_elliptic_theorems_are_foundation_free() {
    check_matrix("frey-elliptic.lim", FREY_ELLIPTIC);
}
