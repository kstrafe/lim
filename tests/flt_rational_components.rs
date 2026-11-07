//! Foundation-free checks for rational arithmetic components.
use lim::{check_theorem_details_from_path_with_config, CompileConfig, ProofBudget};
use std::path::Path;

const INTEGER_CROSS_PRODUCTS: &[&str] = &[
    "integer-multiply-swap-inner",
    "integer-multiply-four-interchange",
    "integer-cross-product-transitive",
];
const INTEGER_FRACTION_SUMS: &[&str] = &[
    "integer-cross-sum-congruent",
    "integer-cross-sum-associative",
];
const INTEGER_FRACTION_DISTRIBUTIVE: &[&str] = &["integer-cross-left-distributive"];
const INTEGER_POWER_PRODUCTS: &[&str] = &["integer-power-product", "integer-power-nonzero"];
const RATIONAL_EQUALITY: &[&str] = &[
    "rational-reflexive",
    "rational-symmetric",
    "rational-transitive",
    "rational-fraction-zero-implies-numerator-zero",
    "rational-zero-numerator",
    "rational-fraction-nonzero",
];
const RATIONAL_CONGRUENCE: &[&str] = &[
    "rational-components-congruent",
    "rational-negate-congruent",
    "rational-multiply-congruent",
    "rational-add-congruent",
    "rational-of-integer-congruent",
    "rational-of-integer-add",
    "rational-of-integer-multiply",
];
const RATIONAL_RING: &[&str] = &[
    "rational-multiply-commutative",
    "rational-multiply-associative",
    "rational-multiply-one",
    "rational-multiply-zero",
    "rational-add-commutative",
    "rational-add-associative",
    "rational-add-zero",
    "rational-add-inverse",
    "rational-negate-involution",
    "rational-multiply-distribute-second",
    "rational-nonzero-numerator",
    "rational-nonzero-product",
    "rational-power-nonzero",
];
const RATIONAL_FRACTIONS: &[&str] = &[
    "rational-integer-embedding-injective",
    "rational-nonzero-integer",
    "rational-fraction-times-denominator",
    "rational-fraction-natural-factor-cancel",
    "rational-power-congruent",
    "rational-one-power",
    "rational-zero-power-successor",
];
const FREY_RATIONAL_CURVE: &[&str] = &[
    "frey-rational-model-b2",
    "frey-rational-model-b4",
    "frey-rational-model-b6",
    "frey-rational-curve-b2",
    "frey-rational-curve-b4",
    "frey-rational-curve-a4-nonzero",
];

fn rational_components_config() -> CompileConfig {
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
    let config = rational_components_config();

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
fn integer_cross_product_theorems_are_foundation_free() {
    check_matrix("integer-cross-products.lim", INTEGER_CROSS_PRODUCTS);
}

#[test]
fn integer_fraction_sum_theorems_are_foundation_free() {
    check_matrix("integer-fraction-sums.lim", INTEGER_FRACTION_SUMS);
}

#[test]
fn integer_fraction_distributive_theorem_is_foundation_free() {
    check_matrix(
        "integer-fraction-distributive.lim",
        INTEGER_FRACTION_DISTRIBUTIVE,
    );
}

#[test]
fn integer_power_product_theorems_are_foundation_free() {
    check_matrix("integer-power-products.lim", INTEGER_POWER_PRODUCTS);
}

#[test]
fn rational_equality_theorems_are_foundation_free() {
    check_matrix("rational-equality.lim", RATIONAL_EQUALITY);
}

#[test]
fn rational_congruence_theorems_are_foundation_free() {
    check_matrix("rational-congruence.lim", RATIONAL_CONGRUENCE);
}

#[test]
fn rational_ring_theorems_are_foundation_free() {
    check_matrix("rational-ring.lim", RATIONAL_RING);
}

#[test]
fn rational_fraction_theorems_are_foundation_free() {
    check_matrix("rational-fractions.lim", RATIONAL_FRACTIONS);
}

#[test]
fn frey_rational_curve_theorems_are_foundation_free() {
    check_matrix("frey-rational-curve.lim", FREY_RATIONAL_CURVE);
}
