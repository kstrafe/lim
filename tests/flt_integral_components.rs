//! Foundation-free checks for the integral FLT components.
use lim::{check_theorem_details_from_path_with_config, CompileConfig, ProofBudget};
use std::path::Path;

const FREY_COEFFICIENT_DIVISIBILITY: &[&str] = &[
    "integer-three-mod-four-plus-one-divisible",
    "integer-three-mod-four-odd-power-plus-one-divisible",
    "integer-even-large-power-divisible-four",
    "integer-even-large-power-divisible-sixteen",
    "frey-integral-coefficients-divisible",
];
const FREY_PACKAGE_COEFFICIENTS: &[&str] = &["frey-package-coefficients-divisible"];
const FREY_PACKAGE_INTEGRAL_MODEL: &[&str] = &[
    "frey-package-has-integral-model",
    "frey-package-integral-discriminant",
    "frey-package-integral-discriminant-nonzero",
];
const INTEGER_FREY_A2_REARRANGE_CROSS: &[&str] = &["integer-frey-a2-rearrange-cross"];
const INTEGER_FREY_INVARIANTS: &[&str] = &[
    "integer-frey-c4-rational",
    "integer-frey-discriminant-rational",
    "integer-frey-c4",
    "integer-frey-discriminant-multiplied",
    "integer-frey-discriminant-nonzero",
];
const INTEGER_FREY_MODEL: &[&str] = &[
    "rational-exact-integer-quotient",
    "integer-frey-quotients-map",
    "integer-frey-model-exists",
    "integer-frey-model-unique",
];
const INTEGER_INTEGRAL_IDENTITIES: &[&str] = &[
    "integer-power-difference-step",
    "integer-frey-a2-rearrange",
    "integer-add-swap-last",
];
const INTEGER_POWER_DIFFERENCE_STEP_CROSS: &[&str] = &["integer-power-difference-step-cross"];
const INTEGER_POWER_DIFFERENCES: &[&str] = &["integer-power-difference-divides"];
const INTEGER_POWER_DIVISIBILITY: &[&str] = &[
    "integer-divides-product-left",
    "integer-divides-product-right",
    "integer-divides-product-powers",
    "integer-power-prefix-divides",
    "integer-power-strict-prefix-divides",
    "integer-one-power",
];
const INTEGER_WEIERSTRASS_MAP: &[&str] = &[
    "integer-weierstrass-b2-map",
    "integer-weierstrass-b4-map",
    "integer-weierstrass-b6-map",
    "integer-weierstrass-b8-map",
    "integer-weierstrass-c4-map",
    "integer-weierstrass-c6-map",
    "integer-weierstrass-discriminant-map",
];
const WEIERSTRASS_INVARIANT_CONGRUENCE: &[&str] = &[
    "rational-weierstrass-b2-congruent",
    "rational-weierstrass-b4-congruent",
    "rational-weierstrass-b6-congruent",
    "rational-weierstrass-b8-congruent",
    "rational-weierstrass-c4-congruent",
    "rational-weierstrass-c6-congruent",
    "rational-weierstrass-discriminant-congruent",
];
const WEIERSTRASS_MODEL_EQUIVALENCE: &[&str] = &[
    "rational-weierstrass-reflexive",
    "rational-weierstrass-symmetric",
    "rational-weierstrass-transitive",
    "integer-weierstrass-map-injective",
];

fn integral_components_config() -> CompileConfig {
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
    let config = integral_components_config();

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
fn frey_coefficient_divisibility_theorems_are_foundation_free() {
    check_matrix(
        "frey-coefficient-divisibility.lim",
        FREY_COEFFICIENT_DIVISIBILITY,
    );
}

#[test]
fn frey_package_coefficients_theorems_are_foundation_free() {
    check_matrix("frey-package-coefficients.lim", FREY_PACKAGE_COEFFICIENTS);
}

#[test]
fn frey_package_integral_model_theorems_are_foundation_free() {
    check_matrix(
        "frey-package-integral-model.lim",
        FREY_PACKAGE_INTEGRAL_MODEL,
    );
}

#[test]
fn integer_frey_a2_rearrange_cross_theorems_are_foundation_free() {
    check_matrix(
        "integer-frey-a2-rearrange-cross.lim",
        INTEGER_FREY_A2_REARRANGE_CROSS,
    );
}

#[test]
fn integer_frey_invariants_theorems_are_foundation_free() {
    check_matrix("integer-frey-invariants.lim", INTEGER_FREY_INVARIANTS);
}

#[test]
fn integer_frey_model_theorems_are_foundation_free() {
    check_matrix("integer-frey-model.lim", INTEGER_FREY_MODEL);
}

#[test]
fn integer_integral_identities_theorems_are_foundation_free() {
    check_matrix(
        "integer-integral-identities.lim",
        INTEGER_INTEGRAL_IDENTITIES,
    );
}

#[test]
fn integer_power_difference_step_cross_theorems_are_foundation_free() {
    check_matrix(
        "integer-power-difference-step-cross.lim",
        INTEGER_POWER_DIFFERENCE_STEP_CROSS,
    );
}

#[test]
fn integer_power_differences_theorems_are_foundation_free() {
    check_matrix("integer-power-differences.lim", INTEGER_POWER_DIFFERENCES);
}

#[test]
fn integer_power_divisibility_theorems_are_foundation_free() {
    check_matrix("integer-power-divisibility.lim", INTEGER_POWER_DIVISIBILITY);
}

#[test]
fn integer_weierstrass_map_theorems_are_foundation_free() {
    check_matrix("integer-weierstrass-map.lim", INTEGER_WEIERSTRASS_MAP);
}

#[test]
fn weierstrass_invariant_congruence_theorems_are_foundation_free() {
    check_matrix(
        "weierstrass-invariant-congruence.lim",
        WEIERSTRASS_INVARIANT_CONGRUENCE,
    );
}

#[test]
fn weierstrass_model_equivalence_theorems_are_foundation_free() {
    check_matrix(
        "weierstrass-model-equivalence.lim",
        WEIERSTRASS_MODEL_EQUIVALENCE,
    );
}
