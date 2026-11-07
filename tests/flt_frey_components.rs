//! Foundation-free checks for the natural-power Frey descent components.
use lim::{check_theorem_details_from_path_with_config, CompileConfig, ProofBudget};
use std::path::Path;

const NATURAL_POWER_PRODUCTS: &[&str] = &[
    "power-product",
    "power-congruent",
    "divides-power-successor",
    "divides-positive-power",
];
const FERMAT_POWER_FACTOR_DESCENT: &[&str] = &[
    "power-common-prime-divides-third",
    "power-remove-common-factor",
    "power-solution-remove-prime",
    "power-common-prime-descends",
];
const FERMAT_POWER_PRIMITIVE: &[&str] = &[
    "natural-power-primitive-induction-step",
    "natural-power-has-primitive",
    "natural-power-refuted-by-primitive",
    "fermat-for-from-primitive-power",
];
const INTEGER_POWER_LAWS: &[&str] = &[
    "integer-power-congruent",
    "integer-power-of-natural",
    "natural-double-successor-shape",
    "integer-negative-even-power",
    "integer-negative-odd-power",
];
const FERMAT_POWER_COPRIMALITY: &[&str] = &[
    "power-solution-first-third-coprime",
    "power-solution-second-third-coprime",
    "odd-positive-base-power",
    "power-solution-odd-first-second-third-even",
];
const FREY_SIGNED_POWER_EQUATIONS: &[&str] = &[
    "integer-sum-reorder-negative",
    "integer-odd-power-reorder-equation",
    "integer-odd-power-negate-equation",
    "natural-power-integer-equation",
];
const FREY_EVEN_POWER_PACKET: &[&str] = &[
    "natural-power-positive-even-packet",
    "natural-power-reordered-even-packet",
    "natural-primitive-power-has-even-signed-packet",
];
const NATURAL_FOUR_REMAINDERS: &[&str] = &["less-than-four-cases"];
const INTEGER_MOD_FOUR_NORMALIZATION: &[&str] = &[
    "integer-gcd-one-even-second-first-not-even",
    "integer-multiple-of-four-even",
    "integer-successor-times-four",
    "integer-negative-one-mod-four-is-three",
    "integer-division-four-sign-cases",
    "integer-not-even-mod-four-sign-cases",
];
const FREY_NORMALIZED_POWER_PACKET: &[&str] = &[
    "integer-even-power-packet-negate",
    "integer-even-power-packet-has-normalized-sign",
    "natural-primitive-power-has-normalized-signed-packet",
];
const FREY_PACKAGE: &[&str] = &[
    "large-prime-positive-and-odd",
    "normalized-power-packet-has-frey-package",
    "natural-power-counterexample-has-frey-package",
    "fermat-for-large-prime-from-frey-refutation",
    "fermat-statement-from-frey-refutation",
];

fn frey_components_config() -> CompileConfig {
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
    let config = frey_components_config();

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
fn natural_power_products_theorems_are_foundation_free() {
    check_matrix("natural-power-products.lim", NATURAL_POWER_PRODUCTS);
}

#[test]
fn fermat_power_factor_descent_theorems_are_foundation_free() {
    check_matrix(
        "fermat-power-factor-descent.lim",
        FERMAT_POWER_FACTOR_DESCENT,
    );
}

#[test]
fn fermat_power_primitive_theorems_are_foundation_free() {
    check_matrix("fermat-power-primitive.lim", FERMAT_POWER_PRIMITIVE);
}

#[test]
fn integer_power_laws_theorems_are_foundation_free() {
    check_matrix("integer-power-laws.lim", INTEGER_POWER_LAWS);
}

#[test]
fn fermat_power_coprimality_theorems_are_foundation_free() {
    check_matrix("fermat-power-coprimality.lim", FERMAT_POWER_COPRIMALITY);
}

#[test]
fn frey_signed_power_equations_theorems_are_foundation_free() {
    check_matrix(
        "frey-signed-power-equations.lim",
        FREY_SIGNED_POWER_EQUATIONS,
    );
}

#[test]
fn frey_even_power_packet_theorems_are_foundation_free() {
    check_matrix("frey-even-power-packet.lim", FREY_EVEN_POWER_PACKET);
}

#[test]
fn natural_four_remainders_theorem_is_foundation_free() {
    check_matrix("natural-four-remainders.lim", NATURAL_FOUR_REMAINDERS);
}

#[test]
fn integer_mod_four_normalization_theorems_are_foundation_free() {
    check_matrix(
        "integer-mod-four-normalization.lim",
        INTEGER_MOD_FOUR_NORMALIZATION,
    );
}

#[test]
fn frey_normalized_power_packet_theorems_are_foundation_free() {
    check_matrix(
        "frey-normalized-power-packet.lim",
        FREY_NORMALIZED_POWER_PACKET,
    );
}

#[test]
fn frey_package_theorems_are_foundation_free() {
    check_matrix("frey-package.lim", FREY_PACKAGE);
}
