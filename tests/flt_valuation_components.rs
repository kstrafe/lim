//! Every local valuation declaration is checked independently with no added axioms.
use lim::{check_theorem_details_from_path_with_config, CompileConfig, ProofBudget};
use std::path::Path;

const NATURAL_EXISTENCE: &[&str] = &[
    "natural-prime-order-zero",
    "natural-prime-order-step",
    "natural-prime-order-exists",
];
const NATURAL_BOUNDS: &[&str] = &[
    "natural-prime-order-power-divides",
    "natural-prime-order-next-nondivisor",
    "natural-prime-order-excludes-higher",
    "natural-prime-order-nonzero",
];
const NATURAL_UNIQUENESS: &[&str] = &[
    "natural-prime-order-unique",
    "natural-prime-order-congruent",
    "natural-prime-order-one",
];
const NATURAL_ARITHMETIC: &[&str] = &[
    "natural-valuation-factor-interchange",
    "natural-prime-order-multiply",
    "natural-prime-order-power",
];
const INTEGER_EXISTENCE: &[&str] = &[
    "integer-prime-order-natural",
    "integer-prime-order-exists",
    "integer-prime-order-zero",
    "integer-prime-order-one",
];
const INTEGER_UNIQUENESS: &[&str] = &[
    "integer-prime-order-unique",
    "integer-prime-order-congruent",
    "integer-prime-order-nonzero",
];
const INTEGER_ARITHMETIC: &[&str] = &["integer-prime-order-multiply", "integer-prime-order-power"];
const INTEGER_COFACTORS: &[&str] = &[
    "integer-prime-factor-embedding",
    "integer-prime-order-cofactor",
];
const INTEGER_SCALING: &[&str] = &[
    "integer-prime-order-nondivisor-factor",
    "integer-prime-order-scaled-power",
];
const FREY_LOCAL: &[&str] = &[
    "integer-frey-discriminant-valuation-away-two",
    "frey-package-discriminant-valuation-away-two",
    "frey-package-has-local-valuations-away-two",
];
const FREY_TWO: &[&str] = &[
    "integer-two-eighth-power-order",
    "integer-frey-discriminant-valuation-at-two",
    "frey-package-discriminant-valuation-at-two",
    "frey-package-has-local-valuations-at-two",
];

fn valuation_config() -> CompileConfig {
    let default = ProofBudget::default();
    let mut config = CompileConfig::default();
    config.set_proof_budget(
        ProofBudget::new(default.work(), default.phase_bytes(), 1024 * 1024 * 1024).unwrap(),
    );
    config
}

fn matrix(module: &str, targets: &[&str]) {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("theorems/flt")
        .join(format!("{module}.lim"));
    let source = std::fs::read_to_string(&path).unwrap();
    let config = valuation_config();
    for &target in targets {
        let report = check_theorem_details_from_path_with_config(&source, &path, &config, target)
            .unwrap_or_else(|e| panic!("{module}::{target}: {}", e.message));
        assert_eq!(
            report.name,
            format!("{}::{target}", path.canonicalize().unwrap().display())
        );
        assert!(
            report.foundations.is_empty(),
            "{target}: {:?}",
            report.foundations
        );
    }
}

#[test]
fn natural_existence_is_foundation_free() {
    matrix("natural-prime-order-existence", NATURAL_EXISTENCE);
}
#[test]
fn natural_bounds_are_foundation_free() {
    matrix("natural-prime-order-bounds", NATURAL_BOUNDS);
}
#[test]
fn natural_uniqueness_is_foundation_free() {
    matrix("natural-prime-order-uniqueness", NATURAL_UNIQUENESS);
}
#[test]
fn natural_arithmetic_is_foundation_free() {
    matrix("natural-prime-order-arithmetic", NATURAL_ARITHMETIC);
}
#[test]
fn integer_existence_is_foundation_free() {
    matrix("integer-prime-order-existence", INTEGER_EXISTENCE);
}
#[test]
fn integer_uniqueness_is_foundation_free() {
    matrix("integer-prime-order-uniqueness", INTEGER_UNIQUENESS);
}
#[test]
fn integer_arithmetic_is_foundation_free() {
    matrix("integer-prime-order-arithmetic", INTEGER_ARITHMETIC);
}
#[test]
fn integer_cofactors_are_foundation_free() {
    matrix("integer-prime-order-cofactors", INTEGER_COFACTORS);
}
#[test]
fn integer_scaling_is_foundation_free() {
    matrix("integer-prime-order-scaling", INTEGER_SCALING);
}
#[test]
fn frey_local_valuations_are_foundation_free() {
    matrix("frey-local-valuations", FREY_LOCAL);
}

#[test]
fn frey_two_valuations_are_foundation_free() {
    matrix("frey-local-valuations-two", FREY_TWO);
}
