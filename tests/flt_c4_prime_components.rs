//! Foundation-free checks for the FLT C4 prime components.
use lim::{check_theorem_details_from_path_with_config, CompileConfig, ProofBudget};
use std::path::Path;

const FREY_C4_ALTERNATE_CROSS: &[&str] = &["integer-c4-alternate-cross"];
const FREY_C4_ALTERNATE: &[&str] = &[
    "integer-c4-alternate-polynomial",
    "frey-c4-power-equation-alternate",
    "frey-c4-power-equation-doubled",
    "frey-rational-curve-c4-alternate",
    "integer-frey-c4-alternate",
];
const FREY_C4_PRIME_DIVISIBILITY: &[&str] = &[
    "frey-c4-prime-first-impossible",
    "frey-c4-prime-second-impossible",
    "frey-c4-prime-third-impossible",
    "frey-c4-prime-nondivisibility",
];
const FREY_PACKAGE_C4_PRIMES: &[&str] = &[
    "frey-package-rational-c4-alternate",
    "frey-package-integral-c4-prime-nondivisibility",
    "frey-package-integral-discriminant-prime-divisor",
    "frey-package-prime-disjoint-invariants",
];
const INTEGER_FREY_C4_PRIMES: &[&str] = &[
    "integer-frey-c4-prime-nondivisibility",
    "integer-frey-discriminant-prime-divisor",
    "integer-frey-discriminant-c4-prime-disjoint",
];
const INTEGER_PRIME_COPRIMALITY: &[&str] = &[
    "integer-divides-positive-power",
    "integer-prime-not-divides-one",
    "integer-prime-coprime-common",
    "integer-prime-solution-common-first-third",
    "integer-prime-solution-common-second-third",
];
const INTEGER_WEIERSTRASS_EVALUATION: &[&str] = &["integer-weierstrass-discriminant-evaluate"];

fn c4_prime_components_config() -> CompileConfig {
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
    let config = c4_prime_components_config();

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
fn frey_c4_alternate_cross_theorems_are_foundation_free() {
    check_matrix("frey-c4-alternate-cross.lim", FREY_C4_ALTERNATE_CROSS);
}

#[test]
fn frey_c4_alternate_theorems_are_foundation_free() {
    check_matrix("frey-c4-alternate.lim", FREY_C4_ALTERNATE);
}

#[test]
fn frey_c4_prime_divisibility_theorems_are_foundation_free() {
    check_matrix("frey-c4-prime-divisibility.lim", FREY_C4_PRIME_DIVISIBILITY);
}

#[test]
fn frey_package_c4_primes_theorems_are_foundation_free() {
    check_matrix("frey-package-c4-primes.lim", FREY_PACKAGE_C4_PRIMES);
}

#[test]
fn integer_frey_c4_primes_theorems_are_foundation_free() {
    check_matrix("integer-frey-c4-primes.lim", INTEGER_FREY_C4_PRIMES);
}

#[test]
fn integer_prime_coprimality_theorems_are_foundation_free() {
    check_matrix("integer-prime-coprimality.lim", INTEGER_PRIME_COPRIMALITY);
}

#[test]
fn integer_weierstrass_evaluation_is_foundation_free() {
    check_matrix(
        "integer-weierstrass-evaluation.lim",
        INTEGER_WEIERSTRASS_EVALUATION,
    );
}
