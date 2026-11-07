//! Audit every valuation consequence and the exact source model predicates.
use lim::{check_theorem_details_from_path_with_config, CompileConfig, ProofBudget};
use std::path::Path;

const NATURAL: &[&str] = &[
    "natural-exponent-divides-doubled-value",
    "natural-above-four-not-two",
    "natural-prime-divides-two-only-two",
    "natural-prime-away-two-not-divides-eight",
    "natural-shifted-valuation-nondivisible",
    "natural-shifted-valuation-nondivisible-above-four",
];
const FREY_DIVISIBILITY: &[&str] = &[
    "frey-package-exponent-divides-away-two-valuation",
    "frey-package-exponent-not-divides-two-valuation",
    "frey-package-has-divisible-away-two-valuation",
    "frey-package-has-nondivisible-two-valuation",
];
const MODEL_PRIMES: &[&str] = &[
    "integer-model-equivalence-maps-rational",
    "integer-model-c4-equivalent",
    "integer-model-discriminant-equivalent",
    "integer-semistable-model-equivalent",
    "integer-good-prime-equivalent",
    "integer-c4-one-is-semistable-model",
];
const FREY_SEMISTABLE: &[&str] = &[
    "frey-package-is-semistable-model",
    "frey-package-has-semistable-model",
];

fn consequences_config(module: &str) -> CompileConfig {
    let default = ProofBudget::default();
    let mut config = CompileConfig::default();
    // This bounds cumulative allocation, not simultaneous resident memory.
    // Combining integral-model construction and its invariant proof needs
    // a larger total allowance; work and per-phase limits remain unchanged.
    let total = if module == "frey-semistable-model" {
        2
    } else {
        1
    };
    config.set_proof_budget(
        ProofBudget::new(
            default.work(),
            default.phase_bytes(),
            total * 1024 * 1024 * 1024,
        )
        .unwrap(),
    );
    config
}

fn matrix(module: &str, targets: &[&str]) {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("theorems/flt")
        .join(format!("{module}.lim"));
    let source = std::fs::read_to_string(&path).unwrap();
    let names: Vec<_> = source
        .lines()
        .filter_map(|line| {
            line.strip_prefix("(#theorem ")
                .and_then(|tail| tail.split_whitespace().next())
        })
        .collect();
    assert_eq!(
        names, targets,
        "every declaration must have an audit target"
    );
    let config = consequences_config(module);
    for &target in targets {
        let report = check_theorem_details_from_path_with_config(&source, &path, &config, target)
            .unwrap_or_else(|error| panic!("{module}::{target}: {}", error.message));
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
fn natural_valuation_divisibility_is_foundation_free() {
    matrix("natural-valuation-divisibility", NATURAL);
}
#[test]
fn frey_valuation_divisibility_is_foundation_free() {
    matrix("frey-valuation-divisibility", FREY_DIVISIBILITY);
}
#[test]
fn model_prime_transport_is_foundation_free() {
    matrix("integer-model-primes", MODEL_PRIMES);
}
#[test]
fn frey_semistable_model_construction_is_foundation_free() {
    matrix("frey-semistable-model", FREY_SEMISTABLE);
}
