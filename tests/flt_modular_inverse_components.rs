//! Inventory and check every native strong-recursion/extended-gcd/inverse theorem.
use lim::{check_theorem_details_from_path_with_config, CompileConfig, ProofBudget};
use std::path::Path;
fn matrix(module: &str, expected: &[&str]) {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("theorems/flt")
        .join(format!("{module}.lim"));
    let source = std::fs::read_to_string(&path).unwrap();
    let declared: Vec<_> = source
        .lines()
        .filter_map(|line| line.strip_prefix("(#theorem ")?.split_whitespace().next())
        .collect();
    assert_eq!(
        declared, expected,
        "every native theorem must be inventoried"
    );
    let target = expected.last().unwrap();
    let mut config = CompileConfig::default();
    let budget = ProofBudget::default();
    config.set_proof_budget(
        ProofBudget::new(budget.work(), budget.phase_bytes(), 1024 * 1024 * 1024).unwrap(),
    );
    let report = check_theorem_details_from_path_with_config(&source, &path, &config, target)
        .unwrap_or_else(|e| panic!("{module}: {}", e.message));
    assert_eq!(
        report.name,
        format!("{}::{target}", path.canonicalize().unwrap().display())
    );
    assert!(report.foundations.is_empty());
}

#[test]
fn finite_prime_field_laws() {
    matrix(
        "finite-prime-field-laws",
        &[
            "finite-prime-multiply-cancel",
            "finite-prime-inverse-involutive-nonzero",
            "finite-prime-inverse-involutive",
            "finite-prime-product-nonzero",
        ],
    );
}

#[test]
fn finite_prime_inverses() {
    matrix(
        "finite-prime-inverses",
        &[
            "modular-prime-positive",
            "finite-prime-residue-coprime",
            "finite-prime-inverse-product",
            "finite-prime-inverse-product-reversed",
            "finite-prime-one-nonzero",
            "finite-prime-inverse-nonzero",
        ],
    );
}

#[test]
fn finite_residue_bezout_reduction() {
    matrix(
        "finite-residue-bezout-reduction",
        &["finite-residue-bezout-reduction"],
    );
}

#[test]
fn finite_residue_canonical_casts() {
    matrix(
        "finite-residue-canonical-casts",
        &[
            "finite-residue-natural-representative",
            "finite-residue-integer-representative",
            "finite-residue-natural-modulus-zero",
            "finite-residue-integer-modulus-zero",
        ],
    );
}

#[test]
fn finite_residue_inverse_units() {
    matrix(
        "finite-residue-inverse-units",
        &[
            "finite-inverse-natural-coprime-product",
            "finite-residue-inverse-coprime-product",
            "finite-residue-natural-coprime",
            "finite-residue-inverse-one",
            "finite-residue-multiplicative-inverse-unique",
        ],
    );
}

#[test]
fn finite_residue_inverses() {
    matrix(
        "finite-residue-inverses",
        &[
            "finite-residue-inverse-zero",
            "finite-residue-inverse-congruent",
            "finite-inverse-natural-gcd-product",
            "finite-residue-inverse-gcd-product",
        ],
    );
}

#[test]
fn finite_residue_unit_data() {
    matrix(
        "finite-residue-unit-data",
        &[
            "finite-residue-unit-product",
            "finite-residue-unit-inverse-unique",
        ],
    );
}

#[test]
fn natural_data_recursion() {
    matrix(
        "natural-data-recursion",
        &["natural-data-strong-recursion-zero"],
    );
}

#[test]
fn natural_extended_gcd_data() {
    matrix(
        "natural-extended-gcd-data",
        &[
            "natural-extended-gcd-base-certificate",
            "natural-extended-gcd-step-certificate",
        ],
    );
}

#[test]
fn natural_extended_gcd() {
    matrix(
        "natural-extended-gcd",
        &[
            "computed-natural-gcd-certificate",
            "computed-natural-bezout-equation",
            "computed-natural-gcd-unique",
        ],
    );
}
