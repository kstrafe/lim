//! Foundation-free checks for the FLT natural, integer, and Eisenstein unit bounds.
use lim::{check_theorem_details_from_path_with_config, CompileConfig, ProofBudget};
use std::path::Path;

const NATURAL_UNIT_BOUND_POLYNOMIAL: &[&str] = &["natural-large-square-triple"];

const NATURAL_UNIT_BOUND: &[&str] = &[
    "natural-large-three-square-budget-impossible",
    "natural-three-square-budget-small",
];

const INTEGER_UNIT_BOUND: &[&str] = &[
    "integer-three-square-magnitude-small",
    "integer-three-square-value-small",
];

const EISENSTEIN_UNIT_COORDINATE_BOUNDS: &[&str] = &[
    "eisenstein-unit-norm-is-one",
    "eisenstein-unit-real-square-budget",
    "eisenstein-unit-real-small",
    "eisenstein-unit-omega-square-budget",
    "eisenstein-unit-omega-small",
];

fn unit_bounds_config() -> CompileConfig {
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
    let config = unit_bounds_config();

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
fn natural_unit_bound_polynomial_theorems_are_foundation_free() {
    check_matrix(
        "natural-unit-bound-polynomial.lim",
        NATURAL_UNIT_BOUND_POLYNOMIAL,
    );
}

#[test]
fn natural_unit_bound_theorems_are_foundation_free() {
    check_matrix("natural-unit-bound.lim", NATURAL_UNIT_BOUND);
}

#[test]
fn integer_unit_bound_theorems_are_foundation_free() {
    check_matrix("integer-unit-bound.lim", INTEGER_UNIT_BOUND);
}

#[test]
fn eisenstein_unit_coordinate_bound_theorems_are_foundation_free() {
    check_matrix(
        "eisenstein-unit-coordinate-bounds.lim",
        EISENSTEIN_UNIT_COORDINATE_BOUNDS,
    );
}

#[path = "support/flt_unit_fixtures.rs"]
mod unit_fixtures;
use unit_fixtures::{fixture, term};

#[test]
fn natural_square_budget_accepts_zero_and_one() {
    for (number, remainder) in [(0, 4), (1, 1)] {
        let number = format!("(#pt-numeral {number})");
        let statement = term(
            "disjunction",
            &[
                &format!("(#pt-eq #pt-nat {number} #pt-zero)"),
                &format!("(#pt-eq #pt-nat {number} (#pt-succ #pt-zero))"),
            ],
        );
        let proof = term(
            "natural-three-square-budget-small",
            &[
                &number,
                &format!("(#pt-numeral {remainder})"),
                "(#pt-refl #pt-nat (#pt-numeral 4))",
            ],
        );
        fixture(&statement, &proof, true, &unit_bounds_config());
    }
}

#[test]
fn natural_square_budget_rejects_an_uncertified_large_coordinate() {
    let two = "(#pt-numeral 2)";
    let statement = term(
        "disjunction",
        &[
            &format!("(#pt-eq #pt-nat {two} #pt-zero)"),
            &format!("(#pt-eq #pt-nat {two} (#pt-succ #pt-zero))"),
        ],
    );
    let proof = term(
        "natural-three-square-budget-small",
        &[two, "#pt-zero", "(#pt-refl #pt-nat (#pt-numeral 4))"],
    );
    fixture(&statement, &proof, false, &unit_bounds_config());
}

#[test]
fn signed_square_budget_handles_both_signs() {
    let one = term("integer-one", &[]);
    let negative = term("integer-negate", &[&one]);
    let zero = term("integer-zero", &[]);
    for number in [&one, &negative] {
        let statement = term(
            "disjunction",
            &[
                &term("integer-equal", &[number, &zero]),
                &term(
                    "disjunction",
                    &[
                        &term("integer-equal", &[number, &one]),
                        &term("integer-equal", &[number, &negative]),
                    ],
                ),
            ],
        );
        let proof = term(
            "integer-three-square-value-small",
            &[number, &one, "(#pt-refl #pt-nat (#pt-numeral 4))"],
        );
        fixture(&statement, &proof, true, &unit_bounds_config());
    }
}
