//! Foundation-free norm estimates for the concrete Eisenstein Euclidean route.
use lim::{check_theorem_details_from_path_with_config, CompileConfig, ProofBudget};
use std::path::Path;

const NATURAL_RECTANGLE_NORM_BOUND: &[&str] = &[
    "natural-square-budget-gap",
    "natural-square-budget-ordered-bound",
    "natural-rectangle-square-budget-bound",
];
const EISENSTEIN_COORDINATE_NORM_BOUND: &[&str] = &[
    "eisenstein-norm-plus-coordinate-product",
    "eisenstein-natural-coordinate-norm-balance",
    "eisenstein-natural-coordinate-norm-bound",
];

fn rectangle_config() -> CompileConfig {
    let mut config = CompileConfig::default();
    let default = ProofBudget::default();
    config.set_proof_budget(
        ProofBudget::new(default.work(), default.phase_bytes(), 1024 * 1024 * 1024).unwrap(),
    );
    config
}

fn check_matrix(module: &str, targets: &[&str]) {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("theorems/flt")
        .join(module);
    let source = std::fs::read_to_string(&path).unwrap();
    for &target in targets {
        let report = check_theorem_details_from_path_with_config(
            &source,
            &path,
            &rectangle_config(),
            target,
        )
        .unwrap_or_else(|error| panic!("failed to check {target}: {}", error.message));
        assert!(report.name == target || report.name.ends_with(&format!("::{target}")));
        assert!(report.foundations.is_empty());
    }
}

#[test]
fn natural_rectangle_norm_bounds_are_foundation_free() {
    check_matrix(
        "natural-rectangle-norm-bound.lim",
        NATURAL_RECTANGLE_NORM_BOUND,
    );
}

#[test]
fn eisenstein_coordinate_norm_bounds_are_foundation_free() {
    check_matrix(
        "eisenstein-coordinate-norm-bound.lim",
        EISENSTEIN_COORDINATE_NORM_BOUND,
    );
}

#[path = "support/flt_division_fixtures.rs"]
mod division_fixtures;
use division_fixtures::{fixture, term};

fn numeral(number: usize) -> String {
    format!("(#pt-numeral {number})")
}
fn reflexive(number: usize) -> String {
    format!("(#pt-refl #pt-nat {})", numeral(number))
}
fn less(lower: usize, upper: usize) -> String {
    let gap = upper.saturating_sub(lower + 1);
    format!("(#pt-construct exists (0) (#pt-nat (#pt-lambda ((gap #pt-nat)) (#pt-eq #pt-nat {} (#pt-app (#pt-use add ()) (#pt-succ {}) gap)))) introduce ({} {}))",numeral(upper),numeral(lower),numeral(gap),reflexive(upper))
}
fn norm_bound(real: usize, omega: usize, norm: usize, bound: usize, certificate: &str) -> String {
    term(
        "eisenstein-natural-coordinate-norm-bound",
        &[
            &numeral(real),
            &numeral(omega),
            &numeral(norm),
            &numeral(bound),
            certificate,
            &less(real, bound),
            &less(omega, bound),
        ],
    )
}

#[test]
fn rectangular_norm_bound_covers_zero_equal_and_both_coordinate_orders() {
    for (real, omega, bound) in [
        (0, 0, 1),
        (0, 2, 3),
        (2, 0, 3),
        (2, 2, 3),
        (1, 2, 3),
        (2, 1, 3),
    ] {
        let norm = real * real + omega * omega - real * omega;
        fixture(
            &term("less-than", &[&numeral(norm), &numeral(bound * bound)]),
            &norm_bound(
                real,
                omega,
                norm,
                bound,
                &reflexive(real * real + omega * omega),
            ),
            true,
            &rectangle_config(),
        );
    }
}

#[test]
fn rectangular_norm_bound_requires_both_strict_coordinate_bounds() {
    for (real, omega) in [(2, 0), (0, 2)] {
        fixture(
            &term("less-than", &[&numeral(4), &numeral(4)]),
            &norm_bound(real, omega, 4, 2, &reflexive(4)),
            false,
            &rectangle_config(),
        );
    }
}

#[test]
fn rectangular_norm_bound_rejects_an_incorrect_natural_norm() {
    fixture(
        &term("less-than", &[&numeral(0), &numeral(4)]),
        &norm_bound(1, 1, 0, 2, &reflexive(2)),
        false,
        &rectangle_config(),
    );
}

#[test]
fn natural_rectangle_bound_rejects_an_incorrect_square_budget() {
    fixture(
        &term("less-than", &[&numeral(2), &numeral(4)]),
        &term(
            "natural-rectangle-square-budget-bound",
            &[
                &numeral(1),
                &numeral(1),
                &numeral(2),
                &numeral(2),
                &reflexive(3),
                &less(1, 2),
                &less(1, 2),
            ],
        ),
        false,
        &rectangle_config(),
    );
}
