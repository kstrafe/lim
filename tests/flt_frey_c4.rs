//! Native source-port checks for the exact Frey c4 identity.
#[path = "support/flt_rational_fixtures.rs"]
mod fixtures;
use fixtures::{fixture, term};
use lim::{check_theorem_details_from_path_with_config, CompileConfig, ProofBudget};
use std::path::Path;

fn matrix(module: &str, targets: &[&str]) {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("theorems/flt")
        .join(format!("{module}.lim"));
    let source = std::fs::read_to_string(&path).unwrap();
    let default = ProofBudget::default();
    let mut config = CompileConfig::default();
    config.set_proof_budget(
        ProofBudget::new(default.work(), default.phase_bytes(), 1024 * 1024 * 1024).unwrap(),
    );
    for target in targets {
        let report = check_theorem_details_from_path_with_config(&source, &path, &config, target)
            .unwrap_or_else(|error| panic!("{module}::{target}: {}", error.message));
        assert_eq!(
            report.name,
            format!("{}::{target}", path.canonicalize().unwrap().display())
        );
        assert!(report.foundations.is_empty());
    }
}

#[test]
fn rational_embedding_laws_have_no_global_foundations() {
    matrix(
        "rational-embedding-laws",
        &[
            "rational-of-integer-negate",
            "rational-of-integer-power",
            "rational-natural-multiple-times-fraction",
        ],
    );
}

#[test]
fn c4_natural_cross_identity_has_no_global_foundations() {
    matrix("frey-c4-cross-identity", &["frey-c4-integer-cross"]);
}

#[test]
fn c4_signed_identity_has_no_global_foundations() {
    matrix("frey-c4-integer-identity", &["frey-c4-integer-identity"]);
}

#[test]
fn c4_frey_specializations_have_no_global_foundations() {
    matrix(
        "frey-rational-c4",
        &["frey-rational-model-c4", "frey-rational-curve-c4"],
    );
}

fn numeral(value: usize) -> String {
    format!("(#pt-numeral {value})")
}

fn integer(value: isize) -> String {
    let positive = term("integer-of-natural", &[&numeral(value.unsigned_abs())]);
    if value < 0 {
        term("integer-negate", &[&positive])
    } else {
        positive
    }
}

fn embed(value: isize) -> String {
    term("rational-of-integer", &[&integer(value)])
}

#[test]
fn integer_embedding_preserves_actual_signed_negation() {
    let value = integer(-3);
    let left = term("rational-negate", &[&embed(-3)]);
    let statement = term("rational-equal", &[&left, &embed(3)]);
    fixture(
        &statement,
        &term("rational-of-integer-negate", &[&value]),
        true,
    );
}

#[test]
fn integer_embedding_preserves_actual_odd_signed_powers() {
    let left = term("rational-power", &[&embed(-2), &numeral(3)]);
    let statement = term("rational-equal", &[&left, &embed(-8)]);
    fixture(
        &statement,
        &term("rational-of-integer-power", &[&integer(-2), &numeral(3)]),
        true,
    );
}

fn scaled_fraction(multiplier: usize, expected: isize) {
    let numerator = integer(-5);
    let denominator = numeral(8);
    let nonzero = term("successor-not-zero", &[&numeral(7)]);
    let fraction =
        format!("(#pt-construct rational () () fraction ({numerator} {denominator} {nonzero}))");
    let left = term(
        "rational-multiply",
        &[&embed((multiplier * 8) as isize), &fraction],
    );
    fixture(
        &term("rational-equal", &[&left, &embed(expected)]),
        &term(
            "rational-natural-multiple-times-fraction",
            &[&numerator, &denominator, &numeral(multiplier), &nonzero],
        ),
        true,
    );
}

#[test]
fn actual_denominator_multiple_cancels_in_a_signed_fraction() {
    scaled_fraction(3, -15);
}

#[test]
fn zero_multiplier_does_not_need_a_false_nonzero_premise() {
    scaled_fraction(0, 0);
}

fn c4_value(first: isize, second: isize, expected: isize, valid: bool) {
    let positive_part = first * first + second * second + (first * second).max(0);
    let first = integer(first);
    let second = integer(second);
    let curve = term("frey-rational-model", &[&first, &second]);
    let left = term("rational-weierstrass-c4", &[&curve]);
    let first_square = term("integer-power", &[&first, &numeral(2)]);
    let second_square = term("integer-power", &[&second, &numeral(2)]);
    let product = term("integer-multiply", &[&first, &second]);
    let first_two = term("integer-add", &[&first_square, &product]);
    let rhs = term("integer-add", &[&first_two, &second_square]);
    let middle = term("rational-of-integer", &[&rhs]);
    let right = embed(expected);
    // Check the small signed integer certificate separately from the curve
    // polynomial. It is a candidate: the kernel checks both cross components.
    let arithmetic = format!("(#pt-refl #pt-nat {})", numeral(positive_part as usize));
    let formula = term("frey-rational-model-c4", &[&first, &second]);
    fixture(
        &term("rational-equal", &[&left, &right]),
        &term(
            "rational-transitive",
            &[&left, &middle, &right, &formula, &arithmetic],
        ),
        valid,
    );
}

#[test]
fn exact_frey_c4_has_its_actual_positive_value() {
    c4_value(1, 1, 3, true);
}

#[test]
fn exact_frey_c4_handles_opposite_signed_inputs() {
    c4_value(2, -1, 3, true);
}

#[test]
fn false_frey_c4_value_is_a_proof_mismatch() {
    c4_value(2, -1, 4, false);
}
