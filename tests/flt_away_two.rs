//! Native denominator cancellation and actual integral discriminant prime divisors.
#[path = "support/flt_integral_fixtures.rs"]
mod fixtures;
use fixtures::{fixture, term};
use lim::{check_theorem_details_from_path_with_config, CompileConfig, ProofBudget};
use std::path::Path;

const PRIME_TARGETS: &[&str] = &[
    "integer-prime-divides-two-only-two",
    "integer-prime-away-two-not-divides-power",
    "integer-prime-cancel-right",
];
const FREY_TARGETS: &[&str] = &[
    "integer-frey-product-prime-divisor-away-two",
    "integer-frey-prime-divisors-equivalent-away-two",
    "frey-package-prime-divisors-equivalent-away-two",
];

fn matrix(module: &str, targets: &[&str]) {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("theorems/flt")
        .join(format!("{module}.lim"));
    let source = std::fs::read_to_string(&path).unwrap();
    let budget = ProofBudget::default();
    let mut config = CompileConfig::default();
    config.set_proof_budget(
        ProofBudget::new(budget.work(), budget.phase_bytes(), 1024 * 1024 * 1024).unwrap(),
    );
    for &target in targets {
        let report = check_theorem_details_from_path_with_config(&source, &path, &config, target)
            .unwrap_or_else(|e| panic!("{module}::{target}: {}", e.message));
        assert_eq!(
            report.name,
            format!("{}::{target}", path.canonicalize().unwrap().display())
        );
        assert!(report.foundations.is_empty());
    }
}

#[test]
fn prime_denominator_theorems_are_foundation_free() {
    matrix("integer-prime-away-two", PRIME_TARGETS);
}

#[test]
fn integral_prime_equivalence_theorems_are_foundation_free() {
    matrix("integer-frey-away-two", FREY_TARGETS);
}

fn n(value: usize) -> String {
    if value <= 128 {
        format!("(#pt-numeral {value})")
    } else {
        term("add", &[&n(128), &n(value - 128)])
    }
}
fn int(value: isize) -> String {
    let magnitude = term("integer-of-natural", &[&n(value.unsigned_abs())]);
    if value < 0 {
        term("integer-negate", &[&magnitude])
    } else {
        magnitude
    }
}
fn refl(value: usize) -> String {
    format!("(#pt-refl #pt-nat {})", n(value))
}
fn idiv(divisor: &str, value: &str) -> String {
    term("integer-divides", &[divisor, value])
}
fn not(prop: &str) -> String {
    format!("(#pt-pi ((denied-proof {prop})) #pt-false)")
}
fn arrow(first: &str, second: &str) -> String {
    format!("(#pt-pi ((divisor-evidence {first})) {second})")
}
fn prime(q: usize) -> String {
    term(if q == 3 { "prime-three" } else { "prime-two" }, &[])
}
fn not_two(q: usize) -> String {
    let mut equality = "equal-to-two".to_owned();
    let (mut a, mut b) = (q, 2);
    while a > 0 && b > 0 {
        equality = term("successor-injective", &[&n(a - 1), &n(b - 1), &equality]);
        a -= 1;
        b -= 1;
    }
    // For q=2 this deliberately claims 1=0 from 0=0, an invalid certificate.
    let contradiction = format!(
        "(#pt-app {} {equality})",
        term("successor-not-zero", &[&n(a.saturating_sub(1))])
    );
    format!(
        "(#pt-lambda ((equal-to-two (#pt-eq #pt-nat {} {}))) {contradiction})",
        n(q),
        n(2)
    )
}
fn division(divisor: isize, value: &str, quotient: isize, cross: usize) -> String {
    let predicate = format!(
        "(#pt-lambda ((candidate-factor (#pt-use integer ()))) {})",
        term(
            "integer-equal",
            &[
                value,
                &term("integer-multiply", &[&int(divisor), "candidate-factor"])
            ]
        )
    );
    format!(
        "(#pt-construct exists (0) ((#pt-use integer ()) {predicate}) introduce ({} {}))",
        int(quotient),
        refl(cross)
    )
}
fn denominator(q: usize, exponent: usize) -> (String, String) {
    let scalar = term(
        "integer-of-natural",
        &[&term("power", &[&n(2), &n(exponent)])],
    );
    (
        not(&idiv(&int(q as isize), &scalar)),
        term(
            "integer-prime-away-two-not-divides-power",
            &[&n(q), &n(exponent), &prime(q), &not_two(q)],
        ),
    )
}

#[test]
fn only_the_prime_two_divides_two() {
    fixture(
        &format!("(#pt-eq #pt-nat {} {})", n(2), n(2)),
        &term(
            "integer-prime-divides-two-only-two",
            &[&n(2), &prime(2), &division(2, &int(2), 1, 2)],
        ),
        true,
    );
}

#[test]
fn denominator_nondivisibility_includes_zero_and_large_exponents() {
    // These are specializations of the unbounded theorem, not bounded search.
    for exponent in [0, 1, 8, 128] {
        let (statement, proof) = denominator(3, exponent);
        fixture(&statement, &proof, true);
    }
}

#[test]
fn composite_numbers_cannot_borrow_prime_evidence() {
    let (statement, proof) = denominator(4, 8);
    fixture(&statement, &proof, false);
}

#[test]
fn two_cannot_borrow_the_away_two_denominator_theorem() {
    let (statement, proof) = denominator(2, 8);
    fixture(&statement, &proof, false);
}

fn cancel(second: isize) -> String {
    let first = int(-6);
    let product = term("integer-multiply", &[&first, &int(second)]);
    term(
        "integer-prime-cancel-right",
        &[
            &n(3),
            &first,
            &int(second),
            &prime(3),
            &denominator(3, 1).1,
            &division(3, &product, -2 * second, (6 * second) as usize),
        ],
    )
}

#[test]
fn signed_product_cancellation_retains_the_nondivisor_premise() {
    fixture(&idiv(&int(3), &int(-6)), &cancel(2), true);
    fixture(&idiv(&int(3), &int(-6)), &cancel(3), false);
}

fn model(zero: bool) -> String {
    term(
        "integer-frey-model",
        &[
            &int(if zero { 0 } else { 4 }),
            &int(if zero { 0 } else { 1 }),
        ],
    )
}
fn model_certificate(zero: bool) -> String {
    term(
        "integer-frey-quotients-map",
        &[
            &int(-1),
            &int(if zero { 0 } else { 16 }),
            &n(1),
            &int(if zero { 0 } else { 4 }),
            &int(if zero { 0 } else { 1 }),
            &refl(if zero { 1 } else { 17 }),
            &refl(if zero { 0 } else { 16 }),
        ],
    )
}
fn positive(exponent: usize) -> String {
    let predicate = format!(
        "(#pt-lambda ((candidate-gap #pt-nat)) (#pt-eq #pt-nat {} {}))",
        n(exponent),
        term("add", &[&n(1), "candidate-gap"])
    );
    format!(
        "(#pt-construct exists (0) (#pt-nat {predicate}) introduce ({} {}))",
        n(exponent.saturating_sub(1)),
        refl(exponent)
    )
}
fn coordinate_product(zero: bool) -> String {
    term(
        "integer-multiply",
        &[
            &term(
                "integer-multiply",
                &[&int(-1), &int(if zero { 0 } else { 16 })],
            ),
            &int(if zero { -1 } else { 15 }),
        ],
    )
}
fn delta(zero: bool) -> String {
    term("integer-weierstrass-discriminant", &[&model(zero)])
}
fn reverse(
    q: usize,
    zero: bool,
    quotient: isize,
    valid_equation: bool,
    valid_positive: bool,
) -> String {
    term(
        "integer-frey-product-prime-divisor-away-two",
        &[
            &n(q),
            &int(-1),
            &int(if zero { 0 } else { 16 }),
            &int(if valid_equation {
                if zero {
                    -1
                } else {
                    15
                }
            } else {
                14
            }),
            &n(1),
            &model(zero),
            &model_certificate(zero),
            &prime(q),
            &not_two(q),
            &positive(if valid_positive { 1 } else { 0 }),
            &refl(if zero { 1 } else { 16 }),
            &division(
                q as isize,
                &coordinate_product(zero),
                quotient,
                if zero { 0 } else { 240 },
            ),
        ],
    )
}

#[test]
fn coordinate_prime_divisors_reach_actual_signed_and_zero_discriminants() {
    for zero in [true, false] {
        fixture(
            &idiv(&int(3), &delta(zero)),
            &reverse(3, zero, if zero { 0 } else { -80 }, true, true),
            true,
        );
    }
}

#[test]
fn actual_discriminant_prime_divisor_equivalence_has_both_directions() {
    for zero in [true, false] {
        let discriminant = idiv(&int(3), &delta(zero));
        let coordinates = idiv(&int(3), &coordinate_product(zero));
        let statement = term(
            "conjunction",
            &[
                &arrow(&discriminant, &coordinates),
                &arrow(&coordinates, &discriminant),
            ],
        );
        let proof = term(
            "integer-frey-prime-divisors-equivalent-away-two",
            &[
                &n(3),
                &int(-1),
                &int(if zero { 0 } else { 16 }),
                &int(if zero { -1 } else { 15 }),
                &n(1),
                &model(zero),
                &model_certificate(zero),
                &prime(3),
                &not_two(3),
                &positive(1),
                &refl(if zero { 1 } else { 16 }),
            ],
        );
        fixture(&statement, &proof, true);
    }
}

#[test]
fn prime_two_is_excluded_from_the_actual_discriminant_reverse_implication() {
    // Here 2 divides a*b*c=-240 but not the actual discriminant 225.
    fixture(
        &idiv(&int(2), &delta(false)),
        &reverse(2, false, -120, true, true),
        false,
    );
}

#[test]
fn forged_coordinate_equation_and_positive_exponent_are_mismatches() {
    for (equation, positive) in [(false, true), (true, false)] {
        fixture(
            &idiv(&int(3), &delta(false)),
            &reverse(3, false, -80, equation, positive),
            false,
        );
    }
}

#[test]
fn forged_coordinate_divisor_quotients_are_mismatches() {
    fixture(
        &idiv(&int(3), &delta(false)),
        &reverse(3, false, -79, true, true),
        false,
    );
}
