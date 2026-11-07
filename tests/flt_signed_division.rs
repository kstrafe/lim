//! Foundation-free checks for signed division FLT theorems.
use lim::{check_theorem_details_from_path_with_config, CompileConfig, ProofBudget};
use std::path::Path;

const NATURAL_REMAINDER_COMPLEMENT: &[&str] = &[
    "natural-zero-or-positive",
    "natural-complement-below-divisor",
    "natural-remainder-complement-exists",
    "natural-negative-division-balance",
];

const INTEGER_DIVISION_DEFS: &[&str] = &[
    "integer-division-congruent-dividend",
    "integer-has-division-congruent-dividend",
    "integer-natural-division-equation",
    "integer-negative-exact-division-equation",
    "integer-negative-complement-division-equation",
];

const INTEGER_DIVISION_EXISTENCE: &[&str] = &[
    "integer-natural-division-exists",
    "integer-negative-division-from-natural",
    "integer-negative-division-exists",
    "integer-division-exists",
];

const EISENSTEIN_COORDINATE_DIVISION: &[&str] = &[
    "eisenstein-coordinate-division-from-components",
    "eisenstein-coordinate-division-exists",
];

fn signed_division_config() -> CompileConfig {
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
    let config = signed_division_config();

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
fn natural_remainder_complement_theorems_are_foundation_free() {
    check_matrix(
        "natural-remainder-complement.lim",
        NATURAL_REMAINDER_COMPLEMENT,
    );
}

#[test]
fn integer_division_definition_theorems_are_foundation_free() {
    check_matrix("integer-division-defs.lim", INTEGER_DIVISION_DEFS);
}

#[test]
fn integer_division_existence_theorems_are_foundation_free() {
    check_matrix("integer-division-existence.lim", INTEGER_DIVISION_EXISTENCE);
}

#[test]
fn eisenstein_coordinate_division_theorems_are_foundation_free() {
    check_matrix(
        "eisenstein-coordinate-division.lim",
        EISENSTEIN_COORDINATE_DIVISION,
    );
}

#[path = "support/flt_division_fixtures.rs"]
mod division_fixtures;
use division_fixtures::{fixture, term};

fn numeral(number: usize) -> String {
    format!("(#pt-numeral {number})")
}
fn natural(number: usize) -> String {
    term("integer-of-natural", &[&numeral(number)])
}
fn negative(number: usize) -> String {
    term("integer-negative-natural", &[&numeral(number)])
}
fn difference(positive: usize, negative: usize) -> String {
    format!(
        "(#pt-construct integer () () difference ({} {}))",
        numeral(positive),
        numeral(negative)
    )
}
fn reflexive(number: usize) -> String {
    format!("(#pt-refl #pt-nat {})", numeral(number))
}
fn less(lower: usize, upper: usize) -> String {
    // For deliberately invalid bounds, the constructor is still presented
    // to the kernel and must fail with a proof type mismatch.
    let gap = upper.saturating_sub(lower + 1);
    format!("(#pt-construct exists (0) (#pt-nat (#pt-lambda ((gap #pt-nat)) (#pt-eq #pt-nat {} (#pt-app (#pt-use add ()) (#pt-succ {}) gap)))) introduce ({} {}))", numeral(upper),numeral(lower),numeral(gap),reflexive(upper))
}
fn certificate(
    number: &str,
    divisor: usize,
    quotient: &str,
    remainder: usize,
    equation: &str,
) -> String {
    let sum=format!("(#pt-app (#pt-use integer-add ()) (#pt-app (#pt-use integer-multiply ()) {quotient} {}) {})",natural(divisor),natural(remainder));
    term(
        "conjunction-introduce",
        &[
            &term("integer-equal", &[number, &sum]),
            &term("less-than", &[&numeral(remainder), &numeral(divisor)]),
            equation,
            &less(remainder, divisor),
        ],
    )
}
fn negative_five_certificate() -> String {
    certificate(
        &negative(5),
        3,
        &negative(2),
        1,
        &term(
            "integer-negative-complement-division-equation",
            &[
                &numeral(5),
                &numeral(3),
                &numeral(1),
                &numeral(2),
                &numeral(1),
                &reflexive(5),
                &reflexive(3),
            ],
        ),
    )
}

#[test]
fn signed_division_exists_for_both_signs_and_noncanonical_representatives() {
    for (number, divisor) in [
        (natural(0), 3),
        (natural(5), 3),
        (negative(0), 3),
        (negative(5), 3),
        (negative(6), 3),
        (difference(2, 7), 3),
        (difference(7, 2), 1),
    ] {
        fixture(
            &term("integer-has-division", &[&number, &numeral(divisor)]),
            &term(
                "integer-division-exists",
                &[&number, &numeral(divisor), &less(0, divisor)],
            ),
            true,
            &signed_division_config(),
        );
    }
}

#[test]
fn negative_exact_and_nonzero_remainders_have_actual_quotient_certificates() {
    let exact = term(
        "integer-negative-exact-division-equation",
        &[&numeral(6), &numeral(3), &numeral(2), &reflexive(6)],
    );
    fixture(
        &term(
            "integer-division-spec",
            &[&negative(6), &numeral(3), &negative(2), &numeral(0)],
        ),
        &certificate(&negative(6), 3, &negative(2), 0, &exact),
        true,
        &signed_division_config(),
    );
    fixture(
        &term(
            "integer-division-spec",
            &[&negative(5), &numeral(3), &negative(2), &numeral(1)],
        ),
        &negative_five_certificate(),
        true,
        &signed_division_config(),
    );
}

#[test]
fn division_rejects_zero_divisors_and_end_boundary_remainders() {
    for (number, divisor, remainder) in [(0, 0, 0), (3, 3, 3)] {
        fixture(
            &term(
                "integer-division-spec",
                &[
                    &natural(number),
                    &numeral(divisor),
                    &natural(0),
                    &numeral(remainder),
                ],
            ),
            &certificate(
                &natural(number),
                divisor,
                &natural(0),
                remainder,
                &reflexive(number),
            ),
            false,
            &signed_division_config(),
        );
    }
}

#[test]
fn negative_adjustment_rejects_incorrect_quotients_and_complements() {
    // The valid certificate uses -2, not truncation toward zero at -1.
    fixture(
        &term(
            "integer-division-spec",
            &[&negative(5), &numeral(3), &negative(1), &numeral(1)],
        ),
        &negative_five_certificate(),
        false,
        &signed_division_config(),
    );
    let wrong = term(
        "integer-negative-complement-division-equation",
        &[
            &numeral(5),
            &numeral(3),
            &numeral(1),
            &numeral(2),
            &numeral(2),
            &reflexive(5),
            &reflexive(3),
        ],
    );
    fixture(
        &term(
            "integer-division-spec",
            &[&negative(5), &numeral(3), &negative(2), &numeral(2)],
        ),
        &certificate(&negative(5), 3, &negative(2), 2, &wrong),
        false,
        &signed_division_config(),
    );
}

#[test]
fn noncanonical_dividend_preserves_the_same_division_certificate() {
    let source = negative(5);
    let target = difference(2, 7);
    fixture(
        &term(
            "integer-division-spec",
            &[&target, &numeral(3), &negative(2), &numeral(1)],
        ),
        &term(
            "integer-division-congruent-dividend",
            &[
                &source,
                &target,
                &numeral(3),
                &negative(2),
                &numeral(1),
                &reflexive(7),
                &negative_five_certificate(),
            ],
        ),
        true,
        &signed_division_config(),
    );
}

#[test]
fn division_certificate_cannot_be_transferred_to_an_unequal_dividend() {
    let source = natural(5);
    let target = natural(6);
    let equation = term(
        "integer-natural-division-equation",
        &[
            &numeral(5),
            &numeral(3),
            &numeral(1),
            &numeral(2),
            &reflexive(5),
        ],
    );
    let cert = certificate(&source, 3, &natural(1), 2, &equation);
    fixture(
        &term(
            "integer-division-spec",
            &[&target, &numeral(3), &natural(1), &numeral(2)],
        ),
        &term(
            "integer-division-congruent-dividend",
            &[
                &source,
                &target,
                &numeral(3),
                &natural(1),
                &numeral(2),
                &reflexive(5),
                &cert,
            ],
        ),
        false,
        &signed_division_config(),
    );
}

#[test]
fn eisenstein_coordinate_division_combines_actual_signed_quotients() {
    let pair =
        |real: &str, omega: &str| format!("(#pt-construct eisenstein () () pair ({real} {omega}))");
    let dividend = pair(&negative(5), &natural(5));
    let quotient = pair(&negative(2), &natural(1));
    let real = negative_five_certificate();
    let omega_equation = term(
        "integer-natural-division-equation",
        &[
            &numeral(5),
            &numeral(3),
            &numeral(1),
            &numeral(2),
            &reflexive(5),
        ],
    );
    let omega = certificate(&natural(5), 3, &natural(1), 2, &omega_equation);
    fixture(
        &term(
            "eisenstein-coordinate-division-spec",
            &[&dividend, &numeral(3), &quotient, &numeral(1), &numeral(2)],
        ),
        &term(
            "eisenstein-coordinate-division-from-components",
            &[
                &dividend,
                &numeral(3),
                &negative(2),
                &natural(1),
                &numeral(1),
                &numeral(2),
                &real,
                &omega,
            ],
        ),
        true,
        &signed_division_config(),
    );
}
