//! Foundation-free checks of the concrete Kummer unit congruence lemma.
use lim::{check_theorem_details_from_path_with_config, CompileConfig, ProofBudget};
use std::path::Path;

const UNIT_KUMMER: &[&str] = &[
    "eisenstein-three-divides-lambda-square",
    "integer-three-divides-eisenstein-omega",
    "integer-three-divides-omega-from-square-congruence",
    "eisenstein-unit-square-integer-congruence-cases",
    "eisenstein-unit-integer-congruence-one-or-negative-one",
];

fn unit_kummer_config() -> CompileConfig {
    let mut config = CompileConfig::default();
    let default = ProofBudget::default();
    config.set_proof_budget(
        ProofBudget::new(default.work(), default.phase_bytes(), 1024 * 1024 * 1024).unwrap(),
    );
    config
}

#[test]
fn unit_kummer_theorems_are_foundation_free() {
    let path =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("theorems/flt/eisenstein-unit-kummer.lim");
    let source = std::fs::read_to_string(&path).unwrap();
    for &target in UNIT_KUMMER {
        let report = check_theorem_details_from_path_with_config(
            &source,
            &path,
            &unit_kummer_config(),
            target,
        )
        .unwrap_or_else(|error| panic!("failed to check {target}: {}", error.message));
        assert!(report.name == target || report.name.ends_with(&format!("::{target}")));
        assert!(report.foundations.is_empty());
    }
}

#[path = "support/flt_unit_fixtures.rs"]
mod unit_fixtures;
use unit_fixtures::{fixture, term};

fn conclusion(number: &str) -> String {
    let one = term("eisenstein-one", &[]);
    term(
        "disjunction",
        &[
            &term("eisenstein-equal", &[number, &one]),
            &term(
                "eisenstein-equal",
                &[number, &term("eisenstein-negate", &[&one])],
            ),
        ],
    )
}

#[test]
fn kummer_accepts_both_integer_units_with_actual_congruence_factors() {
    let one = term("eisenstein-one", &[]);
    let int_one = term("integer-one", &[]);
    let zero = term("eisenstein-zero", &[]);
    let lambda_square = term(
        "eisenstein-power",
        &[&term("eisenstein-lambda", &[]), "(#pt-numeral 2)"],
    );
    for (number, integer) in [
        (one.clone(), int_one.clone()),
        (
            term("eisenstein-negate", &[&one]),
            term("integer-negate", &[&int_one]),
        ),
    ] {
        let difference = term(
            "eisenstein-add",
            &[
                &number,
                &term(
                    "eisenstein-negate",
                    &[&term("eisenstein-of-integer", &[&integer])],
                ),
            ],
        );
        let real_eq = term(
            "integer-equal",
            &[
                &format!("(#pt-project eisenstein 0 {zero})"),
                &format!("(#pt-project eisenstein 0 {difference})"),
            ],
        );
        let omega_eq = term(
            "integer-equal",
            &[
                &format!("(#pt-project eisenstein 1 {zero})"),
                &format!("(#pt-project eisenstein 1 {difference})"),
            ],
        );
        let zero_eq = term(
            "conjunction-introduce",
            &[
                &real_eq,
                &omega_eq,
                "(#pt-refl #pt-nat (#pt-succ #pt-zero))",
                "(#pt-refl #pt-nat #pt-zero)",
            ],
        );
        let divisor = term(
            "eisenstein-divides-congruent-target",
            &[
                &lambda_square,
                &zero,
                &difference,
                &zero_eq,
                &term("eisenstein-divides-zero", &[&lambda_square]),
            ],
        );
        let predicate = format!(
            "(#pt-lambda ((candidate-integer (#pt-use integer ()))) {})",
            term(
                "eisenstein-divides",
                &[
                    &lambda_square,
                    &term(
                        "eisenstein-add",
                        &[
                            &number,
                            &term(
                                "eisenstein-negate",
                                &[&term("eisenstein-of-integer", &["candidate-integer"])]
                            ),
                        ],
                    ),
                ],
            )
        );
        let congruence = format!(
            "(#pt-construct exists (0) ((#pt-use integer ()) {predicate}) introduce ({integer} {divisor}))"
        );
        let unit = term(
            "eisenstein-unit-of-natural-norm-one",
            &[&number, "(#pt-refl #pt-nat (#pt-succ #pt-zero))"],
        );
        fixture(
            &conclusion(&number),
            &term(
                "eisenstein-unit-integer-congruence-one-or-negative-one",
                &[&number, &unit, &congruence],
            ),
            true,
            &unit_kummer_config(),
        );
    }
}

#[test]
fn nonreal_unit_cannot_reuse_the_congruence_of_zero() {
    let omega = term("eisenstein-omega", &[]);
    let lambda_square = term(
        "eisenstein-power",
        &[&term("eisenstein-lambda", &[]), "(#pt-numeral 2)"],
    );
    let unit = term(
        "eisenstein-unit-of-natural-norm-one",
        &[&omega, "(#pt-refl #pt-nat (#pt-succ #pt-zero))"],
    );
    fixture(
        &conclusion(&omega),
        &term(
            "eisenstein-unit-square-integer-congruence-cases",
            &[
                &omega,
                &term("integer-zero", &[]),
                &unit,
                &term("eisenstein-divides-zero", &[&lambda_square]),
            ],
        ),
        false,
        &unit_kummer_config(),
    );
}

#[test]
fn congruence_does_not_remove_the_unit_requirement() {
    let zero = term("eisenstein-zero", &[]);
    let one = term("eisenstein-one", &[]);
    let lambda_square = term(
        "eisenstein-power",
        &[&term("eisenstein-lambda", &[]), "(#pt-numeral 2)"],
    );
    fixture(
        &conclusion(&zero),
        &term(
            "eisenstein-unit-square-integer-congruence-cases",
            &[
                &zero,
                &term("integer-zero", &[]),
                &term(
                    "eisenstein-unit-of-natural-norm-one",
                    &[&one, "(#pt-refl #pt-nat (#pt-succ #pt-zero))"],
                ),
                &term("eisenstein-divides-zero", &[&lambda_square]),
            ],
        ),
        false,
        &unit_kummer_config(),
    );
}
