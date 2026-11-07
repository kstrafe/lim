//! Foundation-free checks for the FLT Eisenstein Bezout linear modules.
use lim::{check_theorem_details_from_path_with_config, CompileConfig, ProofBudget};
use std::path::Path;

const EXPANSION: &[&str] = &["eisenstein-bezout-linear-expansion"];

const ALGEBRA: &[&str] = &[
    "eisenstein-negative-add-inverse",
    "eisenstein-negative-add-cancel",
    "eisenstein-add-cancel-right",
    "eisenstein-inverse-linear-second",
    "eisenstein-complementary-linear-rows",
    "eisenstein-linear-complement",
];

const CHANGE: &[&str] = &[
    "eisenstein-coprime-linear-change",
    "eisenstein-coprime-from-sum-and-unit-shift",
];

fn bezout_linear_config() -> CompileConfig {
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
    let config = bezout_linear_config();

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
fn bezout_linear_expansion_theorems_are_foundation_free() {
    check_matrix("eisenstein-bezout-linear-expansion.lim", EXPANSION);
}

#[test]
fn bezout_linear_algebra_theorems_are_foundation_free() {
    check_matrix("eisenstein-bezout-linear-algebra.lim", ALGEBRA);
}

#[test]
fn bezout_linear_change_theorems_are_foundation_free() {
    check_matrix("eisenstein-bezout-linear-change.lim", CHANGE);
}

#[path = "support/flt_bezout_fixtures.rs"]
mod bezout_fixtures;
use bezout_fixtures::{fixture, product, term};

fn second_coefficient_one(first: &str, second: &str) -> String {
    let one = term("eisenstein-one", &[]);
    let zero = term("eisenstein-zero", &[]);
    let eq = |left: &str, right: &str| {
        term(
            "eisenstein-equal",
            &[
                &one,
                &term(
                    "eisenstein-add",
                    &[&product(left, first), &product(right, second)],
                ),
            ],
        )
    };
    let right_pred = format!(
        "(#pt-lambda ((candidate-right (#pt-use eisenstein ()))) {})",
        eq(&zero, "candidate-right")
    );
    let left_pred=format!("(#pt-lambda ((candidate-left (#pt-use eisenstein ()))) (#pt-app (#pt-use exists (0)) (#pt-use eisenstein ()) (#pt-lambda ((candidate-right (#pt-use eisenstein ()))) {})))",eq("candidate-left","candidate-right"));
    let right = format!(
        "(#pt-construct exists (0) ((#pt-use eisenstein ()) {right_pred}) introduce ({one} {}))",
        term("eisenstein-reflexive", &[&one])
    );
    format!("(#pt-construct exists (0) ((#pt-use eisenstein ()) {left_pred}) introduce ({zero} {right}))")
}

#[test]
fn linear_change_and_unit_shift_transport_actual_coefficients_and_reject_a_false_row() {
    let one = term("eisenstein-one", &[]);
    let zero = term("eisenstein-zero", &[]);
    for (target, valid) in [(&one, true), (&zero, false)] {
        let proof = term(
            "eisenstein-coprime-linear-change",
            &[
                &zero,
                &one,
                &zero,
                target,
                &zero,
                &zero,
                &zero,
                &one,
                &term("eisenstein-reflexive", &[&zero]),
                &term("eisenstein-reflexive", &[&one]),
                &second_coefficient_one(&zero, &one),
            ],
        );
        fixture(
            &term("eisenstein-coprime", &[&zero, target]),
            &proof,
            valid,
            &bezout_linear_config(),
        );
    }
    let negative = term("eisenstein-negate", &[&one]);
    let lambda = term("eisenstein-lambda", &[]);
    let primary = term("eisenstein-add", &[&negative, &one]);
    let scaled = product(&lambda, &zero);
    let primary_eq = term(
        "eisenstein-transitive",
        &[
            &primary,
            &zero,
            &scaled,
            &term("eisenstein-negative-add-inverse", &[&one]),
            &term(
                "eisenstein-symmetric",
                &[
                    &scaled,
                    &zero,
                    &term("eisenstein-multiply-zero", &[&lambda]),
                ],
            ),
        ],
    );
    let u = term("eisenstein-add", &[&term("eisenstein-omega", &[]), &one]);
    for (unit, certificate) in [
        (&one, term("eisenstein-one-unit", &[])),
        (&u, term("eisenstein-omega-plus-one-unit", &[])),
    ] {
        let first = product(&one, &zero);
        let second = product(unit, &one);
        let row = term("eisenstein-add", &[&first, &second]);
        let middle = term("eisenstein-add", &[&zero, unit]);
        let row_eq = term(
            "eisenstein-transitive",
            &[
                &row,
                &middle,
                unit,
                &term(
                    "eisenstein-add-congruent",
                    &[
                        &first,
                        &second,
                        &zero,
                        unit,
                        &term("eisenstein-multiply-zero", &[&one]),
                        &term("eisenstein-multiply-one", &[unit]),
                    ],
                ),
                &term("eisenstein-zero-add", &[unit]),
            ],
        );
        let proof = term(
            "eisenstein-coprime-from-sum-and-unit-shift",
            &[
                &negative,
                &one,
                &zero,
                unit,
                &lambda,
                &one,
                unit,
                &certificate,
                &primary_eq,
                &term("eisenstein-symmetric", &[&row, unit, &row_eq]),
                &second_coefficient_one(&negative, &one),
            ],
        );
        fixture(
            &term("eisenstein-coprime", &[&zero, unit]),
            &proof,
            true,
            &bezout_linear_config(),
        );
    }
}

#[test]
fn unit_linear_change_cannot_drop_its_equations_unit_or_original_bezout_evidence() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("theorems/flt/eisenstein-bezout-linear-change.lim");
    let source = std::fs::read_to_string(&path).unwrap();
    let target = "eisenstein-coprime-from-sum-and-unit-shift";
    let start = source.find(&format!("(#theorem {target}")).unwrap();
    for name in [
        "unit-proof",
        "primary-equivalence",
        "shift-equivalence",
        "coprime-proof",
    ] {
        let parameter = start
            + source[start..]
                .find(&format!("(#parameter {name} "))
                .unwrap();
        let mut depth = 0usize;
        let mut end = parameter;
        for (index, byte) in source.as_bytes()[parameter..].iter().enumerate() {
            if *byte == b'(' {
                depth += 1;
            } else if *byte == b')' {
                depth -= 1;
                if depth == 0 {
                    end = parameter + index + 1;
                    break;
                }
            }
        }
        let changed = format!("{}{}", &source[..parameter], &source[end..]);
        lim::parse_program_from_path(&changed, &path)
            .expect("removing evidence keeps source syntax valid");
        let error = check_theorem_details_from_path_with_config(
            &changed,
            &path,
            &bezout_linear_config(),
            target,
        )
        .unwrap_err();
        assert_eq!(error.code, lim::DiagnosticCode::Proof);
        assert!(
            error
                .message
                .contains(&format!("unbound proof-term name '{name}'")),
            "{}",
            error.message
        );
    }
}
