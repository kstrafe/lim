//! Foundation-free checks for the FLT Eisenstein cubic-shift and rotated-order modules.
use lim::{check_theorem_details_from_path_with_config, CompileConfig, ProofBudget};
use std::path::Path;

const CUBIC_SHIFTS: &[&str] = &[
    "eisenstein-omega-plus-one-unit",
    "eisenstein-omega-lambda-unit-shift",
    "eisenstein-omega-square-lambda-unit-shift",
    "eisenstein-cubic-factor-unit-shift",
];

const CUBIC_ROTATED_ORDERS: &[&str] = &[
    "eisenstein-lambda-order-one-after-square-shift",
    "eisenstein-cubic-omega-factor-order-one",
    "eisenstein-cubic-omega-factor-lambda-divides",
    "eisenstein-cubic-omega-factor-square-not-divides",
    "eisenstein-cubic-omega-square-factor-order-one",
    "eisenstein-cubic-omega-square-factor-lambda-divides",
    "eisenstein-cubic-omega-square-factor-square-not-divides",
];

fn rotated_orders_config() -> CompileConfig {
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
    let config = rotated_orders_config();

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
fn cubic_shift_theorems_are_foundation_free() {
    check_matrix("eisenstein-cubic-shifts.lim", CUBIC_SHIFTS);
}

#[test]
fn cubic_rotated_order_theorems_are_foundation_free() {
    check_matrix("eisenstein-cubic-rotated-orders.lim", CUBIC_ROTATED_ORDERS);
}

#[path = "support/flt_cubic_fixtures.rs"]
mod cubic_fixtures;
use cubic_fixtures::{fixture, power, product, term};

#[test]
fn both_rotated_factors_have_order_one_for_zero_and_nonzero_primary_sums() {
    let one = term("eisenstein-one", &[]);
    let zero = term("eisenstein-zero", &[]);
    let lambda = term("eisenstein-lambda", &[]);
    let negative = term("eisenstein-negate", &[&one]);
    let square = power(&lambda, 2);
    let shifted = term("eisenstein-add", &[&negative, &square]);
    let omega = term("eisenstein-omega", &[]);
    for (first, nonzero_primary) in [(&negative, false), (&shifted, true)] {
        let primary = term("eisenstein-add", &[first, &one]);
        let (target, relation, divides) = if nonzero_primary {
            let middle = term(
                "eisenstein-add",
                &[&term("eisenstein-add", &[&square, &negative]), &one],
            );
            let swap = term(
                "eisenstein-add-congruent",
                &[
                    first,
                    &one,
                    &term("eisenstein-add", &[&square, &negative]),
                    &one,
                    &term("eisenstein-add-commutative", &[&negative, &square]),
                    &term("eisenstein-reflexive", &[&one]),
                ],
            );
            let relation = term(
                "eisenstein-transitive",
                &[
                    &primary,
                    &middle,
                    &square,
                    &swap,
                    &term("eisenstein-add-after-subtract", &[&square, &one]),
                ],
            );
            (
                square.clone(),
                relation,
                term("eisenstein-divides-reflexive", &[&square]),
            )
        } else {
            let middle = term("eisenstein-add", &[&one, &negative]);
            let relation = term(
                "eisenstein-transitive",
                &[
                    &primary,
                    &middle,
                    &zero,
                    &term("eisenstein-add-commutative", &[&negative, &one]),
                    &term("eisenstein-add-inverse", &[&one]),
                ],
            );
            (
                zero.clone(),
                relation,
                term("eisenstein-divides-zero", &[&square]),
            )
        };
        let square_divisor = term(
            "eisenstein-divides-congruent-target",
            &[
                &square,
                &target,
                &primary,
                &term("eisenstein-symmetric", &[&primary, &target, &relation]),
                &divides,
            ],
        );
        for (root, name) in [
            (&omega, "eisenstein-cubic-omega-factor-order-one"),
            (
                &power(&omega, 2),
                "eisenstein-cubic-omega-square-factor-order-one",
            ),
        ] {
            let number = term("eisenstein-add", &[first, &product(root, &one)]);
            let proof = term(
                name,
                &[
                    first,
                    &one,
                    &term("eisenstein-lambda-not-divides-one", &[]),
                    &square_divisor,
                ],
            );
            fixture(
                &term("eisenstein-lambda-order", &[&number, "(#pt-numeral 1)"]),
                &proof,
                true,
                &rotated_orders_config(),
            );
            if !nonzero_primary {
                for wrong in [0, 2] {
                    fixture(
                        &term(
                            "eisenstein-lambda-order",
                            &[&number, &format!("(#pt-numeral {wrong})")],
                        ),
                        &proof,
                        false,
                        &rotated_orders_config(),
                    );
                }
            }
        }
    }
}

#[test]
fn shifted_order_cannot_drop_unit_nondivisibility_or_square_evidence() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("theorems/flt/eisenstein-cubic-rotated-orders.lim");
    let source = std::fs::read_to_string(&path).unwrap();
    let target = "eisenstein-lambda-order-one-after-square-shift";
    let start = source.find(&format!("(#theorem {target}")).unwrap();
    for name in ["unit-proof", "second-not-divides", "primary-square-divides"] {
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
            &rotated_orders_config(),
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
