//! Foundation-free checks for the FLT Eisenstein cubic residual modules.
use lim::{check_theorem_details_from_path_with_config, CompileConfig, ProofBudget};
use std::path::Path;

const BEZOUT_SHIFTS: &[&str] = &[
    "eisenstein-square-root-lambda-difference",
    "eisenstein-linear-factor-shift",
    "eisenstein-lambda-residual-add",
    "eisenstein-cubic-primary-rotated-residual-shift",
    "eisenstein-cubic-rotated-pair-residual-shift",
];

const RESIDUAL_COPRIME: &[&str] = &[
    "eisenstein-cubic-primary-omega-residuals-coprime",
    "eisenstein-cubic-primary-square-residuals-coprime",
    "eisenstein-cubic-rotated-residuals-coprime",
];

const PACKET_COPRIME: &[&str] = &[
    "eisenstein-square-divisible-order-predecessor",
    "eisenstein-cubic-packet-residuals-coprime",
];

fn residual_coprime_config() -> CompileConfig {
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
    let config = residual_coprime_config();

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
fn cubic_bezout_shift_theorems_are_foundation_free() {
    check_matrix("eisenstein-cubic-bezout-shifts.lim", BEZOUT_SHIFTS);
}

#[test]
fn cubic_residual_coprime_theorems_are_foundation_free() {
    check_matrix("eisenstein-cubic-residual-coprime.lim", RESIDUAL_COPRIME);
}

#[test]
fn cubic_packet_coprime_theorems_are_foundation_free() {
    check_matrix("eisenstein-cubic-packet-coprime.lim", PACKET_COPRIME);
}

#[path = "support/flt_bezout_fixtures.rs"]
mod bezout_fixtures;
use bezout_fixtures::{fixture, product, term};

fn power(number: &str, exponent: usize) -> String {
    term(
        "eisenstein-power",
        &[number, &format!("(#pt-numeral {exponent})")],
    )
}
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
    let rp = format!(
        "(#pt-lambda ((candidate-right (#pt-use eisenstein ()))) {})",
        eq(&zero, "candidate-right")
    );
    let lp=format!("(#pt-lambda ((candidate-left (#pt-use eisenstein ()))) (#pt-app (#pt-use exists (0)) (#pt-use eisenstein ()) (#pt-lambda ((candidate-right (#pt-use eisenstein ()))) {})))",eq("candidate-left","candidate-right"));
    let right = format!(
        "(#pt-construct exists (0) ((#pt-use eisenstein ()) {rp}) introduce ({one} {}))",
        term("eisenstein-reflexive", &[&one])
    );
    format!("(#pt-construct exists (0) ((#pt-use eisenstein ()) {lp}) introduce ({zero} {right}))")
}

#[test]
fn all_three_residual_pairs_receive_actual_bezout_witnesses() {
    let one = term("eisenstein-one", &[]);
    let zero = term("eisenstein-zero", &[]);
    let negative = term("eisenstein-negate", &[&one]);
    let lambda = term("eisenstein-lambda", &[]);
    let omega = term("eisenstein-omega", &[]);
    let u = term("eisenstein-add", &[&omega, &one]);
    let primary = term("eisenstein-add", &[&negative, &one]);
    let scaled = product(&power(&lambda, 1), &zero);
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
                    &term("eisenstein-multiply-zero", &[&power(&lambda, 1)]),
                ],
            ),
        ],
    );
    let rotated_eq = |root: &str, coefficient: &str, lemma: &str| {
        let factor = term("eisenstein-add", &[&negative, &product(root, &one)]);
        let simple = term("eisenstein-add", &[&negative, root]);
        let shifted = term("eisenstein-add", &[&one, &product(&lambda, coefficient)]);
        let middle = term("eisenstein-add", &[&negative, &shifted]);
        let h1 = term(
            "eisenstein-add-congruent",
            &[
                &negative,
                &product(root, &one),
                &negative,
                root,
                &term("eisenstein-reflexive", &[&negative]),
                &term("eisenstein-multiply-one", &[root]),
            ],
        );
        let h2 = term(
            "eisenstein-add-congruent",
            &[
                &negative,
                root,
                &negative,
                &shifted,
                &term("eisenstein-reflexive", &[&negative]),
                &term(lemma, &[]),
            ],
        );
        let h3 = term(
            "eisenstein-negative-add-cancel",
            &[&one, &product(&lambda, coefficient)],
        );
        term(
            "eisenstein-transitive",
            &[
                &factor,
                &simple,
                &product(&lambda, coefficient),
                &h1,
                &term(
                    "eisenstein-transitive",
                    &[&simple, &middle, &product(&lambda, coefficient), &h2, &h3],
                ),
            ],
        )
    };
    let omega_eq = rotated_eq(&omega, &one, "eisenstein-omega-lambda-unit-shift");
    let square_eq = rotated_eq(
        &power(&omega, 2),
        &u,
        "eisenstein-omega-square-lambda-unit-shift",
    );
    let original = second_coefficient_one(&negative, &one);
    for (second, proof) in [
        (
            &one,
            term(
                "eisenstein-cubic-primary-omega-residuals-coprime",
                &[
                    &negative,
                    &one,
                    "#pt-zero",
                    &zero,
                    &one,
                    &primary_eq,
                    &omega_eq,
                    &original,
                ],
            ),
        ),
        (
            &u,
            term(
                "eisenstein-cubic-primary-square-residuals-coprime",
                &[
                    &negative,
                    &one,
                    "#pt-zero",
                    &zero,
                    &u,
                    &primary_eq,
                    &square_eq,
                    &original,
                ],
            ),
        ),
    ] {
        fixture(
            &term("eisenstein-coprime", &[&zero, second]),
            &proof,
            true,
            &residual_coprime_config(),
        );
    }
    let proof = term(
        "eisenstein-cubic-rotated-residuals-coprime",
        &[&negative, &one, &one, &u, &omega_eq, &square_eq, &original],
    );
    fixture(
        &term("eisenstein-coprime", &[&one, &u]),
        &proof,
        true,
        &residual_coprime_config(),
    );
}

fn remove_required_evidence(module: &str, target: &str, names: &[&str]) {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("theorems/flt")
        .join(module);
    let source = std::fs::read_to_string(&path).unwrap();
    let start = source.find(&format!("(#theorem {target}")).unwrap();
    for name in names {
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
            &residual_coprime_config(),
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

#[test]
fn residual_pairs_cannot_drop_factor_equations_or_original_coprimality() {
    for target in [
        "eisenstein-cubic-primary-omega-residuals-coprime",
        "eisenstein-cubic-primary-square-residuals-coprime",
    ] {
        remove_required_evidence(
            "eisenstein-cubic-residual-coprime.lim",
            target,
            &[
                "primary-equivalence",
                "rotated-equivalence",
                "coprime-proof",
            ],
        );
    }
    remove_required_evidence(
        "eisenstein-cubic-residual-coprime.lim",
        "eisenstein-cubic-rotated-residuals-coprime",
        &["omega-equivalence", "square-equivalence", "coprime-proof"],
    );
}

#[test]
fn packet_coprimality_cannot_invent_order_divisibility_or_packet_evidence() {
    remove_required_evidence(
        "eisenstein-cubic-packet-coprime.lim",
        "eisenstein-cubic-packet-residuals-coprime",
        &[
            "primary-order-certificate",
            "primary-square-divisor",
            "coprime-proof",
            "residual-packet",
        ],
    );
}
