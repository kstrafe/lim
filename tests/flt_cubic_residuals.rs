//! Foundation-free checks for the FLT Eisenstein cubic residual modules.
use lim::{check_theorem_details_from_path_with_config, CompileConfig, ProofBudget};
use std::path::Path;

const CUBIC_ORDER_BALANCE: &[&str] = &[
    "eisenstein-cubic-primary-nonzero-from-third-order",
    "eisenstein-cubic-orders-balance",
    "eisenstein-cubic-primary-order-exists",
];

const CUBIC_POWER_FACTORS: &[&str] = &[
    "natural-three-times-as-sum",
    "eisenstein-lambda-power-multiply-step",
    "eisenstein-three-lambda-weighted-factors",
    "eisenstein-lambda-power-cube",
    "eisenstein-cube-lambda-powered-factor",
];

const CUBIC_RESIDUAL_EQUATION: &[&str] = &[
    "eisenstein-cubic-residual-equation",
    "eisenstein-cubic-residual-packet-from-order-factors",
    "eisenstein-cubic-remaining-residuals-exist",
    "eisenstein-cubic-solution-residuals-exist",
];

fn cubic_residuals_config() -> CompileConfig {
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
    let config = cubic_residuals_config();

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
fn cubic_order_balance_theorems_are_foundation_free() {
    check_matrix("eisenstein-cubic-order-balance.lim", CUBIC_ORDER_BALANCE);
}

#[test]
fn cubic_power_factor_theorems_are_foundation_free() {
    check_matrix("eisenstein-cubic-power-factors.lim", CUBIC_POWER_FACTORS);
}

#[test]
fn cubic_residual_equation_theorems_are_foundation_free() {
    check_matrix(
        "eisenstein-cubic-residual-equation.lim",
        CUBIC_RESIDUAL_EQUATION,
    );
}

#[path = "support/flt_cubic_fixtures.rs"]
mod cubic_fixtures;
use cubic_fixtures::{fixture, power, product, term};

fn equal(first: &str, second: &str) -> String {
    term("eisenstein-equal", &[first, second])
}
fn symmetric(first: &str, second: &str, proof: &str) -> String {
    term("eisenstein-symmetric", &[first, second, proof])
}
fn transitive(first: &str, middle: &str, last: &str, left: &str, right: &str) -> String {
    term("eisenstein-transitive", &[first, middle, last, left, right])
}
fn reflexive(number: &str) -> String {
    term("eisenstein-reflexive", &[number])
}

#[test]
fn lambda_cube_scaling_handles_zero_and_positive_exponents_and_rejects_a_wrong_coefficient() {
    let lambda = term("eisenstein-lambda", &[]);
    let residual = term(
        "eisenstein-add",
        &[&term("eisenstein-one", &[]), &term("eisenstein-omega", &[])],
    );
    for n in 0..=3 {
        let index = format!("(#pt-numeral {n})");
        let scaled = power(&lambda, 3 * n);
        fixture(
            &equal(&power(&power(&lambda, n), 3), &scaled),
            &term("eisenstein-lambda-power-cube", &[&index]),
            true,
            &cubic_residuals_config(),
        );
        fixture(
            &equal(
                &power(&product(&power(&lambda, n), &residual), 3),
                &product(&scaled, &power(&residual, 3)),
            ),
            &term(
                "eisenstein-cube-lambda-powered-factor",
                &[&index, &residual],
            ),
            true,
            &cubic_residuals_config(),
        );
    }
    fixture(
        "(#pt-eq #pt-nat (#pt-numeral 3) (#pt-numeral 4))",
        &term("natural-three-times-as-sum", &["(#pt-numeral 1)"]),
        false,
        &cubic_residuals_config(),
    );
}

#[test]
fn actual_weighted_factors_cancel_to_the_residual_product_equation() {
    // This tests the cancellation lemma's exact hypotheses. It does not
    // claim a nonzero normalized counterexample to exponent three.
    let one = term("eisenstein-one", &[]);
    let zero = term("eisenstein-zero", &[]);
    let lambda = term("eisenstein-lambda", &[]);
    let omega = term("eisenstein-omega", &[]);
    let first_power = power(&lambda, 1);
    let first_power_one = product(&first_power, &one);
    let lambda_one = product(&lambda, &one);
    let to_one = symmetric(
        &lambda_one,
        &lambda,
        &term("eisenstein-multiply-one", &[&lambda]),
    );
    let to_two_ones = symmetric(
        &first_power_one,
        &lambda_one,
        &term("eisenstein-multiply-one", &[&lambda_one]),
    );
    let third_equivalence = transitive(
        &lambda,
        &lambda_one,
        &first_power_one,
        &to_one,
        &to_two_ones,
    );
    let primary = term("eisenstein-add", &[&lambda, &zero]);
    let primary_equivalence = transitive(
        &primary,
        &lambda,
        &first_power_one,
        &term("eisenstein-add-zero", &[&lambda]),
        &third_equivalence,
    );
    let rotated = |root: &str| {
        let inner = product(root, &zero);
        let number = term("eisenstein-add", &[&lambda, &inner]);
        let step = term(
            "eisenstein-add-congruent",
            &[
                &lambda,
                &inner,
                &lambda,
                &zero,
                &reflexive(&lambda),
                &term("eisenstein-multiply-zero", &[root]),
            ],
        );
        let cancel = transitive(
            &number,
            &primary,
            &lambda,
            &step,
            &term("eisenstein-add-zero", &[&lambda]),
        );
        transitive(&number, &lambda, &lambda_one, &cancel, &to_one)
    };
    let cube = power(&lambda, 3);
    let total = term("eisenstein-add", &[&cube, &power(&zero, 3)]);
    let unit_cube = product(&one, &cube);
    let solution_equation = transitive(
        &total,
        &cube,
        &unit_cube,
        &term("eisenstein-add-zero", &[&cube]),
        &symmetric(
            &unit_cube,
            &cube,
            &term("eisenstein-one-multiply", &[&cube]),
        ),
    );
    let proof = term(
        "eisenstein-cubic-residual-equation",
        &[
            &lambda,
            &zero,
            &lambda,
            &one,
            "(#pt-numeral 1)",
            "(#pt-numeral 1)",
            &one,
            &one,
            &one,
            &one,
            &solution_equation,
            "(#pt-refl #pt-nat (#pt-numeral 3))",
            &primary_equivalence,
            &rotated(&omega),
            &rotated(&power(&omega, 2)),
            &third_equivalence,
        ],
    );
    fixture(
        &equal(
            &product(&product(&one, &one), &one),
            &product(&one, &power(&one, 3)),
        ),
        &proof,
        true,
        &cubic_residuals_config(),
    );
}

#[test]
fn residual_cancellation_requires_the_order_balance_and_actual_third_factor() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("theorems/flt/eisenstein-cubic-residual-equation.lim");
    let source = std::fs::read_to_string(&path).unwrap();
    let target = "eisenstein-cubic-residual-equation";
    let start = source.find(&format!("(#theorem {target}")).unwrap();
    for name in ["orders-balance", "third-equivalence"] {
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
            &cubic_residuals_config(),
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
