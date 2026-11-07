//! Concrete certificates and adversarial controls for native cubic descent.
use lim::{CompileConfig, ProofBudget};
#[path = "support/flt_cubic_descent_fixtures.rs"]
mod fixtures;
use fixtures::{fixture, term};

fn config() -> CompileConfig {
    let mut config = CompileConfig::default();
    let default = ProofBudget::default();
    config.set_proof_budget(
        ProofBudget::new(default.work(), default.phase_bytes(), 1024 * 1024 * 1024).unwrap(),
    );
    config
}
fn n(value: usize) -> String {
    format!("(#pt-numeral {value})")
}
fn refl(value: usize) -> String {
    format!("(#pt-refl #pt-nat {})", n(value))
}
fn one() -> String {
    term("eisenstein-one", &[])
}
fn zero() -> String {
    term("eisenstein-zero", &[])
}
fn lambda() -> String {
    term("eisenstein-lambda", &[])
}
fn omega() -> String {
    term("eisenstein-omega", &[])
}
fn neg(x: &str) -> String {
    term("eisenstein-negate", &[x])
}
fn product(x: &str, y: &str) -> String {
    term("eisenstein-multiply", &[x, y])
}
fn sum(x: &str, y: &str) -> String {
    term("eisenstein-add", &[x, y])
}
fn power(x: &str, exponent: usize) -> String {
    term("eisenstein-power", &[x, &n(exponent)])
}
fn eq(x: &str, y: &str) -> String {
    term("eisenstein-equal", &[x, y])
}
fn nat_eq(x: &str, y: &str) -> String {
    format!("(#pt-eq #pt-nat {x} {y})")
}
fn divides(d: &str, x: &str) -> String {
    term("eisenstein-divides", &[d, x])
}
fn less(x: usize, y: usize) -> String {
    term("less-than", &[&n(x), &n(y)])
}
fn pair(a: &str, b: &str, ha: &str, hb: &str) -> String {
    term("conjunction-introduce", &[a, b, ha, hb])
}
fn sign(x: &str) -> String {
    term("disjunction", &[&eq(x, &one()), &eq(x, &neg(&one()))])
}

// These are candidate reflexivity certificates, not host-side proof oracles.
// The native kernel computes and checks both integer-coordinate equalities.
fn eq_certificate(left: &str, right: &str, real_cross: usize, omega_cross: usize) -> String {
    let coordinate = |i| {
        term(
            "integer-equal",
            &[
                &format!("(#pt-project eisenstein {i} {left})"),
                &format!("(#pt-project eisenstein {i} {right})"),
            ],
        )
    };
    pair(
        &coordinate(0),
        &coordinate(1),
        &refl(real_cross),
        &refl(omega_cross),
    )
}
fn witness(pred: &str, value: &str, evidence: &str) -> String {
    format!("(#pt-construct exists (0) ((#pt-use eisenstein ()) {pred}) introduce ({value} {evidence}))")
}
fn sign_unit(x: &str) -> String {
    let pred = format!("(#pt-lambda ((candidate-inverse (#pt-use eisenstein ()))) (#pt-app (#pt-use conjunction ()) {} {}))", eq(&product(x, "candidate-inverse"), &one()), eq(&product("candidate-inverse", x), &one()));
    let square = product(x, x);
    let cert = eq_certificate(&square, &one(), 1, 0);
    witness(
        &pred,
        x,
        &pair(&eq(&square, &one()), &eq(&square, &one()), &cert, &cert),
    )
}
fn lambda_free_unit(x: &str, certificate: &str) -> String {
    format!(
        "(#pt-lambda ((alleged-divisor {})) (#pt-app {} {}))",
        divides(&lambda(), x),
        term("eisenstein-lambda-not-unit", &[]),
        term(
            "eisenstein-divisor-of-unit-is-unit",
            &[&lambda(), x, certificate, "alleged-divisor"]
        )
    )
}
fn divisor_witness(d: &str, x: &str, factor: &str, certificate: &str) -> String {
    let pred = format!(
        "(#pt-lambda ((candidate-factor (#pt-use eisenstein ()))) {})",
        eq(x, &product(d, "candidate-factor"))
    );
    witness(&pred, factor, certificate)
}
fn normalized_sign_proof(
    y: &str,
    z: &str,
    coefficient: &str,
    right: &str,
    equation: &str,
    square: &str,
    coefficient_unit: &str,
) -> String {
    term(
        "eisenstein-normalized-cubic-coefficient-sign",
        &[
            y,
            z,
            coefficient,
            right,
            &lambda_free_unit(y, &sign_unit(y)),
            &lambda_free_unit(z, &sign_unit(z)),
            equation,
            square,
            coefficient_unit,
        ],
    )
}

#[test]
fn normalized_coefficient_sign_checks_all_four_cube_residue_branches() {
    for y_positive in [true, false] {
        for z_positive in [true, false] {
            let y = if y_positive { one() } else { neg(&one()) };
            let z = if z_positive { one() } else { neg(&one()) };
            let coefficient = if y_positive == z_positive {
                neg(&one())
            } else {
                one()
            };
            let total = sum(&power(&y, 3), &product(&coefficient, &power(&z, 3)));
            let proof = normalized_sign_proof(
                &y,
                &z,
                &coefficient,
                &zero(),
                &eq_certificate(&total, &zero(), 1, 0),
                &term("eisenstein-divides-zero", &[&power(&lambda(), 2)]),
                &sign_unit(&coefficient),
            );
            fixture(&sign(&coefficient), &proof, true, &config());
        }
    }
}

#[test]
fn square_divisor_construction_rejects_a_forged_divisor_of_a_unit() {
    let false_divisor = divisor_witness(&lambda(), &one(), &zero(), &refl(0));
    let proof = term(
        "eisenstein-square-divides-scaled-cube-from-divisor",
        &[&lambda(), &omega(), &one(), &false_divisor],
    );
    let result = divides(&power(&lambda(), 2), &product(&omega(), &power(&one(), 3)));
    fixture(&result, &proof, false, &config());
}

#[test]
fn a_witnessed_factor_of_the_cube_root_produces_a_square_divisor() {
    let cube_root = product(&lambda(), &one());
    let result = divides(
        &power(&lambda(), 2),
        &product(&omega(), &power(&cube_root, 3)),
    );
    let proof = term(
        "eisenstein-square-divides-scaled-factor-cube",
        &[&lambda(), &omega(), &one()],
    );
    fixture(&result, &proof, true, &config());
}

#[test]
fn signed_coefficients_are_absorbed_into_the_second_root() {
    for positive in [true, false] {
        let coefficient = if positive { one() } else { neg(&one()) };
        let right = if positive {
            sum(&one(), &one())
        } else {
            zero()
        };
        let variant = if positive { "left" } else { "right" };
        let equality = term("eisenstein-reflexive", &[&coefficient]);
        let sign_proof = format!(
            "(#pt-construct disjunction () ({} {}) {variant} ({equality}))",
            eq(&coefficient, &one()),
            eq(&coefficient, &neg(&one()))
        );
        let total = sum(&power(&one(), 3), &product(&coefficient, &power(&one(), 3)));
        let equation = eq_certificate(&total, &right, if positive { 2 } else { 1 }, 0);
        let proof = term(
            "eisenstein-signed-cubic-absorption",
            &[&one(), &one(), &coefficient, &right, &sign_proof, &equation],
        );
        let result = eq(
            &sum(&power(&one(), 3), &power(&product(&coefficient, &one()), 3)),
            &right,
        );
        fixture(&result, &proof, true, &config());
    }
}

#[test]
fn absorption_rejects_an_arbitrary_unit_as_a_signed_coefficient() {
    let false_sign = format!(
        "(#pt-construct disjunction () ({} {}) left ({}))",
        eq(&omega(), &one()),
        eq(&omega(), &neg(&one())),
        term("eisenstein-reflexive", &[&omega()])
    );
    let proof = term(
        "eisenstein-signed-coefficient-cube",
        &[&omega(), &false_sign],
    );
    fixture(&eq(&power(&omega(), 3), &omega()), &proof, false, &config());
}

#[test]
fn lambda_free_residual_gives_the_exact_constructed_order() {
    for order in [0, 1, 2] {
        let number = product(&power(&lambda(), order), &one());
        let result = term("eisenstein-lambda-order", &[&number, &n(order)]);
        let proof = term(
            "eisenstein-lambda-powered-free-residual-order",
            &[
                &n(order),
                &one(),
                &lambda_free_unit(&one(), &sign_unit(&one())),
            ],
        );
        fixture(&result, &proof, true, &config());
    }
}

#[test]
fn predecessor_is_positive_and_strictly_smaller() {
    let position = nat_eq(&n(2), &format!("(#pt-succ {})", n(1)));
    let large = term("less-than-successor", &[&n(1)]);
    let positive = term(
        "natural-cubic-predecessor-positive",
        &[&n(2), &n(1), &large, &refl(2)],
    );
    fixture(&less(0, 1), &positive, true, &config());
    let smaller = term(
        "natural-cubic-predecessor-smaller",
        &[&n(2), &n(1), &refl(2)],
    );
    fixture(&less(1, 2), &smaller, true, &config());
    // Independently check the premise used by both applications.
    fixture(&position, &refl(2), true, &config());
}

#[test]
fn predecessor_descent_rejects_the_current_or_a_larger_order() {
    for proposed in [2, 3] {
        let proof = term(
            "natural-cubic-predecessor-smaller",
            &[&n(2), &n(proposed), &refl(2)],
        );
        fixture(&less(proposed, 2), &proof, false, &config());
    }
}

#[test]
fn closed_exponent_three_rejects_transport_along_a_false_exponent_equality() {
    let proof = format!(
        "(#pt-app (#pt-use substitution (0)) #pt-nat \
         (#pt-lambda ((candidate-exponent #pt-nat)) {}) {} {} {} {})",
        term("fermat-for", &["candidate-exponent"]),
        n(3),
        n(5),
        refl(3),
        term("fermat-for-three", &[])
    );
    fixture(&term("fermat-for", &[&n(5)]), &proof, false, &config());
}
