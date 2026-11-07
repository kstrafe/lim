//! Actual prime, coprime, power and unit certificates for cube factor removal.
use lim::{CompileConfig, ProofBudget};
#[path = "support/flt_prime_cube_fixtures.rs"]
mod fixtures;
use fixtures::{fixture, term};
fn config() -> CompileConfig {
    let mut c = CompileConfig::default();
    let d = ProofBudget::default();
    c.set_proof_budget(ProofBudget::new(d.work(), d.phase_bytes(), 1024 * 1024 * 1024).unwrap());
    c
}
fn numeral(n: usize) -> String {
    assert!(n <= 128);
    format!("(#pt-numeral {n})")
}
fn refl(n: usize) -> String {
    format!("(#pt-refl #pt-nat {})", numeral(n))
}
// These calculations author small candidate certificates. They have no proof
// authority: the kernel checks each reflexivity term against the actual syntax.
#[derive(Clone, Copy)]
struct Integer {
    positive: usize,
    negative: usize,
}
impl Integer {
    fn new(n: isize) -> Self {
        Self {
            positive: n.max(0) as usize,
            negative: (-n).max(0) as usize,
        }
    }
    fn add(self, b: Self) -> Self {
        Self {
            positive: self.positive + b.positive,
            negative: self.negative + b.negative,
        }
    }
    fn neg(self) -> Self {
        Self {
            positive: self.negative,
            negative: self.positive,
        }
    }
    fn mul(self, b: Self) -> Self {
        Self {
            positive: self.positive * b.positive + self.negative * b.negative,
            negative: self.positive * b.negative + self.negative * b.positive,
        }
    }
    fn source(self) -> String {
        format!(
            "(#pt-construct integer () () difference ({} {}))",
            numeral(self.positive),
            numeral(self.negative)
        )
    }
}
#[derive(Clone, Copy)]
struct Eisenstein {
    real: Integer,
    omega: Integer,
}
impl Eisenstein {
    fn new(a: isize, b: isize) -> Self {
        Self {
            real: Integer::new(a),
            omega: Integer::new(b),
        }
    }
    fn add(self, b: Self) -> Self {
        Self {
            real: self.real.add(b.real),
            omega: self.omega.add(b.omega),
        }
    }
    fn mul(self, b: Self) -> Self {
        Self {
            real: self.real.mul(b.real).add(self.omega.mul(b.omega).neg()),
            omega: self
                .real
                .mul(b.omega)
                .add(self.omega.mul(b.real))
                .add(self.omega.mul(b.omega).neg()),
        }
    }
    fn source(self) -> String {
        format!(
            "(#pt-construct eisenstein () () pair ({} {}))",
            self.real.source(),
            self.omega.source()
        )
    }
}
fn equivalence(left: &str, l: Eisenstein, right: &str, r: Eisenstein) -> String {
    let proposition = |index| {
        term(
            "integer-equal",
            &[
                &format!("(#pt-project eisenstein {index} {left})"),
                &format!("(#pt-project eisenstein {index} {right})"),
            ],
        )
    };
    assert_eq!(
        l.real.positive + r.real.negative,
        r.real.positive + l.real.negative
    );
    assert_eq!(
        l.omega.positive + r.omega.negative,
        r.omega.positive + l.omega.negative
    );
    term(
        "conjunction-introduce",
        &[
            &proposition(0),
            &proposition(1),
            &refl(l.real.positive + r.real.negative),
            &refl(l.omega.positive + r.omega.negative),
        ],
    )
}
fn divides(divisor: Eisenstein, number: Eisenstein, factor: Eisenstein) -> String {
    let product = term(
        "eisenstein-multiply",
        &[&divisor.source(), &factor.source()],
    );
    let pred = format!(
        "(#pt-lambda ((candidate-factor (#pt-use eisenstein ()))) {})",
        term(
            "eisenstein-equal",
            &[
                &number.source(),
                &term(
                    "eisenstein-multiply",
                    &[&divisor.source(), "candidate-factor"]
                )
            ]
        )
    );
    format!(
        "(#pt-construct exists (0) ((#pt-use eisenstein ()) {pred}) introduce ({} {}))",
        factor.source(),
        equivalence(&number.source(), number, &product, divisor.mul(factor))
    )
}
fn coprime_with_one(first: Eisenstein) -> String {
    let zero = Eisenstein::new(0, 0);
    let one = Eisenstein::new(1, 0);
    let combination = term(
        "eisenstein-add",
        &[
            &term("eisenstein-multiply", &[&zero.source(), &first.source()]),
            &term("eisenstein-multiply", &[&one.source(), &one.source()]),
        ],
    );
    let predright = format!(
        "(#pt-lambda ((candidate-right (#pt-use eisenstein ()))) {})",
        term(
            "eisenstein-equal",
            &[
                &one.source(),
                &term(
                    "eisenstein-add",
                    &[
                        &term("eisenstein-multiply", &[&zero.source(), &first.source()]),
                        &term("eisenstein-multiply", &["candidate-right", &one.source()])
                    ]
                )
            ]
        )
    );
    let predleft=format!("(#pt-lambda ((candidate-left (#pt-use eisenstein ()))) (#pt-app (#pt-use exists (0)) (#pt-use eisenstein ()) (#pt-lambda ((candidate-right (#pt-use eisenstein ()))) {})))",term("eisenstein-equal",&[&one.source(),&term("eisenstein-add",&[&term("eisenstein-multiply",&["candidate-left",&first.source()]),&term("eisenstein-multiply",&["candidate-right",&one.source()])]) ]));
    let eqn = equivalence(
        &one.source(),
        one,
        &combination,
        zero.mul(first).add(one.mul(one)),
    );
    format!("(#pt-construct exists (0) ((#pt-use eisenstein ()) {predleft}) introduce ({} (#pt-construct exists (0) ((#pt-use eisenstein ()) {predright}) introduce ({} {eqn}))))",zero.source(),one.source())
}

#[test]
fn prime_power_divisibility_requires_an_actual_power_divisor() {
    let p = term("eisenstein-lambda", &[]);
    let primality = term("eisenstein-lambda-prime", &[]);
    for n in [1, 3] {
        fixture(
            &term("eisenstein-divides", &[&p, &p]),
            &term(
                "eisenstein-prime-divides-power",
                &[
                    &p,
                    &p,
                    &numeral(n),
                    &primality,
                    &term("eisenstein-power-divisor", &[&p, &numeral(n - 1)]),
                ],
            ),
            true,
            &config(),
        );
    }
    let one = term("eisenstein-one", &[]);
    let zero = term("eisenstein-zero", &[]);
    let pred = format!(
        "(#pt-lambda ((candidate-factor (#pt-use eisenstein ()))) {})",
        term(
            "eisenstein-equal",
            &[
                &one,
                &term("eisenstein-multiply", &[&p, "candidate-factor"])
            ]
        )
    );
    let fake = format!(
        "(#pt-construct exists (0) ((#pt-use eisenstein ()) {pred}) introduce ({zero} {}))",
        term("eisenstein-reflexive", &[&one])
    );
    fixture(
        &term("eisenstein-divides", &[&p, &p]),
        &term(
            "eisenstein-prime-divides-power",
            &[&p, &p, &numeral(0), &primality, &fake],
        ),
        false,
        &config(),
    );
}
#[test]
fn coprime_factor_removal_preserves_and_requires_actual_coefficients() {
    let lambda = Eisenstein::new(-1, 1);
    let one = Eisenstein::new(1, 0);
    let cp = coprime_with_one(lambda);
    let divisor = divides(lambda, lambda, one);
    fixture(
        &term("eisenstein-coprime", &[&lambda.source(), &one.source()]),
        &term(
            "eisenstein-coprime-divisor-left",
            &[
                &lambda.source(),
                &one.source(),
                &lambda.source(),
                &cp,
                &divisor,
            ],
        ),
        true,
        &config(),
    );
    let forbidden = term("eisenstein-divides", &[&lambda.source(), &one.source()]);
    fixture(
        &format!("(#pt-pi ((denied-proof {forbidden})) #pt-false)"),
        &term(
            "eisenstein-prime-divisor-excludes-coprime-factor",
            &[
                &lambda.source(),
                &lambda.source(),
                &one.source(),
                &term("eisenstein-lambda-prime", &[]),
                &cp,
                &divisor,
            ],
        ),
        true,
        &config(),
    );
    let false_cp = cp.replacen(&refl(1), &refl(0), 1);
    assert_ne!(false_cp, cp);
    fixture(
        &term("eisenstein-coprime", &[&lambda.source(), &one.source()]),
        &term(
            "eisenstein-coprime-divisor-left",
            &[
                &lambda.source(),
                &one.source(),
                &lambda.source(),
                &false_cp,
                &divisor,
            ],
        ),
        false,
        &config(),
    );
}
#[test]
fn actual_unit_cube_equation_forces_the_prime_into_its_root() {
    let lambda = Eisenstein::new(-1, 1);
    let one = Eisenstein::new(1, 0);
    let square = lambda.mul(lambda);
    let cube = lambda.mul(square);
    let left = term("eisenstein-multiply", &[&lambda.source(), &square.source()]);
    let cube_expr = term("eisenstein-power", &[&lambda.source(), &numeral(3)]);
    let right = term("eisenstein-multiply", &[&one.source(), &cube_expr]);
    let equation = equivalence(&left, cube, &right, one.mul(cube));
    let proof = term(
        "eisenstein-prime-divides-unit-cube-root",
        &[
            &lambda.source(),
            &lambda.source(),
            &square.source(),
            &one.source(),
            &lambda.source(),
            &term("eisenstein-lambda-prime", &[]),
            &term("eisenstein-one-unit", &[]),
            &equation,
            &divides(lambda, lambda, one),
        ],
    );
    fixture(
        &term("eisenstein-divides", &[&lambda.source(), &lambda.source()]),
        &proof,
        true,
        &config(),
    );
    let fake = proof.replace(&equation, &term("eisenstein-reflexive", &[&one.source()]));
    assert_ne!(fake, proof);
    fixture(
        &term("eisenstein-divides", &[&lambda.source(), &lambda.source()]),
        &fake,
        false,
        &config(),
    );
}
