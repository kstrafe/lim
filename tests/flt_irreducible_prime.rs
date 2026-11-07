//! Constructive divisibility, unit cases and prime/irreducible certificates.
use lim::{check_theorem_details_from_path_with_config, CompileConfig, ProofBudget};
use std::path::Path;
const DIVISIBILITY_CASES: &[&str] = &[
    "eisenstein-euclidean-zero-remainder-divides",
    "eisenstein-euclidean-nonzero-remainder-not-divides",
    "eisenstein-euclidean-divisibility-cases",
    "eisenstein-divisibility-cases-nonzero-with-norm",
    "eisenstein-divisibility-cases-nonzero",
    "eisenstein-unit-cases",
];
const IRREDUCIBLE_PRIME: &[&str] = &[
    "eisenstein-irreducible-divisor-unit-or-associated",
    "eisenstein-irreducible-coprime-of-not-divides",
    "eisenstein-irreducible-prime",
    "eisenstein-prime-factorization-unit-cofactor",
    "eisenstein-prime-irreducible",
    "eisenstein-lambda-irreducible",
];
fn prime_config() -> CompileConfig {
    let mut config = CompileConfig::default();
    let d = ProofBudget::default();
    config
        .set_proof_budget(ProofBudget::new(d.work(), d.phase_bytes(), 1024 * 1024 * 1024).unwrap());
    config
}
fn check_matrix(module: &str, targets: &[&str]) {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("theorems/flt")
        .join(module);
    let source = std::fs::read_to_string(&path).unwrap();
    for &target in targets {
        let report =
            check_theorem_details_from_path_with_config(&source, &path, &prime_config(), target)
                .unwrap_or_else(|error| panic!("failed to check {target}: {}", error.message));
        assert!(report.name == target || report.name.ends_with(&format!("::{target}")));
        assert!(report.foundations.is_empty());
    }
}
#[test]
fn divisibility_and_unit_cases_are_foundation_free() {
    check_matrix("eisenstein-divisibility-cases.lim", DIVISIBILITY_CASES);
}
#[test]
fn prime_irreducible_theorems_are_foundation_free() {
    check_matrix("eisenstein-irreducible-prime.lim", IRREDUCIBLE_PRIME);
}
#[path = "support/flt_prime_fixtures.rs"]
mod prime_fixtures;
use prime_fixtures::{fixture, term};
fn numeral(n: usize) -> String {
    assert!(n <= 128);
    format!("(#pt-numeral {n})")
}
fn refl(n: usize) -> String {
    format!("(#pt-refl #pt-nat {})", numeral(n))
}
fn less(a: usize, b: usize) -> String {
    let gap = b.saturating_sub(a + 1);
    format!("(#pt-construct exists (0) (#pt-nat (#pt-lambda ((gap #pt-nat)) (#pt-eq #pt-nat {} (#pt-app (#pt-use add ()) (#pt-succ {}) gap)))) introduce ({} {}))",numeral(b),numeral(a),numeral(gap),refl(b))
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
    fn norm_certificate(self, n: usize) -> String {
        let norm = self
            .real
            .mul(self.real)
            .add(self.real.mul(self.omega).neg())
            .add(self.omega.mul(self.omega));
        assert_eq!(norm.positive, n + norm.negative);
        refl(norm.positive)
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
fn division_packet(
    x: Eisenstein,
    y: Eisenstein,
    q: Eisenstein,
    r: Eisenstein,
    d: usize,
    m: usize,
) -> String {
    let rhs = term(
        "eisenstein-add",
        &[
            &term("eisenstein-multiply", &[&y.source(), &q.source()]),
            &r.source(),
        ],
    );
    let eqn = term("eisenstein-equal", &[&x.source(), &rhs]);
    let nr = term("eisenstein-natural-norm", &[&r.source(), &numeral(m)]);
    let bound = term("less-than", &[&numeral(m), &numeral(d)]);
    let tail = term("conjunction", &[&nr, &bound]);
    term(
        "conjunction-introduce",
        &[
            &eqn,
            &tail,
            &equivalence(&x.source(), x, &rhs, y.mul(q).add(r)),
            &term(
                "conjunction-introduce",
                &[&nr, &bound, &r.norm_certificate(m), &less(m, d)],
            ),
        ],
    )
}

#[test]
fn zero_and_nonzero_remainders_give_actual_divisibility_and_refutation() {
    let p = Eisenstein::new(-1, 1);
    let one = Eisenstein::new(1, 0);
    let zero = Eisenstein::new(0, 0);
    fixture(
        &term("eisenstein-divides", &[&p.source(), &p.source()]),
        &term(
            "eisenstein-euclidean-zero-remainder-divides",
            &[
                &p.source(),
                &p.source(),
                &numeral(3),
                &one.source(),
                &zero.source(),
                &numeral(0),
                &division_packet(p, p, one, zero, 3, 0),
                &equivalence(&zero.source(), zero, &term("eisenstein-zero", &[]), zero),
            ],
        ),
        true,
        &prime_config(),
    );
    fixture(
        &format!(
            "(#pt-pi ((denied-proof {})) #pt-false)",
            term("eisenstein-divides", &[&p.source(), &one.source()])
        ),
        &term(
            "eisenstein-euclidean-nonzero-remainder-not-divides",
            &[
                &one.source(),
                &p.source(),
                &numeral(3),
                &zero.source(),
                &one.source(),
                &numeral(1),
                &division_packet(one, p, zero, one, 3, 1),
                &p.norm_certificate(3),
                &term("eisenstein-one-nonzero", &[]),
            ],
        ),
        true,
        &prime_config(),
    );
}

#[test]
fn unit_cases_cover_zero_one_and_a_nonunit() {
    for number in [
        Eisenstein::new(0, 0),
        Eisenstein::new(1, 0),
        Eisenstein::new(-1, 1),
    ] {
        let u = term("eisenstein-unit", &[&number.source()]);
        let not_u = format!("(#pt-pi ((denied-proof {u})) #pt-false)");
        fixture(
            &term("disjunction", &[&u, &not_u]),
            &term("eisenstein-unit-cases", &[&number.source()]),
            true,
            &prime_config(),
        );
    }
}

#[test]
fn coprime_symmetry_and_product_cancellation_retain_actual_coefficients() {
    let p = Eisenstein::new(-1, 1);
    let one = Eisenstein::new(1, 0);
    fixture(
        &term("eisenstein-coprime", &[&one.source(), &p.source()]),
        &term(
            "eisenstein-coprime-symmetric",
            &[&p.source(), &one.source(), &coprime_with_one(p)],
        ),
        true,
        &prime_config(),
    );
    // The product one*p is equivalent to p, with the actual factor one.
    let product = term("eisenstein-multiply", &[&one.source(), &p.source()]);
    let pred = format!(
        "(#pt-lambda ((candidate-factor (#pt-use eisenstein ()))) {})",
        term(
            "eisenstein-equal",
            &[
                &product,
                &term("eisenstein-multiply", &[&p.source(), "candidate-factor"])
            ]
        )
    );
    let proof = format!(
        "(#pt-construct exists (0) ((#pt-use eisenstein ()) {pred}) introduce ({} {}))",
        one.source(),
        equivalence(
            &product,
            one.mul(p),
            &term("eisenstein-multiply", &[&p.source(), &one.source()]),
            p.mul(one)
        )
    );
    fixture(
        &term("eisenstein-divides", &[&p.source(), &p.source()]),
        &term(
            "eisenstein-coprime-divides-product",
            &[
                &p.source(),
                &one.source(),
                &p.source(),
                &coprime_with_one(p),
                &proof,
            ],
        ),
        true,
        &prime_config(),
    );
}

#[test]
fn lambda_irreducibility_roundtrips_to_the_existing_prime_proposition() {
    let p = Eisenstein::new(-1, 1);
    let one = Eisenstein::new(1, 0);
    fixture(
        &term("eisenstein-irreducible", &[&p.source()]),
        &term("eisenstein-lambda-irreducible", &[]),
        true,
        &prime_config(),
    );
    fixture(
        &term("eisenstein-prime", &[&p.source()]),
        &term(
            "eisenstein-irreducible-prime",
            &[&p.source(), &term("eisenstein-lambda-irreducible", &[])],
        ),
        true,
        &prime_config(),
    );
    let prod = term("eisenstein-multiply", &[&p.source(), &one.source()]);
    fixture(
        &term("eisenstein-unit", &[&one.source()]),
        &term(
            "eisenstein-prime-factorization-unit-cofactor",
            &[
                &p.source(),
                &p.source(),
                &one.source(),
                &term("eisenstein-lambda-prime", &[]),
                &equivalence(&p.source(), p, &prod, p.mul(one)),
                &divides(p, p, one),
            ],
        ),
        true,
        &prime_config(),
    );
}

#[test]
fn unit_and_irreducible_certificates_cannot_be_transferred_to_unrelated_values() {
    let one = Eisenstein::new(1, 0);
    let p = Eisenstein::new(-1, 1);
    fixture(
        &term("eisenstein-unit", &[&p.source()]),
        &term(
            "eisenstein-unit-of-divides-one",
            &[&p.source(), &divides(one, one, one)],
        ),
        false,
        &prime_config(),
    );
    fixture(
        &term("eisenstein-prime", &[&one.source()]),
        &term(
            "eisenstein-irreducible-prime",
            &[&one.source(), &term("eisenstein-lambda-irreducible", &[])],
        ),
        false,
        &prime_config(),
    );
}

// Give the intended coprime type directly, but present the impossible
// equation 1=0*p+1*p. Its real-coordinate proof would require 2=0.
fn uncertified_self_coprime(p: Eisenstein) -> String {
    let zero = Eisenstein::new(0, 0);
    let one = Eisenstein::new(1, 0);
    let combination = term(
        "eisenstein-add",
        &[
            &term("eisenstein-multiply", &[&zero.source(), &p.source()]),
            &term("eisenstein-multiply", &[&one.source(), &p.source()]),
        ],
    );
    let coord = |index| {
        term(
            "integer-equal",
            &[
                &format!("(#pt-project eisenstein {index} {})", one.source()),
                &format!("(#pt-project eisenstein {index} {combination})"),
            ],
        )
    };
    let false_equation = term(
        "conjunction-introduce",
        &[&coord(0), &coord(1), &refl(2), &refl(0)],
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
                        &term("eisenstein-multiply", &[&zero.source(), &p.source()]),
                        &term("eisenstein-multiply", &["candidate-right", &p.source()])
                    ]
                )
            ]
        )
    );
    let predleft=format!("(#pt-lambda ((candidate-left (#pt-use eisenstein ()))) (#pt-app (#pt-use exists (0)) (#pt-use eisenstein ()) (#pt-lambda ((candidate-right (#pt-use eisenstein ()))) {})))",term("eisenstein-equal",&[&one.source(),&term("eisenstein-add",&[&term("eisenstein-multiply",&["candidate-left",&p.source()]),&term("eisenstein-multiply",&["candidate-right",&p.source()])]) ]));
    format!("(#pt-construct exists (0) ((#pt-use eisenstein ()) {predleft}) introduce ({} (#pt-construct exists (0) ((#pt-use eisenstein ()) {predright}) introduce ({} {false_equation}))))",zero.source(),one.source())
}

#[test]
fn coprime_cancellation_rejects_an_uncertified_coefficient_equation() {
    let p = Eisenstein::new(-1, 1);
    let one = Eisenstein::new(1, 0);
    let product = term("eisenstein-multiply", &[&p.source(), &one.source()]);
    let pred = format!(
        "(#pt-lambda ((candidate-factor (#pt-use eisenstein ()))) {})",
        term(
            "eisenstein-equal",
            &[
                &product,
                &term("eisenstein-multiply", &[&p.source(), "candidate-factor"])
            ]
        )
    );
    let div = format!(
        "(#pt-construct exists (0) ((#pt-use eisenstein ()) {pred}) introduce ({} {}))",
        one.source(),
        equivalence(
            &product,
            p.mul(one),
            &term("eisenstein-multiply", &[&p.source(), &one.source()]),
            p.mul(one)
        )
    );
    fixture(
        &term("eisenstein-divides", &[&p.source(), &one.source()]),
        &term(
            "eisenstein-coprime-divides-product",
            &[
                &p.source(),
                &p.source(),
                &one.source(),
                &uncertified_self_coprime(p),
                &div,
            ],
        ),
        false,
        &prime_config(),
    );
}

#[test]
fn prime_cofactor_unit_requires_the_actual_factor_divisibility() {
    let p = Eisenstein::new(-1, 1);
    let one = Eisenstein::new(1, 0);
    let product = term("eisenstein-multiply", &[&one.source(), &p.source()]);
    fixture(
        &term("eisenstein-unit", &[&p.source()]),
        &term(
            "eisenstein-prime-factorization-unit-cofactor",
            &[
                &p.source(),
                &one.source(),
                &p.source(),
                &term("eisenstein-lambda-prime", &[]),
                &equivalence(&p.source(), p, &product, one.mul(p)),
                &divides(p, p, one),
            ],
        ),
        false,
        &prime_config(),
    );
}

#[test]
fn division_refutation_requires_the_actual_nonzero_remainder_and_strict_bound() {
    let p = Eisenstein::new(-1, 1);
    let one = Eisenstein::new(1, 0);
    let zero = Eisenstein::new(0, 0);
    let denied = format!(
        "(#pt-pi ((denied-proof {})) #pt-false)",
        term("eisenstein-divides", &[&p.source(), &p.source()])
    );
    fixture(
        &denied,
        &term(
            "eisenstein-euclidean-nonzero-remainder-not-divides",
            &[
                &p.source(),
                &p.source(),
                &numeral(3),
                &one.source(),
                &zero.source(),
                &numeral(0),
                &division_packet(p, p, one, zero, 3, 0),
                &p.norm_certificate(3),
                &term("eisenstein-one-nonzero", &[]),
            ],
        ),
        false,
        &prime_config(),
    );
    fixture(
        &denied,
        &term(
            "eisenstein-euclidean-nonzero-remainder-not-divides",
            &[
                &p.source(),
                &p.source(),
                &numeral(3),
                &zero.source(),
                &p.source(),
                &numeral(3),
                &division_packet(p, p, zero, p, 3, 3),
                &p.norm_certificate(3),
                &term("eisenstein-lambda-nonzero", &[]),
            ],
        ),
        false,
        &prime_config(),
    );
}
