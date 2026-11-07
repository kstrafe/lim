//! Native cube-extraction instances and rejection of false certificates.
use lim::{CompileConfig, ProofBudget};
#[path = "support/flt_cube_extraction_fixtures.rs"]
mod fixtures;
use fixtures::{fixture, term};
fn config() -> CompileConfig {
    let mut c = CompileConfig::default();
    let d = ProofBudget::default();
    c.set_proof_budget(ProofBudget::new(d.work(), d.phase_bytes(), 1024 * 1024 * 1024).unwrap());
    c
}
fn numeral(n: usize) -> String {
    if n <= 128 {
        format!("(#pt-numeral {n})")
    } else {
        term("add", &["(#pt-numeral 128)", &numeral(n - 128)])
    }
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

const E: &str = "(#pt-use eisenstein ())";
fn exists(pred: &str) -> String {
    format!("(#pt-app (#pt-use exists (0)) {E} {pred})")
}
fn witness(pred: &str, value: &str, evidence: &str) -> String {
    format!("(#pt-construct exists (0) ({E} {pred}) introduce ({value} {evidence}))")
}
fn pair(a: &str, b: &str) -> String {
    term("conjunction", &[a, b])
}
fn pair_proof(a: &str, b: &str, ha: &str, hb: &str) -> String {
    term("conjunction-introduce", &[a, b, ha, hb])
}
fn power(x: Eisenstein, n: usize) -> Eisenstein {
    (0..n).fold(Eisenstein::new(1, 0), |acc, _| x.mul(acc))
}
fn cube(x: &str) -> String {
    term("eisenstein-power", &[x, &numeral(3)])
}
fn associated(x: Eisenstein) -> String {
    term("eisenstein-associated-cube", &[&x.source()])
}
fn coprime(x: Eisenstein, y: Eisenstein, s: Eisenstein, t: Eisenstein) -> String {
    let one = Eisenstein::new(1, 0);
    let expr = term(
        "eisenstein-add",
        &[
            &term("eisenstein-multiply", &[&s.source(), &x.source()]),
            &term("eisenstein-multiply", &[&t.source(), &y.source()]),
        ],
    );
    let right_pred = format!(
        "(#pt-lambda ((candidate-right (#pt-use eisenstein ()))) {})",
        term(
            "eisenstein-equal",
            &[
                &one.source(),
                &term(
                    "eisenstein-add",
                    &[
                        &term("eisenstein-multiply", &[&s.source(), &x.source()]),
                        &term("eisenstein-multiply", &["candidate-right", &y.source()])
                    ]
                )
            ]
        )
    );
    let outer_pred = format!(
        "(#pt-lambda ((candidate-left (#pt-use eisenstein ()))) {})",
        exists(&format!(
            "(#pt-lambda ((candidate-right (#pt-use eisenstein ()))) {})",
            term(
                "eisenstein-equal",
                &[
                    &one.source(),
                    &term(
                        "eisenstein-add",
                        &[
                            &term("eisenstein-multiply", &["candidate-left", &x.source()]),
                            &term("eisenstein-multiply", &["candidate-right", &y.source()])
                        ]
                    )
                ]
            )
        ))
    );
    witness(
        &outer_pred,
        &s.source(),
        &witness(
            &right_pred,
            &t.source(),
            &equivalence(&one.source(), one, &expr, s.mul(x).add(t.mul(y))),
        ),
    )
}
fn unit(x: Eisenstein, inverse: Eisenstein) -> String {
    let one = Eisenstein::new(1, 0);
    let pred = format!(
        "(#pt-lambda ((inverse (#pt-use eisenstein ()))) {})",
        pair(
            &term(
                "eisenstein-equal",
                &[
                    &term("eisenstein-multiply", &[&x.source(), "inverse"]),
                    &one.source()
                ]
            ),
            &term(
                "eisenstein-equal",
                &[
                    &term("eisenstein-multiply", &["inverse", &x.source()]),
                    &one.source()
                ]
            )
        )
    );
    let left = term("eisenstein-multiply", &[&x.source(), &inverse.source()]);
    let right = term("eisenstein-multiply", &[&inverse.source(), &x.source()]);
    witness(
        &pred,
        &inverse.source(),
        &pair_proof(
            &term("eisenstein-equal", &[&left, &one.source()]),
            &term("eisenstein-equal", &[&right, &one.source()]),
            &equivalence(&left, x.mul(inverse), &one.source(), one),
            &equivalence(&right, inverse.mul(x), &one.source(), one),
        ),
    )
}
fn equation(x: Eisenstein, y: Eisenstein, u: Eisenstein, z: Eisenstein) -> String {
    let left = term("eisenstein-multiply", &[&x.source(), &y.source()]);
    let right = term("eisenstein-multiply", &[&u.source(), &cube(&z.source())]);
    equivalence(&left, x.mul(y), &right, u.mul(power(z, 3)))
}
fn extract(
    x: Eisenstein,
    y: Eisenstein,
    u: Eisenstein,
    z: Eisenstein,
    cp: &str,
    un: &str,
    eq: &str,
) -> String {
    term(
        "eisenstein-coprime-product-associated-cubes",
        &[
            &x.source(),
            &y.source(),
            &u.source(),
            &z.source(),
            cp,
            un,
            eq,
        ],
    )
}
fn pair_statement(x: Eisenstein, y: Eisenstein) -> String {
    pair(&associated(x), &associated(y))
}
fn factor_statement(p: &str, n: usize, x: &str, y: &str, residual: &str) -> String {
    exists(&format!(
        "(#pt-lambda ((candidate-quotient (#pt-use eisenstein ()))) {})",
        pair(
            &term(
                "eisenstein-equal",
                &[
                    x,
                    &term(
                        "eisenstein-multiply",
                        &[
                            &term("eisenstein-power", &[p, &numeral(n)]),
                            "candidate-quotient"
                        ]
                    )
                ]
            ),
            &term(
                "eisenstein-equal",
                &[
                    &term("eisenstein-multiply", &["candidate-quotient", y]),
                    residual
                ]
            )
        )
    ))
}
#[test]
fn associated_cubes_include_zero_units_and_equivalent_representatives() {
    let zero = Eisenstein::new(0, 0);
    let one = Eisenstein::new(1, 0);
    fixture(
        &associated(zero),
        &term("eisenstein-zero-associated-cube", &[]),
        true,
        &config(),
    );
    for u in [one, Eisenstein::new(-1, 0)] {
        let un = term(
            "eisenstein-unit-of-natural-norm-one",
            &[&u.source(), &u.norm_certificate(1)],
        );
        fixture(
            &associated(u),
            &term("eisenstein-unit-associated-cube", &[&u.source(), &un]),
            true,
            &config(),
        );
    }
    let noncanonical = Eisenstein {
        real: Integer {
            positive: 3,
            negative: 3,
        },
        omega: Integer {
            positive: 1,
            negative: 1,
        },
    };
    fixture(
        &associated(noncanonical),
        &term(
            "eisenstein-associated-cube-congruent",
            &[
                &zero.source(),
                &noncanonical.source(),
                &equivalence(&zero.source(), zero, &noncanonical.source(), noncanonical),
                &term("eisenstein-zero-associated-cube", &[]),
            ],
        ),
        true,
        &config(),
    );
}
#[test]
fn coprime_power_factor_extraction_covers_zero_and_cubic_exponents() {
    let p = Eisenstein::new(-1, 1);
    let y = Eisenstein::new(1, 0);
    let r = Eisenstein::new(-1, 0);
    let zero = Eisenstein::new(0, 0);
    for n in [0, 3] {
        let x = power(p, n).mul(r);
        let pow = term("eisenstein-power", &[&p.source(), &numeral(n)]);
        let left = term("eisenstein-multiply", &[&x.source(), &y.source()]);
        let right = term("eisenstein-multiply", &[&pow, &r.source()]);
        let eq = equivalence(&left, x.mul(y), &right, power(p, n).mul(r));
        fixture(
            &factor_statement(&p.source(), n, &x.source(), &y.source(), &r.source()),
            &term(
                "eisenstein-coprime-extract-power",
                &[
                    &p.source(),
                    &y.source(),
                    &numeral(n),
                    &x.source(),
                    &r.source(),
                    &term("eisenstein-lambda-nonzero", &[]),
                    &coprime(p, y, zero, y),
                    &eq,
                ],
            ),
            true,
            &config(),
        );
    }
}
#[test]
fn prime_cube_removal_preserves_quotients_and_rejects_a_false_divisor() {
    let p = Eisenstein::new(-1, 1);
    let x = power(p, 3);
    let one = Eisenstein::new(1, 0);
    let zero = Eisenstein::new(0, 0);
    let q = "candidate-first-quotient";
    let r = "candidate-root-quotient";
    let first = term(
        "eisenstein-equal",
        &[
            &x.source(),
            &term("eisenstein-multiply", &[&cube(&p.source()), q]),
        ],
    );
    let second = term(
        "eisenstein-equal",
        &[&p.source(), &term("eisenstein-multiply", &[&p.source(), r])],
    );
    let residual = term(
        "eisenstein-equal",
        &[
            &term("eisenstein-multiply", &[q, &one.source()]),
            &term("eisenstein-multiply", &[&one.source(), &cube(r)]),
        ],
    );
    let predicate = format!(
        "(#pt-lambda (({q} {E})) {})",
        exists(&format!(
            "(#pt-lambda (({r} {E})) {})",
            pair(
                &first,
                &pair(
                    &second,
                    &pair(&residual, &term("eisenstein-coprime", &[q, &one.source()]))
                )
            )
        ))
    );
    let div = term("eisenstein-power-divisor", &[&p.source(), &numeral(2)]);
    let baseargs = [
        x.source(),
        one.source(),
        one.source(),
        p.source(),
        term("eisenstein-lambda-prime", &[]),
        coprime(x, one, zero, one),
        term("eisenstein-one-unit", &[]),
        equation(x, one, one, p),
    ];
    let args = |d: &str| {
        term(
            "eisenstein-prime-cube-factor-removal",
            &[
                &p.source(),
                &baseargs[0],
                &baseargs[1],
                &baseargs[2],
                &baseargs[3],
                &baseargs[4],
                &baseargs[5],
                &baseargs[6],
                &baseargs[7],
                d,
            ],
        )
    };
    fixture(&exists(&predicate), &args(&div), true, &config());
    // The candidate zero factor falsely claims x=p*0; its coefficient proof
    // must fail, rather than failing because of a missing declaration.
    fixture(
        &exists(&predicate),
        &args(&divides(p, x, zero)),
        false,
        &config(),
    );
}
#[test]
fn complete_cube_extraction_covers_nonunit_pairs_and_signed_representatives() {
    let one = Eisenstein::new(1, 0);
    let zero = Eisenstein::new(0, 0);
    let x = Eisenstein::new(8, 0);
    let y = Eisenstein::new(27, 0);
    let z = Eisenstein::new(6, 0);
    fixture(
        &pair_statement(x, y),
        &extract(
            x,
            y,
            one,
            z,
            &coprime(x, y, Eisenstein::new(-10, 0), Eisenstein::new(3, 0)),
            &term("eisenstein-one-unit", &[]),
            &equation(x, y, one, z),
        ),
        true,
        &config(),
    );
    let signed = Eisenstein {
        real: Integer {
            positive: 3,
            negative: 11,
        },
        omega: Integer {
            positive: 1,
            negative: 1,
        },
    };
    fixture(
        &pair_statement(signed, one),
        &extract(
            signed,
            one,
            one,
            Eisenstein::new(-2, 0),
            &coprime(signed, one, zero, one),
            &term("eisenstein-one-unit", &[]),
            &equation(signed, one, one, Eisenstein::new(-2, 0)),
        ),
        true,
        &config(),
    );
}
#[test]
fn prime_cube_norm_decrease_requires_the_actual_norm_certificate() {
    let p = Eisenstein::new(-1, 1);
    // Keep the actual norm certificate small. Noncanonical representatives
    // are covered separately, and expanding their raw squares here obscures
    // the strict-bound interface this probe checks.
    let x = Eisenstein::new(3, 6);
    let one = Eisenstein::new(1, 0);
    let right = term("eisenstein-multiply", &[&cube(&p.source()), &one.source()]);
    let eq = equivalence(&x.source(), x, &right, power(p, 3).mul(one));
    let nonzero = format!(
        "(#pt-lambda ((zero-equivalence {})) {})",
        term(
            "eisenstein-equal",
            &[&x.source(), &term("eisenstein-zero", &[])]
        ),
        term(
            "successor-not-zero",
            &[
                &numeral(2),
                &term(
                    "conjunction-left",
                    &[
                        &term(
                            "integer-equal",
                            &[&x.real.source(), &Integer::new(0).source()]
                        ),
                        &term(
                            "integer-equal",
                            &[&x.omega.source(), &Integer::new(0).source()]
                        ),
                        "zero-equivalence",
                    ]
                )
            ]
        )
    );
    for (n, valid) in [(27, true), (26, false)] {
        let proof = term(
            "eisenstein-prime-cube-quotient-norm-decreases",
            &[
                &p.source(),
                &x.source(),
                &one.source(),
                &numeral(n),
                &numeral(1),
                &term("eisenstein-lambda-prime", &[]),
                &x.norm_certificate(27),
                &one.norm_certificate(1),
                &nonzero,
                &eq,
            ],
        );
        fixture(
            &term("less-than", &[&numeral(1), &numeral(n)]),
            &proof,
            valid,
            &config(),
        );
    }
}
#[test]
fn complete_extraction_rejects_a_missing_coprimality_equation() {
    let x = Eisenstein::new(2, 0);
    let y = Eisenstein::new(4, 0);
    let one = Eisenstein::new(1, 0);
    let zero = Eisenstein::new(0, 0);
    fixture(
        &pair_statement(x, y),
        &extract(
            x,
            y,
            one,
            x,
            &coprime(x, y, zero, zero),
            &term("eisenstein-one-unit", &[]),
            &equation(x, y, one, x),
        ),
        false,
        &config(),
    );
}
#[test]
fn complete_extraction_rejects_a_false_product_equation() {
    let x = Eisenstein::new(2, 0);
    let y = Eisenstein::new(3, 0);
    let one = Eisenstein::new(1, 0);
    fixture(
        &pair_statement(x, y),
        &extract(
            x,
            y,
            one,
            x,
            &coprime(x, y, Eisenstein::new(-1, 0), one),
            &term("eisenstein-one-unit", &[]),
            &equation(x, y, one, x),
        ),
        false,
        &config(),
    );
}
#[test]
fn complete_extraction_rejects_a_nonunit_with_a_forged_inverse() {
    let one = Eisenstein::new(1, 0);
    let eight = Eisenstein::new(8, 0);
    let zero = Eisenstein::new(0, 0);
    fixture(
        &pair_statement(one, eight),
        &extract(
            one,
            eight,
            eight,
            one,
            &coprime(one, eight, one, zero),
            &unit(eight, zero),
            &equation(one, eight, eight, one),
        ),
        false,
        &config(),
    );
}

#[test]
fn triple_cube_extraction_constructs_all_three_root_unit_witnesses() {
    let x = Eisenstein::new(-1, 0);
    let y = Eisenstein::new(8, 0);
    let z = Eisenstein::new(27, 0);
    let one = Eisenstein::new(1, 0);
    let zero = Eisenstein::new(0, 0);
    let root = Eisenstein::new(-6, 0);
    let left = term(
        "eisenstein-multiply",
        &[
            &term("eisenstein-multiply", &[&x.source(), &y.source()]),
            &z.source(),
        ],
    );
    let right = term(
        "eisenstein-multiply",
        &[&one.source(), &cube(&root.source())],
    );
    let equation = equivalence(&left, x.mul(y).mul(z), &right, one.mul(power(root, 3)));
    fixture(
        &pair(&associated(x), &pair(&associated(y), &associated(z))),
        &term(
            "eisenstein-coprime-triple-associated-cubes",
            &[
                &x.source(),
                &y.source(),
                &z.source(),
                &one.source(),
                &root.source(),
                &coprime(x, y, x, zero),
                &coprime(x, z, x, zero),
                &coprime(y, z, Eisenstein::new(-10, 0), Eisenstein::new(3, 0)),
                &term("eisenstein-one-unit", &[]),
                &equation,
            ],
        ),
        true,
        &config(),
    );
}
