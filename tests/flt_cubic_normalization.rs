//! Concrete root, unit and normalized-cubic certificates and negative probes.
use lim::{CompileConfig, ProofBudget};
#[path = "support/flt_cubic_normalization_fixtures.rs"]
mod fixtures;
use fixtures::{fixture, fixture_with_prelude, term};
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

fn eq(x: &str, y: &str) -> String {
    term("eisenstein-equal", &[x, y])
}
fn product(x: &str, y: &str) -> String {
    term("eisenstein-multiply", &[x, y])
}
fn sum(x: &str, y: &str) -> String {
    term("eisenstein-add", &[x, y])
}
fn negative(x: &str) -> String {
    term("eisenstein-negate", &[x])
}
fn eunit(x: &str) -> String {
    term("eisenstein-unit", &[x])
}
fn not(p: &str) -> String {
    format!("(#pt-pi ((denied-proof {p})) #pt-false)")
}
fn nat_eq(x: &str, y: &str) -> String {
    format!("(#pt-eq #pt-nat {x} {y})")
}
fn nat_exists(p: &str) -> String {
    format!("(#pt-app (#pt-use exists (0)) #pt-nat {p})")
}
fn invoke(name: &str, args: &[String]) -> String {
    term(name, &args.iter().map(String::as_str).collect::<Vec<_>>())
}
fn inverse_certificate(x: Eisenstein, v: Eisenstein) -> String {
    let one = Eisenstein::new(1, 0);
    let l = product(&x.source(), &v.source());
    let r = product(&v.source(), &x.source());
    pair_proof(
        &eq(&l, &one.source()),
        &eq(&r, &one.source()),
        &equivalence(&l, x.mul(v), &one.source(), one),
        &equivalence(&r, v.mul(x), &one.source(), one),
    )
}
fn cube_equation(x: Eisenstein, u: Eisenstein, r: Eisenstein) -> String {
    let right = product(&u.source(), &cube(&r.source()));
    equivalence(&x.source(), x, &right, u.mul(power(r, 3)))
}
fn lambda_not_divides_one() -> String {
    let l = term("eisenstein-lambda", &[]);
    let one = Eisenstein::new(1, 0).source();
    format!(
        "(#pt-lambda ((divides-one {})) (#pt-app {} {}))",
        term("eisenstein-divides", &[&l, &one]),
        term("eisenstein-lambda-not-unit", &[]),
        term("eisenstein-unit-of-divides-one", &[&l, "divides-one"])
    )
}
fn normalized(order: &str, rx: &str, ry: &str, rz: &str, u1: &str, u3: &str, v: &str) -> String {
    let w = term("eisenstein-omega", &[]);
    let w2 = term("eisenstein-power", &[&w, &numeral(2)]);
    let u4 = product(&product(&w, u3), v);
    let u5 = negative(&product(&product(&w2, u1), v));
    let lp = term(
        "eisenstein-power",
        &[&term("eisenstein-lambda", &[]), order],
    );
    eq(
        &sum(&cube(ry), &product(&u4, &cube(rz))),
        &product(&u5, &cube(&product(&lp, rx))),
    )
}
fn order_statement(m: usize, k: usize) -> String {
    let ph = term("multiply", &[&numeral(3), "candidate-predecessor"]);
    nat_exists(&format!(
        "(#pt-lambda ((candidate-predecessor #pt-nat)) {})",
        pair(
            &nat_eq(&numeral(k), "(#pt-succ candidate-predecessor)"),
            &nat_eq(&numeral(m), &format!("(#pt-succ {ph})"))
        )
    ))
}
// Share the language's named constants in the larger applications. Repeating
// their constructor trees forces unnecessary conversions of the same values.
fn constant(value: Eisenstein) -> String {
    match (
        value.real.positive,
        value.real.negative,
        value.omega.positive,
        value.omega.negative,
    ) {
        (0, 0, 0, 0) => term("eisenstein-zero", &[]),
        (1, 0, 0, 0) => term("eisenstein-one", &[]),
        (0, 1, 0, 0) => negative(&term("eisenstein-one", &[])),
        (1, 0, 1, 0) => negative(&term(
            "eisenstein-power",
            &[&term("eisenstein-omega", &[]), &numeral(2)],
        )),
        _ => value.source(),
    }
}
fn norm_cube_certificate(x: Eisenstein, u: Eisenstein, r: Eisenstein) -> String {
    let right = product(&constant(u), &cube(&constant(r)));
    equivalence(&constant(x), x, &right, u.mul(power(r, 3)))
}
fn norm_args(
    m: usize,
    k: usize,
    h: Option<usize>,
    v: Eisenstein,
    px: Eisenstein,
    rx: Eisenstein,
) -> Vec<String> {
    let aa = Eisenstein::new(-1, 0);
    let bb = Eisenstein::new(1, 0);
    let one = bb;
    let p = Eisenstein::new(-1, 1);
    let w = Eisenstein::new(0, 1);
    let w2 = power(w, 2);
    let pz = Eisenstein::new(1, 1);
    let f0 = sum(&constant(aa), &constant(bb));
    let omega = term("eisenstein-omega", &[]);
    let lambda = term("eisenstein-lambda", &[]);
    let f1 = sum(&constant(aa), &product(&omega, &constant(bb)));
    let f2 = sum(
        &constant(aa),
        &product(
            &term("eisenstein-power", &[&omega, &numeral(2)]),
            &constant(bb),
        ),
    );
    let mut args = vec![
        constant(aa),
        constant(bb),
        numeral(m),
        numeral(k),
        constant(px),
        constant(one),
        constant(pz),
        constant(rx),
        constant(one),
        constant(one),
        constant(one),
        constant(one),
        constant(pz),
        constant(v),
    ];
    if let Some(hh) = h {
        args.push(numeral(hh));
    }
    args.extend([
        refl(m + 2),
        equivalence(
            &f0,
            aa.add(bb),
            &product(
                &term("eisenstein-power", &[&lambda, &numeral(m)]),
                &constant(px),
            ),
            power(p, m).mul(px),
        ),
        equivalence(
            &f1,
            aa.add(w.mul(bb)),
            &product(&lambda, &constant(one)),
            p.mul(one),
        ),
        equivalence(
            &f2,
            aa.add(w2.mul(bb)),
            &product(&lambda, &constant(pz)),
            p.mul(pz),
        ),
        norm_cube_certificate(px, one, rx),
        norm_cube_certificate(one, one, one),
        norm_cube_certificate(pz, pz, one),
        inverse_certificate(one, v),
    ]);
    if h.is_some() {
        args.push(refl(k));
    }
    args
}
// Check each numerical premise once, then use its named certificate in the
// larger application. This keeps the same cases inside the ordinary budget.
fn staged_norm_args(m: usize, k: usize, h: Option<usize>) -> (String, Vec<String>) {
    let one = Eisenstein::new(1, 0);
    let zero = Eisenstein::new(0, 0);
    let mut args = norm_args(m, k, h, one, zero, zero);
    let omega = term("eisenstein-omega", &[]);
    let lambda = term("eisenstein-lambda", &[]);
    let square = term("eisenstein-power", &[&omega, &numeral(2)]);
    let span = term(
        "add",
        &[&term("add", &[&numeral(m), &numeral(1)]), &numeral(1)],
    );
    let mut types = vec![
        nat_eq(&span, &term("multiply", &[&numeral(3), &numeral(k)])),
        eq(
            &sum(&args[0], &args[1]),
            &product(&term("eisenstein-power", &[&lambda, &numeral(m)]), &args[4]),
        ),
        eq(
            &sum(&args[0], &product(&omega, &args[1])),
            &product(&lambda, &args[5]),
        ),
        eq(
            &sum(&args[0], &product(&square, &args[1])),
            &product(&lambda, &args[6]),
        ),
        eq(&args[4], &product(&args[10], &cube(&args[7]))),
        eq(&args[5], &product(&args[11], &cube(&args[8]))),
        eq(&args[6], &product(&args[12], &cube(&args[9]))),
        pair(
            &eq(&product(&args[11], &args[13]), &constant(one)),
            &eq(&product(&args[13], &args[11]), &constant(one)),
        ),
    ];
    if let Some(hh) = h {
        types.push(nat_eq(&numeral(k), &format!("(#pt-succ {})", numeral(hh))));
    }
    let start = if h.is_some() { 15 } else { 14 };
    let mut prelude = String::new();
    for (i, ty) in types.iter().enumerate() {
        let name = format!("normalization-evidence-{i}");
        let candidate = if i == 1 {
            // Use the proved zero-product law for lambda^m*0. Computing its
            // raw coordinates is unnecessary and grows quickly with m.
            let first = sum(&args[0], &args[1]);
            let reversed = sum(&args[1], &args[0]);
            let scale = term("eisenstein-power", &[&lambda, &numeral(m)]);
            let scaled_zero = product(&scale, &constant(zero));
            let first_zero = term(
                "eisenstein-transitive",
                &[
                    &first,
                    &reversed,
                    &constant(zero),
                    &term("eisenstein-add-commutative", &[&args[0], &args[1]]),
                    &term("eisenstein-add-inverse", &[&args[1]]),
                ],
            );
            term(
                "eisenstein-transitive",
                &[
                    &first,
                    &constant(zero),
                    &scaled_zero,
                    &first_zero,
                    &term(
                        "eisenstein-symmetric",
                        &[
                            &scaled_zero,
                            &constant(zero),
                            &term("eisenstein-multiply-zero", &[&scale]),
                        ],
                    ),
                ],
            )
        } else {
            args[start + i].clone()
        };
        prelude.push_str(&format!(
            "(#theorem {name} (#universes) (#parameters) (#statement {ty}) (#proof {candidate}))\n"
        ));
        args[start + i] = term(&name, &[]);
    }
    (prelude, args)
}
#[test]
fn cube_roots_retain_actual_divisors_and_coprimality() {
    let x = Eisenstein::new(8, 0);
    let y = Eisenstein::new(27, 0);
    let r = Eisenstein::new(2, 0);
    let s = Eisenstein::new(3, 0);
    let one = Eisenstein::new(1, 0);
    let hx = cube_equation(x, one, r);
    let hy = cube_equation(y, one, s);
    fixture(
        &term("eisenstein-divides", &[&r.source(), &x.source()]),
        &term(
            "eisenstein-cube-root-divides-value",
            &[&x.source(), &one.source(), &r.source(), &hx],
        ),
        true,
        &config(),
    );
    fixture(
        &term("eisenstein-coprime", &[&r.source(), &s.source()]),
        &term(
            "eisenstein-cube-roots-coprime",
            &[
                &x.source(),
                &y.source(),
                &one.source(),
                &one.source(),
                &r.source(),
                &s.source(),
                &hx,
                &hy,
                &coprime(x, y, Eisenstein::new(-10, 0), Eisenstein::new(3, 0)),
            ],
        ),
        true,
        &config(),
    );
}
#[test]
fn noncanonical_roots_inherit_lambda_nondivisibility_and_nonzero() {
    let one = Eisenstein::new(1, 0);
    let minus = Eisenstein::new(-1, 0);
    let root = Eisenstein {
        real: Integer {
            positive: 1,
            negative: 2,
        },
        omega: Integer::new(0),
    };
    let l = term("eisenstein-lambda", &[]);
    let proof = term(
        "eisenstein-cube-root-nondivisor",
        &[
            &l,
            &one.source(),
            &minus.source(),
            &root.source(),
            &cube_equation(one, minus, root),
            &lambda_not_divides_one(),
        ],
    );
    fixture(
        &not(&term("eisenstein-divides", &[&l, &root.source()])),
        &proof,
        true,
        &config(),
    );
    fixture(
        &not(&eq(&root.source(), &Eisenstein::new(0, 0).source())),
        &term(
            "eisenstein-nondivisor-implies-nonzero",
            &[&l, &root.source(), &proof],
        ),
        true,
        &config(),
    );
}
#[test]
fn inverse_product_negation_and_power_units_have_actual_certificates() {
    let w = Eisenstein::new(0, 1);
    let v = Eisenstein::new(-1, -1);
    let minus = Eisenstein::new(-1, 0);
    let uw = unit(w, v);
    fixture(
        &eunit(&v.source()),
        &term(
            "eisenstein-witnessed-inverse-is-unit",
            &[&w.source(), &v.source(), &inverse_certificate(w, v)],
        ),
        true,
        &config(),
    );
    fixture(
        &eunit(&product(&w.source(), &minus.source())),
        &term(
            "eisenstein-units-multiply",
            &[&w.source(), &minus.source(), &uw, &unit(minus, minus)],
        ),
        true,
        &config(),
    );
    fixture(
        &eunit(&negative(&w.source())),
        &term("eisenstein-unit-negate", &[&w.source(), &uw]),
        true,
        &config(),
    );
    for n in [0, 3] {
        let p = term("eisenstein-power", &[&w.source(), &numeral(n)]);
        fixture(
            &eunit(&p),
            &term("eisenstein-unit-power", &[&w.source(), &numeral(n), &uw]),
            true,
            &config(),
        );
    }
}
#[test]
fn omega_weighted_factor_relation_holds_for_signed_coordinates() {
    let aa = Eisenstein::new(2, -1);
    let bb = Eisenstein::new(-1, 2);
    let w = Eisenstein::new(0, 1);
    let w2 = term("eisenstein-power", &[&w.source(), &numeral(2)]);
    let f0 = sum(&aa.source(), &bb.source());
    let f1 = sum(&aa.source(), &product(&w.source(), &bb.source()));
    let f2 = sum(&aa.source(), &product(&w2, &bb.source()));
    let weighted = sum(&sum(&f0, &product(&w.source(), &f1)), &product(&w2, &f2));
    fixture(
        &eq(&weighted, &Eisenstein::new(0, 0).source()),
        &term(
            "eisenstein-omega-weighted-linear-sum",
            &[&aa.source(), &bb.source()],
        ),
        true,
        &config(),
    );
}
#[test]
fn normalized_cubic_and_predecessor_follow_actual_balanced_factors() {
    let one = Eisenstein::new(1, 0);
    let zero = Eisenstein::new(0, 0);
    let u3 = Eisenstein::new(1, 1);
    for (m, k, h) in [(1, 1, 0), (4, 2, 1)] {
        eprintln!("checking normalized equation: m={m}, k={k}, h={h}");
        let (prelude, args) = staged_norm_args(m, k, Some(h));
        fixture_with_prelude(
            &prelude,
            &normalized(
                &numeral(h),
                &constant(zero),
                &constant(one),
                &constant(one),
                &constant(one),
                &constant(u3),
                &constant(one),
            ),
            &invoke("eisenstein-normalized-cubic-from-balanced-factors", &args),
            true,
            &config(),
        );
        let pred = format!(
            "(#pt-lambda ((candidate-root-order #pt-nat)) {})",
            pair(
                &nat_eq(&numeral(k), "(#pt-succ candidate-root-order)"),
                &normalized(
                    "candidate-root-order",
                    &constant(zero),
                    &constant(one),
                    &constant(one),
                    &constant(one),
                    &constant(u3),
                    &constant(one)
                )
            )
        );
        eprintln!("checking normalized predecessor: m={m}, k={k}, h={h}");
        let (prelude, args) = staged_norm_args(m, k, None);
        fixture_with_prelude(
            &prelude,
            &nat_exists(&pred),
            &invoke("eisenstein-normalized-cubic-order-exists", &args),
            true,
            &config(),
        );
    }
}
#[test]
fn order_balance_constructs_predecessors_and_rejects_false_balance() {
    for (m, k, h) in [(1, 1, 0), (4, 2, 1), (7, 3, 2)] {
        fixture(
            &nat_eq(&numeral(m), &numeral(m)),
            &term(
                "natural-cubic-balance-predecessor-order",
                &[
                    &numeral(m),
                    &numeral(k),
                    &numeral(h),
                    &refl(m + 2),
                    &refl(k),
                ],
            ),
            true,
            &config(),
        );
    }
    fixture(
        &order_statement(2, 1),
        &term(
            "natural-cubic-balance-has-predecessor",
            &[&numeral(2), &numeral(1), &refl(4)],
        ),
        false,
        &config(),
    );
}
#[test]
fn normalization_rejects_a_forged_inverse() {
    let one = Eisenstein::new(1, 0);
    let zero = Eisenstein::new(0, 0);
    let u3 = Eisenstein::new(1, 1);
    let omega = term("eisenstein-omega", &[]);
    let square = term("eisenstein-power", &[&omega, &numeral(2)]);
    let u4 = product(&product(&omega, &u3.source()), &zero.source());
    let u5 = negative(&product(&product(&square, &one.source()), &zero.source()));
    fixture(
        &pair(&eunit(&u4), &eunit(&u5)),
        &term(
            "eisenstein-normalized-cubic-units",
            &[
                &one.source(),
                &one.source(),
                &u3.source(),
                &zero.source(),
                &unit(one, one),
                &unit(u3, Eisenstein::new(0, -1)),
                &inverse_certificate(one, zero),
            ],
        ),
        false,
        &config(),
    );
}
#[test]
fn normalization_rejects_a_false_primary_factor_equation() {
    let one = Eisenstein::new(1, 0);
    let u3 = Eisenstein::new(1, 1);
    fixture(
        &normalized(
            &numeral(0),
            &one.source(),
            &one.source(),
            &one.source(),
            &one.source(),
            &u3.source(),
            &one.source(),
        ),
        &invoke(
            "eisenstein-normalized-cubic-from-balanced-factors",
            &norm_args(1, 1, Some(0), one, one, one),
        ),
        false,
        &config(),
    );
}
#[test]
fn root_properties_reject_a_false_cube_equation() {
    let x = Eisenstein::new(8, 0);
    let one = Eisenstein::new(1, 0);
    let wrong = Eisenstein::new(3, 0);
    fixture(
        &term("eisenstein-divides", &[&wrong.source(), &x.source()]),
        &term(
            "eisenstein-cube-root-divides-value",
            &[
                &x.source(),
                &one.source(),
                &wrong.source(),
                &cube_equation(x, one, wrong),
            ],
        ),
        false,
        &config(),
    );
}
