//! Foundation-free Euclidean division and actual non-scalar certificates.
use lim::{check_theorem_details_from_path_with_config, CompileConfig, ProofBudget};
use std::path::Path;

const EISENSTEIN_EUCLIDEAN_NORM: &[&str] = &[
    "eisenstein-remainder-natural-norm-equation",
    "eisenstein-remainder-natural-norm-decreases",
    "eisenstein-remainder-small-norm-exists",
];
const EISENSTEIN_EUCLIDEAN_DIVISION: &[&str] = &[
    "eisenstein-euclidean-division-from-coordinates",
    "eisenstein-euclidean-division-with-norm-exists",
    "eisenstein-euclidean-division-exists",
];

fn euclidean_division_config() -> CompileConfig {
    let mut config = CompileConfig::default();
    let default = ProofBudget::default();
    config.set_proof_budget(
        ProofBudget::new(default.work(), default.phase_bytes(), 1024 * 1024 * 1024).unwrap(),
    );
    config
}
fn check_matrix(module: &str, targets: &[&str]) {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("theorems/flt")
        .join(module);
    let source = std::fs::read_to_string(&path).unwrap();
    for &target in targets {
        let report = check_theorem_details_from_path_with_config(
            &source,
            &path,
            &euclidean_division_config(),
            target,
        )
        .unwrap_or_else(|error| panic!("failed to check {target}: {}", error.message));
        assert!(report.name == target || report.name.ends_with(&format!("::{target}")));
        assert!(report.foundations.is_empty());
    }
}
#[test]
fn euclidean_remainder_norm_theorems_are_foundation_free() {
    check_matrix("eisenstein-euclidean-norm.lim", EISENSTEIN_EUCLIDEAN_NORM);
}
#[test]
fn euclidean_division_theorems_are_foundation_free() {
    check_matrix(
        "eisenstein-euclidean-division.lim",
        EISENSTEIN_EUCLIDEAN_DIVISION,
    );
}

#[path = "support/flt_euclidean_fixtures.rs"]
mod euclidean_fixtures;
use euclidean_fixtures::{fixture, term};

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
    fn neg(self) -> Self {
        Self {
            real: self.real.neg(),
            omega: self.omega.neg(),
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
    fn conjugate(self) -> Self {
        Self {
            real: self.real.add(self.omega.neg()),
            omega: self.omega.neg(),
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
    fn nonzero(self) -> String {
        assert!(self.real.positive == 0 || self.real.negative == 0);
        let magnitude = self.real.positive + self.real.negative;
        assert!(magnitude > 0);
        let zero = term("eisenstein-zero", &[]);
        let value = self.source();
        let coord = |index| {
            term(
                "integer-equal",
                &[
                    &format!("(#pt-project eisenstein {index} {value})"),
                    &format!("(#pt-project eisenstein {index} {zero})"),
                ],
            )
        };
        let mut evidence = term(
            "conjunction-left",
            &[&coord(0), &coord(1), "zero-equivalence"],
        );
        if self.real.positive == 0 {
            evidence = format!(
                "(#pt-app (#pt-use symmetry (0)) #pt-nat #pt-zero {} {evidence})",
                numeral(magnitude)
            );
        }
        format!(
            "(#pt-lambda ((zero-equivalence {})) {})",
            term("eisenstein-equal", &[&value, &zero]),
            term("successor-not-zero", &[&numeral(magnitude - 1), &evidence])
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
fn example() -> (Eisenstein, Eisenstein, Eisenstein) {
    (
        Eisenstein::new(5, 2),
        Eisenstein::new(2, 1),
        Eisenstein::new(2, -1),
    )
}
fn coordinate_certificate(x: Eisenstein, y: Eisenstein, q: Eisenstein) -> String {
    let gamma = term(
        "eisenstein-multiply",
        &[&x.source(), &term("eisenstein-conjugate", &[&y.source()])],
    );
    let gamma_value = x.mul(y.conjugate());
    let scalar = Eisenstein::new(3, 0);
    let small = Eisenstein::new(1, 2);
    let right = term(
        "eisenstein-add",
        &[
            &term(
                "eisenstein-multiply",
                &[
                    &term("eisenstein-of-integer", &[&Integer::new(3).source()]),
                    &q.source(),
                ],
            ),
            &small.source(),
        ],
    );
    let equality = term("eisenstein-equal", &[&gamma, &right]);
    let first_bound = term("less-than", &[&numeral(1), &numeral(3)]);
    let second_bound = term("less-than", &[&numeral(2), &numeral(3)]);
    let bounds = format!("(#pt-app (#pt-use conjunction ()) {first_bound} {second_bound})");
    term(
        "conjunction-introduce",
        &[
            &equality,
            &bounds,
            &equivalence(&gamma, gamma_value, &right, scalar.mul(q).add(small)),
            &term(
                "conjunction-introduce",
                &[&first_bound, &second_bound, &less(1, 3), &less(2, 3)],
            ),
        ],
    )
}

#[test]
fn division_exists_for_units_non_scalar_and_noncanonical_inputs() {
    let mut noncanonical = Eisenstein::new(5, -2);
    noncanonical.real = Integer {
        positive: 7,
        negative: 2,
    };
    for (x, y) in [
        (Eisenstein::new(0, 0), Eisenstein::new(1, 0)),
        (Eisenstein::new(5, 2), Eisenstein::new(2, 1)),
        (noncanonical, Eisenstein::new(2, 1)),
        (Eisenstein::new(-1, -2), Eisenstein::new(-1, -1)),
    ] {
        fixture(
            &term(
                "eisenstein-has-euclidean-division",
                &[&x.source(), &y.source()],
            ),
            &term(
                "eisenstein-euclidean-division-exists",
                &[&x.source(), &y.source(), &y.nonzero()],
            ),
            true,
            &euclidean_division_config(),
        );
    }
}

#[test]
fn actual_non_scalar_division_certificate_has_norm_one_remainder() {
    let (x, y, q) = example();
    let r = Eisenstein::new(0, 1);
    let right = term(
        "eisenstein-add",
        &[
            &term("eisenstein-multiply", &[&y.source(), &q.source()]),
            &r.source(),
        ],
    );
    let equation = term("eisenstein-equal", &[&x.source(), &right]);
    let nr = term("eisenstein-natural-norm", &[&r.source(), &numeral(1)]);
    let bound = term("less-than", &[&numeral(1), &numeral(3)]);
    let pack = format!("(#pt-app (#pt-use conjunction ()) {nr} {bound})");
    let proof = term(
        "conjunction-introduce",
        &[
            &equation,
            &pack,
            &equivalence(&x.source(), x, &right, y.mul(q).add(r)),
            &term(
                "conjunction-introduce",
                &[&nr, &bound, &r.norm_certificate(1), &less(1, 3)],
            ),
        ],
    );
    fixture(
        &term(
            "eisenstein-euclidean-division-spec",
            &[
                &x.source(),
                &y.source(),
                &numeral(3),
                &q.source(),
                &r.source(),
                &numeral(1),
            ],
        ),
        &proof,
        true,
        &euclidean_division_config(),
    );
}

#[test]
fn actual_coordinate_packet_proves_strict_remainder_norm_decrease() {
    let (x, y, q) = example();
    let remainder = x.add(y.mul(q).neg());
    fixture(
        &term("less-than", &[&numeral(1), &numeral(3)]),
        &term(
            "eisenstein-remainder-natural-norm-decreases",
            &[
                &x.source(),
                &y.source(),
                &q.source(),
                &numeral(3),
                &numeral(1),
                &numeral(2),
                &numeral(1),
                &numeral(3),
                &y.norm_certificate(3),
                &coordinate_certificate(x, y, q),
                &remainder.norm_certificate(1),
                &Eisenstein::new(1, 2).norm_certificate(3),
                &y.nonzero(),
            ],
        ),
        true,
        &euclidean_division_config(),
    );
    fixture(
        &term(
            "eisenstein-euclidean-has-division",
            &[&x.source(), &y.source(), &numeral(3)],
        ),
        &term(
            "eisenstein-euclidean-division-from-coordinates",
            &[
                &x.source(),
                &y.source(),
                &numeral(3),
                &q.source(),
                &numeral(1),
                &numeral(2),
                &y.norm_certificate(3),
                &coordinate_certificate(x, y, q),
                &y.nonzero(),
            ],
        ),
        true,
        &euclidean_division_config(),
    );
}

#[test]
fn zero_divisor_cannot_reuse_a_units_nonzero_proof() {
    let x = Eisenstein::new(1, 0).source();
    let zero = Eisenstein::new(0, 0).source();
    fixture(
        &term("eisenstein-has-euclidean-division", &[&x, &zero]),
        &term(
            "eisenstein-euclidean-division-exists",
            &[&x, &zero, &term("eisenstein-one-nonzero", &[])],
        ),
        false,
        &euclidean_division_config(),
    );
}

#[test]
fn division_rejects_a_forged_zero_divisor_norm() {
    let x = Eisenstein::new(0, 0);
    let y = Eisenstein::new(1, 0);
    fixture(
        &term(
            "eisenstein-euclidean-has-division",
            &[&x.source(), &y.source(), &numeral(0)],
        ),
        &term(
            "eisenstein-euclidean-division-with-norm-exists",
            &[
                &x.source(),
                &y.source(),
                &numeral(0),
                &refl(1),
                &y.nonzero(),
            ],
        ),
        false,
        &euclidean_division_config(),
    );
}

#[test]
fn division_rejects_an_unrelated_coordinate_packet() {
    let (x, y, q) = example();
    fixture(
        &term(
            "eisenstein-euclidean-has-division",
            &[&x.source(), &y.source(), &numeral(3)],
        ),
        &term(
            "eisenstein-euclidean-division-from-coordinates",
            &[
                &x.source(),
                &y.source(),
                &numeral(3),
                &q.source(),
                &numeral(0),
                &numeral(2),
                &y.norm_certificate(3),
                &coordinate_certificate(x, y, q),
                &y.nonzero(),
            ],
        ),
        false,
        &euclidean_division_config(),
    );
}

#[test]
fn division_certificate_rejects_equal_remainder_and_divisor_norms() {
    let one = Eisenstein::new(1, 0);
    let zero = Eisenstein::new(0, 0);
    let bound = term("less-than", &[&numeral(1), &numeral(1)]);
    let nr = term("eisenstein-natural-norm", &[&one.source(), &numeral(1)]);
    let right = term(
        "eisenstein-add",
        &[
            &term("eisenstein-multiply", &[&one.source(), &zero.source()]),
            &one.source(),
        ],
    );
    let eqn = term("eisenstein-equal", &[&one.source(), &right]);
    let pack = format!("(#pt-app (#pt-use conjunction ()) {nr} {bound})");
    let proof = term(
        "conjunction-introduce",
        &[
            &eqn,
            &pack,
            &equivalence(&one.source(), one, &right, one.mul(zero).add(one)),
            &term(
                "conjunction-introduce",
                &[&nr, &bound, &one.norm_certificate(1), &less(1, 1)],
            ),
        ],
    );
    fixture(
        &term(
            "eisenstein-euclidean-division-spec",
            &[
                &one.source(),
                &one.source(),
                &numeral(1),
                &zero.source(),
                &one.source(),
                &numeral(1),
            ],
        ),
        &proof,
        false,
        &euclidean_division_config(),
    );
}

#[test]
fn product_order_reflection_rejects_a_false_strict_bound() {
    fixture(
        &term("less-than", &[&numeral(1), &numeral(1)]),
        &term(
            "natural-multiply-strict-reflect",
            &[
                &numeral(1),
                &numeral(1),
                &numeral(1),
                &term("successor-not-zero", &[&numeral(0)]),
                &less(1, 1),
            ],
        ),
        false,
        &euclidean_division_config(),
    );
}
