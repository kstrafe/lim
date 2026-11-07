//! Foundation-free Euclidean gcd/Bezout existence and adversarial certificates.
use lim::{check_theorem_details_from_path_with_config, CompileConfig, ProofBudget};
use std::path::Path;
const BEZOUT_GCD_INDUCTION: &[&str] = &[
    "eisenstein-natural-norm-positive-nonzero",
    "eisenstein-bezout-gcd-division-step",
    "eisenstein-bezout-gcd-positive-step",
    "eisenstein-bezout-gcd-induction-step",
    "eisenstein-bezout-gcd-with-norm-exists",
];
const BEZOUT_GCD: &[&str] = &["eisenstein-bezout-gcd-exists"];
const EISENSTEIN_GCD: &[&str] = &[
    "eisenstein-gcd-of-bezout-certificate",
    "eisenstein-gcd-exists",
];
fn bezout_gcd_config() -> CompileConfig {
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
        let report = check_theorem_details_from_path_with_config(
            &source,
            &path,
            &bezout_gcd_config(),
            target,
        )
        .unwrap_or_else(|error| panic!("failed to check {target}: {}", error.message));
        assert!(report.name == target || report.name.ends_with(&format!("::{target}")));
        assert!(report.foundations.is_empty());
    }
}
#[test]
fn bezout_gcd_induction_theorems_are_foundation_free() {
    check_matrix("eisenstein-bezout-gcd-induction.lim", BEZOUT_GCD_INDUCTION);
}
#[test]
fn bezout_gcd_existence_is_foundation_free() {
    check_matrix("eisenstein-bezout-gcd.lim", BEZOUT_GCD);
}
#[test]
fn eisenstein_gcd_theorems_are_foundation_free() {
    check_matrix("eisenstein-gcd.lim", EISENSTEIN_GCD);
}
#[path = "support/flt_bezout_gcd_fixtures.rs"]
mod gcd_fixtures;
use gcd_fixtures::{fixture, term};
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
fn certificate(
    x: Eisenstein,
    y: Eisenstein,
    g: Eisenstein,
    s: Eisenstein,
    t: Eisenstein,
    fx: Eisenstein,
    fy: Eisenstein,
) -> String {
    let combination = term(
        "eisenstein-add",
        &[
            &term("eisenstein-multiply", &[&s.source(), &x.source()]),
            &term("eisenstein-multiply", &[&t.source(), &y.source()]),
        ],
    );
    let eqn = term("eisenstein-equal", &[&g.source(), &combination]);
    let gy = term("eisenstein-divides", &[&g.source(), &y.source()]);
    let tail = term("conjunction", &[&gy, &eqn]);
    term(
        "conjunction-introduce",
        &[
            &term("eisenstein-divides", &[&g.source(), &x.source()]),
            &tail,
            &divides(g, x, fx),
            &term(
                "conjunction-introduce",
                &[
                    &gy,
                    &eqn,
                    &divides(g, y, fy),
                    &equivalence(&g.source(), g, &combination, s.mul(x).add(t.mul(y))),
                ],
            ),
        ],
    )
}
fn old_certificate() -> String {
    certificate(
        Eisenstein::new(2, 1),
        Eisenstein::new(0, 1),
        Eisenstein::new(0, 1),
        Eisenstein::new(0, 0),
        Eisenstein::new(1, 0),
        Eisenstein::new(-1, -2),
        Eisenstein::new(1, 0),
    )
}

#[test]
fn bezout_gcd_exists_for_zero_noncanonical_and_non_scalar_pairs() {
    let mut noncanonical = Eisenstein::new(5, -2);
    noncanonical.real = Integer {
        positive: 7,
        negative: 2,
    };
    for (x, y) in [
        (Eisenstein::new(0, 0), Eisenstein::new(0, 0)),
        (Eisenstein::new(2, 1), Eisenstein::new(0, 0)),
        (noncanonical, Eisenstein::new(-1, -1)),
        (Eisenstein::new(5, 2), Eisenstein::new(2, 1)),
    ] {
        fixture(
            &term("eisenstein-has-bezout-gcd", &[&x.source(), &y.source()]),
            &term("eisenstein-bezout-gcd-exists", &[&x.source(), &y.source()]),
            true,
            &bezout_gcd_config(),
        );
    }
    let x = Eisenstein::new(5, 2);
    let y = Eisenstein::new(2, 1);
    fixture(
        &term("eisenstein-has-bezout-gcd", &[&x.source(), &y.source()]),
        &term(
            "eisenstein-bezout-gcd-with-norm-exists",
            &[
                &numeral(3),
                &x.source(),
                &y.source(),
                &y.norm_certificate(3),
            ],
        ),
        true,
        &bezout_gcd_config(),
    );
}

#[test]
fn standard_gcd_specification_follows_from_actual_coefficients() {
    let y = Eisenstein::new(2, 1);
    let r = Eisenstein::new(0, 1);
    let zero = Eisenstein::new(0, 0);
    let one = Eisenstein::new(1, 0);
    fixture(
        &term(
            "eisenstein-gcd-spec",
            &[&y.source(), &r.source(), &r.source()],
        ),
        &term(
            "eisenstein-gcd-of-bezout-certificate",
            &[
                &y.source(),
                &r.source(),
                &r.source(),
                &zero.source(),
                &one.source(),
                &old_certificate(),
            ],
        ),
        true,
        &bezout_gcd_config(),
    );
    fixture(
        &term("eisenstein-has-gcd", &[&y.source(), &r.source()]),
        &term("eisenstein-gcd-exists", &[&y.source(), &r.source()]),
        true,
        &bezout_gcd_config(),
    );
}

#[test]
fn euclidean_step_preserves_the_actual_divisors_and_coefficients() {
    let x = Eisenstein::new(5, 2);
    let y = Eisenstein::new(2, 1);
    let q = Eisenstein::new(2, -1);
    let r = Eisenstein::new(0, 1);
    let one = Eisenstein::new(1, 0);
    let zero = Eisenstein::new(0, 0);
    let right = term(
        "eisenstein-add",
        &[
            &term("eisenstein-multiply", &[&y.source(), &q.source()]),
            &r.source(),
        ],
    );
    let equation = equivalence(&x.source(), x, &right, y.mul(q).add(r));
    let coefficient = term(
        "eisenstein-add",
        &[
            &zero.source(),
            &term(
                "eisenstein-negate",
                &[&term("eisenstein-multiply", &[&one.source(), &q.source()])],
            ),
        ],
    );
    fixture(
        &term(
            "eisenstein-bezout-gcd-spec",
            &[
                &x.source(),
                &y.source(),
                &r.source(),
                &one.source(),
                &coefficient,
            ],
        ),
        &term(
            "eisenstein-bezout-gcd-euclidean-step",
            &[
                &x.source(),
                &y.source(),
                &q.source(),
                &r.source(),
                &r.source(),
                &zero.source(),
                &one.source(),
                &equation,
                &old_certificate(),
            ],
        ),
        true,
        &bezout_gcd_config(),
    );
}

#[test]
fn every_common_divisor_divides_the_certified_gcd() {
    let y = Eisenstein::new(2, 1);
    let r = Eisenstein::new(0, 1);
    let one = Eisenstein::new(1, 0);
    let zero = Eisenstein::new(0, 0);
    fixture(
        &term("eisenstein-divides", &[&r.source(), &r.source()]),
        &term(
            "eisenstein-bezout-gcd-common-divisor",
            &[
                &y.source(),
                &r.source(),
                &r.source(),
                &zero.source(),
                &one.source(),
                &r.source(),
                &old_certificate(),
                &divides(r, y, Eisenstein::new(-1, -2)),
                &divides(r, r, one),
            ],
        ),
        true,
        &bezout_gcd_config(),
    );
}

#[test]
fn gcd_certificate_rejects_mismatched_input_divisibility() {
    let y = Eisenstein::new(2, 1);
    let r = Eisenstein::new(0, 1);
    let valid = old_certificate();
    let first = divides(r, y, Eisenstein::new(-1, -2));
    let second = divides(r, r, Eisenstein::new(1, 0));
    assert!(valid.contains(&first));
    let false_certificate = valid.replacen(&first, &second, 1);
    fixture(
        &term(
            "eisenstein-bezout-gcd-spec",
            &[
                &y.source(),
                &r.source(),
                &r.source(),
                &Eisenstein::new(0, 0).source(),
                &Eisenstein::new(1, 0).source(),
            ],
        ),
        &false_certificate,
        false,
        &bezout_gcd_config(),
    );
}

#[test]
fn gcd_certificate_rejects_an_incorrect_coefficient_equation() {
    let y = Eisenstein::new(2, 1);
    let r = Eisenstein::new(0, 1);
    let zero = Eisenstein::new(0, 0);
    fixture(
        &term(
            "eisenstein-bezout-gcd-spec",
            &[
                &y.source(),
                &r.source(),
                &r.source(),
                &zero.source(),
                &zero.source(),
            ],
        ),
        &old_certificate(),
        false,
        &bezout_gcd_config(),
    );
}

#[test]
fn euclidean_coefficient_update_requires_actual_reconstruction() {
    let x = Eisenstein::new(5, 2);
    let y = Eisenstein::new(2, 1);
    let q = Eisenstein::new(2, -1);
    let r = Eisenstein::new(0, 1);
    let one = Eisenstein::new(1, 0);
    let zero = Eisenstein::new(0, 0);
    let right = term(
        "eisenstein-add",
        &[
            &term("eisenstein-multiply", &[&y.source(), &q.source()]),
            &r.source(),
        ],
    );
    let equation = equivalence(&x.source(), x, &right, y.mul(q).add(r));
    let coefficient = term(
        "eisenstein-add",
        &[
            &zero.source(),
            &term(
                "eisenstein-negate",
                &[&term("eisenstein-multiply", &[&one.source(), &q.source()])],
            ),
        ],
    );
    fixture(
        &term(
            "eisenstein-bezout-gcd-spec",
            &[
                &zero.source(),
                &y.source(),
                &r.source(),
                &one.source(),
                &coefficient,
            ],
        ),
        &term(
            "eisenstein-bezout-gcd-euclidean-step",
            &[
                &zero.source(),
                &y.source(),
                &q.source(),
                &r.source(),
                &r.source(),
                &zero.source(),
                &one.source(),
                &equation,
                &old_certificate(),
            ],
        ),
        false,
        &bezout_gcd_config(),
    );
}

#[test]
fn gcd_induction_cannot_use_the_current_or_a_larger_norm() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("theorems/flt");
    let original =
        std::fs::read_to_string(root.join("eisenstein-bezout-gcd-induction.lim")).unwrap();
    // Resolve the copied source's relative aliases without changing the original.
    let mut source = original.clone();
    for path in original
        .split_whitespace()
        .filter(|token| token.starts_with("./") && token.contains(".lim::"))
    {
        let (file, name) = path.split_once("::").unwrap();
        source = source.replace(path, &format!("{}::{name}", root.join(file).display()));
    }
    let position = source
        .match_indices("given-history")
        .find_map(|(position, name)| {
            let tail = &source[position + name.len()..];
            let trimmed = tail.trim_start();
            trimmed
                .starts_with("remainder-norm")
                .then_some(position + name.len() + tail.len() - trimmed.len())
        })
        .expect("the Euclidean step must apply history at the actual remainder norm");
    for (index, replacement) in ["divisor-norm", "(#pt-succ divisor-norm)"]
        .into_iter()
        .enumerate()
    {
        let mut mutant = source.clone();
        mutant.replace_range(position..position + "remainder-norm".len(), replacement);
        let directory = std::env::temp_dir().join(format!(
            "lim-flt-gcd-induction-{}-{index}",
            std::process::id()
        ));
        std::fs::create_dir(&directory).unwrap();
        let path = directory.join("probe.lim");
        std::fs::write(&path, &mutant).unwrap();
        let result = check_theorem_details_from_path_with_config(
            &mutant,
            &path,
            &bezout_gcd_config(),
            "eisenstein-bezout-gcd-division-step",
        );
        std::fs::remove_dir_all(&directory).unwrap();
        let error = result.unwrap_err();
        assert_eq!(error.code, lim::DiagnosticCode::Proof);
        assert!(error.message.contains("mismatch"), "{}", error.message);
    }
}
