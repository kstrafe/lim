//! Regression certificates for the constructive finite-search prime proof.
use lim::{CompileConfig, ProofBudget};
#[path = "support/flt_finite_prime_fixtures.rs"]
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

fn exists(ty: &str, pred: &str) -> String {
    format!("(#pt-app (#pt-use exists (0)) {ty} {pred})")
}
fn witness(ty: &str, pred: &str, value: &str, evidence: &str) -> String {
    format!("(#pt-construct exists (0) ({ty} {pred}) introduce ({value} {evidence}))")
}
#[test]
fn coordinate_search_covers_signs_zero_and_noncanonical_integers() {
    let noncanonical = Eisenstein {
        real: Integer {
            positive: 2,
            negative: 1,
        },
        omega: Integer {
            positive: 1,
            negative: 1,
        },
    };
    for (value, n) in [
        (Eisenstein::new(0, 0), 0),
        (Eisenstein::new(1, 2), 3),
        (Eisenstein::new(1, -2), 7),
        (Eisenstein::new(-1, 2), 7),
        (Eisenstein::new(-1, -2), 3),
        (noncanonical, 1),
    ] {
        fixture(
            &term(
                "eisenstein-has-finite-coordinates",
                &[&value.source(), &numeral(n)],
            ),
            &term(
                "eisenstein-finite-coordinates-exist",
                &[&value.source(), &numeral(n), &value.norm_certificate(n)],
            ),
            true,
            &config(),
        );
    }
}
#[test]
fn coordinate_budget_requires_the_actual_square_equation() {
    for (m, q, b) in [(0, 0, 0), (1, 2, 5), (2, 1, 13)] {
        fixture(
            &term("less-than", &[&numeral(m), &numeral(b + 1)]),
            &term(
                "natural-three-square-budget-magnitude-bound",
                &[&numeral(m), &numeral(q), &numeral(b), &refl(b)],
            ),
            true,
            &config(),
        );
    }
    let negative = Integer::new(-2).source();
    fixture(
        &term("less-than", &[&numeral(2), &numeral(14)]),
        &term(
            "integer-three-square-magnitude-bound",
            &[
                &negative,
                &Integer::new(1).source(),
                &numeral(2),
                &numeral(13),
                &term("integer-negative-magnitude", &[&numeral(2)]),
                &refl(13),
            ],
        ),
        true,
        &config(),
    );
    fixture(
        &term("less-than", &[&numeral(2), &numeral(13)]),
        &term(
            "natural-three-square-budget-magnitude-bound",
            &[&numeral(2), &numeral(1), &numeral(12), &refl(12)],
        ),
        false,
        &config(),
    );
}
#[test]
fn minimum_search_does_not_mistake_a_late_witness_for_the_minimum() {
    let property = format!(
        "(#pt-lambda ((index #pt-nat)) {})",
        term("less-than", &[&numeral(1), "index"])
    );
    let cases = format!(
        "(#pt-lambda ((candidate #pt-nat)) {})",
        term("natural-order-decided", &[&numeral(1), "candidate"])
    );
    let late = witness(
        "#pt-nat",
        &format!(
            "(#pt-lambda ((candidate-witness #pt-nat)) (#pt-app {property} candidate-witness))"
        ),
        &numeral(5),
        &less(1, 5),
    );
    fixture(
        &term("has-minimum", &[&property]),
        &term(
            "minimum-exists-from-proposition-cases",
            &[&property, &cases, &late],
        ),
        true,
        &config(),
    );
    let refuter_type = format!("(#pt-pi ((smaller #pt-nat) (smaller-position {}) (smaller-property (#pt-app {property} smaller))) #pt-false)",term("less-than", &["smaller",&numeral(5)]));
    let fake = format!("(#pt-lambda ((smaller #pt-nat) (smaller-position {}) (smaller-property (#pt-app {property} smaller))) (#pt-app {} smaller-position))",term("less-than", &["smaller",&numeral(5)]),term("not-less-than-self", &[&numeral(5)]));
    let bad = term(
        "conjunction-introduce",
        &[
            &format!("(#pt-app {property} {})", numeral(5)),
            &refuter_type,
            &less(1, 5),
            &fake,
        ],
    );
    fixture(
        &term("minimum", &[&property, &numeral(5)]),
        &bad,
        false,
        &config(),
    );
}
#[test]
fn invariant_unit_property_roundtrips_through_finite_norm_search() {
    let property = format!(
        "(#pt-lambda ((value (#pt-use eisenstein ()))) {})",
        term("eisenstein-unit", &["value"])
    );
    let preservation = format!("(#pt-lambda ((source (#pt-use eisenstein ())) (target (#pt-use eisenstein ())) (equivalent {}) (source-evidence (#pt-app {property} source))) {})",term("eisenstein-equal", &["source","target"]),term("eisenstein-unit-congruent", &["source","target","equivalent","source-evidence"]));
    let one = term("eisenstein-one", &[]);
    let predicate = format!(
        "(#pt-lambda ((candidate-value (#pt-use eisenstein ()))) {})",
        term(
            "eisenstein-norm-property",
            &[&property, "candidate-value", &numeral(1)]
        )
    );
    let guard = term(
        "conjunction-introduce",
        &[
            &format!("(#pt-app {property} {one})"),
            &term("eisenstein-natural-norm", &[&one, &numeral(1)]),
            &term("eisenstein-one-unit", &[]),
            &refl(1),
        ],
    );
    let found = witness("(#pt-use eisenstein ())", &predicate, &one, &guard);
    let searched = term(
        "eisenstein-norm-existence-to-search",
        &[&property, &numeral(1), &preservation, &found],
    );
    fixture(
        &term("eisenstein-norm-property-exists", &[&property, &numeral(1)]),
        &term(
            "eisenstein-search-to-norm-existence",
            &[&property, &numeral(1), &searched],
        ),
        true,
        &config(),
    );
}
fn three_nonunit() -> String {
    let lambda = term("eisenstein-lambda", &[]);
    let three = Eisenstein::new(3, 0).source();
    format!(
        "(#pt-lambda ((three-unit {})) (#pt-app {} {}))",
        term("eisenstein-unit", &[&three]),
        term("eisenstein-lambda-not-unit", &[]),
        term(
            "eisenstein-divisor-of-unit-is-unit",
            &[
                &lambda,
                &three,
                "three-unit",
                &term("eisenstein-lambda-divides-three", &[])
            ]
        )
    )
}
#[test]
fn prime_divisors_exist_for_a_prime_and_a_composite() {
    for (value, nonzero, nonunit) in [
        (
            term("eisenstein-lambda", &[]),
            term("eisenstein-lambda-nonzero", &[]),
            term("eisenstein-lambda-not-unit", &[]),
        ),
        (
            Eisenstein::new(3, 0).source(),
            Eisenstein::new(3, 0).nonzero(),
            three_nonunit(),
        ),
    ] {
        let pred = format!(
            "(#pt-lambda ((candidate-prime (#pt-use eisenstein ()))) {})",
            term(
                "conjunction",
                &[
                    &term("eisenstein-prime", &["candidate-prime"]),
                    &term("eisenstein-divides", &["candidate-prime", &value])
                ]
            )
        );
        fixture(
            &exists("(#pt-use eisenstein ())", &pred),
            &term(
                "eisenstein-prime-divisor-exists",
                &[&value, &nonzero, &nonunit],
            ),
            true,
            &config(),
        );
    }
}
#[test]
fn actual_nonunit_factorization_strictly_decreases_norm() {
    let p = Eisenstein::new(3, 0);
    let a = Eisenstein::new(-1, 1);
    let b = Eisenstein::new(-2, -1);
    let factor = Eisenstein::new(1, 1);
    let lambda = term("eisenstein-lambda", &[]);
    let b_nonunit = format!(
        "(#pt-lambda ((cofactor-unit {})) (#pt-app {} {}))",
        term("eisenstein-unit", &[&b.source()]),
        term("eisenstein-lambda-not-unit", &[]),
        term(
            "eisenstein-divisor-of-unit-is-unit",
            &[
                &lambda,
                &b.source(),
                "cofactor-unit",
                &divides(a, b, factor)
            ]
        )
    );
    let product = term("eisenstein-multiply", &[&a.source(), &b.source()]);
    let equation = equivalence(&p.source(), p, &product, a.mul(b));
    fixture(
        &term("less-than", &[&numeral(3), &numeral(9)]),
        &term(
            "eisenstein-nonunit-factor-norm-decreases",
            &[
                &p.source(),
                &a.source(),
                &b.source(),
                &numeral(9),
                &numeral(3),
                &numeral(3),
                &p.norm_certificate(9),
                &a.norm_certificate(3),
                &b.norm_certificate(3),
                &p.nonzero(),
                &equation,
                &b_nonunit,
            ],
        ),
        true,
        &config(),
    );
}
#[test]
fn finite_search_rejects_representation_sensitive_property_transport() {
    let property = "(#pt-lambda ((value (#pt-use eisenstein ()))) (#pt-eq #pt-nat (#pt-project integer 0 (#pt-project eisenstein 0 value)) (#pt-numeral 2)))";
    let x = Eisenstein {
        real: Integer {
            positive: 2,
            negative: 1,
        },
        omega: Integer::new(0),
    };
    let fake = format!("(#pt-lambda ((source (#pt-use eisenstein ())) (target (#pt-use eisenstein ())) (equivalent {}) (source-evidence (#pt-app {property} source))) source-evidence)",term("eisenstein-equal", &["source","target"]));
    let predicate = format!(
        "(#pt-lambda ((candidate-value (#pt-use eisenstein ()))) {})",
        term(
            "eisenstein-norm-property",
            &[property, "candidate-value", &numeral(1)]
        )
    );
    let guard = term(
        "conjunction-introduce",
        &[
            &format!("(#pt-app {property} {})", x.source()),
            &term("eisenstein-natural-norm", &[&x.source(), &numeral(1)]),
            &refl(2),
            &x.norm_certificate(1),
        ],
    );
    let found = witness("(#pt-use eisenstein ())", &predicate, &x.source(), &guard);
    fixture(
        &term(
            "eisenstein-coordinate-property-search",
            &[property, &numeral(1)],
        ),
        &term(
            "eisenstein-norm-existence-to-search",
            &[property, &numeral(1), &fake, &found],
        ),
        false,
        &config(),
    );
}
#[test]
fn finite_search_coverage_rejects_an_undersized_coordinate_box() {
    use lim::check_theorem_details_from_path_with_config;
    use std::{fs, path::Path};
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("theorems/flt");
    let original = fs::read_to_string(root.join("eisenstein-finite-norm-search.lim")).unwrap();
    let start = original
        .find("(#math-definition eisenstein-coordinate-property-search")
        .unwrap();
    let mut depth = 0i32;
    let end = original[start..]
        .char_indices()
        .find_map(|(offset, c)| {
            if c == '(' {
                depth += 1;
            } else if c == ')' {
                depth -= 1;
            }
            (depth == 0).then_some(start + offset + 1)
        })
        .unwrap();
    let block = &original[start..end];
    assert_eq!(block.matches("(#pt-numeral 4)").count(), 2);
    let mut mutant = original.clone();
    mutant.replace_range(start..end, &block.replace("(#pt-numeral 4)", "#pt-zero"));
    // Aliases can span several lines after formatting. Resolve their path
    // tokens rather than assuming the alias and its target share a line.
    let references: Vec<String> = mutant
        .split_whitespace()
        .filter(|token| token.starts_with("./"))
        .map(str::to_owned)
        .collect();
    assert!(!references.is_empty());
    let mut source = mutant;
    for reference in references {
        source = source.replace(
            &reference,
            &format!("{}/{}", root.display(), &reference[2..]),
        );
    }
    let dir = std::env::temp_dir().join(format!("lim-flt-short-box-{}", std::process::id()));
    fs::create_dir(&dir).unwrap();
    let path = dir.join("mutant.lim");
    fs::write(&path, &source).unwrap();
    let result = check_theorem_details_from_path_with_config(
        &source,
        &path,
        &config(),
        "eisenstein-box-property-search",
    );
    fs::remove_dir_all(&dir).unwrap();
    let error = result.unwrap_err();
    assert_eq!(error.code, lim::DiagnosticCode::Proof, "{}", error.message);
    assert!(error.message.contains("mismatch"), "{}", error.message);
}
