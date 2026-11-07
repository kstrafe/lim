//! Computed monic division, actual quotient correspondence and forged-evidence controls.
use lim::{
    check_theorem_details_from_path_with_config, CompileConfig, DiagnosticCode, ProofBudget,
};
use std::{
    collections::HashSet,
    fs,
    path::Path,
    sync::atomic::{AtomicUsize, Ordering},
};

fn n(x: usize) -> String {
    format!("(#pt-numeral {x})")
}

fn app(name: &str, args: &[&str]) -> String {
    args.iter().fold(format!("(#pt-use {name} ())"), |f, a| {
        format!("(#pt-app {f} {a})")
    })
}

fn eq(a: &str, b: &str) -> String {
    format!("(#pt-eq #pt-nat {a} {b})")
}

fn positive(q: usize) -> String {
    app("zero-less-successor", &[&n(q - 1)])
}

fn bound(x: usize, q: usize) -> String {
    assert!(x < q);
    format!("(#pt-construct exists (0) (#pt-nat (#pt-lambda ((gap #pt-nat)) (#pt-eq #pt-nat {} (#pt-app (#pt-use add ()) (#pt-succ {}) gap)))) introduce ({} (#pt-refl #pt-nat {})))", n(q), n(x), n(q-x-1), n(q))
}

fn residue(q: usize, x: usize) -> String {
    format!(
        "(#pt-construct finite-residue () ({}) representative ({} {}))",
        n(q),
        n(x),
        bound(x, q)
    )
}

fn val(r: &str) -> String {
    format!("(#pt-project finite-residue 0 {r})")
}

const MODULES: &[&str] = &[
    "quadratic-division-data",
    "quadratic-division-equation",
    "quadratic-division-local-equation",
    "quadratic-division-scalar-laws",
    "quadratic-division-step-equation",
    "quadratic-quotient-coefficient-add-constant-identity",
    "quadratic-quotient-coefficient-add-linear-identity",
    "quadratic-quotient-coefficient-map",
    "quadratic-quotient-coefficient-multiply-constant-identity",
    "quadratic-quotient-coefficient-multiply-linear-identity",
    "quadratic-quotient-congruence",
    "quadratic-quotient-correspondence",
    "quadratic-quotient-divisibility",
    "quadratic-quotient-divisor-zero-constant-identity",
    "quadratic-quotient-divisor-zero-linear-identity",
    "quadratic-quotient-equivalence",
    "quadratic-quotient-evaluation",
    "quadratic-quotient-isomorphism",
    "quadratic-quotient-kernel",
    "quadratic-quotient-linear-evaluation-constant-identity",
    "quadratic-quotient-linear-evaluation-linear-identity",
    "quadratic-quotient-linear-operations",
    "quadratic-quotient-relation",
    "quadratic-quotient-remainder-correspondence",
    "quadratic-quotient-remainder-evaluation",
    "quadratic-quotient-ring-structure",
    "quadratic-quotient-zero-remainder",
    "ring-evaluation-addition",
    "ring-evaluation-congruence",
    "ring-evaluation-data",
    "ring-evaluation-morphism",
    "ring-evaluation-multiplication",
    "ring-evaluation-negation",
    "ring-evaluation-scaling",
    "ring-evaluation-zero-coefficients",
    "weierstrass-coordinate-quotient",
    "commutative-ring-cancellation",
    "commutative-ring-data",
    "commutative-ring-elementary-laws",
    "commutative-ring-sign-laws",
    "finite-residue-ring-structure",
    "quadratic-algebra-additive-laws",
    "quadratic-algebra-basis-conjugation",
    "quadratic-algebra-data",
    "quadratic-algebra-left-matrix",
    "quadratic-algebra-multiplication-laws",
    "quadratic-algebra-norm-laws",
    "quadratic-algebra-ring-structure",
    "quadratic-associative-constant-identity",
    "quadratic-associative-linear-identity",
    "quadratic-basic-scalar-identities",
    "quadratic-commutative-constant-identity",
    "quadratic-commutative-linear-identity",
    "quadratic-distributive-constant-identity",
    "quadratic-distributive-linear-identity",
    "quadratic-left-matrix-0-identity",
    "quadratic-left-matrix-1-identity",
    "quadratic-left-matrix-2-identity",
    "quadratic-left-matrix-3-identity",
    "quadratic-norm-determinant-identity",
    "rational-ring-structure",
    "ring-matrix2-data",
    "ring-matrix2-determinant-laws",
    "ring-matrix2-determinant-product-identity",
    "ring-polynomial-additive-laws",
    "ring-polynomial-coefficient-laws",
    "ring-polynomial-congruence",
    "ring-polynomial-data",
    "ring-polynomial-equivalence",
    "ring-polynomial-finite-support",
    "ring-polynomial-horner-distributivity",
    "ring-polynomial-horner-second-argument",
    "ring-polynomial-multiplication-laws",
    "ring-polynomial-multiplicative-identities",
    "ring-polynomial-scalar-laws",
    "ring-polynomial-shift-laws",
    "ring-polynomial-structure",
    "weierstrass-coordinate-norm-formula",
    "weierstrass-coordinate-normal-form",
    "finite-residue-defs",
    "finite-list-defs",
    "rational-defs",
    "rational-equality",
    "integer-defs",
    "natural-discrete-order",
    "natural-nonzero",
    "logic-exists",
    "logical-connectives",
    "../fermat_statement",
];

fn check(prelude: &str, statement: &str, proof: &str, good: bool) {
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let dir = std::env::temp_dir().join(format!(
        "lim-quadratic-quotient-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir(&dir).unwrap();
    let path = dir.join("fixture.lim");
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("theorems/flt");
    let terms = format!("{prelude} {statement} {proof}");
    let used: HashSet<_> = terms
        .split(|c: char| c.is_whitespace() || c == '(' || c == ')')
        .collect();
    let mut source = String::new();
    for module in MODULES {
        let module_path = root.join(format!("{module}.lim"));
        let text = fs::read_to_string(&module_path).unwrap();
        for line in text.lines() {
            for prefix in ["(#theorem ", "(#math-definition ", "(#math-inductive "] {
                if let Some(tail) = line.strip_prefix(prefix) {
                    let name = tail.split_whitespace().next().unwrap();
                    if used.contains(name) {
                        source.push_str(&format!(
                            "(#alias {name} = {}::{name})\n",
                            module_path.display()
                        ));
                    }
                }
            }
        }
    }
    source.push_str(prelude);
    source.push_str(&format!("(#theorem observed-coordinate-algebra (#universes) (#parameters) (#statement {statement}) (#proof {proof}))"));
    fs::write(&path, &source).unwrap();
    let mut config = CompileConfig::default();
    let d = ProofBudget::default();
    let total = if used.contains("rational-ring-structure") {
        2 * 1024 * 1024 * 1024
    } else {
        1024 * 1024 * 1024
    };
    config.set_proof_budget(ProofBudget::new(d.work(), d.phase_bytes(), total).unwrap());
    let expected = format!(
        "{}::observed-coordinate-algebra",
        path.canonicalize().unwrap().display()
    );
    let result = check_theorem_details_from_path_with_config(
        &source,
        &path,
        &config,
        "observed-coordinate-algebra",
    );
    fs::remove_dir_all(dir).unwrap();
    if good {
        let report = result.unwrap_or_else(|e| {
            panic!(
                "{}: {}",
                statement.chars().take(260).collect::<String>(),
                e.message
            )
        });
        assert_eq!(report.name, expected);
        assert!(report.foundations.is_empty());
    } else {
        let e = result.expect_err("incorrect algebra claim unexpectedly checked");
        assert_eq!(e.code, DiagnosticCode::Proof);
        assert!(e.message.contains("mismatch"), "{}", e.message);
    }
}
fn observe(actual: &str, expected: usize, good: bool) {
    check(
        "",
        &eq(actual, &n(expected)),
        &format!("(#pt-refl #pt-nat {})", n(expected)),
        good,
    );
}
fn carrier(q: usize) -> String {
    app("finite-residue", &[&n(q)])
}
fn ring(q: usize) -> String {
    app("finite-residue-ring", &[&n(q), &positive(q)])
}
fn list(ty: &str, values: &[String]) -> String {
    values.iter().rev().fold(
        format!("(#pt-construct finite-list () ({ty}) nil ())"),
        |tail, head| format!("(#pt-construct finite-list () ({ty}) cons ({head} {tail}))"),
    )
}
fn poly(q: usize, values: &[usize]) -> String {
    list(
        &carrier(q),
        &values.iter().map(|&v| residue(q, v)).collect::<Vec<_>>(),
    )
}
fn coeff(q: usize, p: &str, index: usize) -> String {
    app(
        "ring-polynomial-coefficient",
        &[&carrier(q), &ring(q), p, &n(index)],
    )
}
fn component(p: &str, i: usize) -> String {
    format!("(#pt-project quadratic-element {i} {p})")
}
fn ratio(numerator: isize, denominator: usize) -> String {
    assert!(denominator > 0);
    format!("(#pt-construct rational () () fraction ((#pt-construct integer () () difference ({} {})) {} {}))",n(numerator.max(0) as usize),n((-numerator).max(0) as usize),n(denominator),app("successor-not-zero",&[&n(denominator-1)]))
}
fn ratio_proof(a: &str, b: &str) -> String {
    let numerator = |p: &str| format!("(#pt-project rational 0 {p})");
    let denominator = |p: &str| format!("(#pt-project rational 1 {p})");
    let left = app(
        "integer-multiply",
        &[
            &numerator(a),
            &app("integer-of-natural", &[&denominator(b)]),
        ],
    );
    let right = app(
        "integer-multiply",
        &[
            &numerator(b),
            &app("integer-of-natural", &[&denominator(a)]),
        ],
    );
    format!(
        "(#pt-refl #pt-nat {})",
        app(
            "add",
            &[
                &format!("(#pt-project integer 0 {left})"),
                &format!("(#pt-project integer 1 {right})")
            ]
        )
    )
}

fn division(q: usize, alpha: usize, beta: usize, p: &str) -> String {
    app(
        "quadratic-division-compute",
        &[
            &carrier(q),
            &ring(q),
            &residue(q, alpha),
            &residue(q, beta),
            p,
        ],
    )
}
fn remainder(q: usize, alpha: usize, beta: usize, p: &str) -> String {
    app(
        "quadratic-division-remainder",
        &[
            &carrier(q),
            &ring(q),
            &residue(q, alpha),
            &residue(q, beta),
            p,
        ],
    )
}
fn quotient_relation(q: usize, alpha: usize, beta: usize, p: &str, other: &str) -> String {
    app(
        "quadratic-quotient-equal",
        &[
            &carrier(q),
            &ring(q),
            &residue(q, alpha),
            &residue(q, beta),
            p,
            other,
        ],
    )
}
fn pair_proof(left: &str, right: &str, expected: [usize; 2]) -> String {
    app(
        "conjunction-introduce",
        &[
            &eq(&val(&component(left, 0)), &val(&component(right, 0))),
            &eq(&val(&component(left, 1)), &val(&component(right, 1))),
            &format!("(#pt-refl #pt-nat {})", n(expected[0])),
            &format!("(#pt-refl #pt-nat {})", n(expected[1])),
        ],
    )
}
fn division_case(
    q: usize,
    alpha: usize,
    beta: usize,
    power: usize,
    quotient: &[usize],
    expected: [usize; 2],
) {
    let mut coefficients = vec![0; power + 1];
    coefficients[power] = 1;
    let input = poly(q, &coefficients);
    let data = division(q, alpha, beta, &input);
    let polynomial_quotient = format!("(#pt-project quadratic-division-data 0 {data})");
    for index in 0..=quotient.len() {
        observe(
            &val(&coeff(q, &polynomial_quotient, index)),
            quotient.get(index).copied().unwrap_or(0),
            true,
        );
    }
    for (index, value) in expected.into_iter().enumerate() {
        let actual = format!("(#pt-project quadratic-division-data {} {data})", index + 1);
        observe(&val(&actual), value, true);
    }
}

#[test]
fn monic_division_computes_quotients_and_remainders_modulo_three() {
    division_case(3, 1, 2, 2, &[1], [2, 2]);
    division_case(3, 1, 2, 3, &[2, 1], [1, 0]);
    division_case(3, 1, 2, 4, &[0, 2, 1], [0, 1]);
}

#[test]
fn monic_division_works_over_composite_coefficient_rings() {
    division_case(8, 3, 2, 2, &[1], [2, 5]);
    division_case(8, 3, 2, 3, &[5, 1], [2, 3]);
    division_case(8, 3, 2, 4, &[3, 5, 1], [6, 1]);
}

#[test]
fn monic_division_preserves_characteristic_two() {
    division_case(2, 1, 1, 2, &[1], [1, 1]);
    division_case(2, 1, 1, 3, &[1, 1], [1, 0]);
}

#[test]
fn zero_constants_linear_terms_and_trailing_zeros_reduce_correctly() {
    for (input, expected) in [
        (&[][..], [0, 0]),
        (&[2][..], [2, 0]),
        (&[2, 1][..], [2, 1]),
        (&[2, 1, 0, 0][..], [2, 1]),
    ] {
        let p = poly(3, input);
        let r = remainder(3, 1, 2, &p);
        for (i, v) in expected.into_iter().enumerate() {
            observe(&val(&component(&r, i)), v, true);
        }
    }
    let unit_zero = remainder(1, 0, 0, &poly(1, &[0, 0, 0]));
    observe(&val(&component(&unit_zero, 0)), 0, true);
    observe(&val(&component(&unit_zero, 1)), 0, true);
}

#[test]
fn computed_remainders_construct_actual_quotient_equivalence() {
    let q = 3;
    let p = poly(q, &[0, 0, 1]);
    let other = poly(q, &[2, 2]);
    let rp = remainder(q, 1, 2, &p);
    let rq = remainder(q, 1, 2, &other);
    let proof = app(
        "quadratic-quotient-remainders-equal",
        &[
            &carrier(q),
            &ring(q),
            &residue(q, 1),
            &residue(q, 2),
            &p,
            &other,
            &pair_proof(&rp, &rq, [2, 2]),
        ],
    );
    check("", &quotient_relation(q, 1, 2, &p, &other), &proof, true);
    let bad = poly(q, &[2, 1]);
    let rb = remainder(q, 1, 2, &bad);
    let forged = app(
        "quadratic-quotient-remainders-equal",
        &[
            &carrier(q),
            &ring(q),
            &residue(q, 1),
            &residue(q, 2),
            &p,
            &bad,
            &pair_proof(&rp, &rb, [2, 2]),
        ],
    );
    check("", &quotient_relation(q, 1, 2, &p, &bad), &forged, false);
}

#[test]
fn false_signs_and_incorrect_quotient_coefficients_are_rejected() {
    let data = division(3, 1, 2, &poly(3, &[0, 0, 1]));
    observe(
        &val(&format!("(#pt-project quadratic-division-data 1 {data})")),
        1,
        false,
    );
    observe(
        &val(&format!("(#pt-project quadratic-division-data 2 {data})")),
        1,
        false,
    );
    let q = format!("(#pt-project quadratic-division-data 0 {data})");
    observe(&val(&coeff(3, &q, 0)), 2, false);
}

#[test]
fn quotient_does_not_confuse_polynomial_functions_with_formal_coefficients() {
    // Y^2+Y vanishes at both points of F2, but modulo Y^2+Y+1 its
    // formal remainder is one. Finite point evaluation cannot prove this zero.
    let p = poly(2, &[0, 1, 1]);
    for x in [0, 1] {
        let value = app(
            "ring-polynomial-evaluate",
            &[&carrier(2), &ring(2), &p, &residue(2, x)],
        );
        observe(&val(&value), 0, true);
    }
    let r = remainder(2, 1, 1, &p);
    observe(&val(&component(&r, 0)), 1, true);
    observe(&val(&component(&r, 0)), 0, false);
}

#[test]
fn forged_divisor_witness_is_rejected() {
    let p = poly(3, &[0, 0, 1]);
    let d = app(
        "quadratic-division-divisor",
        &[&carrier(3), &ring(3), &residue(3, 1), &residue(3, 2)],
    );
    let ty = app("finite-list", &[&carrier(3)]);
    let multiple = app(
        "ring-polynomial-multiply",
        &[&carrier(3), &ring(3), &d, "candidate-quotient"],
    );
    let predicate = format!(
        "(#pt-lambda ((candidate-quotient {ty})) {})",
        app(
            "ring-polynomial-equal",
            &[&carrier(3), &ring(3), &p, &multiple]
        )
    );
    let proof = format!(
        "(#pt-construct exists (0) ({ty} {predicate}) introduce ({} {}))",
        poly(3, &[1]),
        app("ring-polynomial-reflexive", &[&carrier(3), &ring(3), &p])
    );
    let statement = app(
        "quadratic-quotient-divides",
        &[&carrier(3), &ring(3), &residue(3, 1), &residue(3, 2), &p],
    );
    check("", &statement, &proof, false);
}

#[test]
fn rational_remainders_retain_noncanonical_fraction_equivalence() {
    let ty = app("rational", &[]);
    let r = app("rational-ring-structure", &[]);
    let zero = ratio(0, 1);
    let p = list(&ty, &[zero.clone(), zero, ratio(1, 1)]);
    let data = app(
        "quadratic-division-compute",
        &[&ty, &r, &ratio(3, 2), &ratio(5, 3), &p],
    );
    let constant = format!("(#pt-project quadratic-division-data 1 {data})");
    let linear = format!("(#pt-project quadratic-division-data 2 {data})");
    for (actual, expected) in [(constant, ratio(10, 6)), (linear, ratio(-6, 4))] {
        check(
            "",
            &app("rational-equal", &[&actual, &expected]),
            &ratio_proof(&actual, &expected),
            true,
        );
    }
}

#[test]
fn selected_target_cannot_skip_a_false_earlier_theorem() {
    let bad = "(#theorem invalid-quotient-claim (#universes) (#parameters) (#statement (#pt-eq #pt-nat (#pt-numeral 0) (#pt-numeral 1))) (#proof (#pt-refl #pt-nat (#pt-numeral 0))))";
    check(
        bad,
        &eq(&n(0), &n(0)),
        &format!("(#pt-refl #pt-nat {})", n(0)),
        false,
    );
}
