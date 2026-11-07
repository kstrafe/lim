//! Actual norm degrees, exact branch boundaries, zero cases and forged-evidence controls.
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
    "coordinate-norm-degree-nilpotent-counterexample",
    "coordinate-norm-degree-polynomial-domain",
    "coordinate-norm-degree-nonzero-norm",
    "coordinate-norm-degree-certified-formula",
    "coordinate-norm-degree-computed-formula",
    "coordinate-norm-degree-contradictions",
    "coordinate-norm-degree-coordinate-domain",
    "coordinate-norm-degree-cubic-at-least-three-identity",
    "coordinate-norm-degree-cubic-successor-identity",
    "coordinate-norm-degree-data-uniqueness",
    "coordinate-norm-degree-dichotomy",
    "coordinate-norm-degree-double-successor-identity",
    "coordinate-norm-degree-exclusion",
    "coordinate-norm-degree-exhaustive",
    "coordinate-norm-degree-formula",
    "coordinate-norm-degree-high-branch",
    "coordinate-norm-degree-high-cross-identity",
    "coordinate-norm-degree-high-cubic-identity",
    "coordinate-norm-degree-index-gaps",
    "coordinate-norm-degree-integer-exclusion",
    "coordinate-norm-degree-low-branch",
    "coordinate-norm-degree-low-cross-finish-identity",
    "coordinate-norm-degree-low-cross-reorder-identity",
    "coordinate-norm-degree-low-square-identity",
    "coordinate-norm-degree-maximum",
    "coordinate-norm-degree-maximum-formula",
    "coordinate-norm-degree-maximum-order",
    "coordinate-norm-degree-nonzero-exclusion",
    "coordinate-norm-degree-regroup",
    "coordinate-norm-degree-source-obstruction",
    "coordinate-norm-degree-support-gaps",
    "coordinate-norm-degree-term-bounds",
    "coordinate-norm-degree-zero-cases",
    "coordinate-norm-degree-zero-equations",
    "coordinate-norm-degree-zero-kernel",
    "ring-polynomial-degree-X-powers",
    "ring-polynomial-degree-certificates",
    "ring-polynomial-degree-computation",
    "ring-polynomial-degree-computed-congruence",
    "ring-polynomial-degree-data",
    "ring-polynomial-degree-dominance",
    "ring-polynomial-degree-existence",
    "ring-polynomial-degree-leading",
    "ring-polynomial-degree-positive-bridge",
    "ring-polynomial-degree-powers",
    "ring-polynomial-degree-product",
    "ring-polynomial-degree-product-constant-head",
    "ring-polynomial-degree-product-indices",
    "ring-polynomial-degree-rational-instance",
    "ring-polynomial-degree-residue-instance",
    "ring-polynomial-degree-uniqueness",
    "ring-polynomial-degree-weierstrass",
    "ring-polynomial-domain-data",
    "ring-polynomial-domain-lift",
    "ring-polynomial-domain-residue-instance",
    "ring-polynomial-product-top",
    "ring-polynomial-support-data",
    "ring-polynomial-support-further-operations",
    "ring-polynomial-support-operations",
    "ring-polynomial-support-strict-index",
    "ring-polynomial-support-transport",
    "natural-prime-two",
    "natural-prime-three",
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
        "lim-norm-degree-{}-{}",
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
    let total = if used.contains("rational-ring-structure")
        || used.contains("ring-polynomial-degree-rational-zero-decider")
    {
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

fn chooser(q: usize) -> String {
    app(
        "ring-polynomial-degree-residue-zero-decider",
        &[&n(q), &positive(q)],
    )
}
fn natural(q: usize, p: &str) -> String {
    app(
        "ring-polynomial-degree-natural",
        &[&carrier(q), &ring(q), &chooser(q), p],
    )
}
fn tag(q: usize, p: &str) -> String {
    app(
        "ring-polynomial-degree-has-leading",
        &[&carrier(q), &ring(q), &chooser(q), p],
    )
}
fn degree(q: usize, p: &str, d: usize) -> String {
    app(
        "ring-polynomial-degree-witness",
        &[&carrier(q), &ring(q), p, &n(d)],
    )
}
fn certificate(q: usize, p: &str, d: usize, leading: usize) -> String {
    assert!(leading > 0);
    let zero = app("ring-zero", &[&carrier(q), &ring(q)]);
    let ceq = app(
        "ring-equal",
        &[&carrier(q), &ring(q), &coeff(q, p, d), &zero],
    );
    let nz = format!("(#pt-pi ((zero-leading {ceq})) #pt-false)");
    let upper = app(
        "ring-polynomial-support-from",
        &[&carrier(q), &ring(q), p, &n(d + 1)],
    );
    app(
        "conjunction-introduce",
        &[
            &nz,
            &upper,
            &app("successor-not-zero", &[&n(leading - 1)]),
            &app(
                "ring-polynomial-support-length",
                &[&carrier(q), &ring(q), p],
            ),
        ],
    )
}
fn domain(q: usize) -> String {
    assert!(q == 2 || q == 3);
    let prime = app(if q == 2 { "prime-two" } else { "prime-three" }, &[]);
    app(
        "ring-polynomial-domain-prime-residue",
        &[&n(q), &positive(q), &prime],
    )
}

fn apply(name: &str, args: &[String]) -> String {
    app(name, &args.iter().map(String::as_str).collect::<Vec<_>>())
}
fn parameters(m: usize, a: [usize; 5]) -> Vec<String> {
    let mut args = vec![carrier(m), ring(m)];
    args.extend(a.map(|v| residue(m, v)));
    args
}
fn domain_parameters(m: usize, a: [usize; 5]) -> Vec<String> {
    let mut args = parameters(m, a);
    args.insert(2, domain(m));
    args
}
fn norm(m: usize, a: [usize; 5], p: &str, q: &str) -> String {
    let mut args = parameters(m, a);
    args.extend([p.to_owned(), q.to_owned()]);
    apply("coordinate-norm-degree-value", &args)
}
fn data(m: usize, p: &str) -> String {
    app(
        "ring-polynomial-degree-compute",
        &[&carrier(m), &ring(m), &chooser(m), p],
    )
}
fn formula_data(m: usize, a: [usize; 5], p: &str, q: &str) -> String {
    let mut args = domain_parameters(m, a);
    args.extend([p.to_owned(), q.to_owned(), data(m, p), data(m, q)]);
    apply("coordinate-norm-degree-from-inputs", &args)
}
fn formula_index(m: usize, a: [usize; 5], p: &str, q: &str) -> String {
    app(
        "ring-polynomial-degree-data-natural",
        &[
            &carrier(m),
            &ring(m),
            &norm(m, a, p, q),
            &formula_data(m, a, p, q),
        ],
    )
}
fn formula_tag(m: usize, a: [usize; 5], p: &str, q: &str) -> String {
    app(
        "ring-polynomial-degree-data-has-leading",
        &[
            &carrier(m),
            &ring(m),
            &norm(m, a, p, q),
            &formula_data(m, a, p, q),
        ],
    )
}
fn agreement(m: usize, a: [usize; 5], p: &str, q: &str) {
    let actual = norm(m, a, p, q);
    let left = eq(&natural(m, &actual), &formula_index(m, a, p, q));
    let right = eq(&tag(m, &actual), &formula_tag(m, a, p, q));
    let statement = app("conjunction", &[&left, &right]);
    let mut args = domain_parameters(m, a);
    args.extend([chooser(m), p.to_owned(), q.to_owned()]);
    check(
        "",
        &statement,
        &apply("coordinate-norm-degree-computed-formula", &args),
        true,
    );
}
fn branch(m: usize, a: [usize; 5], p: &[usize], q: &[usize], high: bool, gap: usize, good: bool) {
    let pd = p.len() - 1;
    let qd = q.len() - 1;
    let pv = poly(m, p);
    let qv = poly(m, q);
    let mut args = domain_parameters(m, a);
    let position = if high { pd } else { qd + 1 };
    args.extend([
        pv.clone(),
        qv.clone(),
        n(pd),
        n(qd),
        n(gap),
        certificate(m, &pv, pd, p[pd]),
        certificate(m, &qv, qd, q[qd]),
        format!("(#pt-refl #pt-nat {})", n(position)),
    ]);
    let expected = if high { 2 * pd } else { 2 * qd + 3 };
    let name = if high {
        "coordinate-norm-degree-square-dominant"
    } else {
        "coordinate-norm-degree-cubic-dominant"
    };
    check(
        "",
        &degree(m, &norm(m, a, &pv, &qv), expected),
        &apply(name, &args),
        good,
    );
}
fn zero_polynomial_proof(m: usize, count: usize) -> String {
    let nil = poly(m, &[]);
    let mut p = nil.clone();
    let mut evidence = app("ring-polynomial-reflexive", &[&carrier(m), &ring(m), &nil]);
    for _ in 0..count {
        let next = format!(
            "(#pt-construct finite-list () ({}) cons ({} {p}))",
            carrier(m),
            residue(m, 0)
        );
        let singleton = poly(m, &[0]);
        let constructor = app(
            "ring-polynomial-cons-congruent",
            &[
                &carrier(m),
                &ring(m),
                &residue(m, 0),
                &residue(m, 0),
                &p,
                &nil,
                &format!("(#pt-refl #pt-nat {})", n(0)),
                &evidence,
            ],
        );
        evidence = app(
            "ring-polynomial-transitive",
            &[
                &carrier(m),
                &ring(m),
                &next,
                &singleton,
                &nil,
                &constructor,
                &app("ring-polynomial-shift-nil", &[&carrier(m), &ring(m)]),
            ],
        );
        p = next;
    }
    evidence
}

#[test]
fn all_zero_and_single_nonzero_inputs_keep_degree_zero_distinct() {
    let m = 2;
    let a = [1; 5];
    for (p, q, expected, has) in [
        (&[][..], &[][..], 0, 0),
        (&[1][..], &[][..], 0, 1),
        (&[][..], &[1][..], 3, 1),
    ] {
        let p = poly(m, p);
        let q = poly(m, q);
        observe(&formula_index(m, a, &p, &q), expected, true);
        observe(&formula_tag(m, a, &p, &q), has, true);
        let actual = norm(m, a, &p, &q);
        observe(&natural(m, &actual), expected, true);
        observe(&tag(m, &actual), has, true);
        agreement(m, a, &p, &q);
    }
}

#[test]
fn both_dominance_equality_boundaries_hold_in_characteristic_two() {
    let m = 2;
    let a = [1; 5];
    for (p, expected, coefficients, high) in [
        (&[1, 1][..], 3, &[1, 1, 1, 1][..], false),
        (&[1, 0, 1][..], 4, &[1, 0, 0, 0, 1][..], true),
    ] {
        let pv = poly(m, p);
        let qv = poly(m, &[1]);
        let actual = norm(m, a, &pv, &qv);
        observe(&formula_index(m, a, &pv, &qv), expected, true);
        observe(&formula_tag(m, a, &pv, &qv), 1, true);
        observe(&natural(m, &actual), expected, true);
        for (i, v) in coefficients.iter().copied().enumerate() {
            observe(&val(&coeff(m, &actual, i)), v, true);
        }
        branch(m, a, p, &[1], high, 0, true);
    }
}

#[test]
fn nonzero_degree_gaps_cover_each_dominance_direction() {
    for (p, q, a, expected, gap, high, top) in [
        (&[1, 2, 0, 1][..], &[1][..], [2, 1, 1, 2, 1], 6, 1, true, 1),
        (&[1][..], &[1, 1][..], [1; 5], 5, 2, false, 2),
    ] {
        let m = 3;
        let pv = poly(m, p);
        let qv = poly(m, q);
        let actual = norm(m, a, &pv, &qv);
        observe(&formula_index(m, a, &pv, &qv), expected, true);
        observe(&formula_tag(m, a, &pv, &qv), 1, true);
        observe(&natural(m, &actual), expected, true);
        observe(&val(&coeff(m, &actual, expected)), top, true);
        observe(&val(&coeff(m, &actual, expected + 1)), 0, true);
        agreement(m, a, &pv, &qv);
        branch(m, a, p, q, high, gap, true);
    }
}

#[test]
fn norm_coefficients_and_degree_are_computed_from_the_actual_polynomial() {
    let m = 5;
    let actual = norm(m, [3, 4, 2, 1, 3], &poly(m, &[1, 0, 1]), &poly(m, &[2]));
    for (i, v) in [0, 0, 2, 0, 1].into_iter().enumerate() {
        observe(&val(&coeff(m, &actual, i)), v, true);
    }
    observe(&natural(m, &actual), 4, true);
    observe(&tag(m, &actual), 1, true);
}

#[test]
fn source_exclusions_apply_to_zero_constants_and_general_coordinates() {
    for (m, p, q, a) in [
        (2, &[][..], &[][..], [1; 5]),
        (2, &[1][..], &[1][..], [1; 5]),
        (2, &[1, 0, 1][..], &[1][..], [1; 5]),
        (3, &[1, 2, 0, 1][..], &[1][..], [2, 1, 1, 2, 1]),
    ] {
        let p = poly(m, p);
        let q = poly(m, q);
        let actual = norm(m, a, &p, &q);
        let statement = format!(
            "(#pt-pi ((claimed-degree {})) #pt-false)",
            degree(m, &actual, 1)
        );
        let mut args = domain_parameters(m, a);
        args.extend([p, q]);
        check(
            "",
            &statement,
            &apply("coordinate-norm-degree-not-one", &args),
            true,
        );
    }
    let m = 2;
    let a = [1; 5];
    let p = poly(m, &[1, 0, 1]);
    let q = poly(m, &[1]);
    let actual = norm(m, a, &p, &q);
    let statement = format!(
        "(#pt-pi ((natural-degree-equation {})) #pt-false)",
        eq(&natural(m, &actual), &n(1))
    );
    let mut args = domain_parameters(m, a);
    args.extend([chooser(m), p, q]);
    check(
        "",
        &statement,
        &apply("coordinate-norm-degree-natural-not-one", &args),
        true,
    );
}

#[test]
fn actual_recursive_maximum_covers_zero_and_order_boundaries() {
    for (a, b, expected) in [
        (0, 0, 0),
        (0, 3, 3),
        (4, 0, 4),
        (2, 3, 3),
        (4, 3, 4),
        (7, 7, 7),
        (9, 12, 12),
    ] {
        observe(
            &app("coordinate-norm-degree-maximum", &[&n(a), &n(b)]),
            expected,
            true,
        );
    }
    observe(
        &app("coordinate-norm-degree-maximum", &[&n(2), &n(3)]),
        2,
        false,
    );
}

#[test]
fn zero_norm_kernel_retains_noncanonical_zero_polynomials() {
    let m = 2;
    let a = [1; 5];
    let p = poly(m, &[0, 0]);
    let q = poly(m, &[0, 0, 0]);
    let nil = poly(m, &[]);
    let mut equation_args = parameters(m, a);
    equation_args.extend([
        p.clone(),
        q.clone(),
        zero_polynomial_proof(m, 2),
        zero_polynomial_proof(m, 3),
    ]);
    let zero_norm = apply("coordinate-norm-degree-both-zero", &equation_args);
    let mut args = domain_parameters(m, a);
    args.extend([chooser(m), p.clone(), q.clone(), zero_norm]);
    let statement = app(
        "conjunction",
        &[
            &app("ring-polynomial-equal", &[&carrier(m), &ring(m), &p, &nil]),
            &app("ring-polynomial-equal", &[&carrier(m), &ring(m), &q, &nil]),
        ],
    );
    check(
        "",
        &statement,
        &apply("coordinate-norm-degree-zero-kernel", &args),
        true,
    );
}

#[test]
fn constructed_coordinate_domain_has_actual_nonzero_products() {
    let m = 2;
    let a = [1; 5];
    let one = poly(m, &[1]);
    let nil = poly(m, &[]);
    let polyty = app("finite-list", &[&carrier(m)]);
    let qty = app("quadratic-element", &[&polyty]);
    let x = format!("(#pt-construct quadratic-element () ({polyty}) coordinates ({one} {nil}))");
    let y = format!("(#pt-construct quadratic-element () ({polyty}) coordinates ({nil} {one}))");
    let r = apply("weierstrass-coordinate-ring", &parameters(m, a));
    let z = app("ring-zero", &[&qty, &r]);
    let xzero = app("ring-equal", &[&qty, &r, &x, &z]);
    let yzero = app("ring-equal", &[&qty, &r, &y, &z]);
    let poly_nonzero = app(
        "ring-polynomial-degree-nonzero",
        &[
            &carrier(m),
            &ring(m),
            &one,
            &n(0),
            &certificate(m, &one, 0, 1),
        ],
    );
    let xnz=format!("(#pt-lambda ((zero-coordinate {xzero})) (#pt-app {poly_nonzero} (#pt-project conjunction 0 zero-coordinate)))");
    let ynz=format!("(#pt-lambda ((zero-coordinate {yzero})) (#pt-app {poly_nonzero} (#pt-project conjunction 1 zero-coordinate)))");
    let product = app("ring-multiply", &[&qty, &r, &x, &y]);
    let statement = format!(
        "(#pt-pi ((zero-product {})) #pt-false)",
        app("ring-equal", &[&qty, &r, &product, &z])
    );
    let mut args = domain_parameters(m, a);
    args.extend([x, y, xnz, ynz]);
    check(
        "",
        &statement,
        &apply("coordinate-norm-degree-coordinate-domain-product", &args),
        true,
    );
}

#[test]
fn degree_one_can_occur_over_a_ring_with_zero_divisors() {
    // In Z/8, p=1,q=4,alpha=X gives N=1-4X, because q^2=0.
    // This is why the source obstruction requires a checked domain.
    let m = 8;
    let ty = carrier(m);
    let r = ring(m);
    let one = app("ring-one", &[&ty, &r]);
    let zero = app("ring-zero", &[&ty, &r]);
    let p = list(&ty, &[one.clone()]);
    let q = list(&ty, &[residue(m, 4)]);
    let actual = app(
        "coordinate-norm-degree-value",
        &[&ty, &r, &one, &zero, &zero, &zero, &zero, &p, &q],
    );
    observe(&val(&coeff(8, &actual, 0)), 1, true);
    observe(&val(&coeff(8, &actual, 1)), 4, true);
    let certificate = app(
        "coordinate-norm-degree-nilpotent-counterexample",
        &[
            &ty,
            &r,
            &residue(m, 4),
            &app("successor-not-zero", &[&n(3)]),
            &format!("(#pt-refl #pt-nat {})", n(0)),
        ],
    );
    check("", &degree(m, &actual, 1), &certificate, true);
    let agrees = app(
        "ring-polynomial-degree-computed-agrees",
        &[&ty, &r, &chooser(m), &actual, &n(1), &certificate],
    );
    check("", &eq(&natural(m, &actual), &n(1)), &agrees, true);
    let nonzero = app(
        "ring-polynomial-degree-nonzero",
        &[&ty, &r, &actual, &n(1), &certificate],
    );
    let tag_proof = app(
        "ring-polynomial-degree-data-nonzero-tag",
        &[&ty, &r, &actual, &data(m, &actual), &nonzero],
    );
    check("", &eq(&tag(m, &actual), &n(1)), &tag_proof, true);
}

#[test]
fn rational_constants_keep_actual_fraction_equivalence_and_nonzero_tag() {
    let ty = app("rational", &[]);
    let r = app("rational-ring-structure", &[]);
    let chooser = app("ring-polynomial-degree-rational-zero-decider", &[]);
    let domain = app("ring-polynomial-domain-rational", &[]);
    let p = list(&ty, &[ratio(2, 4)]);
    let q = list(&ty, &[]);
    let mut args = vec![ty.clone(), r.clone()];
    args.extend((0..5).map(|_| ratio(0, 1)));
    args.extend([p.clone(), q.clone()]);
    let actual = apply("coordinate-norm-degree-value", &args);
    observe(
        &app(
            "ring-polynomial-degree-natural",
            &[&ty, &r, &chooser, &actual],
        ),
        0,
        true,
    );
    observe(
        &app(
            "ring-polynomial-degree-has-leading",
            &[&ty, &r, &chooser, &actual],
        ),
        1,
        true,
    );
    let leading = app("ring-polynomial-coefficient", &[&ty, &r, &actual, &n(0)]);
    check(
        "",
        &app("rational-equal", &[&leading, &ratio(1, 4)]),
        &ratio_proof(&leading, &ratio(1, 4)),
        true,
    );
    args.insert(2, domain);
    let statement = format!(
        "(#pt-pi ((degree-one {})) #pt-false)",
        app("ring-polynomial-degree-witness", &[&ty, &r, &actual, &n(1)])
    );
    check(
        "",
        &statement,
        &apply("coordinate-norm-degree-not-one", &args),
        true,
    );
}

#[test]
fn false_gaps_and_forged_degree_results_are_mathematical_mismatches() {
    branch(2, [1; 5], &[1], &[1], false, 0, false);
    branch(2, [1; 5], &[1, 0, 1], &[1], true, 1, false);
    observe(
        &formula_tag(2, [1; 5], &poly(2, &[]), &poly(2, &[])),
        1,
        false,
    );
    observe(
        &formula_index(2, [1; 5], &poly(2, &[1, 0, 1]), &poly(2, &[1])),
        3,
        false,
    );
}

#[test]
fn an_unused_forged_coordinate_domain_is_still_checked() {
    let m = 2;
    let a = [1; 5];
    let polyty = app("finite-list", &[&carrier(m)]);
    let qty = app("quadratic-element", &[&polyty]);
    let r = apply("weierstrass-coordinate-ring", &parameters(m, a));
    let ty = app("ring-polynomial-domain-data", &[&qty, &r]);
    let value=format!("(#pt-construct ring-polynomial-domain-data () ({qty} {r}) domain ((#pt-refl #pt-nat (#pt-numeral 0)) (#pt-refl #pt-nat (#pt-numeral 0))))");
    let prelude = format!("(#math-definition forged-coordinate-domain () {ty} {value})");
    check(
        &prelude,
        &eq(&n(0), &n(0)),
        &format!("(#pt-refl #pt-nat {})", n(0)),
        false,
    );
}
