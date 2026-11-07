//! Computed degree witnesses, highest coefficients and explicit domain controls.
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
        "lim-polynomial-degree-{}-{}",
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

#[test]
fn zero_and_nonzero_constants_have_distinct_degree_data() {
    for p in [poly(3, &[]), poly(3, &[0]), poly(3, &[0, 0, 0])] {
        observe(&natural(3, &p), 0, true);
        observe(&tag(3, &p), 0, true);
    }
    for q in [2, 3, 8] {
        let p = poly(q, &[1]);
        observe(&natural(q, &p), 0, true);
        observe(&tag(q, &p), 1, true);
    }
    observe(&tag(1, &poly(1, &[0, 0])), 0, true);
}

#[test]
fn trailing_zeros_and_internal_zeros_preserve_the_actual_highest_index() {
    for (values, d, leading) in [
        (&[0, 1, 0, 0][..], 1, 1),
        (&[2, 0, 1, 0][..], 2, 1),
        (&[1, 0, 0, 2, 0, 0][..], 3, 2),
    ] {
        let p = poly(3, values);
        observe(&natural(3, &p), d, true);
        let value = app(
            "ring-polynomial-degree-leading-coefficient",
            &[&carrier(3), &ring(3), &chooser(3), &p],
        );
        observe(&val(&value), leading, true);
    }
}

#[test]
fn cancellation_lowers_degree_and_can_produce_zero() {
    let a = poly(2, &[1, 1]);
    for (b, d, has) in [(poly(2, &[0, 1]), 0, 1), (a.clone(), 0, 0)] {
        let sum = app("ring-polynomial-add", &[&carrier(2), &ring(2), &a, &b]);
        observe(&natural(2, &sum), d, true);
        observe(&tag(2, &sum), has, true);
    }
    let p = poly(3, &[1, 0, 2]);
    let negated = app("ring-polynomial-negate", &[&carrier(3), &ring(3), &p]);
    observe(&natural(3, &negated), 2, true);
    let lead = app(
        "ring-polynomial-degree-leading-coefficient",
        &[&carrier(3), &ring(3), &chooser(3), &negated],
    );
    observe(&val(&lead), 1, true);
}

#[test]
fn product_coefficients_and_computed_degrees_are_actual_operations() {
    let a = poly(5, &[1, 2]);
    let b = poly(5, &[3, 4]);
    let product = app("ring-polynomial-multiply", &[&carrier(5), &ring(5), &a, &b]);
    for (index, value) in [3, 0, 3].into_iter().enumerate() {
        observe(&val(&coeff(5, &product, index)), value, true);
    }
    observe(&natural(5, &product), 2, true);
    let a = poly(5, &[2, 0, 1]);
    let square = app(
        "ring-polynomial-degree-power",
        &[&carrier(5), &ring(5), &a, &n(2)],
    );
    for (index, value) in [4, 0, 4, 0, 1].into_iter().enumerate() {
        observe(&val(&coeff(5, &square, index)), value, true);
    }
    observe(&natural(5, &square), 4, true);
}

#[test]
fn checked_domain_product_and_power_laws_accept_true_certificates() {
    let q = 3;
    let a = poly(q, &[1, 2]);
    let b = poly(q, &[2, 1]);
    let product = app("ring-polynomial-multiply", &[&carrier(q), &ring(q), &a, &b]);
    let proof = app(
        "ring-polynomial-degree-product",
        &[
            &carrier(q),
            &ring(q),
            &domain(q),
            &a,
            &b,
            &n(1),
            &n(1),
            &certificate(q, &a, 1, 2),
            &certificate(q, &b, 1, 1),
        ],
    );
    check("", &degree(q, &product, 2), &proof, true);
    let q = 2;
    let a = poly(q, &[1, 1]);
    let power = app(
        "ring-polynomial-degree-power",
        &[&carrier(q), &ring(q), &a, &n(3)],
    );
    let proof = app(
        "ring-polynomial-degree-power-law",
        &[
            &carrier(q),
            &ring(q),
            &domain(q),
            &a,
            &n(1),
            &n(3),
            &certificate(q, &a, 1, 1),
        ],
    );
    check("", &degree(q, &power, 3), &proof, true);
}

#[test]
fn constant_factors_and_zero_exponents_retain_degree_zero() {
    let q = 2;
    let a = poly(q, &[1]);
    let b = poly(q, &[1, 1]);
    let product = app("ring-polynomial-multiply", &[&carrier(q), &ring(q), &a, &b]);
    let proof = app(
        "ring-polynomial-degree-product",
        &[
            &carrier(q),
            &ring(q),
            &domain(q),
            &a,
            &b,
            &n(0),
            &n(1),
            &certificate(q, &a, 0, 1),
            &certificate(q, &b, 1, 1),
        ],
    );
    check("", &degree(q, &product, 1), &proof, true);
    let power = app(
        "ring-polynomial-degree-power",
        &[&carrier(q), &ring(q), &b, &n(0)],
    );
    observe(&natural(q, &power), 0, true);
    observe(&tag(q, &power), 1, true);
}

#[test]
fn composite_coefficients_do_not_gain_a_domain_assumption() {
    let a = poly(8, &[0, 2]);
    let b = poly(8, &[0, 4]);
    observe(&tag(8, &a), 1, true);
    observe(&tag(8, &b), 1, true);
    let product = app("ring-polynomial-multiply", &[&carrier(8), &ring(8), &a, &b]);
    observe(&tag(8, &product), 0, true);
    observe(&natural(8, &product), 0, true);
    let ty = app("ring-polynomial-domain-data", &[&carrier(8), &ring(8)]);
    let forged=format!("(#pt-construct ring-polynomial-domain-data () ({} {}) domain ((#pt-refl #pt-nat (#pt-numeral 0)) (#pt-refl #pt-nat (#pt-numeral 0))))",carrier(8),ring(8));
    let prelude = format!("(#math-definition forged-domain () {ty} {forged})");
    check(
        &prelude,
        &eq(&n(0), &n(0)),
        &format!("(#pt-refl #pt-nat {})", n(0)),
        false,
    );
}

#[test]
fn strict_leading_dominance_is_checked_with_formal_support() {
    let q = 3;
    let p = poly(q, &[1, 0, 1]);
    let other = poly(q, &[2, 1]);
    let sum = app("ring-polynomial-add", &[&carrier(q), &ring(q), &p, &other]);
    let support = app(
        "ring-polynomial-support-length",
        &[&carrier(q), &ring(q), &other],
    );
    let proof = app(
        "ring-polynomial-degree-add-left-dominant",
        &[
            &carrier(q),
            &ring(q),
            &p,
            &other,
            &n(2),
            &certificate(q, &p, 2, 1),
            &support,
        ],
    );
    check("", &degree(q, &sum, 2), &proof, true);
}

#[test]
fn rational_zero_decisions_preserve_noncanonical_representatives() {
    let ty = app("rational", &[]);
    let ring = app("rational-ring-structure", &[]);
    let decider = app("ring-polynomial-degree-rational-zero-decider", &[]);
    let p = list(&ty, &[ratio(1, 2), ratio(0, 1)]);
    let q = list(&ty, &[ratio(2, 4)]);
    for input in [&p, &q] {
        observe(
            &app(
                "ring-polynomial-degree-natural",
                &[&ty, &ring, &decider, input],
            ),
            0,
            true,
        );
        observe(
            &app(
                "ring-polynomial-degree-has-leading",
                &[&ty, &ring, &decider, input],
            ),
            1,
            true,
        );
    }
    let nil = list(&ty, &[]);
    let zero_tail = list(&ty, &[ratio(0, 1)]);
    let relation = app(
        "ring-polynomial-cons-congruent",
        &[
            &ty,
            &ring,
            &ratio(1, 2),
            &ratio(2, 4),
            &zero_tail,
            &nil,
            &ratio_proof(&ratio(1, 2), &ratio(2, 4)),
            &app("ring-polynomial-shift-nil", &[&ty, &ring]),
        ],
    );
    let proof = app(
        "ring-polynomial-degree-natural-congruent",
        &[&ty, &ring, &decider, &p, &q, &relation],
    );
    check(
        "",
        &eq(
            &app(
                "ring-polynomial-degree-natural",
                &[&ty, &ring, &decider, &p],
            ),
            &app(
                "ring-polynomial-degree-natural",
                &[&ty, &ring, &decider, &q],
            ),
        ),
        &proof,
        true,
    );
    let zero=format!("(#pt-construct rational () () fraction ((#pt-construct integer () () difference ({} {})) {} {}))",n(3),n(3),n(7),app("successor-not-zero",&[&n(6)]));
    let p = list(&ty, &[zero]);
    observe(
        &app(
            "ring-polynomial-degree-has-leading",
            &[&ty, &ring, &decider, &p],
        ),
        0,
        true,
    );
}

#[test]
fn actual_weierstrass_coefficients_have_the_proved_bounds() {
    let q = 2;
    let cs = [1, 0, 1, 1, 1].map(|x| residue(q, x));
    let mut args = vec![carrier(q), ring(q)];
    args.extend(cs);
    let references: Vec<_> = args.iter().map(String::as_str).collect();
    let cubic = app("weierstrass-coordinate-cubic", &references);
    observe(&natural(q, &cubic), 3, true);
    let mut proof_args = vec![carrier(q), ring(q), domain(q)];
    proof_args.extend(args[2..].iter().cloned());
    let references: Vec<_> = proof_args.iter().map(String::as_str).collect();
    let proof = app("ring-polynomial-degree-weierstrass-cubic", &references);
    check("", &degree(q, &cubic, 3), &proof, true);
    args[2] = residue(q, 0);
    let references: Vec<_> = args.iter().map(String::as_str).collect();
    let linear = app("weierstrass-coordinate-linear", &references);
    observe(&natural(q, &linear), 0, true);
    observe(&tag(q, &linear), 1, true);
}

#[test]
fn forged_degree_and_wrong_computed_results_fail_mathematically() {
    let p = poly(3, &[1]);
    check("", &degree(3, &p, 1), &certificate(3, &p, 1, 1), false);
    observe(&natural(3, &poly(3, &[0, 1, 0, 0])), 2, false);
    observe(&tag(3, &p), 0, false);
    let p = poly(3, &[]);
    let data = format!(
        "(#pt-construct ring-polynomial-degree-data () ({} {} {p}) zero ({}))",
        carrier(3),
        ring(3),
        app("ring-polynomial-reflexive", &[&carrier(3), &ring(3), &p])
    );
    let proof = app(
        "ring-polynomial-degree-positive-natural-bridge",
        &[
            &carrier(3),
            &ring(3),
            &p,
            &data,
            &n(1),
            &positive(1),
            &format!("(#pt-refl #pt-nat {})", n(0)),
        ],
    );
    check("", &degree(3, &p, 1), &proof, false);
}

#[test]
fn selecting_a_valid_target_cannot_skip_an_invalid_degree_record() {
    let p = poly(3, &[1, 1]);
    let data_ty = app("ring-polynomial-degree-data", &[&carrier(3), &ring(3), &p]);
    let value = format!(
        "(#pt-construct ring-polynomial-degree-data () ({} {} {p}) leading ({} {}))",
        carrier(3),
        ring(3),
        n(0),
        certificate(3, &p, 0, 1)
    );
    let prelude = format!("(#math-definition forged-degree () {data_ty} {value})");
    check(
        &prelude,
        &eq(&n(0), &n(0)),
        &format!("(#pt-refl #pt-nat {})", n(0)),
        false,
    );
}
