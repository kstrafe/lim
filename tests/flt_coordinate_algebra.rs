//! Actual ring/polynomial/quadratic computations and forged-certificate controls.
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
        "lim-coordinate-algebra-{}-{}",
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
fn element(ty: &str, a: &str, b: &str) -> String {
    format!("(#pt-construct quadratic-element () ({ty}) coordinates ({a} {b}))")
}
fn component(p: &str, i: usize) -> String {
    format!("(#pt-project quadratic-element {i} {p})")
}
fn norm(q: usize, alpha: usize, beta: usize, p: &str) -> String {
    app(
        "quadratic-norm",
        &[
            &carrier(q),
            &ring(q),
            &residue(q, alpha),
            &residue(q, beta),
            p,
        ],
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

#[test]
fn finite_ring_instances_include_composite_and_unit_moduli() {
    for q in [1, 2, 3, 8] {
        let one = app("ring-one", &[&carrier(q), &ring(q)]);
        observe(&val(&one), if q == 1 { 0 } else { 1 }, true);
        let zero = app("ring-zero", &[&carrier(q), &ring(q)]);
        let product = app("ring-multiply", &[&carrier(q), &ring(q), &zero, &one]);
        observe(&val(&product), 0, true);
    }
}
#[test]
fn polynomial_products_coefficients_and_trailing_zeros_are_formal() {
    let q = 5;
    let a = poly(q, &[1, 2]);
    let b = poly(q, &[3, 4]);
    let product = app("ring-polynomial-multiply", &[&carrier(q), &ring(q), &a, &b]);
    for (i, v) in [(0, 3), (1, 0), (2, 3), (9, 0)] {
        observe(&val(&coeff(q, &product, i)), v, true);
    }
    let nil = poly(q, &[]);
    let z = poly(q, &[0]);
    let t = poly(q, &[2, 0]);
    let u = poly(q, &[2]);
    let zproof = app("ring-polynomial-shift-nil", &[&carrier(q), &ring(q)]);
    let tproof = app(
        "ring-polynomial-cons-congruent",
        &[
            &carrier(q),
            &ring(q),
            &residue(q, 2),
            &residue(q, 2),
            &z,
            &nil,
            "(#pt-refl #pt-nat (#pt-numeral 2))",
            &zproof,
        ],
    );
    let proof = app(
        "ring-polynomial-cons-congruent",
        &[
            &carrier(q),
            &ring(q),
            &residue(q, 1),
            &residue(q, 1),
            &t,
            &u,
            "(#pt-refl #pt-nat (#pt-numeral 1))",
            &tproof,
        ],
    );
    check(
        "",
        &app(
            "ring-polynomial-equal",
            &[&carrier(q), &ring(q), &poly(q, &[1, 2, 0]), &a],
        ),
        &proof,
        true,
    );
}
#[test]
fn equality_is_not_only_evaluation_at_finite_field_points() {
    let q = 2;
    let p = poly(q, &[0, 1, 1]);
    for x in [0, 1] {
        let v = app(
            "ring-polynomial-evaluate",
            &[&carrier(q), &ring(q), &p, &residue(q, x)],
        );
        observe(&val(&v), 0, true);
    }
    observe(&val(&coeff(q, &p, 1)), 1, true);
    let statement = app(
        "ring-polynomial-equal",
        &[&carrier(q), &ring(q), &p, &poly(q, &[])],
    );
    check(
        "",
        &statement,
        &app("ring-polynomial-reflexive", &[&carrier(q), &ring(q), &p]),
        false,
    );
}
#[test]
fn rational_coefficients_preserve_noncanonical_equivalence() {
    let ty = "(#pt-use rational ())";
    let s = "(#pt-use rational-ring-structure ())";
    let nil = list(ty, &[]);
    let a = ratio(1, 2);
    let b = ratio(2, 4);
    let statement = app(
        "ring-polynomial-equal",
        &[ty, s, &list(ty, &[a.clone()]), &list(ty, &[b.clone()])],
    );
    let proof = app(
        "ring-polynomial-cons-congruent",
        &[
            ty,
            s,
            &a,
            &b,
            &nil,
            &nil,
            &ratio_proof(&a, &b),
            &app("ring-polynomial-reflexive", &[ty, s, &nil]),
        ],
    );
    check("", &statement, &proof, true);
    let b = ratio(1, 3);
    let statement = app(
        "ring-polynomial-equal",
        &[ty, s, &list(ty, &[a.clone()]), &list(ty, &[b.clone()])],
    );
    let proof = app(
        "ring-polynomial-cons-congruent",
        &[
            ty,
            s,
            &a,
            &b,
            &nil,
            &nil,
            &ratio_proof(&a, &b),
            &app("ring-polynomial-reflexive", &[ty, s, &nil]),
        ],
    );
    check("", &statement, &proof, false);
}
#[test]
fn support_bound_covers_every_offset_but_not_nonzero_coefficients() {
    let q = 3;
    let p = poly(q, &[1, 2, 0]);
    let proof = app(
        "ring-polynomial-finite-support",
        &[&carrier(q), &ring(q), &p, &n(4)],
    );
    check("", &eq(&val(&coeff(q, &p, 7)), &n(0)), &proof, true);
    observe(&val(&coeff(q, &p, 1)), 0, false);
}
#[test]
fn quadratic_relation_conjugation_and_zero_norm_compute() {
    let q = 3;
    let ty = carrier(q);
    let y = element(&ty, &residue(q, 0), &residue(q, 1));
    let square = app(
        "quadratic-multiply",
        &[&ty, &ring(q), &residue(q, 1), &residue(q, 2), &y, &y],
    );
    for i in [0, 1] {
        observe(&val(&component(&square, i)), 2, true);
    }
    let p = element(&ty, &residue(q, 1), &residue(q, 1));
    let z = element(&ty, &residue(q, 2), &residue(q, 1));
    observe(&val(&norm(q, 1, 2, &p)), 1, true);
    observe(&val(&norm(q, 1, 2, &z)), 0, true);
    observe(&val(&norm(q, 1, 2, &z)), 1, false);
    let conjugate = app("quadratic-conjugate", &[&ty, &ring(q), &residue(q, 1), &p]);
    let product = app(
        "quadratic-multiply",
        &[
            &ty,
            &ring(q),
            &residue(q, 1),
            &residue(q, 2),
            &p,
            &conjugate,
        ],
    );
    observe(&val(&component(&product, 0)), 1, true);
    observe(&val(&component(&product, 1)), 0, true);
}
#[test]
fn norm_multiplicativity_is_for_the_actual_product() {
    let q = 3;
    let ty = carrier(q);
    let p = element(&ty, &residue(q, 1), &residue(q, 1));
    let z = element(&ty, &residue(q, 2), &residue(q, 1));
    let product = app(
        "quadratic-multiply",
        &[&ty, &ring(q), &residue(q, 1), &residue(q, 2), &p, &z],
    );
    let lhs = norm(q, 1, 2, &product);
    let rhs = app(
        "ring-multiply",
        &[&ty, &ring(q), &norm(q, 1, 2, &p), &norm(q, 1, 2, &z)],
    );
    let proof = app(
        "quadratic-norm-multiply",
        &[&ty, &ring(q), &residue(q, 1), &residue(q, 2), &p, &z],
    );
    check(
        "",
        &app("ring-equal", &[&ty, &ring(q), &lhs, &rhs]),
        &proof,
        true,
    );
    check(
        "",
        &app("ring-equal", &[&ty, &ring(q), &lhs, &residue(q, 1)]),
        &proof,
        false,
    );
}
#[test]
fn weierstrass_norm_uses_the_actual_cubic_polynomial() {
    let q = 2;
    let ty = carrier(q);
    let pt = app("finite-list", &[&ty]);
    let coords = element(&pt, &poly(q, &[1]), &poly(q, &[1]));
    let parameters = [
        ty.clone(),
        ring(q),
        residue(q, 0),
        residue(q, 0),
        residue(q, 1),
        residue(q, 0),
        residue(q, 0),
        coords,
    ];
    let refs: Vec<_> = parameters.iter().map(String::as_str).collect();
    let norm = app("weierstrass-coordinate-norm", &refs);
    for (i, v) in [(0, 0), (1, 0), (2, 0), (3, 1)] {
        observe(&val(&coeff(q, &norm, i)), v, true);
    }
    let coords = element(&pt, &poly(q, &[1, 1]), &poly(q, &[]));
    let mut parameters = parameters;
    *parameters.last_mut().unwrap() = coords;
    let refs: Vec<_> = parameters.iter().map(String::as_str).collect();
    let norm = app("weierstrass-coordinate-norm", &refs);
    for (i, v) in [(0, 1), (1, 0), (2, 1)] {
        observe(&val(&coeff(q, &norm, i)), v, true);
    }
}
#[test]
fn rational_norm_is_an_actual_fraction_computation() {
    let ty = "(#pt-use rational ())";
    let s = "(#pt-use rational-ring-structure ())";
    let p = element(ty, &ratio(1, 2), &ratio(1, 1));
    let norm = app("quadratic-norm", &[ty, s, &ratio(0, 1), &ratio(1, 1), &p]);
    let prelude = format!("(#math-definition checked-norm () {ty} {norm})\n");
    let value = "(#pt-use checked-norm ())";
    let expected = ratio(-3, 4);
    check(
        &prelude,
        &app("rational-equal", &[value, &expected]),
        &ratio_proof(value, &expected),
        true,
    );
    let expected = ratio(-2, 4);
    check(
        &prelude,
        &app("rational-equal", &[value, &expected]),
        &ratio_proof(value, &expected),
        false,
    );
}
#[test]
fn corrupted_operations_and_equality_laws_are_rejected_even_if_unused() {
    let q = 2;
    let ty = carrier(q);
    let good = ring(q);
    for field in [2, 5] {
        let mut fields: Vec<_> = (0..21)
            .map(|i| format!("(#pt-project commutative-ring {i} {good})"))
            .collect();
        fields[field] = format!(
            "(#pt-lambda ((bad-left {ty}) (bad-right {ty})) {})",
            if field == 2 {
                residue(q, 0)
            } else {
                "#pt-false".to_owned()
            }
        );
        let bad = format!(
            "(#pt-construct commutative-ring () ({ty}) structure ({}))",
            fields.join(" ")
        );
        let prelude = format!(
            "(#math-definition corrupted-ring () {} {bad})",
            app("commutative-ring", &[&ty])
        );
        check(
            &prelude,
            &eq(&n(0), &n(0)),
            "(#pt-refl #pt-nat (#pt-numeral 0))",
            false,
        );
    }
}
