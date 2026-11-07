//! Native regressions for finite Weierstrass affine-point operations.
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
fn curve(q: usize, c: [usize; 5]) -> String {
    format!(
        "(#pt-construct finite-weierstrass-curve () ({}) coefficients ({}))",
        n(q),
        c.into_iter()
            .map(|x| residue(q, x))
            .collect::<Vec<_>>()
            .join(" ")
    )
}
fn observe(actual: &str, expected: usize, valid: bool) {
    fixture(
        &eq(actual, &n(expected)),
        &format!("(#pt-refl #pt-nat {})", n(expected)),
        valid,
    );
}

fn fixture(statement: &str, proof: &str, valid: bool) {
    fixture_with_prelude("", statement, proof, valid);
}
fn fixture_with_prelude(prelude: &str, statement: &str, proof: &str, valid: bool) {
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let dir = std::env::temp_dir().join(format!(
        "lim-affine-negation-{}-{}",
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
    // Resolve only declarations from finite FLT modules and the small logic/natural
    // support set needed to construct checked residues and nonsingularity evidence.
    let modules = [
        "finite-affine-point-negation",
        "finite-weierstrass-neg-y",
        "finite-weierstrass-negation-formulas",
        "finite-weierstrass-negation-nonsingular",
        "finite-weierstrass-points",
        "finite-weierstrass-reduction",
        "finite-affine-point-identities",
        "finite-weierstrass-slopes",
        "finite-weierstrass-slope-certificates",
        "finite-weierstrass-line-evaluation",
        "finite-weierstrass-add-coordinates",
        "finite-residue-geometric-division",
        "finite-residue-inverses",
        "finite-prime-inverses",
        "finite-residue-extensional",
        "finite-affine-line-cubic-evaluation-polynomial",
        "finite-residue-defs",
        "finite-residue-negation",
        "finite-residue-operations",
        "finite-residue-semiring",
        "finite-residue-differences",
        "finite-residue-powers",
        "logical-connectives",
        "logic-exists",
        "equality",
        "natural-order",
        "natural-discrete-order",
        "natural-nonzero",
        "natural-addition",
        "natural-prime-two",
        "natural-prime-three",
        "../fermat_statement",
    ];
    for module in modules {
        let mp = root.join(format!("{module}.lim"));
        let Ok(text) = fs::read_to_string(&mp) else {
            continue;
        };
        for line in text.lines() {
            for prefix in ["(#theorem ", "(#math-definition ", "(#math-inductive "] {
                if let Some(tail) = line.strip_prefix(prefix) {
                    let name = tail.split_whitespace().next().unwrap();
                    if used.contains(name) {
                        source.push_str(&format!("(#alias {name} = {}::{name})\n", mp.display()));
                    }
                }
            }
        }
    }
    source.push_str(prelude);
    source.push_str(&format!("(#theorem observed-affine-negation (#universes) (#parameters) (#statement {statement}) (#proof {proof}))"));
    fs::write(&path, &source).unwrap();
    let mut config = CompileConfig::default();
    let d = ProofBudget::default();
    config
        .set_proof_budget(ProofBudget::new(d.work(), d.phase_bytes(), 1024 * 1024 * 1024).unwrap());
    let expected = format!(
        "{}::observed-affine-negation",
        path.canonicalize().unwrap().display()
    );
    let result = check_theorem_details_from_path_with_config(
        &source,
        &path,
        &config,
        "observed-affine-negation",
    );
    fs::remove_dir_all(dir).unwrap();
    if valid {
        let report = result.unwrap_or_else(|e| {
            panic!(
                "{}: {}",
                statement.chars().take(300).collect::<String>(),
                e.message
            )
        });
        assert_eq!(report.name, expected);
        assert!(report.foundations.is_empty());
    } else {
        let e = result.expect_err("incorrect affine point claim unexpectedly checked");
        assert_eq!(e.code, DiagnosticCode::Proof);
        assert!(e.message.contains("mismatch"), "{}", e.message);
    }
}

fn neg_y(q: usize, c: [usize; 5], x: usize, y: usize) -> String {
    app(
        "finite-weierstrass-neg-y",
        &[
            &n(q),
            &positive(q),
            &curve(q, c),
            &residue(q, x),
            &residue(q, y),
        ],
    )
}

#[test]
fn raw_negation_handles_a1_a3_and_characteristics_two_three() {
    for (q, c, x, y, z) in [
        (2, [0, 0, 1, 0, 0], 0, 0, 1),
        (3, [0, 0, 0, 0, 1], 0, 1, 2),
        (5, [1, 0, 1, 0, 2], 1, 1, 2),
    ] {
        observe(&val(&neg_y(q, c, x, y)), z, true);
        observe(&val(&neg_y(q, c, x, y)), (z + 1) % q, false);
    }
}

#[test]
fn raw_negation_accounts_for_both_linear_coefficients() {
    for (q, c, x, y, z) in [(7, [2, 0, 3, 0, 0], 1, 4, 5), (5, [0, 0, 4, 0, 0], 2, 1, 0)] {
        observe(&val(&neg_y(q, c, x, y)), z, true);
    }
}

fn nonsingular(q: usize, c: &str, x: usize, y: usize, dy: usize) -> String {
    nonsingular_with_derivative(q, c, x, y, false, dy)
}
fn nonsingular_with_derivative(
    q: usize,
    c: &str,
    x: usize,
    y: usize,
    use_x: bool,
    derivative: usize,
) -> String {
    assert!(derivative > 0 && derivative < q);
    let polynomial = app(
        "finite-weierstrass-polynomial",
        &[&n(q), &positive(q), c, &residue(q, x), &residue(q, y)],
    );
    let dx = app(
        "finite-weierstrass-derivative-x",
        &[&n(q), &positive(q), c, &residue(q, x), &residue(q, y)],
    );
    let derivative_y = app(
        "finite-weierstrass-derivative-y",
        &[&n(q), &positive(q), c, &residue(q, x), &residue(q, y)],
    );
    let ex = eq(&val(&dx), &n(0));
    let ey = eq(&val(&derivative_y), &n(0));
    let nx = format!("(#pt-pi ((denied {ex})) #pt-false)");
    let ny = format!("(#pt-pi ((denied {ey})) #pt-false)");
    let actual_value = val(if use_x { &dx } else { &derivative_y });
    let known = n(derivative);
    let path=format!("(#pt-app (#pt-use symmetry (0)) #pt-nat {actual_value} {known} (#pt-refl #pt-nat {known}))");
    let predicate="(#pt-lambda ((derivative-value #pt-nat)) (#pt-pi ((is-zero (#pt-eq #pt-nat derivative-value #pt-zero))) #pt-false))";
    let proof_y = format!(
        "(#pt-app (#pt-use substitution (0)) #pt-nat {predicate} {known} {actual_value} {path} {})",
        app("successor-not-zero", &[&n(derivative - 1)])
    );
    let disjunction = app("disjunction", &[&nx, &ny]);
    let dy_proof = app(
        if use_x {
            "disjunction-left"
        } else {
            "disjunction-right"
        },
        &[&nx, &ny, &proof_y],
    );
    app(
        "conjunction-introduce",
        &[
            &eq(&val(&polynomial), &n(0)),
            &disjunction,
            "(#pt-refl #pt-nat #pt-zero)",
            &dy_proof,
        ],
    )
}

#[test]
fn x_derivative_evidence_covers_zero_and_nonzero_y_derivatives() {
    for (q, cs, x, y, dx, expected_y) in [
        (2, [0, 0, 0, 0, 0], 1, 1, 1, 1),
        (3, [1, 0, 0, 0, 1], 1, 1, 1, 1),
        (5, [1, 0, 1, 0, 2], 1, 1, 3, 2),
    ] {
        let c = curve(q, cs);
        let h = nonsingular_with_derivative(q, &c, x, y, true, dx);
        let p = point(q, &c, x, y, &h);
        let prelude = named_point(q, &c, &p);
        let out = negate(q, &c, "(#pt-use checked-point ())");
        observe_with_prelude(
            &prelude,
            &observer("finite-affine-point-tag", q, &c, &out),
            1,
            true,
        );
        observe_with_prelude(
            &prelude,
            &val(&observer("finite-affine-point-y-or-zero", q, &c, &out)),
            expected_y,
            true,
        );
    }
}
fn point(q: usize, c: &str, x: usize, y: usize, proof: &str) -> String {
    format!(
        "(#pt-construct finite-affine-point () ({} {} {c}) coordinate ({} {} {proof}))",
        n(q),
        positive(q),
        residue(q, x),
        residue(q, y)
    )
}
fn negate(q: usize, c: &str, p: &str) -> String {
    app("finite-affine-point-negate", &[&n(q), &positive(q), c, p])
}
fn observer(name: &str, q: usize, c: &str, p: &str) -> String {
    app(name, &[&n(q), &positive(q), c, p])
}
fn named_point(q: usize, c: &str, p: &str) -> String {
    format!(
        "(#math-definition checked-point () {} {p})\n",
        app("finite-affine-point", &[&n(q), &positive(q), c])
    )
}
fn observe_with_prelude(prelude: &str, actual: &str, expected: usize, valid: bool) {
    fixture_with_prelude(
        prelude,
        &eq(actual, &n(expected)),
        &format!("(#pt-refl #pt-nat {})", n(expected)),
        valid,
    );
}

#[test]
fn actual_point_negation_preserves_infinity_and_coordinate_tag() {
    for (q, cs) in [(1, [0, 0, 0, 0, 0]), (5, [1, 0, 1, 0, 2])] {
        let c = curve(q, cs);
        let infinity = format!(
            "(#pt-construct finite-affine-point () ({} {} {}) infinity ())",
            n(q),
            positive(q),
            c
        );
        let neg = app(
            "finite-affine-point-negate",
            &[&n(q), &positive(q), &c, &infinity],
        );
        let tag = app("finite-affine-point-tag", &[&n(q), &positive(q), &c, &neg]);
        observe(&tag, 0, true);
        observe(&tag, 1, false);
    }
}

#[test]
fn point_negation_observers_match_known_nonsingular_coordinates() {
    for (q, cs, x, y, z, dy) in [
        (2, [0, 0, 1, 0, 0], 0, 0, 1, 1),
        (3, [0, 0, 0, 0, 1], 0, 1, 2, 2),
        (5, [1, 0, 1, 0, 2], 1, 1, 2, 4),
    ] {
        let c = curve(q, cs);
        let h = nonsingular(q, &c, x, y, dy);
        let p = point(q, &c, x, y, &h);
        let prelude = named_point(q, &c, &p);
        let out = negate(q, &c, "(#pt-use checked-point ())");
        observe_with_prelude(
            &prelude,
            &observer("finite-affine-point-tag", q, &c, &out),
            1,
            true,
        );
        observe_with_prelude(
            &prelude,
            &val(&observer("finite-affine-point-x-or-zero", q, &c, &out)),
            x,
            true,
        );
        observe_with_prelude(
            &prelude,
            &val(&observer("finite-affine-point-y-or-zero", q, &c, &out)),
            z,
            true,
        );
    }
}

#[test]
fn double_negation_and_observer_contract_are_checked_on_affine_points() {
    for (q, cs, x, y, dy) in [
        (2, [0, 0, 1, 0, 0], 0, 0, 1),
        (3, [0, 0, 0, 0, 1], 0, 1, 2),
        (5, [1, 0, 1, 0, 2], 1, 1, 4),
    ] {
        let c = curve(q, cs);
        let p = point(q, &c, x, y, &nonsingular(q, &c, x, y, dy));
        let prelude = named_point(q, &c, &p);
        let p = "(#pt-use checked-point ())";
        let twice = negate(q, &c, &negate(q, &c, p));
        let ty = app("finite-affine-point", &[&n(q), &positive(q), &c]);
        let statement = format!("(#pt-eq {ty} {twice} {p})");
        fixture_with_prelude(
            &prelude,
            &statement,
            &app(
                "finite-affine-point-negate-involutive",
                &[&n(q), &positive(q), &c, p],
            ),
            true,
        );
        observe_with_prelude(
            &prelude,
            &val(&observer("finite-affine-point-y-or-zero", q, &c, &twice)),
            y,
            true,
        );
    }
}

#[test]
fn false_or_foreign_nonsingularity_evidence_is_rejected() {
    let q = 3;
    let singular = curve(q, [0, 0, 0, 0, 0]);
    let fake = nonsingular(q, &singular, 0, 0, 1);
    let invalid = point(q, &singular, 0, 0, &fake);
    observe(
        &observer(
            "finite-affine-point-tag",
            q,
            &singular,
            &negate(q, &singular, &invalid),
        ),
        1,
        false,
    );
    let good = curve(q, [0, 0, 0, 0, 1]);
    let valid = nonsingular(q, &good, 0, 1, 2);
    let foreign = point(q, &singular, 0, 1, &valid);
    observe(
        &observer(
            "finite-affine-point-tag",
            q,
            &singular,
            &negate(q, &singular, &foreign),
        ),
        1,
        false,
    );
    let wrong_coordinates = point(q, &good, 1, 1, &valid);
    observe(
        &observer(
            "finite-affine-point-tag",
            q,
            &good,
            &negate(q, &good, &wrong_coordinates),
        ),
        1,
        false,
    );
}

fn slope(q: usize, c: &str, x1: usize, x2: usize, y1: usize, y2: usize) -> String {
    app(
        "finite-weierstrass-slope",
        &[
            &n(q),
            &positive(q),
            c,
            &residue(q, x1),
            &residue(q, x2),
            &residue(q, y1),
            &residue(q, y2),
        ],
    )
}

#[test]
fn slopes_compute_secant_tangent_and_vertical_cases() {
    for (q, cs, x1, x2, y1, y2, expected) in [
        (5, [0, 0, 0, 0, 2], 3, 4, 2, 1, 4),
        (5, [0, 0, 0, 0, 2], 3, 3, 2, 2, 3),
        (5, [0, 0, 0, 0, 2], 3, 3, 2, 3, 0),
        (2, [0, 0, 1, 0, 0], 0, 0, 0, 0, 0),
        (3, [0, 0, 0, 0, 1], 0, 0, 1, 1, 0),
        (3, [1, 0, 0, 0, 1], 1, 1, 1, 1, 0),
        (5, [1, 0, 1, 0, 2], 1, 1, 1, 1, 3),
    ] {
        observe(
            &val(&slope(q, &curve(q, cs), x1, x2, y1, y2)),
            expected,
            true,
        );
    }
    observe(
        &val(&slope(5, &curve(5, [0, 0, 0, 0, 2]), 3, 4, 2, 1)),
        3,
        false,
    );
}

fn zero_unequal_one(first: &str, second: &str) -> String {
    let equality = eq(first, second);
    format!("(#pt-lambda ((denied {equality})) (#pt-app {} (#pt-app (#pt-use symmetry (0)) #pt-nat {first} {second} denied)))", app("successor-not-zero",&[&n(0)]))
}

#[test]
fn secant_line_requires_the_correct_prime_and_distinct_x_evidence() {
    let q = 2;
    let c = curve(q, [0, 0, 1, 0, 0]);
    let x1 = residue(q, 0);
    let x2 = residue(q, 1);
    let y1 = residue(q, 0);
    let y2 = residue(q, 1);
    let distinct = zero_unequal_one(&val(&x1), &val(&x2));
    let s = slope(q, &c, 0, 1, 0, 1);
    let actual = val(&app(
        "finite-weierstrass-line-evaluate",
        &[&n(q), &positive(q), &x1, &y1, &s, &x2],
    ));
    let proof = app(
        "finite-weierstrass-secant-line-at-other",
        &[
            &n(q),
            &positive(q),
            "(#pt-use prime-two ())",
            &c,
            &x1,
            &x2,
            &y1,
            &y2,
            &distinct,
        ],
    );
    fixture(&eq(&actual, &n(1)), &proof, true);
    let foreign = app(
        "finite-weierstrass-secant-line-at-other",
        &[
            &n(q),
            &positive(q),
            "(#pt-use prime-three ())",
            &c,
            &x1,
            &x2,
            &y1,
            &y2,
            &distinct,
        ],
    );
    fixture(&eq(&actual, &n(1)), &foreign, false);
    let forged = app(
        "finite-weierstrass-secant-line-at-other",
        &[
            &n(q),
            &positive(q),
            "(#pt-use prime-two ())",
            &c,
            &x1,
            &x1,
            &y1,
            &y2,
            &distinct,
        ],
    );
    fixture(&eq(&actual, &n(1)), &forged, false);
}

#[test]
fn tangent_certificate_checks_the_curve_equations_and_nonvertical_case() {
    let q = 2;
    let c = curve(q, [0, 0, 1, 0, 0]);
    let x = residue(q, 0);
    let y = residue(q, 0);
    let inverse = neg_y(q, [0, 0, 1, 0, 0], 0, 0);
    let not_inverse = zero_unequal_one(&val(&y), &val(&inverse));
    let proof = app(
        "finite-weierstrass-tangent-denominator-nonzero",
        &[
            &n(q),
            &positive(q),
            "(#pt-use prime-two ())",
            &c,
            &x,
            &x,
            &y,
            &y,
            "(#pt-refl #pt-nat #pt-zero)",
            "(#pt-refl #pt-nat #pt-zero)",
            "(#pt-refl #pt-nat #pt-zero)",
            &not_inverse,
        ],
    );
    let dy = app(
        "finite-weierstrass-derivative-y",
        &[&n(q), &positive(q), &c, &x, &y],
    );
    let statement = app("finite-residue-nonzero", &[&n(q), &dy]);
    fixture(&statement, &proof, true);
    let singular = curve(q, [0, 0, 0, 0, 0]);
    let forged = app(
        "finite-weierstrass-tangent-denominator-nonzero",
        &[
            &n(q),
            &positive(q),
            "(#pt-use prime-two ())",
            &singular,
            &x,
            &x,
            &y,
            &y,
            "(#pt-refl #pt-nat #pt-zero)",
            "(#pt-refl #pt-nat #pt-zero)",
            "(#pt-refl #pt-nat #pt-zero)",
            &not_inverse,
        ],
    );
    fixture(&statement, &forged, false);
}

#[test]
fn actual_add_coordinates_and_cubic_identity_reject_changed_results() {
    let q = 5;
    let c = curve(q, [1, 0, 1, 0, 2]);
    for (function, expected) in [
        ("finite-weierstrass-add-x", 0),
        ("finite-weierstrass-add-y", 1),
    ] {
        let mut args = vec![n(q), positive(q), c.clone(), residue(q, 1), residue(q, 1)];
        if function.ends_with("-y") {
            args.push(residue(q, 1));
        }
        args.push(residue(q, 3));
        let refs: Vec<_> = args.iter().map(String::as_str).collect();
        observe(&val(&app(function, &refs)), expected, true);
        observe(&val(&app(function, &refs)), (expected + 1) % q, false);
    }
    // a1,a2,a3,a4,a6,evaluation-x,line-intercept,line-slope, in the
    // identity's explicit alphabetically sorted parameter order.
    let mut args = vec![n(3), positive(3)];
    args.extend([0, 0, 0, 0, 1, 0, 1, 1].map(|v| residue(3, v)));
    let refs: Vec<_> = args.iter().map(String::as_str).collect();
    let proof = app("finite-affine-line-cubic-evaluation-polynomial", &refs);
    fixture(&eq(&n(0), &n(0)), &proof, true);
    fixture(&eq(&n(0), &n(1)), &proof, false);
}
