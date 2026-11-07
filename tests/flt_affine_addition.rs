//! Native numerical/adversarial regressions for actual affine-point addition.
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

fn point(q: usize, c: &str, x: usize, y: usize, proof: &str) -> String {
    format!(
        "(#pt-construct finite-affine-point () ({} {} {c}) coordinate ({} {} {proof}))",
        n(q),
        positive(q),
        residue(q, x),
        residue(q, y)
    )
}

fn check(prelude: &str, statement: &str, proof: &str, valid: bool) {
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let dir = std::env::temp_dir().join(format!(
        "lim-affine-addition-{}-{}",
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
        "finite-affine-point-addition",
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
    source.push_str(&format!("(#theorem observed-affine-addition (#universes) (#parameters) (#statement {statement}) (#proof {proof}))"));
    fs::write(&path, &source).unwrap();
    let mut config = CompileConfig::default();
    let d = ProofBudget::default();
    config.set_proof_budget(
        ProofBudget::new(d.work(), d.phase_bytes(), 2 * 1024 * 1024 * 1024).unwrap(),
    );
    let expected = format!(
        "{}::observed-affine-addition",
        path.canonicalize().unwrap().display()
    );
    let result = check_theorem_details_from_path_with_config(
        &source,
        &path,
        &config,
        "observed-affine-addition",
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
        let e = result.expect_err("incorrect affine addition claim unexpectedly checked");
        assert_eq!(e.code, DiagnosticCode::Proof);
        assert!(e.message.contains("mismatch"), "{}", e.message);
    }
}

fn infinity(q: usize, c: &str) -> String {
    format!(
        "(#pt-construct finite-affine-point () ({} {} {c}) infinity ())",
        n(q),
        positive(q)
    )
}
fn named(name: &str, q: usize, c: &str, p: &str) -> String {
    format!(
        "(#math-definition {name} () {} {p})\n",
        app("finite-affine-point", &[&n(q), &positive(q), c])
    )
}
fn input(q: usize, c: &str, p: Option<(usize, usize, bool, usize)>) -> String {
    match p {
        None => infinity(q, c),
        Some((x, y, use_x, d)) => point(
            q,
            c,
            x,
            y,
            &if use_x {
                nonsingular_with_derivative(q, c, x, y, true, d)
            } else {
                nonsingular(q, c, x, y, d)
            },
        ),
    }
}
fn observe(q: usize, c: &str, point: &str, expected: Option<(usize, usize)>) -> (String, String) {
    let (tag, x, y) = expected.map_or((0, 0, 0), |(x, y)| (1, x, y));
    let observer = |name| app(name, &[&n(q), &positive(q), c, point]);
    let tag_eq = eq(&observer("finite-affine-point-tag"), &n(tag));
    let x_eq = eq(&val(&observer("finite-affine-point-x-or-zero")), &n(x));
    let y_eq = eq(&val(&observer("finite-affine-point-y-or-zero")), &n(y));
    let xy = app("conjunction", &[&x_eq, &y_eq]);
    let xyproof = app(
        "conjunction-introduce",
        &[
            &x_eq,
            &y_eq,
            &format!("(#pt-refl #pt-nat {})", n(x)),
            &format!("(#pt-refl #pt-nat {})", n(y)),
        ],
    );
    (
        app("conjunction", &[&tag_eq, &xy]),
        app(
            "conjunction-introduce",
            &[
                &tag_eq,
                &xy,
                &format!("(#pt-refl #pt-nat {})", n(tag)),
                &xyproof,
            ],
        ),
    )
}
fn case(
    q: usize,
    cs: [usize; 5],
    a: Option<(usize, usize, bool, usize)>,
    b: Option<(usize, usize, bool, usize)>,
    expected: Option<(usize, usize)>,
    valid: bool,
) {
    let c = curve(q, cs);
    let a = input(q, &c, a);
    let b = input(q, &c, b);
    case_terms(
        q,
        &c,
        &a,
        &b,
        if q == 2 {
            "(#pt-use prime-two ())"
        } else {
            "(#pt-use prime-three ())"
        },
        expected,
        valid,
    );
}
fn case_terms(
    q: usize,
    c: &str,
    a: &str,
    b: &str,
    prime: &str,
    expected: Option<(usize, usize)>,
    valid: bool,
) {
    let sum = app(
        "finite-affine-point-add",
        &[
            &n(q),
            &positive(q),
            prime,
            c,
            "(#pt-use first-point ())",
            "(#pt-use second-point ())",
        ],
    );
    let prelude = named("first-point", q, c, a)
        + &named("second-point", q, c, b)
        + &named("checked-result", q, c, &sum);
    let (statement, proof) = observe(q, c, "(#pt-use checked-result ())", expected);
    check(&prelude, &statement, &proof, valid);
}
const TWO: [usize; 5] = [0, 0, 1, 0, 0];
const THREE: [usize; 5] = [1, 0, 0, 0, 1];
const P: Option<(usize, usize, bool, usize)> = Some((0, 0, false, 1));
const Q: Option<(usize, usize, bool, usize)> = Some((0, 1, false, 1));
const A: Option<(usize, usize, bool, usize)> = Some((0, 1, false, 2));
const B: Option<(usize, usize, bool, usize)> = Some((1, 1, true, 1));
const C: Option<(usize, usize, bool, usize)> = Some((2, 0, false, 2));

#[test]
fn characteristic_two_tangent_and_inverse_pair() {
    case(2, TWO, P, P, Some((0, 1)), true);
    case(2, TWO, P, Q, None, true);
    case(2, TWO, Q, Q, Some((0, 0)), true);
}
#[test]
fn secant_third_x_distinct_from_both_sources() {
    case(3, THREE, A, B, Some((2, 0)), true);
}
#[test]
fn tangent_third_x_distinct_from_both_sources() {
    case(3, THREE, A, A, Some((2, 1)), true);
}
#[test]
fn coincident_third_x_transports_each_input_witness() {
    case(3, THREE, A, C, Some((0, 2)), true);
    case(3, THREE, C, A, Some((0, 2)), true);
}
#[test]
fn self_inverse_point_with_only_x_derivative_nonzero() {
    case(3, THREE, B, B, None, true);
}
#[test]
fn infinity_is_a_two_sided_identity() {
    case(3, THREE, None, A, Some((0, 1)), true);
    case(3, THREE, A, None, Some((0, 1)), true);
    case(3, THREE, None, None, None, true);
}
#[test]
fn changed_sum_tag_and_coordinate_are_rejected() {
    case(2, TWO, P, Q, Some((0, 1)), false);
    case(3, THREE, A, B, Some((2, 1)), false);
}
#[test]
fn wrong_prime_singular_and_foreign_witnesses_are_rejected() {
    let c = curve(2, TWO);
    let p = input(2, &c, P);
    case_terms(
        2,
        &c,
        &p,
        &p,
        "(#pt-use prime-three ())",
        Some((0, 1)),
        false,
    );
    let singular = curve(3, [0, 0, 0, 0, 0]);
    let bad = input(3, &singular, Some((0, 0, false, 1)));
    case_terms(
        3,
        &singular,
        &bad,
        &bad,
        "(#pt-use prime-three ())",
        None,
        false,
    );
    let singular = curve(2, [0, 0, 0, 0, 0]);
    let foreign = point(2, &singular, 0, 0, &nonsingular(2, &c, 0, 0, 1));
    case_terms(
        2,
        &singular,
        &foreign,
        &foreign,
        "(#pt-use prime-two ())",
        None,
        false,
    );
}
