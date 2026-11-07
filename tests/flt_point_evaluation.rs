//! Computed root factors and actual coordinate-kernel/quotient regressions.
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

const MODULES: &[&str] = &[
    "polynomial-root-division-data",
    "polynomial-root-local-equation",
    "polynomial-root-step-equation",
    "polynomial-root-division-equation",
    "polynomial-root-remainder-evaluation",
    "polynomial-root-division-evaluation",
    "polynomial-root-factor",
    "polynomial-root-identity-morphism",
    "polynomial-root-evaluation-bridge",
    "polynomial-root-evaluation-laws",
    "polynomial-root-evaluation-generators",
    "polynomial-root-evaluation-morphism",
    "point-evaluation-map-negate",
    "point-evaluation-kernel",
    "polynomial-root-principal-member",
    "polynomial-root-kernel-is-principal",
    "polynomial-root-vanishes-if-principal",
    "point-evaluation-quotient-divides-zero",
    "point-evaluation-quotient-congruence",
    "point-evaluation-quotient-morphism",
    "point-evaluation-composition",
    "point-evaluation-quadratic-morphism",
    "point-evaluation-quadratic-formula",
    "point-evaluation-constant-linear-product",
    "point-evaluation-linear-decomposition",
    "point-evaluation-embedded-multiple",
    "polynomial-root-evaluation-negation",
    "point-evaluation-coordinate-morphism",
    "point-evaluation-coordinate-formula",
    "point-evaluation-coordinate-generators",
    "point-evaluation-coordinate-ideal-contained",
    "point-evaluation-coordinate-constant-root",
    "point-evaluation-coordinate-constant-contained",
    "point-evaluation-coordinate-kernel-contained",
    "point-evaluation-coordinate-kernel-is-point-ideal",
    "point-evaluation-naturality",
    "point-evaluation-coordinate-source-equation",
    "point-evaluation-image-ring",
    "point-evaluation-image-map-laws",
    "point-evaluation-image-morphism",
    "point-evaluation-section-laws",
    "point-evaluation-section-morphism",
    "point-evaluation-kernel-difference",
    "point-evaluation-coordinate-section",
    "point-evaluation-coordinate-quotient-relation",
    "point-evaluation-coordinate-quotient-isomorphism",
    "commutative-ring-data",
    "ring-evaluation-morphism",
    "ring-evaluation-data",
    "quadratic-division-data",
    "quadratic-algebra-ring-structure",
    "finite-residue-defs",
    "finite-residue-ring-structure",
    "natural-discrete-order",
    "natural-nonzero",
    "finite-list-defs",
    "ring-polynomial-data",
    "ring-polynomial-structure",
    "quadratic-algebra-data",
    "ring-ideal-data",
    "ring-ideal-principal",
    "coordinate-point-ideal-data",
    "logical-connectives",
    "logic-exists",
    "../fermat_statement",
];

fn check(prelude: &str, statement: &str, proof: &str, good: bool) {
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let dir = std::env::temp_dir().join(format!(
        "lim-point-evaluation-{}-{}",
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
    source.push_str(&format!("(#theorem observed-point-evaluation (#universes) (#parameters) (#statement {statement}) (#proof {proof}))"));
    fs::write(&path, &source).unwrap();
    let mut config = CompileConfig::default();
    let d = ProofBudget::default();
    let total = 1024 * 1024 * 1024;
    config.set_proof_budget(ProofBudget::new(d.work(), d.phase_bytes(), total).unwrap());
    let expected = format!(
        "{}::observed-point-evaluation",
        path.canonicalize().unwrap().display()
    );
    let result = check_theorem_details_from_path_with_config(
        &source,
        &path,
        &config,
        "observed-point-evaluation",
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

fn carrier(q: usize) -> String {
    app("finite-residue", &[&n(q)])
}

fn ring(q: usize) -> String {
    app("finite-residue-ring", &[&n(q), &positive(q)])
}

fn op(q: usize, label: &str, args: &[&str]) -> String {
    let ty = carrier(q);
    let r = ring(q);
    let mut all = vec![ty.as_str(), r.as_str()];
    all.extend_from_slice(args);
    app(&format!("ring-{label}"), &all)
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
fn root(q: usize, x: usize, label: &str, args: &[&str]) -> String {
    let ty = carrier(q);
    let r = ring(q);
    let point = residue(q, x);
    let mut all = vec![ty.as_str(), r.as_str(), point.as_str()];
    all.extend_from_slice(args);
    app(&format!("polynomial-root-{label}"), &all)
}
fn value(term: &str) -> String {
    format!("(#pt-project finite-residue 0 {term})")
}
fn observe(term: &str, expected: usize, good: bool) {
    check(
        "",
        &eq(term, &n(expected)),
        &format!("(#pt-refl #pt-nat {})", n(expected)),
        good,
    );
}
fn polynomial_ring(q: usize) -> String {
    op(q, "polynomial-structure", &[])
}
fn polynomial_ideal(q: usize, label: &str, args: &[&str]) -> String {
    let ty = app("finite-list", &[&carrier(q)]);
    let r = polynomial_ring(q);
    let mut all = vec![ty.as_str(), r.as_str()];
    all.extend_from_slice(args);
    app(&format!("ring-ideal-{label}"), &all)
}

#[test]
fn computed_division_retains_zero_and_trailing_zero_lists() {
    for (q, x, p, remainder, coefficients) in [
        (5, 2, vec![1, 2, 3], 2, vec![3, 3, 0]),
        (8, 2, vec![4, 2], 0, vec![2, 0]),
        (5, 4, vec![3, 0, 0], 3, vec![0, 0]),
        (1, 0, vec![], 0, vec![0]),
    ] {
        let polynomial = poly(q, &p);
        observe(
            &value(&root(q, x, "remainder", &[&polynomial])),
            remainder,
            true,
        );
        let quotient = root(q, x, "quotient", &[&polynomial]);
        for (index, c) in coefficients.into_iter().enumerate() {
            observe(
                &value(&op(q, "polynomial-coefficient", &[&quotient, &n(index)])),
                c,
                true,
            );
        }
    }
}

fn factor(q: usize, x: usize, p: &str, good: bool) {
    let quotient = root(q, x, "quotient", &[p]);
    let divisor = root(q, x, "divisor", &[]);
    let product = op(q, "polynomial-multiply", &[&divisor, &quotient]);
    check(
        "",
        &op(q, "polynomial-equal", &[p, &product]),
        &root(q, x, "factor", &[p, &op(q, "reflexive", &[&residue(q, 0)])]),
        good,
    );
}

#[test]
fn actual_root_factors_cover_characteristic_two_composites_and_trivial_ring() {
    for (q, x, p) in [
        (8, 2, vec![4, 2]),
        (6, 3, vec![3, 1]),
        (2, 1, vec![1, 1]),
        (1, 0, vec![0, 0]),
    ] {
        factor(q, x, &poly(q, &p), true);
    }
}

#[test]
fn polynomial_principal_kernel_gives_both_directions() {
    let q = 8;
    let x = 2;
    let p = poly(q, &[4, 2]);
    let principal = polynomial_ideal(q, "principal", &[&root(q, x, "divisor", &[])]);
    let member = root(
        q,
        x,
        "principal-member",
        &[&p, &op(q, "reflexive", &[&residue(q, 0)])],
    );
    check(
        "",
        &polynomial_ideal(q, "member", &[&principal, &p]),
        &member,
        true,
    );
    check(
        "",
        &op(
            q,
            "equal",
            &[
                &op(q, "polynomial-evaluate", &[&p, &residue(q, x)]),
                &residue(q, 0),
            ],
        ),
        &root(q, x, "vanishes-if-principal", &[&p, &member]),
        true,
    );
}

struct Coordinate {
    prelude: String,
    args: Vec<String>,
    element: String,
    ty: String,
    ring: String,
    map: String,
}
impl Coordinate {
    fn call(&self, label: &str, args: &[&str]) -> String {
        let mut all: Vec<_> = self.args.iter().map(String::as_str).collect();
        all.extend_from_slice(args);
        app(&format!("point-evaluation-coordinate-{label}"), &all)
    }
    fn eval(&self, element: &str) -> String {
        app(
            "ring-evaluation-map",
            &[
                &self.ty,
                &self.ring,
                &self.args[0],
                &self.args[1],
                &self.map,
                element,
            ],
        )
    }
    fn ideal(&self) -> String {
        app(
            "coordinate-point-ideal-XY",
            &self.args[..6]
                .iter()
                .map(String::as_str)
                .collect::<Vec<_>>(),
        )
    }
}
fn definition(name: &str, ty: &str, body: &str) -> String {
    format!("(#math-definition {name} () {ty} {body})\n")
}
fn coordinate(
    q: usize,
    x: usize,
    beta: &[usize],
    yp: &[usize],
    p: &[usize],
    linear: &[usize],
) -> Coordinate {
    let mut prelude = String::new();
    let c = app("fixture-carrier", &[]);
    let r = app("fixture-ring", &[]);
    prelude.push_str(&definition("fixture-carrier", "(#pt-type 0)", &carrier(q)));
    prelude.push_str(&definition(
        "fixture-ring",
        &app("commutative-ring", &[&c]),
        &ring(q),
    ));
    let l = app("finite-list", &[&c]);
    let pr = app("ring-polynomial-structure", &[&c, &r]);
    let alpha = app("fixture-alpha", &[]);
    let beta_name = app("fixture-beta", &[]);
    let point = app("fixture-x", &[]);
    let y = app("fixture-y-polynomial", &[]);
    for (name, ty, body) in [
        ("fixture-alpha", l.as_str(), poly(q, &[])),
        ("fixture-beta", l.as_str(), poly(q, beta)),
        ("fixture-x", c.as_str(), residue(q, x)),
        ("fixture-y-polynomial", l.as_str(), poly(q, yp)),
    ] {
        prelude.push_str(&definition(name, ty, &body));
    }
    let poly_map = app("polynomial-root-evaluation-morphism", &[&c, &r, &point]);
    let y_value = app("ring-polynomial-evaluate", &[&c, &r, &y, &point]);
    let divisor = app("quadratic-division-divisor", &[&l, &pr, &alpha, &beta_name]);
    let curve = app(
        "ring-evaluation",
        &[&l, &pr, &c, &r, &poly_map, &y_value, &divisor],
    );
    let zero = app("ring-zero", &[&c, &r]);
    prelude.push_str(&format!(
        "(#theorem fixture-curve (#universes) (#parameters) (#statement {}) (#proof {}))\n",
        app("ring-equal", &[&c, &r, &curve, &zero]),
        app("ring-reflexive", &[&c, &r, &zero])
    ));
    let args = vec![c, r, alpha, beta_name, point, y, app("fixture-curve", &[])];
    let ty = app("quadratic-element", &[&l]);
    let structure = app("quadratic-ring-structure", &[&l, &pr, &args[2], &args[3]]);
    let element = format!(
        "(#pt-construct quadratic-element () ({l}) coordinates ({} {}))",
        poly(q, p),
        poly(q, linear)
    );
    let map = app(
        "point-evaluation-coordinate-morphism",
        &args.iter().map(String::as_str).collect::<Vec<_>>(),
    );
    Coordinate {
        prelude,
        args,
        element,
        ty,
        ring: structure,
        map,
    }
}

#[test]
fn coordinate_maps_compute_actual_values() {
    for (q, x, beta, yp, p, linear, answer) in [
        (2, 1, vec![], vec![], vec![1, 1], vec![1], 0),
        (5, 2, vec![1], vec![1], vec![1, 1], vec![2], 0),
        (1, 0, vec![], vec![], vec![], vec![], 0),
    ] {
        let f = coordinate(q, x, &beta, &yp, &p, &linear);
        check(
            &f.prelude,
            &eq(&value(&f.eval(&f.element)), &n(answer)),
            &format!("(#pt-refl #pt-nat {})", n(answer)),
            true,
        );
    }
}

#[test]
fn coordinate_kernel_to_point_ideal_uses_actual_nonzero_linear_parts() {
    for (q, x, beta, yp, p, linear) in [
        (2, 1, vec![], vec![], vec![1, 1], vec![1]),
        (5, 2, vec![1], vec![1], vec![1, 1], vec![2]),
    ] {
        let f = coordinate(q, x, &beta, &yp, &p, &linear);
        let member = app(
            "point-evaluation-kernel-introduce",
            &[
                &f.ty,
                &f.ring,
                &f.args[0],
                &f.args[1],
                &f.map,
                &f.element,
                &app(
                    "ring-reflexive",
                    &[
                        &f.args[0],
                        &f.args[1],
                        &app("ring-zero", &[&f.args[0], &f.args[1]]),
                    ],
                ),
            ],
        );
        let proof = f.call("kernel-contained", &[&f.element, &member]);
        check(
            &f.prelude,
            &app(
                "ring-ideal-member",
                &[&f.ty, &f.ring, &f.ideal(), &f.element],
            ),
            &proof,
            true,
        );
    }
}

#[test]
fn coordinate_quotient_maps_are_inverse() {
    for (q, x, beta, yp) in [(2, 1, vec![], vec![]), (5, 2, vec![1], vec![1])] {
        let f = coordinate(q, x, &beta, &yp, &[1], &[1]);
        let qr = f.call("quotient-ring", &[]);
        let forward = f.call("quotient-forward", &[]);
        let backward = f.call("quotient-inverse", &[]);
        let mapped = app(
            "ring-evaluation-map",
            &[&f.ty, &qr, &f.args[0], &f.args[1], &forward, &f.element],
        );
        let restored = app(
            "ring-evaluation-map",
            &[&f.args[0], &f.args[1], &f.ty, &qr, &backward, &mapped],
        );
        check(
            &f.prelude,
            &app("ring-equal", &[&f.ty, &qr, &restored, &f.element]),
            &f.call("quotient-left-inverse", &[&f.element]),
            true,
        );
        let scalar = residue(q, 1);
        let lifted = app(
            "ring-evaluation-map",
            &[&f.args[0], &f.args[1], &f.ty, &qr, &backward, &scalar],
        );
        let mapped = app(
            "ring-evaluation-map",
            &[&f.ty, &qr, &f.args[0], &f.args[1], &forward, &lifted],
        );
        check(
            &f.prelude,
            &app("ring-equal", &[&f.args[0], &f.args[1], &mapped, &scalar]),
            &f.call("quotient-right-inverse", &[&scalar]),
            true,
        );
    }
}

#[test]
fn source_nested_equation_matches_constructed_curve_value() {
    let f = coordinate(5, 2, &[1], &[1], &[1], &[2]);
    let l = app("finite-list", &[&f.args[0]]);
    let pr = app("ring-polynomial-structure", &[&f.args[0], &f.args[1]]);
    let d = app(
        "quadratic-division-divisor",
        &[&l, &pr, &f.args[2], &f.args[3]],
    );
    let nested_poly = app("ring-polynomial-evaluate", &[&l, &pr, &d, &f.args[5]]);
    let nested = app(
        "ring-polynomial-evaluate",
        &[&f.args[0], &f.args[1], &nested_poly, &f.args[4]],
    );
    let pm = app(
        "polynomial-root-evaluation-morphism",
        &[&f.args[0], &f.args[1], &f.args[4]],
    );
    let y = app(
        "ring-polynomial-evaluate",
        &[&f.args[0], &f.args[1], &f.args[5], &f.args[4]],
    );
    let curve = app(
        "ring-evaluation",
        &[&l, &pr, &f.args[0], &f.args[1], &pm, &y, &d],
    );
    let proof = app(
        "point-evaluation-coordinate-source-equation",
        &f.args[..6].iter().map(String::as_str).collect::<Vec<_>>(),
    );
    check(
        &f.prelude,
        &app("ring-equal", &[&f.args[0], &f.args[1], &nested, &curve]),
        &proof,
        true,
    );
}

#[test]
fn quotient_image_equality_constructs_actual_ideal_difference_membership() {
    let f = coordinate(2, 1, &[], &[], &[1], &[1]);
    let difference = app(
        "ring-add",
        &[
            &f.ty,
            &f.ring,
            &f.element,
            &app("ring-negate", &[&f.ty, &f.ring, &f.element]),
        ],
    );
    let relation = f.call("quotient-relation", &[&f.element, &f.element]);
    let proof = format!(
        "(#pt-app (#pt-project conjunction 1 {relation}) {})",
        app(
            "ring-reflexive",
            &[&f.args[0], &f.args[1], &f.eval(&f.element)]
        )
    );
    check(
        &f.prelude,
        &app(
            "ring-ideal-member",
            &[&f.ty, &f.ring, &f.ideal(), &difference],
        ),
        &proof,
        true,
    );
}

#[test]
fn wrong_root_equations_and_computed_remainders_are_rejected() {
    factor(5, 2, &poly(5, &[0, 1]), false);
    factor(8, 2, &poly(8, &[2, 2]), false);
    observe(
        &value(&root(5, 2, "remainder", &[&poly(5, &[1, 2, 3])])),
        1,
        false,
    );
}

#[test]
fn a_forged_coordinate_curve_equation_is_rejected() {
    let f = coordinate(5, 2, &[2], &[1], &[1], &[1]);
    check(
        &f.prelude,
        &eq(&n(0), &n(0)),
        &format!("(#pt-refl #pt-nat {})", n(0)),
        false,
    );
}

#[test]
fn a_wrong_quotient_roundtrip_result_is_rejected() {
    let f = coordinate(5, 2, &[1], &[1], &[1], &[1]);
    let qr = f.call("quotient-ring", &[]);
    let backward = f.call("quotient-inverse", &[]);
    let forward = f.call("quotient-forward", &[]);
    let x = residue(5, 1);
    let restored = app(
        "ring-evaluation-map",
        &[
            &f.ty,
            &qr,
            &f.args[0],
            &f.args[1],
            &forward,
            &app(
                "ring-evaluation-map",
                &[&f.args[0], &f.args[1], &f.ty, &qr, &backward, &x],
            ),
        ],
    );
    check(
        &f.prelude,
        &app(
            "ring-equal",
            &[&f.args[0], &f.args[1], &restored, &residue(5, 2)],
        ),
        &f.call("quotient-right-inverse", &[&x]),
        false,
    );
}

#[test]
fn an_unused_false_root_factor_is_still_checked() {
    let q = 5;
    let x = 2;
    let p = poly(q, &[0, 1]);
    let statement = op(
        q,
        "polynomial-equal",
        &[
            &p,
            &op(
                q,
                "polynomial-multiply",
                &[&root(q, x, "divisor", &[]), &root(q, x, "quotient", &[&p])],
            ),
        ],
    );
    let proof = root(
        q,
        x,
        "factor",
        &[&p, &op(q, "reflexive", &[&residue(q, 0)])],
    );
    let prelude = format!("(#theorem unused-invalid-factor (#universes) (#parameters) (#statement {statement}) (#proof {proof}))");
    check(
        &prelude,
        &eq(&n(0), &n(0)),
        &format!("(#pt-refl #pt-nat {})", n(0)),
        false,
    );
}
