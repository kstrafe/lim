//! Actual point-ideal representations, matrix factors and nonprincipality controls.
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
    "../fermat_statement",
    "commutative-ring-data",
    "coordinate-norm-degree-source-obstruction",
    "coordinate-point-ideal-data",
    "coordinate-point-ideal-membership",
    "finite-list-defs",
    "finite-residue-defs",
    "finite-residue-ring-structure",
    "logic-exists",
    "logical-connectives",
    "natural-discrete-order",
    "natural-nonzero",
    "natural-prime-three",
    "natural-prime-two",
    "point-evaluation-kernel",
    "point-evaluation-coordinate-kernel-contained",
    "point-evaluation-coordinate-morphism",
    "point-evaluation-coordinate-section",
    "point-ideal-basis-constant-factor",
    "point-ideal-basis-constant-multiply",
    "point-ideal-basis-data",
    "point-ideal-basis-linear-quadratic-principal",
    "point-ideal-basis-reconstruction",
    "point-ideal-basis-zero-linear-Y-square",
    "point-ideal-degree-factor-nonvanishing",
    "point-ideal-degree-linear-mutual-factors",
    "point-ideal-degree-root-linear",
    "point-ideal-degree-small-indices",
    "point-ideal-matrix-Y-column",
    "point-ideal-matrix-column-factorization",
    "point-ideal-matrix-columns",
    "point-ideal-matrix-equivalence",
    "point-ideal-matrix-left-action",
    "point-ideal-matrix-multiplication-columns",
    "point-ideal-principal-forward-matrix",
    "point-ideal-principal-norm-forward-factor",
    "point-ideal-principal-norm-reverse-factor",
    "point-ideal-principal-reverse-matrix",
    "point-ideal-principal-weierstrass-impossible",
    "polynomial-root-division-data",
    "polynomial-root-evaluation-morphism",
    "quadratic-algebra-data",
    "quadratic-algebra-left-matrix",
    "quadratic-algebra-ring-structure",
    "quadratic-division-data",
    "ring-evaluation-data",
    "ring-evaluation-morphism",
    "ring-ideal-data",
    "ring-ideal-principal",
    "ring-matrix2-data",
    "ring-polynomial-data",
    "ring-polynomial-domain-residue-instance",
    "ring-polynomial-structure",
    "ring-polynomial-support-data",
    "weierstrass-coordinate-normal-form",
];

fn check(prelude: &str, statement: &str, proof: &str, good: bool) {
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let dir = std::env::temp_dir().join(format!(
        "lim-point-ideal-{}-{}",
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
    source.push_str(&format!("(#theorem observed-point-ideal (#universes) (#parameters) (#statement {statement}) (#proof {proof}))"));
    fs::write(&path, &source).unwrap();
    let mut config = CompileConfig::default();
    let d = ProofBudget::default();
    let total = 1024 * 1024 * 1024;
    config.set_proof_budget(ProofBudget::new(d.work(), d.phase_bytes(), total).unwrap());
    let expected = format!(
        "{}::observed-point-ideal",
        path.canonicalize().unwrap().display()
    );
    let result = check_theorem_details_from_path_with_config(
        &source,
        &path,
        &config,
        "observed-point-ideal",
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
        assert!(
            e.message.contains("mismatch"),
            "{}: {}",
            statement.chars().take(260).collect::<String>(),
            e.message
        );
    }
}

fn carrier(q: usize) -> String {
    app("finite-residue", &[&n(q)])
}

fn ring(q: usize) -> String {
    app("finite-residue-ring", &[&n(q), &positive(q)])
}

fn named(q: usize, name: &str, args: &[&str]) -> String {
    let ty = carrier(q);
    let r = ring(q);
    let mut all = vec![ty.as_str(), r.as_str()];
    all.extend_from_slice(args);
    app(name, &all)
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
        &values.iter().map(|&x| residue(q, x)).collect::<Vec<_>>(),
    )
}
fn vector(q: usize, values: [usize; 2]) -> String {
    format!(
        "(#pt-construct quadratic-element () ({}) coordinates ({} {}))",
        carrier(q),
        residue(q, values[0]),
        residue(q, values[1])
    )
}
fn matrix(q: usize, values: [usize; 4]) -> String {
    format!(
        "(#pt-construct ring-matrix2 () ({}) entries ({}))",
        carrier(q),
        values.map(|x| residue(q, x)).join(" ")
    )
}
fn project(ty: &str, index: usize, object: &str) -> String {
    format!("(#pt-project {ty} {index} {object})")
}
fn value(object: &str) -> String {
    project("finite-residue", 0, object)
}
fn observe(prelude: &str, actual: &str, expected: usize, good: bool) {
    check(
        prelude,
        &eq(actual, &n(expected)),
        &format!("(#pt-refl #pt-nat {})", n(expected)),
        good,
    );
}
fn definition(name: &str, ty: &str, body: &str) -> String {
    format!("(#math-definition {name} () {ty} {body})\n")
}

#[test]
fn actual_matrix_actions_detect_row_and_column_orientation() {
    for (q, m, v, result) in [
        (5, [1, 2, 3, 4], [2, 1], [4, 0]),
        (8, [7, 3, 2, 6], [5, 7], [0, 4]),
        (1, [0, 0, 0, 0], [0, 0], [0, 0]),
    ] {
        let actual = named(
            q,
            "point-ideal-matrix-action",
            &[&matrix(q, m), &vector(q, v)],
        );
        for (i, expected) in result.into_iter().enumerate() {
            observe(
                "",
                &value(&project("quadratic-element", i, &actual)),
                expected,
                true,
            );
        }
    }
}

#[test]
fn existing_left_matrix_represents_actual_quadratic_multiplication() {
    let q = 6;
    let v = vector(q, [2, 1]);
    let w = vector(q, [3, 4]);
    let alpha = residue(q, 2);
    let beta = residue(q, 3);
    let product = named(q, "quadratic-multiply", &[&alpha, &beta, &v, &w]);
    let m = named(q, "quadratic-left-matrix", &[&alpha, &beta, &v]);
    let action = named(q, "point-ideal-matrix-action", &[&m, &w]);
    check(
        "",
        &named(q, "quadratic-equal", &[&product, &action]),
        &named(
            q,
            "point-ideal-matrix-left-action",
            &[&alpha, &beta, &v, &w],
        ),
        true,
    );
    observe(
        "",
        &value(&project("quadratic-element", 0, &product)),
        0,
        true,
    );
    observe(
        "",
        &value(&project("quadratic-element", 1, &product)),
        3,
        true,
    );
}

#[test]
fn constant_multiplication_is_actual_scaling_with_zero_divisors() {
    let q = 8;
    let c = residue(q, 3);
    let v = vector(q, [5, 6]);
    let alpha = residue(q, 1);
    let beta = residue(q, 7);
    let product = named(
        q,
        "quadratic-multiply",
        &[&alpha, &beta, &vector(q, [3, 0]), &v],
    );
    let scaled = named(q, "quadratic-scale", &[&c, &v]);
    check(
        "",
        &named(q, "quadratic-equal", &[&product, &scaled]),
        &named(
            q,
            "point-ideal-basis-constant-multiply",
            &[&alpha, &beta, &c, &v],
        ),
        true,
    );
    observe(
        "",
        &value(&project("quadratic-element", 0, &product)),
        7,
        true,
    );
    observe(
        "",
        &value(&project("quadratic-element", 1, &product)),
        2,
        true,
    );
}

#[derive(Clone, Copy)]
enum Model {
    Flat,
    Linear,
    Weierstrass,
}
struct Frame {
    prelude: String,
    args: Vec<String>,
    ty: String,
    ring: String,
    element: String,
    map: String,
}
impl Frame {
    fn call(&self, name: &str, args: &[&str]) -> String {
        let mut all = self.args.iter().map(String::as_str).collect::<Vec<_>>();
        all.extend_from_slice(args);
        app(name, &all)
    }
    fn coefficient_ring(&self) -> String {
        app("ring-polynomial-structure", &[&self.args[0], &self.args[1]])
    }
    fn coefficient_type(&self) -> String {
        app("finite-list", &[&self.args[0]])
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
    fn coordinates(&self) -> String {
        app(
            "point-ideal-basis-coordinates",
            &[
                &self.args[0],
                &self.args[1],
                &self.args[4],
                &self.args[5],
                &self.element,
            ],
        )
    }
    fn basis_matrix(&self) -> String {
        app(
            "point-ideal-basis-matrix",
            &[&self.args[0], &self.args[1], &self.args[4], &self.args[5]],
        )
    }
    fn eval(&self, e: &str) -> String {
        app(
            "ring-evaluation-map",
            &[
                &self.ty,
                &self.ring,
                &self.args[0],
                &self.args[1],
                &self.map,
                e,
            ],
        )
    }
    fn member(&self, e: &str) -> String {
        let zero = app("ring-zero", &[&self.args[0], &self.args[1]]);
        let vanishes = app("ring-reflexive", &[&self.args[0], &self.args[1], &zero]);
        let kernel = app(
            "point-evaluation-kernel-introduce",
            &[
                &self.ty,
                &self.ring,
                &self.args[0],
                &self.args[1],
                &self.map,
                e,
                &vanishes,
            ],
        );
        self.call(
            "point-evaluation-coordinate-kernel-contained",
            &[e, &kernel],
        )
    }
    fn coefficient(&self, p: &str, index: usize) -> String {
        app(
            "ring-polynomial-coefficient",
            &[&self.args[0], &self.args[1], p, &n(index)],
        )
    }
    fn ideal_equal(&self, a: &str, b: &str) -> String {
        app("ring-ideal-equal", &[&self.ty, &self.ring, a, b])
    }
    fn principal(&self, g: &str) -> String {
        app("ring-ideal-principal", &[&self.ty, &self.ring, g])
    }
    fn y(&self) -> String {
        app(
            "quadratic-Y",
            &[&self.coefficient_type(), &self.coefficient_ring()],
        )
    }
    fn principal_control(&self) -> String {
        app(
            "point-ideal-basis-linear-quadratic-principal",
            &[&self.args[0], &self.args[1], &self.args[4]],
        )
    }
}
fn frame(q: usize, model: Model, p: &[usize], linear: &[usize]) -> Frame {
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
    let point = app("fixture-x", &[]);
    let alpha = app("fixture-alpha", &[]);
    let beta = app("fixture-beta", &[]);
    let yp = app("fixture-y-polynomial", &[]);
    prelude.push_str(&definition(
        "fixture-x",
        &c,
        &residue(q, if matches!(model, Model::Flat) { 2 } else { 0 }),
    ));
    let zero = app("ring-zero", &[&c, &r]);
    let mut coeff = vec![c.as_str(), r.as_str()];
    coeff.extend([zero.as_str(); 5]);
    let a = if matches!(model, Model::Weierstrass) {
        app("weierstrass-coordinate-linear", &coeff)
    } else {
        poly(q, &[])
    };
    let b = match model {
        Model::Flat => poly(q, &[1]),
        Model::Linear => app("polynomial-root-divisor", &[&c, &r, &point]),
        Model::Weierstrass => app("weierstrass-coordinate-cubic", &coeff),
    };
    prelude.push_str(&definition("fixture-alpha", &l, &a));
    prelude.push_str(&definition("fixture-beta", &l, &b));
    prelude.push_str(&definition(
        "fixture-y-polynomial",
        &l,
        &poly(
            q,
            if matches!(model, Model::Flat) {
                &[1]
            } else {
                &[]
            },
        ),
    ));
    let poly_map = app("polynomial-root-evaluation-morphism", &[&c, &r, &point]);
    let y_value = app("ring-polynomial-evaluate", &[&c, &r, &yp, &point]);
    let divisor = app("quadratic-division-divisor", &[&l, &pr, &alpha, &beta]);
    let curve = app(
        "ring-evaluation",
        &[&l, &pr, &c, &r, &poly_map, &y_value, &divisor],
    );
    prelude.push_str(&format!(
        "(#theorem fixture-curve (#universes) (#parameters) (#statement {}) (#proof {}))\n",
        app("ring-equal", &[&c, &r, &curve, &zero]),
        app("ring-reflexive", &[&c, &r, &zero])
    ));
    let args = vec![c, r, alpha, beta, point, yp, app("fixture-curve", &[])];
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
    Frame {
        prelude,
        args,
        ty,
        ring: structure,
        element,
        map,
    }
}

#[test]
fn actual_point_matrix_and_determinant_keep_both_generators() {
    let f = frame(5, Model::Flat, &[1, 1], &[2]);
    let m = f.basis_matrix();
    let l = f.coefficient_type();
    let r = f.coefficient_ring();
    let det = app("ring-matrix2-determinant", &[&l, &r, &m]);
    for (index, expected) in [(0, 3), (1, 1), (2, 0)] {
        observe(
            &f.prelude,
            &value(&f.coefficient(&det, index)),
            expected,
            true,
        );
    }
    observe(
        &f.prelude,
        &value(&f.coefficient(&project("ring-matrix2", 1, &m), 0)),
        4,
        true,
    );
}

#[test]
fn computed_member_coordinates_retain_nonzero_linear_parts_and_trailing_zeros() {
    for trailing in [false, true] {
        let f = frame(
            5,
            Model::Flat,
            if trailing { &[1, 1, 0] } else { &[1, 1] },
            if trailing { &[2, 0] } else { &[2] },
        );
        let coordinates = f.coordinates();
        observe(&f.prelude, &value(&f.eval(&f.element)), 0, true);
        for (component, index, expected) in [(0, 0, 1), (0, 1, 0), (1, 0, 2)] {
            observe(
                &f.prelude,
                &value(&f.coefficient(
                    &project("quadratic-element", component, &coordinates),
                    index,
                )),
                expected,
                true,
            );
        }
        let action = app(
            "point-ideal-matrix-action",
            &[
                &f.coefficient_type(),
                &f.coefficient_ring(),
                &f.basis_matrix(),
                &coordinates,
            ],
        );
        let equation = app(
            "quadratic-equal",
            &[
                &f.coefficient_type(),
                &f.coefficient_ring(),
                &f.element,
                &action,
            ],
        );
        check(
            &f.prelude,
            &equation,
            &f.call(
                "point-ideal-basis-reconstruct",
                &[&f.element, &f.member(&f.element)],
            ),
            true,
        );
    }
}

#[test]
fn the_actual_linear_quadratic_model_has_a_principal_point_ideal() {
    let f = frame(5, Model::Linear, &[], &[1]);
    let y = f.y();
    check(
        &f.prelude,
        &f.ideal_equal(&f.ideal(), &f.principal(&y)),
        &f.principal_control(),
        true,
    );
    let u = f.call("point-ideal-principal-forward-matrix", &[&y]);
    for (i, expected) in [0, 1, 1, 0].into_iter().enumerate() {
        observe(
            &f.prelude,
            &value(&f.coefficient(&project("ring-matrix2", i, &u), 0)),
            expected,
            true,
        );
    }
    let det = app(
        "ring-matrix2-determinant",
        &[&f.coefficient_type(), &f.coefficient_ring(), &u],
    );
    observe(&f.prelude, &value(&f.coefficient(&det, 0)), 4, true);
}

#[test]
fn actual_principal_membership_constructs_both_matrix_factorizations() {
    let f = frame(2, Model::Linear, &[], &[1]);
    let y = f.y();
    let control = f.principal_control();
    let l = f.coefficient_type();
    let r = f.coefficient_ring();
    let fm = app(
        "quadratic-left-matrix",
        &[&l, &r, &f.args[2], &f.args[3], &y],
    );
    let nm = f.basis_matrix();
    let u = f.call("point-ideal-principal-forward-matrix", &[&y]);
    check(
        &f.prelude,
        &app(
            "ring-matrix2-equal",
            &[
                &l,
                &r,
                &fm,
                &app("ring-matrix2-multiply", &[&l, &r, &nm, &u]),
            ],
        ),
        &f.call(
            "point-ideal-principal-forward-factorization",
            &[&y, &control],
        ),
        true,
    );
    let ty = app("ring-matrix2", &[&l]);
    let predicate = format!(
        "(#pt-lambda ((reverse {ty})) {})",
        app(
            "ring-matrix2-equal",
            &[
                &l,
                &r,
                &nm,
                &app("ring-matrix2-multiply", &[&l, &r, &fm, "reverse"])
            ]
        )
    );
    check(
        &f.prelude,
        &format!("(#pt-app (#pt-use exists (0)) {ty} {predicate})"),
        &f.call(
            "point-ideal-principal-reverse-factorization",
            &[&y, &control],
        ),
        true,
    );
}

#[test]
fn both_actual_determinant_factors_and_norm_sign_are_checked() {
    let f = frame(2, Model::Linear, &[], &[1]);
    let y = f.y();
    let l = f.coefficient_type();
    let r = f.coefficient_ring();
    let norm = app("quadratic-norm", &[&l, &r, &f.args[2], &f.args[3], &y]);
    let d = app(
        "polynomial-root-divisor",
        &[&f.args[0], &f.args[1], &f.args[4]],
    );
    let u = f.call("point-ideal-principal-forward-matrix", &[&y]);
    let du = app("ring-matrix2-determinant", &[&l, &r, &u]);
    let multiply = app(
        "ring-polynomial-multiply",
        &[&f.args[0], &f.args[1], &d, &du],
    );
    check(
        &f.prelude,
        &app(
            "ring-polynomial-equal",
            &[&f.args[0], &f.args[1], &norm, &multiply],
        ),
        &f.call(
            "point-ideal-principal-norm-forward-factor",
            &[&y, &f.principal_control()],
        ),
        true,
    );
    let predicate = format!(
        "(#pt-lambda ((coefficient {l})) {})",
        app(
            "ring-polynomial-equal",
            &[
                &f.args[0],
                &f.args[1],
                &d,
                &app(
                    "ring-polynomial-multiply",
                    &[&f.args[0], &f.args[1], &norm, "coefficient"]
                )
            ]
        )
    );
    check(
        &f.prelude,
        &format!("(#pt-app (#pt-use exists (0)) {l} {predicate})"),
        &f.call(
            "point-ideal-principal-norm-reverse-factor",
            &[&y, &f.principal_control()],
        ),
        true,
    );
    observe(&f.prelude, &value(&f.coefficient(&norm, 1)), 1, true);
}

#[test]
fn exact_degree_indices_include_the_zero_boundary() {
    check(
        "",
        &eq(&n(1), &n(1)),
        &app(
            "point-ideal-degree-one-sum-collapse",
            &[&n(0), &n(0), &format!("(#pt-refl #pt-nat {})", n(1))],
        ),
        true,
    );
    check(
        "",
        &eq(&n(2), &n(1)),
        &app(
            "point-ideal-degree-one-sum-collapse",
            &[&n(1), &n(0), &format!("(#pt-refl #pt-nat {})", n(1))],
        ),
        false,
    );
}

#[test]
fn actual_weierstrass_nonprincipality_covers_zero_one_and_y_candidates() {
    for (q, p, linear) in [
        (2, vec![], vec![]),
        (3, vec![1], vec![]),
        (2, vec![], vec![1]),
    ] {
        let f = frame(q, Model::Weierstrass, &p, &linear);
        let prime = app(if q == 2 { "prime-two" } else { "prime-three" }, &[]);
        let domain = app(
            "ring-polynomial-domain-prime-residue",
            &[&n(q), &positive(q), &prime],
        );
        let zero = app("ring-zero", &[&f.args[0], &f.args[1]]);
        let mut args = vec![f.args[0].as_str(), f.args[1].as_str(), domain.as_str()];
        args.extend([zero.as_str(); 5]);
        args.extend([
            f.args[4].as_str(),
            f.args[5].as_str(),
            f.args[6].as_str(),
            f.element.as_str(),
        ]);
        let statement = format!(
            "(#pt-pi ((denied {})) #pt-false)",
            f.ideal_equal(&f.ideal(), &f.principal(&f.element))
        );
        check(
            &f.prelude,
            &statement,
            &app("point-ideal-principal-weierstrass-impossible", &args),
            true,
        );
    }
}

#[test]
fn wrong_coordinates_and_transposed_matrix_values_are_rejected() {
    let f = frame(5, Model::Flat, &[1, 1], &[2]);
    observe(
        &f.prelude,
        &value(&f.coefficient(&project("quadratic-element", 0, &f.coordinates()), 0)),
        2,
        false,
    );
    let actual = named(
        5,
        "point-ideal-matrix-action",
        &[&matrix(5, [1, 2, 3, 4]), &vector(5, [2, 1])],
    );
    observe(
        "",
        &value(&project("quadratic-element", 0, &actual)),
        0,
        false,
    );
}

#[test]
fn a_nonmember_or_wrong_model_cannot_forge_the_conclusions() {
    let f = frame(5, Model::Flat, &[1], &[]);
    let one = app("ring-one", &[&f.args[0], &f.args[1]]);
    let nonmember = f.call("point-evaluation-coordinate-section", &[&one]);
    let wrong_zero = f.call("point-evaluation-coordinate-section-inverse", &[&one]);
    let wrong_kernel = app(
        "point-evaluation-kernel-introduce",
        &[
            &f.ty,
            &f.ring,
            &f.args[0],
            &f.args[1],
            &f.map,
            &nonmember,
            &wrong_zero,
        ],
    );
    let statement = app(
        "ring-ideal-member",
        &[&f.ty, &f.ring, &f.ideal(), &nonmember],
    );
    check(
        &f.prelude,
        &statement,
        &f.call(
            "point-evaluation-coordinate-kernel-contained",
            &[&nonmember, &wrong_kernel],
        ),
        false,
    );
    // Test the exact model-sensitive norm premise, using the positive
    // linear model whose actual norm has degree one.
    let f = frame(2, Model::Linear, &[], &[1]);
    let y = f.y();
    let norm = app(
        "quadratic-norm",
        &[
            &f.coefficient_type(),
            &f.coefficient_ring(),
            &f.args[2],
            &f.args[3],
            &y,
        ],
    );
    let leading = app(
        "ring-polynomial-degree-witness",
        &[&f.args[0], &f.args[1], &norm, &n(1)],
    );
    let statement = format!("(#pt-pi ((denied {leading})) #pt-false)");
    let domain = app(
        "ring-polynomial-domain-prime-residue",
        &[&n(2), &positive(2), &app("prime-two", &[])],
    );
    let zero = app("ring-zero", &[&f.args[0], &f.args[1]]);
    let mut args = vec![f.args[0].as_str(), f.args[1].as_str(), domain.as_str()];
    args.extend([zero.as_str(); 5]);
    args.push(y.as_str());
    check(
        &f.prelude,
        &statement,
        &app("coordinate-norm-degree-element-not-one", &args),
        false,
    );
}
