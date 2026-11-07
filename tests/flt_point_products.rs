//! Concrete opposite-point products and adversarial field/Jacobian evidence.
#[path = "support/native_proof_cases.rs"]
mod native;
use native::check;

fn n(value: usize) -> String {
    format!("(#pt-numeral {value})")
}
fn app(name: &str, args: &[&str]) -> String {
    args.iter().fold(format!("(#pt-use {name} ())"), |f, x| {
        format!("(#pt-app {f} {x})")
    })
}
fn use_name(name: &str) -> String {
    app(name, &[])
}
fn definition(name: &str, ty: &str, body: &str) -> String {
    format!("(#math-definition {name} () {ty} {body})\n")
}
fn theorem(name: &str, ty: &str, body: &str) -> String {
    format!("(#theorem {name} (#universes) (#parameters) (#statement {ty}) (#proof {body}))\n")
}
fn positive(q: usize) -> String {
    app("zero-less-successor", &[&n(q - 1)])
}
fn residue(q: usize, value: usize) -> String {
    assert!(value < q);
    let bound = format!("(#pt-construct exists (0) (#pt-nat (#pt-lambda ((gap #pt-nat)) (#pt-eq #pt-nat {} (#pt-app (#pt-use add ()) (#pt-succ {}) gap)))) introduce ({} (#pt-refl #pt-nat {})))", n(q), n(value), n(q-value-1), n(q));
    format!(
        "(#pt-construct finite-residue () ({}) representative ({} {bound}))",
        n(q),
        n(value)
    )
}
fn list(ty: &str, values: &[String]) -> String {
    values.iter().rev().fold(
        format!("(#pt-construct finite-list () ({ty}) nil ())"),
        |tail, head| format!("(#pt-construct finite-list () ({ty}) cons ({head} {tail}))"),
    )
}
fn negate(proposition: &str) -> String {
    format!("(#pt-pi ((denied {proposition})) #pt-false)")
}

struct Model {
    prelude: String,
    args: Vec<String>,
    carrier: String,
    ring: String,
    alpha: String,
    beta: String,
    curve: String,
}
impl Model {
    fn finite(q: usize, values: [usize; 7]) -> Self {
        Self::build(
            &app("finite-residue", &[&n(q)]),
            &app("finite-residue-ring", &[&n(q), &positive(q)]),
            values.map(|x| residue(q, x)),
        )
    }
    fn rational(values: [usize; 7]) -> Self {
        Self::build(
            &use_name("rational"),
            &use_name("rational-ring-structure"),
            values.map(|x| {
                app(
                    "rational-of-integer",
                    &[&app("integer-of-natural", &[&n(x)])],
                )
            }),
        )
    }
    fn build(carrier: &str, ring: &str, values: [String; 7]) -> Self {
        let mut prelude = definition("fixture-carrier", "(#pt-type 0)", carrier);
        let carrier = use_name("fixture-carrier");
        prelude += &definition("fixture-ring", &app("commutative-ring", &[&carrier]), ring);
        let ring = use_name("fixture-ring");
        let mut args = vec![carrier.clone(), ring.clone()];
        for (name, value) in ["a1", "a2", "a3", "a4", "a6", "root", "ordinate"]
            .into_iter()
            .zip(values)
        {
            let name = format!("fixture-{name}");
            prelude += &definition(&name, &carrier, &value);
            args.push(use_name(&name));
        }
        let coefficients = args[..7].iter().map(String::as_str).collect::<Vec<_>>();
        let l = app("finite-list", &[&carrier]);
        prelude += &definition(
            "fixture-alpha",
            &l,
            &app("weierstrass-coordinate-linear", &coefficients),
        );
        prelude += &definition(
            "fixture-beta",
            &l,
            &app("weierstrass-coordinate-cubic", &coefficients),
        );
        let alpha = use_name("fixture-alpha");
        let beta = use_name("fixture-beta");
        let pr = app("ring-polynomial-structure", &[&carrier, &ring]);
        let map = app(
            "polynomial-root-evaluation-morphism",
            &[&carrier, &ring, &args[7]],
        );
        let u = list(&carrier, &[args[8].clone()]);
        let eval_u = app("ring-polynomial-evaluate", &[&carrier, &ring, &u, &args[7]]);
        let divisor = app("quadratic-division-divisor", &[&l, &pr, &alpha, &beta]);
        let curve = app(
            "ring-evaluation",
            &[&l, &pr, &carrier, &ring, &map, &eval_u, &divisor],
        );
        prelude += &definition("fixture-curve", &carrier, &curve);
        Self {
            prelude,
            args,
            carrier,
            ring,
            alpha,
            beta,
            curve: use_name("fixture-curve"),
        }
    }
    fn scalar(&self, name: &str, args: &[&str]) -> String {
        let mut all = vec![self.carrier.as_str(), self.ring.as_str()];
        all.extend(args);
        app(name, &all)
    }
    fn call(&self, name: &str, args: &[&str]) -> String {
        let mut all = self.args.iter().map(String::as_str).collect::<Vec<_>>();
        all.extend(args);
        app(name, &all)
    }
    fn equal(&self, x: &str, y: &str) -> String {
        self.scalar("ring-equal", &[x, y])
    }
    fn zero(&self) -> String {
        self.scalar("ring-zero", &[])
    }
    fn nonzero(&self, x: &str) -> String {
        negate(&self.equal(x, &self.zero()))
    }
    fn partial(&self, axis: &str) -> String {
        self.call(&format!("point-ideal-product-partial-{axis}"), &[])
    }
    fn jacobian(&self) -> String {
        app(
            "disjunction",
            &[
                &self.nonzero(&self.partial("x")),
                &self.nonzero(&self.partial("y")),
            ],
        )
    }
    fn finite_branch(&mut self, q: usize, axis: &str, actual: usize) -> String {
        assert!(actual != 0);
        // Compute the representative once, then use an abstract bridge.
        // Repeated normalization of the closed modular expression inside a
        // negation needlessly exhausts the default per-declaration work budget.
        self.prelude += &finite_nonzero_bridge();
        let projection = format!("(#pt-project finite-residue 0 {})", self.partial(axis));
        self.prelude += &theorem(
            "fixture-partial-value",
            &format!("(#pt-eq #pt-nat {projection} {})", n(actual)),
            &format!("(#pt-refl #pt-nat {})", n(actual)),
        );
        let evidence = app(
            "fixture-nonzero-from-value",
            &[
                &n(q),
                &positive(q),
                &self.partial(axis),
                &n(actual - 1),
                &use_name("fixture-partial-value"),
            ],
        );
        self.prelude += &theorem(
            "fixture-partial-nonzero",
            &self.nonzero(&self.partial(axis)),
            &evidence,
        );
        format!(
            "(#pt-construct disjunction () ({} {}) {} ({}))",
            self.nonzero(&self.partial("x")),
            self.nonzero(&self.partial("y")),
            if axis == "x" { "left" } else { "right" },
            use_name("fixture-partial-nonzero")
        )
    }
    fn certify_equation_and_jacobian(&mut self, branch: &str, raw_curve_proof: &str) {
        let curve_eq = self.equal(&self.source_curve(), &self.zero());
        self.prelude += &theorem("fixture-curve-equation", &curve_eq, raw_curve_proof);
        self.prelude += &theorem("fixture-jacobian", &self.jacobian(), branch);
    }
    fn certify(&mut self, branch: &str, raw_curve_proof: &str) {
        self.certify_equation_and_jacobian(branch, raw_curve_proof);
        let curve_eq = self.equal(&self.source_curve(), &self.zero());
        let ns = self.call("point-ideal-product-nonsingular", &[]);
        let proof = format!(
            "(#pt-construct conjunction () ({} {}) both ({} {}))",
            curve_eq,
            self.jacobian(),
            use_name("fixture-curve-equation"),
            use_name("fixture-jacobian")
        );
        self.prelude += &theorem("fixture-nonsingular", &ns, &proof);
    }
    fn coordinate_parts(&self) -> (String, String) {
        let l = app("finite-list", &[&self.carrier]);
        let pr = self.scalar("ring-polynomial-structure", &[]);
        (
            app("quadratic-element", &[&l]),
            app(
                "quadratic-ring-structure",
                &[&l, &pr, &self.alpha, &self.beta],
            ),
        )
    }
    fn point_ideal(&self, ordinate: &str) -> String {
        let coefficients = self.args[..7]
            .iter()
            .map(String::as_str)
            .collect::<Vec<_>>();
        let alpha = app("weierstrass-coordinate-linear", &coefficients);
        let beta = app("weierstrass-coordinate-cubic", &coefficients);
        self.scalar(
            "coordinate-point-ideal-XY",
            &[
                &alpha,
                &beta,
                &self.args[7],
                &list(&self.carrier, &[ordinate.to_owned()]),
            ],
        )
    }
    fn source_curve(&self) -> String {
        let coefficients = self.args[..7]
            .iter()
            .map(String::as_str)
            .collect::<Vec<_>>();
        let alpha = app("weierstrass-coordinate-linear", &coefficients);
        let beta = app("weierstrass-coordinate-cubic", &coefficients);
        let l = app("finite-list", &[&self.carrier]);
        let pr = self.scalar("ring-polynomial-structure", &[]);
        let map = self.scalar("polynomial-root-evaluation-morphism", &[&self.args[7]]);
        let ordinate = self.scalar(
            "ring-polynomial-evaluate",
            &[&list(&self.carrier, &[self.args[8].clone()]), &self.args[7]],
        );
        let divisor = app("quadratic-division-divisor", &[&l, &pr, &alpha, &beta]);
        app(
            "ring-evaluation",
            &[
                &l,
                &pr,
                &self.carrier,
                &self.ring,
                &map,
                &ordinate,
                &divisor,
            ],
        )
    }
    fn product_goal(&self) -> String {
        let (ty, _) = self.coordinate_parts();
        let ring = app(
            "weierstrass-coordinate-ring",
            &self.args[..7]
                .iter()
                .map(String::as_str)
                .collect::<Vec<_>>(),
        );
        let negative_y = self.call("point-ideal-product-negative-y", &[]);
        let product = app(
            "ring-ideal-product",
            &[
                &ty,
                &ring,
                &self.point_ideal(&negative_y),
                &self.point_ideal(&self.args[8]),
            ],
        );
        let x = self.scalar("coordinate-point-ideal-X-class", &[&self.args[7]]);
        let principal = app("ring-ideal-principal", &[&ty, &ring, &x]);
        app("ring-ideal-equal", &[&ty, &ring, &product, &principal])
    }
    fn prime_field(&self, q: usize) -> String {
        app(
            "point-ideal-product-prime-field",
            &[
                &n(q),
                &positive(q),
                &use_name(if q == 2 { "prime-two" } else { "prime-three" }),
            ],
        )
    }
}

fn finite_nonzero_bridge() -> String {
    let ty = app("finite-residue", &["modulus"]);
    let ring = app("finite-residue-ring", &["modulus", "positive-modulus"]);
    let zero = app("ring-zero", &[&ty, &ring]);
    let proposition = app("ring-equal", &[&ty, &ring, "element", &zero]);
    let value = "(#pt-project finite-residue 0 element)";
    let zero_value = format!("(#pt-project finite-residue 0 {zero})");
    format!(
        "(#theorem fixture-nonzero-from-value (#universes) (#parameters
      (#parameter modulus #pt-nat)
      (#parameter positive-modulus (#pt-app (#pt-use less-than ()) #pt-zero modulus))
      (#parameter element {ty}) (#parameter predecessor #pt-nat)
      (#parameter value-equation (#pt-eq #pt-nat {value} (#pt-succ predecessor))))
      (#statement (#pt-pi ((zero-evidence {proposition})) #pt-false))
      (#proof (#pt-lambda ((zero-evidence {proposition}))
        (#pt-app (#pt-use successor-not-zero ()) predecessor
          (#pt-app (#pt-use transitivity (0)) #pt-nat (#pt-succ predecessor) {zero_value} #pt-zero
            (#pt-app (#pt-use transitivity (0)) #pt-nat (#pt-succ predecessor) {value} {zero_value}
              (#pt-app (#pt-use symmetry (0)) #pt-nat {value} (#pt-succ predecessor) value-equation)
              zero-evidence)
            (#pt-app (#pt-use finite-residue-zero-value ()) modulus positive-modulus))))))\n"
    )
}

fn equivalent_nonzero_bridge() -> String {
    let eq = |a: &str, b: &str| app("ring-equal", &["Carrier", "ring", a, b]);
    let zero = app("ring-zero", &["Carrier", "ring"]);
    let proof = format!(
        "(#pt-lambda ((zero-evidence {})) (#pt-app right-nonzero {}))",
        eq("left", &zero),
        app(
            "ring-transitive",
            &[
                "Carrier",
                "ring",
                "right",
                "left",
                &zero,
                &app(
                    "ring-symmetric",
                    &["Carrier", "ring", "left", "right", "value-equation"]
                ),
                "zero-evidence"
            ]
        )
    );
    format!(
        "(#theorem fixture-equivalent-nonzero (#universes) (#parameters
      (#parameter Carrier (#pt-type 0))
      (#parameter ring (#pt-app (#pt-use commutative-ring ()) Carrier))
      (#parameter left Carrier) (#parameter right Carrier)
      (#parameter value-equation {}) (#parameter right-nonzero {}))
      (#statement {}) (#proof {proof}))\n",
        eq("left", "right"),
        negate(&eq("right", &zero)),
        negate(&eq("left", &zero))
    )
}

#[test]
fn both_nonsingular_jacobian_branches_prove_actual_opposite_products_in_small_characteristics() {
    for (q, values, axis, partial) in [
        (2, [0, 0, 0, 0, 0, 1, 1], "x", 1),
        (2, [0, 0, 1, 0, 0, 0, 0], "y", 1),
        (3, [0, 0, 0, 1, 0, 0, 0], "x", 2),
        (3, [0, 0, 0, 0, 1, 0, 1], "y", 2),
    ] {
        let mut model = Model::finite(q, values);
        let branch = model.finite_branch(q, axis, partial);
        model.certify(&branch, "(#pt-refl #pt-nat #pt-zero)");
        let proof = model.call(
            "point-ideal-product-nonsingular-opposite",
            &[&model.prime_field(q), &use_name("fixture-nonsingular")],
        );
        check(&model.prelude, &model.product_goal(), &proof, true);
    }
}

#[test]
fn actual_jacobian_partials_and_opposite_ordinates_keep_characteristic_dependence() {
    for (q, values, expected) in [
        (2, [0, 0, 0, 0, 0, 1, 1], [1, 0, 1]),
        (2, [0, 0, 1, 0, 0, 0, 0], [0, 1, 1]),
        (3, [0, 0, 0, 1, 0, 0, 0], [2, 0, 0]),
        (3, [0, 0, 0, 0, 1, 0, 1], [0, 2, 2]),
    ] {
        let model = Model::finite(q, values);
        for (value, expected) in [
            model.partial("x"),
            model.partial("y"),
            model.call("point-ideal-product-negative-y", &[]),
        ]
        .into_iter()
        .zip(expected)
        {
            let actual = format!("(#pt-project finite-residue 0 {value})");
            check(
                &model.prelude,
                &format!("(#pt-eq #pt-nat {actual} {})", n(expected)),
                &format!("(#pt-refl #pt-nat {})", n(expected)),
                true,
            );
        }
    }
}

#[test]
fn rational_field_proves_an_actual_opposite_product() {
    let mut model = Model::rational([0, 0, 1, 0, 0, 0, 0]);
    model.prelude += &equivalent_nonzero_bridge();
    let one = &model.args[4];
    let one_nonzero = format!(
        "(#pt-lambda ((zero-evidence {})) (#pt-app {} zero-evidence))",
        model.equal(one, &model.zero()),
        app("successor-not-zero", &[&n(0)])
    );
    let value_equation = app(
        "point-ideal-product-origin-y",
        &model.args[..7]
            .iter()
            .map(String::as_str)
            .collect::<Vec<_>>(),
    );
    let evidence = app(
        "fixture-equivalent-nonzero",
        &[
            &model.carrier,
            &model.ring,
            &model.partial("y"),
            one,
            &value_equation,
            &one_nonzero,
        ],
    );
    model.prelude += &theorem(
        "fixture-rational-partial-nonzero",
        &model.nonzero(&model.partial("y")),
        &evidence,
    );
    let branch = format!(
        "(#pt-construct disjunction () ({} {}) right ({}))",
        model.nonzero(&model.partial("x")),
        model.nonzero(&model.partial("y")),
        use_name("fixture-rational-partial-nonzero")
    );
    model.certify_equation_and_jacobian(&branch, "(#pt-refl #pt-nat #pt-zero)");
    model.prelude += &definition(
        "fixture-rational-product-proposition",
        "#pt-prop",
        &model.product_goal(),
    );
    check(
        &model.prelude,
        &use_name("fixture-rational-product-proposition"),
        &model.call(
            "point-ideal-product-weierstrass-opposite",
            &[
                &use_name("fixture-curve-equation"),
                &use_name("point-ideal-product-rational-field"),
                &use_name("fixture-jacobian"),
            ],
        ),
        true,
    );
}

fn same_values(
    q: usize,
    root: usize,
    left: &[usize],
    right: &[usize],
    expected: usize,
    good: bool,
) {
    let ty = app("finite-residue", &[&n(q)]);
    let ring = app("finite-residue-ring", &[&n(q), &positive(q)]);
    let p = |xs: &[usize]| list(&ty, &xs.iter().map(|&x| residue(q, x)).collect::<Vec<_>>());
    let left = p(left);
    let right = p(right);
    let empty = p(&[]);
    let root = residue(q, root);
    let l = app("finite-list", &[&ty]);
    let pr = app("ring-polynomial-structure", &[&ty, &ring]);
    let qr = app("quadratic-ring-structure", &[&l, &pr, &empty, &empty]);
    let qt = app("quadratic-element", &[&l]);
    let ideal = |y: &str| {
        app(
            "coordinate-point-ideal-XY",
            &[&ty, &ring, &empty, &empty, &root, y],
        )
    };
    let goal = app(
        "ring-ideal-equal",
        &[&qt, &qr, &ideal(&left), &ideal(&right)],
    );
    let equation = app("ring-reflexive", &[&ty, &ring, &residue(q, expected)]);
    let proof = app(
        "point-ideal-product-same-value-ideals",
        &[&ty, &ring, &empty, &empty, &root, &left, &right, &equation],
    );
    check("", &goal, &proof, good);
}

#[test]
fn equivalent_y_generators_need_neither_a_field_nor_a_curve_premise() {
    same_values(3, 1, &[1, 1], &[2], 2, true);
    same_values(6, 2, &[2, 2], &[], 0, true);
}

#[test]
fn differing_y_values_cannot_forge_an_ideal_generator_change() {
    same_values(3, 1, &[1, 1], &[1], 2, false);
}

#[test]
fn singular_points_do_not_supply_a_nonsingular_certificate() {
    let mut model = Model::finite(2, [0, 0, 0, 0, 0, 0, 0]);
    // Intentionally claim the zero X-partial is one; the kernel must reject
    // the equality argument, not time out or fail to resolve a fixture symbol.
    let branch = model.finite_branch(2, "x", 1);
    model.certify(&branch, "(#pt-refl #pt-nat #pt-zero)");
    check(
        &model.prelude,
        "(#pt-eq #pt-nat #pt-zero #pt-zero)",
        "(#pt-refl #pt-nat #pt-zero)",
        false,
    );
}

#[test]
fn a_false_curve_equation_cannot_build_a_point_certificate() {
    let model = Model::finite(2, [0, 0, 0, 0, 0, 0, 1]);
    check(
        &model.prelude,
        &model.equal(&model.curve, &model.zero()),
        "(#pt-refl #pt-nat #pt-zero)",
        false,
    );
}

#[test]
fn a_zero_inverse_does_not_make_the_x_partial_a_unit() {
    let mut model = Model::finite(2, [0, 0, 0, 0, 0, 1, 1]);
    let branch = model.finite_branch(2, "x", 1);
    model.certify(&branch, "(#pt-refl #pt-nat #pt-zero)");
    let bad = model.scalar("ring-multiply", &[&model.partial("x"), &model.zero()]);
    check(
        &model.prelude,
        &model.equal(&bad, &model.scalar("ring-one", &[])),
        "(#pt-refl #pt-nat #pt-zero)",
        false,
    );
}

#[test]
fn composite_residues_cannot_reuse_prime_two_as_field_evidence() {
    let ty = app("finite-residue", &[&n(6)]);
    let ring = app("finite-residue-ring", &[&n(6), &positive(6)]);
    let field = app("point-ideal-product-field-data", &[&ty, &ring]);
    let bad = app(
        "point-ideal-product-prime-field",
        &[&n(6), &positive(6), &use_name("prime-two")],
    );
    let prelude = definition("fixture-composite-field", &field, &bad);
    check(
        &prelude,
        "(#pt-eq #pt-nat #pt-zero #pt-zero)",
        "(#pt-refl #pt-nat #pt-zero)",
        false,
    );
}

fn inverse_statement(ty: &str, ring: &str, value: &str) -> String {
    let product = app("ring-multiply", &[ty, ring, value, "inverse"]);
    let one = app("ring-one", &[ty, ring]);
    let equation = app("ring-equal", &[ty, ring, &product, &one]);
    format!("(#pt-app (#pt-use exists (0)) {ty} (#pt-lambda ((inverse {ty})) {equation}))")
}

#[test]
fn prime_field_inverse_is_backed_by_the_actual_modular_computation() {
    let q = 3;
    let ty = app("finite-residue", &[&n(q)]);
    let ring = app("finite-residue-ring", &[&n(q), &positive(q)]);
    let value = residue(q, 2);
    let field = app(
        "point-ideal-product-prime-field",
        &[&n(q), &positive(q), &use_name("prime-three")],
    );
    let nonzero = app(
        "fixture-nonzero-from-value",
        &[
            &n(q),
            &positive(q),
            &value,
            &n(1),
            "(#pt-refl #pt-nat (#pt-numeral 2))",
        ],
    );
    check(
        &finite_nonzero_bridge(),
        &inverse_statement(&ty, &ring, &value),
        &app(
            "point-ideal-product-field-inverse",
            &[&ty, &ring, &field, &value, &nonzero],
        ),
        true,
    );
    let inverse = app("finite-residue-inverse", &[&n(q), &positive(q), &value]);
    check(
        "",
        &format!(
            "(#pt-eq #pt-nat (#pt-project finite-residue 0 {inverse}) {})",
            n(2)
        ),
        &format!("(#pt-refl #pt-nat {})", n(2)),
        true,
    );
}

#[test]
fn rational_field_accepts_a_noncanonical_nonzero_fraction() {
    let ty = use_name("rational");
    let ring = use_name("rational-ring-structure");
    let numerator = app("integer-of-natural", &[&n(2)]);
    let denominator_nonzero = app("successor-not-zero", &[&n(3)]);
    let value = format!(
        "(#pt-construct rational () () fraction ({numerator} {} {denominator_nonzero}))",
        n(4)
    );
    let numerator_nonzero = app(
        "integer-natural-embedding-nonzero",
        &[&n(2), &app("successor-not-zero", &[&n(1)])],
    );
    let nonzero = app("rational-fraction-nonzero", &[&value, &numerator_nonzero]);
    let proof = app(
        "point-ideal-product-field-inverse",
        &[
            &ty,
            &ring,
            &use_name("point-ideal-product-rational-field"),
            &value,
            &nonzero,
        ],
    );
    check("", &inverse_statement(&ty, &ring, &value), &proof, true);
}

#[test]
fn actual_coordinate_generators_are_nonzero_in_both_small_characteristics() {
    for q in [2, 3] {
        let model = Model::finite(q, [0, 0, 0, 0, 0, 0, 0]);
        let l = app("finite-list", &[&model.carrier]);
        let pr = model.scalar("ring-polynomial-structure", &[]);
        let zero = app("quadratic-zero", &[&l, &pr]);
        for axis in ["X", "Y"] {
            let generator = if axis == "X" {
                model.scalar("coordinate-point-ideal-X-class", &[&model.args[7]])
            } else {
                model.scalar(
                    "coordinate-point-ideal-Y-class",
                    &[&list(&model.carrier, &[model.args[8].clone()])],
                )
            };
            let equation = app("quadratic-equal", &[&l, &pr, &generator, &zero]);
            let proof = model.call(
                &format!("point-ideal-product-{axis}-nonzero"),
                &[&model.prime_field(q)],
            );
            check(&model.prelude, &negate(&equation), &proof, true);
        }
    }
}
