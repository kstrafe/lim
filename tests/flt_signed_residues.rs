//! Signed cast, actual coefficient reduction and nonsingular-point regressions.
use lim::{
    check_theorem_details_from_path_with_config, CompileConfig, DiagnosticCode, ProofBudget,
};
use std::{
    collections::HashSet,
    fs,
    path::Path,
    sync::atomic::{AtomicUsize, Ordering},
};

const MODULES: &[&str] = &[
    "../fermat_statement",
    "logic-exists",
    "natural-order",
    "natural-discrete-order",
    "natural-nonzero",
    "natural-addition",
    "logical-connectives",
    "logical-decision",
    "natural-decision",
    "integer-defs",
    "integer-weierstrass-defs",
    "weierstrass-model-equivalence",
    "finite-residue-defs",
    "finite-residue-operations",
    "finite-residue-congruence",
    "finite-residue-arithmetic-laws",
    "finite-residue-nested-reduction",
    "finite-residue-semiring",
    "finite-residue-negation",
    "finite-residue-congruence-laws",
    "finite-residue-cancellation",
    "finite-residue-additive-rearrangement",
    "finite-residue-multiplicative-signs",
    "finite-residue-differences",
    "finite-residue-difference-congruence",
    "finite-residue-integer-cast",
    "finite-residue-integer-operations",
    "finite-residue-powers",
    "finite-weierstrass-reduction",
    "finite-residue-extensional",
    "finite-weierstrass-equivalence",
    "finite-weierstrass-points",
    "finite-weierstrass-point-congruence",
    "decidable-negation",
    "finite-weierstrass-point-decisions",
    "finite-weierstrass-integer-evaluation",
];
fn term(name: &str, args: &[&str]) -> String {
    let head = format!("(#pt-use {name} ())");
    if args.is_empty() {
        head
    } else {
        format!("(#pt-app {head} {})", args.join(" "))
    }
}
fn n(x: usize) -> String {
    format!("(#pt-numeral {x})")
}
fn eq(x: &str, y: &str) -> String {
    format!("(#pt-eq #pt-nat {x} {y})")
}
fn refl(x: usize) -> String {
    format!("(#pt-refl #pt-nat {})", n(x))
}
fn positive(q: usize) -> String {
    term("zero-less-successor", &[&n(q - 1)])
}
fn integer(p: usize, n_: usize) -> String {
    format!(
        "(#pt-construct integer () () difference ({} {}))",
        n(p),
        n(n_)
    )
}
fn signed(x: i32) -> String {
    integer(x.max(0) as usize, (-x).max(0) as usize)
}
fn cast(q: usize, x: &str) -> String {
    term("finite-residue-of-integer", &[&n(q), &positive(q), x])
}
fn val(x: &str) -> String {
    format!("(#pt-project finite-residue 0 {x})")
}
fn bound(x: usize, q: usize) -> String {
    assert!(x < q);
    format!("(#pt-construct exists (0) (#pt-nat (#pt-lambda ((gap #pt-nat)) (#pt-eq #pt-nat {} (#pt-app (#pt-use add ()) (#pt-succ {}) gap)))) introduce ({} {}))", n(q), n(x), n(q-x-1), refl(q))
}
fn residue(q: usize, x: usize) -> String {
    format!(
        "(#pt-construct finite-residue () ({}) representative ({} {}))",
        n(q),
        n(x),
        bound(x, q)
    )
}
fn curve(q: usize, coefficients: [usize; 5]) -> String {
    format!(
        "(#pt-construct finite-weierstrass-curve () ({}) coefficients ({}))",
        n(q),
        coefficients
            .into_iter()
            .map(|x| residue(q, x))
            .collect::<Vec<_>>()
            .join(" ")
    )
}
fn integer_curve(coefficients: &[String; 5]) -> String {
    format!(
        "(#pt-construct integer-weierstrass-curve () () coefficients ({}))",
        coefficients.join(" ")
    )
}
fn conjunction(xs: &[String]) -> String {
    if xs.len() == 1 {
        xs[0].clone()
    } else {
        term("conjunction", &[&xs[0], &conjunction(&xs[1..])])
    }
}
fn both(xs: &[String], hs: &[String]) -> String {
    if xs.len() == 1 {
        hs[0].clone()
    } else {
        term(
            "conjunction-introduce",
            &[
                &xs[0],
                &conjunction(&xs[1..]),
                &hs[0],
                &both(&xs[1..], &hs[1..]),
            ],
        )
    }
}
fn fixture(prelude: &str, statement: &str, proof: &str, valid: bool) {
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let directory = std::env::temp_dir().join(format!(
        "lim-signed-residue-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir(&directory).unwrap();
    let path = directory.join("probe.lim");
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("theorems/flt");
    let terms = format!("{prelude} {statement} {proof}");
    let referenced: HashSet<_> = terms
        .split(|c: char| c.is_whitespace() || c == '(' || c == ')')
        .collect();
    let mut source = String::new();
    for module in MODULES {
        let module_path = root.join(format!("{module}.lim"));
        for line in fs::read_to_string(&module_path).unwrap().lines() {
            for prefix in ["(#theorem ", "(#math-definition ", "(#math-inductive "] {
                if let Some(tail) = line.strip_prefix(prefix) {
                    let name = tail.split_whitespace().next().unwrap();
                    if referenced.contains(name) {
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
    source.push_str(&format!("(#theorem observed-signed-residue (#universes) (#parameters) (#statement {statement}) (#proof {proof}))"));
    fs::write(&path, &source).unwrap();
    let mut config = CompileConfig::default();
    let budget = ProofBudget::default();
    config.set_proof_budget(
        ProofBudget::new(budget.work(), budget.phase_bytes(), 1024 * 1024 * 1024).unwrap(),
    );
    let expected = format!(
        "{}::observed-signed-residue",
        path.canonicalize().unwrap().display()
    );
    let result = check_theorem_details_from_path_with_config(
        &source,
        &path,
        &config,
        "observed-signed-residue",
    );
    fs::remove_dir_all(directory).unwrap();
    if valid {
        let report = result.unwrap_or_else(|e| panic!("{}", e.message));
        assert_eq!(report.name, expected);
        assert!(report.foundations.is_empty());
    } else {
        let error = result.unwrap_err();
        assert_eq!(error.code, DiagnosticCode::Proof);
        assert!(error.message.contains("mismatch"), "{}", error.message);
    }
}
fn observe(actual: &str, expected: usize, valid: bool) {
    fixture("", &eq(actual, &n(expected)), &refl(expected), valid);
}

#[test]
fn signed_casts_cover_negatives_zero_noncanonical_pairs_and_unit_modulus() {
    for (q, p, m, expected) in [
        (1, 2, 7, 0),
        (2, 0, 1, 1),
        (3, 0, 1, 2),
        (5, 0, 2, 3),
        (5, 2, 5, 2),
        (5, 7, 7, 0),
        (5, 6, 2, 4),
    ] {
        observe(&val(&cast(q, &integer(p, m))), expected, true);
    }
    observe(&val(&cast(5, &signed(-2))), 2, false);
}
#[test]
fn equal_integer_pairs_produce_the_same_residue() {
    let a = integer(0, 2);
    let b = integer(3, 5);
    let proof = term(
        "finite-residue-integer-congruent",
        &[&n(5), &positive(5), &a, &b, &refl(5)],
    );
    fixture(
        "",
        &eq(&val(&cast(5, &a)), &val(&cast(5, &b))),
        &proof,
        true,
    );
    let bad = integer(4, 5);
    let proof = term(
        "finite-residue-integer-congruent",
        &[&n(5), &positive(5), &a, &bad, &refl(5)],
    );
    fixture(
        "",
        &eq(&val(&cast(5, &a)), &val(&cast(5, &bad))),
        &proof,
        false,
    );
}
#[test]
fn signed_addition_multiplication_and_negation_compute_the_expected_residue() {
    let a = signed(-2);
    let b = signed(3);
    for (op, expected) in [("integer-add", 1), ("integer-multiply", 4)] {
        let product = term(op, &[&a, &b]);
        observe(&val(&cast(5, &product)), expected, true);
        observe(&val(&cast(5, &product)), expected + 1, false);
    }
    observe(&val(&cast(5, &term("integer-negate", &[&a]))), 2, true);
}
#[test]
fn signed_power_is_preserved_for_zero_even_and_odd_exponents() {
    for (k, expected) in [(0, 1), (1, 3), (2, 4), (3, 2)] {
        let power = term("integer-power", &[&signed(-2), &n(k)]);
        observe(&val(&cast(5, &power)), expected, true);
    }
    let power = term(
        "finite-residue-power",
        &[&n(5), &positive(5), &residue(5, 3), &n(3)],
    );
    observe(&val(&power), 2, true);
    observe(&val(&power), 3, false);
}
#[test]
fn a_forged_representative_equation_cannot_prove_record_identity() {
    let a = residue(3, 1);
    let b = residue(3, 2);
    let ty = term("finite-residue", &[&n(3)]);
    let proof = term(
        "finite-residue-extensional",
        &[&n(3), &positive(3), &a, &b, &refl(1)],
    );
    let statement = format!("(#pt-eq {ty} {a} {b})");
    fixture("", &statement, &proof, false);
    let proof = term(
        "finite-residue-extensional",
        &[&n(3), &positive(3), &a, &a, &refl(1)],
    );
    fixture("", &format!("(#pt-eq {ty} {a} {a})"), &proof, true);
}
#[test]
fn every_actual_signed_curve_coefficient_is_reduced_in_the_correct_position() {
    let ints = [signed(-1), signed(2), signed(-2), signed(1), signed(0)];
    let iw = integer_curve(&ints);
    let reduced = term("finite-weierstrass-reduction", &[&n(5), &positive(5), &iw]);
    for (i, expected) in [4, 2, 3, 1, 0].into_iter().enumerate() {
        let actual = format!("(#pt-project finite-weierstrass-curve {i} {reduced})");
        observe(&val(&actual), expected, true);
    }
    observe(
        &val(&format!(
            "(#pt-project finite-weierstrass-curve 0 {reduced})"
        )),
        3,
        false,
    );
}
#[test]
fn actual_model_equivalence_preserves_all_reduced_coefficients() {
    let a = [signed(-1), signed(2), signed(-2), signed(1), signed(0)];
    let b = [
        integer(2, 3),
        integer(5, 3),
        integer(1, 3),
        integer(4, 3),
        integer(3, 3),
    ];
    let clauses: Vec<_> = a
        .iter()
        .zip(&b)
        .map(|(x, y)| term("integer-equal", &[x, y]))
        .collect();
    let proofs = [refl(3), refl(5), refl(3), refl(4), refl(3)];
    let certificate = both(&clauses, &proofs);
    let wa = integer_curve(&a);
    let wb = integer_curve(&b);
    let ra = term("finite-weierstrass-reduction", &[&n(5), &positive(5), &wa]);
    let rb = term("finite-weierstrass-reduction", &[&n(5), &positive(5), &wb]);
    let statement = term("finite-weierstrass-equivalent", &[&n(5), &ra, &rb]);
    let proof = term(
        "finite-weierstrass-reduction-congruent",
        &[&n(5), &positive(5), &wa, &wb, &certificate],
    );
    fixture("", &statement, &proof, true);
}

const DECISION_TAG: &str = "(#math-definition decision-tag () (#pt-pi ((proposition #pt-prop) (value (#pt-app (#pt-use decision ()) proposition))) #pt-nat) (#pt-lambda ((proposition #pt-prop) (value (#pt-app (#pt-use decision ()) proposition))) (#pt-induct decision () (proposition) (#pt-lambda ((subject (#pt-app (#pt-use decision ()) proposition))) #pt-nat) ((#pt-lambda ((refutation (#pt-pi ((evidence proposition)) #pt-false))) #pt-zero) (#pt-lambda ((evidence proposition)) (#pt-succ #pt-zero))) value)))";
fn point_decision(
    q: usize,
    coefficients: [usize; 5],
    x: usize,
    y: usize,
    nonsingular: bool,
    expected: usize,
    valid: bool,
) {
    let w = curve(q, coefficients);
    let xx = residue(q, x);
    let yy = residue(q, y);
    let suffix = if nonsingular {
        "nonsingular"
    } else {
        "equation"
    };
    let proposition = term(
        &format!("finite-weierstrass-{suffix}"),
        &[&n(q), &positive(q), &w, &xx, &yy],
    );
    let decision = term(
        &format!("finite-weierstrass-decide-{suffix}"),
        &[&n(q), &positive(q), &w, &xx, &yy],
    );
    let tag = term("decision-tag", &[&proposition, &decision]);
    fixture(
        DECISION_TAG,
        &eq(&tag, &n(expected)),
        &refl(expected),
        valid,
    );
}
#[test]
fn singular_origin_satisfies_the_equation_but_is_not_a_point() {
    point_decision(2, [0, 0, 0, 0, 0], 0, 0, false, 1, true);
    point_decision(2, [0, 0, 0, 0, 0], 0, 0, true, 0, true);
    point_decision(2, [0, 0, 0, 0, 0], 0, 0, true, 1, false);
}
#[test]
fn either_nonzero_partial_derivative_is_sufficient_at_an_actual_solution() {
    point_decision(2, [0, 0, 1, 0, 0], 0, 0, true, 1, true);
    point_decision(2, [0, 0, 0, 1, 0], 0, 0, true, 1, true);
    point_decision(3, [0, 0, 1, 0, 0], 0, 0, true, 1, true);
}
#[test]
fn a_nonzero_derivative_does_not_bypass_the_equation() {
    point_decision(2, [0, 0, 1, 0, 1], 0, 0, true, 0, true);
    point_decision(2, [0, 0, 1, 0, 1], 0, 0, true, 1, false);
}
#[test]
fn characteristic_two_and_three_keep_singular_solutions_out() {
    point_decision(2, [0, 0, 0, 0, 1], 0, 1, false, 1, true);
    point_decision(2, [0, 0, 0, 0, 1], 0, 1, true, 0, true);
    point_decision(2, [0, 0, 0, 0, 1], 1, 0, true, 1, true);
    point_decision(3, [0, 0, 0, 0, 1], 2, 0, false, 1, true);
    point_decision(3, [0, 0, 0, 0, 1], 2, 0, true, 0, true);
    point_decision(3, [0, 0, 0, 0, 1], 0, 1, true, 1, true);
}
#[test]
fn unit_modulus_has_no_nonsingular_affine_coordinate() {
    point_decision(1, [0, 0, 0, 0, 0], 0, 0, false, 1, true);
    point_decision(1, [0, 0, 0, 0, 0], 0, 0, true, 0, true);
}

#[test]
fn additive_cancellation_requires_the_actual_common_addend_equation() {
    let one = residue(5, 1);
    let zero = residue(5, 0);
    let four = residue(5, 4);
    let proof = term(
        "finite-residue-add-cancel-right",
        &[&n(5), &positive(5), &one, &one, &four, &refl(0)],
    );
    fixture("", &eq(&val(&one), &val(&one)), &proof, true);
    let proof = term(
        "finite-residue-add-cancel-right",
        &[&n(5), &positive(5), &one, &zero, &four, &refl(0)],
    );
    fixture("", &eq(&val(&one), &val(&zero)), &proof, false);
}
fn nonsingular_origin_proof(w: &str) -> String {
    let zero = residue(2, 0);
    let args = [n(2), positive(2), w.to_owned(), zero.clone(), zero];
    let refs: Vec<_> = args.iter().map(String::as_str).collect();
    let equation = term("finite-weierstrass-equation", &refs);
    let z = term("finite-residue-zero", &[&n(2), &positive(2)]);
    let dx = term("finite-weierstrass-derivative-x", &refs);
    let dy = term("finite-weierstrass-derivative-y", &refs);
    let no_x = format!("(#pt-pi ((bad {})) #pt-false)", eq(&val(&dx), &val(&z)));
    let no_y = format!("(#pt-pi ((bad {})) #pt-false)", eq(&val(&dy), &val(&z)));
    let either = term("disjunction", &[&no_x, &no_y]);
    let nonzero = term(
        "disjunction-right",
        &[&no_x, &no_y, &term("successor-not-zero", &[&n(0)])],
    );
    term(
        "conjunction-introduce",
        &[&equation, &either, &refl(0), &nonzero],
    )
}
#[test]
fn the_point_at_infinity_exists_even_for_the_zero_equation() {
    for q in [1, 2, 3] {
        let w = curve(q, [0, 0, 0, 0, 0]);
        let ty = term("finite-affine-point", &[&n(q), &positive(q), &w]);
        let infinity = format!(
            "(#pt-construct finite-affine-point () ({} {} {w}) infinity ())",
            n(q),
            positive(q)
        );
        fixture(
            "",
            &format!("(#pt-eq {ty} {infinity} {infinity})"),
            &format!("(#pt-refl {ty} {infinity})"),
            true,
        );
    }
}
#[test]
fn an_affine_point_requires_nonsingularity_and_an_equation_alone_is_rejected() {
    let zero = residue(2, 0);
    let w = curve(2, [0, 0, 1, 0, 0]);
    let ty = term("finite-affine-point", &[&n(2), &positive(2), &w]);
    let point = format!(
        "(#pt-construct finite-affine-point () ({} {} {w}) coordinate ({zero} {zero} {}))",
        n(2),
        positive(2),
        nonsingular_origin_proof(&w)
    );
    fixture(
        "",
        &format!("(#pt-eq {ty} {point} {point})"),
        &format!("(#pt-refl {ty} {point})"),
        true,
    );
    let w = curve(2, [0, 0, 0, 0, 0]);
    let ty = term("finite-affine-point", &[&n(2), &positive(2), &w]);
    let forged = format!(
        "(#pt-construct finite-affine-point () ({} {} {w}) coordinate ({zero} {zero} {}))",
        n(2),
        positive(2),
        refl(0)
    );
    fixture(
        "",
        &format!("(#pt-eq {ty} {forged} {forged})"),
        &format!("(#pt-refl {ty} {forged})"),
        false,
    );
}
#[test]
fn nonsingularity_transfer_cannot_mix_up_models_or_coordinates() {
    let w = curve(2, [0, 0, 1, 0, 0]);
    let singular = curve(2, [0, 0, 0, 0, 0]);
    let zero = residue(2, 0);
    let one = residue(2, 1);
    let model_eq = term("finite-weierstrass-reflexive", &[&n(2), &positive(2), &w]);
    let evidence = nonsingular_origin_proof(&w);
    let target = term(
        "finite-weierstrass-nonsingular",
        &[&n(2), &positive(2), &w, &zero, &zero],
    );
    let proof = term(
        "finite-weierstrass-nonsingular-congruent",
        &[
            &n(2),
            &positive(2),
            &w,
            &w,
            &zero,
            &zero,
            &zero,
            &zero,
            &model_eq,
            &refl(0),
            &refl(0),
            &evidence,
        ],
    );
    fixture("", &target, &proof, true);
    let target = term(
        "finite-weierstrass-nonsingular",
        &[&n(2), &positive(2), &singular, &zero, &zero],
    );
    let proof = term(
        "finite-weierstrass-nonsingular-congruent",
        &[
            &n(2),
            &positive(2),
            &w,
            &singular,
            &zero,
            &zero,
            &zero,
            &zero,
            &model_eq,
            &refl(0),
            &refl(0),
            &evidence,
        ],
    );
    fixture("", &target, &proof, false);
    let target = term(
        "finite-weierstrass-nonsingular",
        &[&n(2), &positive(2), &w, &one, &zero],
    );
    let proof = term(
        "finite-weierstrass-nonsingular-congruent",
        &[
            &n(2),
            &positive(2),
            &w,
            &w,
            &zero,
            &zero,
            &one,
            &zero,
            &model_eq,
            &refl(0),
            &refl(0),
            &evidence,
        ],
    );
    fixture("", &target, &proof, false);
}

#[test]
fn integer_equation_reduction_does_not_claim_to_preserve_nonsingularity() {
    // y^2 = x^3 + 1 has the integer point (0,1). Modulo two its
    // equation still holds, but both partial derivatives vanish there.
    let w = integer_curve(&[signed(0), signed(0), signed(0), signed(0), signed(1)]);
    let ix = signed(0);
    let iy = signed(1);
    let reduced = term("finite-weierstrass-reduction", &[&n(2), &positive(2), &w]);
    let x = cast(2, &ix);
    let y = cast(2, &iy);
    let args = [n(2), positive(2), reduced.clone(), x.clone(), y.clone()];
    let refs: Vec<_> = args.iter().map(String::as_str).collect();
    let statement = term("finite-weierstrass-equation", &refs);
    let proof = term(
        "finite-weierstrass-integer-equation-map",
        &[&n(2), &positive(2), &w, &ix, &iy, &refl(1)],
    );
    fixture("", &statement, &proof, true);
    observe(
        &val(&term("finite-weierstrass-derivative-y", &refs)),
        0,
        true,
    );
    let proposition = term("finite-weierstrass-nonsingular", &refs);
    let decision = term("finite-weierstrass-decide-nonsingular", &refs);
    let tag = term("decision-tag", &[&proposition, &decision]);
    fixture(DECISION_TAG, &eq(&tag, &n(0)), &refl(0), true);
    fixture(DECISION_TAG, &eq(&tag, &n(1)), &refl(1), false);
    let zero_y = cast(2, &signed(0));
    let wrong_statement = term(
        "finite-weierstrass-equation",
        &[&n(2), &positive(2), &reduced, &x, &zero_y],
    );
    let wrong_proof = term(
        "finite-weierstrass-integer-equation-map",
        &[&n(2), &positive(2), &w, &ix, &signed(0), &refl(1)],
    );
    fixture("", &wrong_statement, &wrong_proof, false);
}
