//! Actual ideal membership, witnesses, product laws, and mathematical rejection controls.
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
    "ring-ideal-data",
    "ring-ideal-equivalence",
    "ring-ideal-zero-unit",
    "ring-ideal-expression",
    "ring-ideal-span-construction",
    "ring-ideal-span-universal",
    "ring-ideal-principal",
    "ring-ideal-principal-universal",
    "ring-ideal-sum",
    "ring-ideal-sum-universal",
    "ring-ideal-pair",
    "ring-ideal-pair-span",
    "ring-ideal-pair-generator-change",
    "ring-ideal-product",
    "ring-ideal-product-basic-laws",
    "ring-ideal-colon-element",
    "ring-ideal-colon-factorization",
    "ring-ideal-operation-congruence",
    "ring-ideal-product-associative-inclusion",
    "ring-ideal-product-associative",
    "ring-ideal-product-sum-colon",
    "ring-ideal-product-distribute-first-inclusion",
    "ring-ideal-product-distribute-first",
    "ring-ideal-product-distributive",
    "ring-ideal-product-zero-unit",
    "ring-ideal-principal-product-reorder",
    "ring-ideal-principal-product-inclusion",
    "ring-ideal-principal-product",
    "ring-ideal-principal-pair-product",
    "ring-ideal-pair-product",
    "ring-ideal-pair-bezout-top",
    "coordinate-point-ideal-data",
    "coordinate-point-ideal-membership",
    "coordinate-point-ideal-product-expansion",
    "commutative-ring-data",
    "commutative-ring-elementary-laws",
    "commutative-ring-sign-laws",
    "finite-residue-defs",
    "finite-residue-ring-structure",
    "natural-discrete-order",
    "natural-nonzero",
    "logical-connectives",
    "logic-exists",
    "finite-list-defs",
    "ring-polynomial-data",
    "../fermat_statement",
];

fn check(prelude: &str, statement: &str, proof: &str, good: bool) {
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let dir = std::env::temp_dir().join(format!(
        "lim-ideal-{}-{}",
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
    source.push_str(&format!("(#theorem observed-ideal (#universes) (#parameters) (#statement {statement}) (#proof {proof}))"));
    fs::write(&path, &source).unwrap();
    let mut config = CompileConfig::default();
    let d = ProofBudget::default();
    let total = 1024 * 1024 * 1024;
    config.set_proof_budget(ProofBudget::new(d.work(), d.phase_bytes(), total).unwrap());
    let expected = format!("{}::observed-ideal", path.canonicalize().unwrap().display());
    let result =
        check_theorem_details_from_path_with_config(&source, &path, &config, "observed-ideal");
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

fn op(q: usize, name: &str, args: &[&str]) -> String {
    let ty = carrier(q);
    let structure = ring(q);
    let mut all = vec![ty.as_str(), structure.as_str()];
    all.extend_from_slice(args);
    app(&format!("ring-{name}"), &all)
}

fn ideal(q: usize, name: &str, args: &[&str]) -> String {
    op(q, &format!("ideal-{name}"), args)
}

fn principal(q: usize, x: usize) -> String {
    ideal(q, "principal", &[&residue(q, x)])
}

fn pair(q: usize, x: usize, y: usize) -> String {
    ideal(q, "pair", &[&residue(q, x), &residue(q, y)])
}

fn witness(q: usize, generator: usize, value: usize, coefficient: usize) -> String {
    ideal(
        q,
        "principal-introduce",
        &[
            &residue(q, generator),
            &residue(q, value),
            &residue(q, coefficient),
            &op(q, "reflexive", &[&residue(q, value)]),
        ],
    )
}

fn assert_ideal_eq(q: usize, left: &str, right: &str, proof: &str) {
    check("", &ideal(q, "equal", &[left, right]), proof, true);
}

#[test]
fn principal_witnesses_cover_units_zero_divisors_and_the_trivial_ring() {
    for (q, g, value, c) in [(6, 2, 4, 2), (8, 2, 6, 3), (1, 0, 0, 0), (5, 2, 1, 3)] {
        check(
            "",
            &ideal(q, "member", &[&principal(q, g), &residue(q, value)]),
            &witness(q, g, value, c),
            true,
        );
    }
}

#[test]
fn two_generator_membership_has_actual_signed_coefficient_witnesses() {
    for (q, a, b, value, c, d) in [(6, 2, 3, 1, 2, 5), (6, 2, 4, 2, 1, 0), (1, 0, 0, 0, 0, 0)] {
        let proof = ideal(
            q,
            "pair-introduce",
            &[
                &residue(q, a),
                &residue(q, b),
                &residue(q, value),
                &residue(q, c),
                &residue(q, d),
                &op(q, "reflexive", &[&residue(q, value)]),
            ],
        );
        check(
            "",
            &ideal(q, "member", &[&pair(q, a, b), &residue(q, value)]),
            &proof,
            true,
        );
    }
}

#[test]
fn sums_retain_the_actual_input_members_and_sum_equation() {
    let q = 6;
    let left = principal(q, 2);
    let right = principal(q, 3);
    let proof = ideal(
        q,
        "sum-introduce",
        &[
            &left,
            &right,
            &residue(q, 1),
            &residue(q, 4),
            &residue(q, 3),
            &witness(q, 2, 4, 2),
            &witness(q, 3, 3, 1),
            &op(q, "reflexive", &[&residue(q, 1)]),
        ],
    );
    check(
        "",
        &ideal(
            q,
            "member",
            &[&ideal(q, "sum", &[&left, &right]), &residue(q, 1)],
        ),
        &proof,
        true,
    );
}

#[test]
fn generator_change_is_valid_with_nonunits_and_zero_coefficients() {
    for (q, a, b, c) in [(6, 2, 3, 2), (8, 4, 2, 0), (1, 0, 0, 0)] {
        let adjusted = op(
            q,
            "add",
            &[
                &residue(q, b),
                &op(q, "multiply", &[&residue(q, c), &residue(q, a)]),
            ],
        );
        assert_ideal_eq(
            q,
            &ideal(q, "pair", &[&residue(q, a), &adjusted]),
            &pair(q, a, b),
            &ideal(
                q,
                "pair-add-multiple",
                &[&residue(q, a), &residue(q, b), &residue(q, c)],
            ),
        );
    }
}

#[test]
fn principal_products_include_zero_divisors_and_nonzero_square_products() {
    for (q, a, b) in [(6, 2, 3), (8, 2, 2), (1, 0, 0)] {
        let result = ideal(
            q,
            "principal",
            &[&op(q, "multiply", &[&residue(q, a), &residue(q, b)])],
        );
        assert_ideal_eq(
            q,
            &ideal(q, "product", &[&principal(q, a), &principal(q, b)]),
            &result,
            &ideal(q, "principal-product", &[&residue(q, a), &residue(q, b)]),
        );
    }
}

#[test]
fn actual_ideal_products_are_associative_and_distribute_over_sums() {
    let q = 6;
    let a = principal(q, 2);
    let b = principal(q, 3);
    let c = ideal(q, "top", &[]);
    assert_ideal_eq(
        q,
        &ideal(q, "product", &[&ideal(q, "product", &[&a, &b]), &c]),
        &ideal(q, "product", &[&a, &ideal(q, "product", &[&b, &c])]),
        &ideal(q, "product-associative", &[&a, &b, &c]),
    );
    assert_ideal_eq(
        q,
        &ideal(q, "product", &[&ideal(q, "sum", &[&a, &b]), &c]),
        &ideal(
            q,
            "sum",
            &[
                &ideal(q, "product", &[&a, &c]),
                &ideal(q, "product", &[&b, &c]),
            ],
        ),
        &ideal(q, "product-distribute-first", &[&a, &b, &c]),
    );
}

#[test]
fn pair_products_expand_to_the_four_actual_ring_products() {
    let q = 6;
    let a = residue(q, 2);
    let b = residue(q, 3);
    let c = residue(q, 4);
    let d = residue(q, 5);
    let result = ideal(
        q,
        "sum",
        &[
            &ideal(
                q,
                "pair",
                &[&op(q, "multiply", &[&a, &c]), &op(q, "multiply", &[&a, &d])],
            ),
            &ideal(
                q,
                "pair",
                &[&op(q, "multiply", &[&b, &c]), &op(q, "multiply", &[&b, &d])],
            ),
        ],
    );
    assert_ideal_eq(
        q,
        &ideal(q, "product", &[&pair(q, 2, 3), &pair(q, 4, 5)]),
        &result,
        &ideal(q, "pair-product", &[&a, &b, &c, &d]),
    );
}

#[test]
fn zero_unit_and_bezout_identities_need_no_integral_domain() {
    for q in [1, 6] {
        let i = principal(q, 0);
        assert_ideal_eq(
            q,
            &ideal(q, "product", &[&i, &ideal(q, "top", &[])]),
            &i,
            &ideal(q, "product-top", &[&i]),
        );
        assert_ideal_eq(
            q,
            &ideal(q, "product", &[&i, &ideal(q, "bottom", &[])]),
            &ideal(q, "bottom", &[]),
            &ideal(q, "product-bottom", &[&i]),
        );
    }
    assert_ideal_eq(
        6,
        &pair(6, 2, 3),
        &ideal(6, "top", &[]),
        &ideal(
            6,
            "pair-bezout-top",
            &[
                &residue(6, 2),
                &residue(6, 3),
                &residue(6, 2),
                &residue(6, 5),
                &op(6, "reflexive", &[&residue(6, 1)]),
            ],
        ),
    );
}

#[test]
fn forged_principal_coefficients_are_mathematical_mismatches() {
    for (q, generator, value, c) in [(6, 2, 1, 1), (8, 4, 2, 1), (8, 4, 2, 0)] {
        check(
            "",
            &ideal(q, "member", &[&principal(q, generator), &residue(q, value)]),
            &witness(q, generator, value, c),
            false,
        );
    }
}

#[test]
fn forged_pair_coefficients_are_rejected_even_when_other_witnesses_exist() {
    for (a, b, value, c, d) in [(2, 3, 1, 0, 0), (2, 4, 1, 1, 0)] {
        let q = 6;
        check(
            "",
            &ideal(q, "member", &[&pair(q, a, b), &residue(q, value)]),
            &ideal(
                q,
                "pair-introduce",
                &[
                    &residue(q, a),
                    &residue(q, b),
                    &residue(q, value),
                    &residue(q, c),
                    &residue(q, d),
                    &op(q, "reflexive", &[&residue(q, value)]),
                ],
            ),
            false,
        );
    }
}

#[test]
fn forged_sum_equations_are_rejected() {
    let q = 6;
    let a = principal(q, 2);
    let b = principal(q, 3);
    check(
        "",
        &ideal(q, "member", &[&ideal(q, "sum", &[&a, &b]), &residue(q, 2)]),
        &ideal(
            q,
            "sum-introduce",
            &[
                &a,
                &b,
                &residue(q, 2),
                &residue(q, 4),
                &residue(q, 3),
                &witness(q, 2, 4, 2),
                &witness(q, 3, 3, 1),
                &op(q, "reflexive", &[&residue(q, 2)]),
            ],
        ),
        false,
    );
}

#[test]
fn an_unused_forged_membership_is_still_checked() {
    let q = 6;
    let statement = ideal(q, "member", &[&principal(q, 2), &residue(q, 1)]);
    let proof = witness(q, 2, 1, 1);
    let prelude = format!("(#theorem unused-invalid-ideal (#universes) (#parameters) (#statement {statement}) (#proof {proof}))");
    check(
        &prelude,
        &eq(&n(0), &n(0)),
        &format!("(#pt-refl #pt-nat {})", n(0)),
        false,
    );
}
