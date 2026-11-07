//! Exhaustive point enumeration, cardinality coherence and signed trace controls.
use lim::{
    check_theorem_details_from_path_with_config, CompileConfig, DiagnosticCode, ProofBudget,
};
use std::{
    collections::HashSet,
    fs,
    path::Path,
    sync::atomic::{AtomicUsize, Ordering},
};

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
fn pos(q: usize) -> String {
    term("zero-less-successor", &[&n(q - 1)])
}
fn integer(p: usize, m: usize) -> String {
    format!(
        "(#pt-construct integer () () difference ({} {}))",
        n(p),
        n(m)
    )
}
fn signed(x: i32) -> String {
    integer(x.max(0) as usize, (-x).max(0) as usize)
}
fn list_ty() -> String {
    term("finite-list", &["#pt-nat"])
}
fn list(xs: &[usize]) -> String {
    xs.iter().rev().fold(
        "(#pt-construct finite-list () (#pt-nat) nil ())".to_owned(),
        |tail, x| {
            format!(
                "(#pt-construct finite-list () (#pt-nat) cons ({} {tail}))",
                n(*x)
            )
        },
    )
}
fn member(x: &str, xs: &str) -> String {
    term("finite-list-member", &["#pt-nat", x, xs])
}
fn nodup(xs: &str) -> String {
    term("finite-list-no-duplicates", &["#pt-nat", xs])
}
fn left(p: &str, q: &str, h: &str) -> String {
    term("disjunction-left", &[p, q, h])
}
fn right(p: &str, q: &str, h: &str) -> String {
    term("disjunction-right", &[p, q, h])
}
fn nil_not_member(x: &str) -> String {
    format!(
        "(#pt-lambda ((impossible {})) impossible)",
        member(x, &list(&[]))
    )
}
fn distinct_two(a: usize, b: usize) -> String {
    assert!((a == 0 && b == 1) || (a == 1 && b == 0));
    let a = n(a);
    let b = n(b);
    let equality = eq(&a, &b);
    let denied = if a == n(1) {
        "collision".to_owned()
    } else {
        format!("(#pt-app (#pt-use symmetry (0)) #pt-nat {a} {b} collision)")
    };
    let contradiction = format!(
        "(#pt-app {} {denied})",
        term("successor-not-zero", &[&n(0)])
    );
    let denied_eq = format!("(#pt-lambda ((collision {equality})) {contradiction})");
    let empty = format!("(#pt-lambda ((empty #pt-false)) empty)");
    let proof = format!(
        "(#pt-lambda ((membership {})) {})",
        member(&a, &list(&[if b == n(1) { 1 } else { 0 }])),
        term(
            "disjunction-eliminate",
            &[
                &equality,
                "#pt-false",
                "#pt-false",
                &denied_eq,
                &empty,
                "membership"
            ]
        )
    );
    let tail = list(&[if b == n(1) { 1 } else { 0 }]);
    let tail_nd = term(
        "finite-list-cons-no-duplicates",
        &[
            "#pt-nat",
            &b,
            &list(&[]),
            &nil_not_member(&b),
            &term("finite-list-nil-no-duplicates", &["#pt-nat"]),
        ],
    );
    term(
        "finite-list-cons-no-duplicates",
        &["#pt-nat", &a, &tail, &proof, &tail_nd],
    )
}
fn swap_inclusion(a: usize, b: usize) -> String {
    let source = list(&[a, b]);
    let target = list(&[b, a]);
    let x = "candidate";
    let xa = eq(x, &n(a));
    let xb = eq(x, &n(b));
    let goal = member(x, &target);
    let branch_a = format!(
        "(#pt-lambda ((at-first {xa})) {})",
        right(
            &xb,
            &member(x, &list(&[a])),
            &left(&xa, "#pt-false", "at-first")
        )
    );
    let branch_b = format!(
        "(#pt-lambda ((at-second {xb})) {})",
        left(&xb, &member(x, &list(&[a])), "at-second")
    );
    let empty = format!(
        "(#pt-lambda ((empty #pt-false)) {})",
        term("false-elimination", &[&goal, "empty"])
    );
    let remaining = format!(
        "(#pt-lambda ((in-tail {})) {})",
        member(x, &list(&[b])),
        term(
            "disjunction-eliminate",
            &[&xb, "#pt-false", &goal, &branch_b, &empty, "in-tail"]
        )
    );
    format!(
        "(#pt-lambda ((candidate #pt-nat) (membership {})) {})",
        member(x, &source),
        term(
            "disjunction-eliminate",
            &[
                &xa,
                &member(x, &list(&[b])),
                &goal,
                &branch_a,
                &remaining,
                "membership"
            ]
        )
    )
}
fn residue(q: usize, x: usize) -> String {
    assert!(x < q);
    let bound=format!("(#pt-construct exists (0) (#pt-nat (#pt-lambda ((gap #pt-nat)) (#pt-eq #pt-nat {} (#pt-app (#pt-use add ()) (#pt-succ {}) gap)))) introduce ({} {}))",n(q),n(x),n(q-x-1),refl(q));
    format!(
        "(#pt-construct finite-residue () ({}) representative ({} {bound}))",
        n(q),
        n(x)
    )
}
fn curve(q: usize, cs: [usize; 5]) -> String {
    format!(
        "(#pt-construct finite-weierstrass-curve () ({}) coefficients ({}))",
        n(q),
        cs.into_iter()
            .map(|x| residue(q, x))
            .collect::<Vec<_>>()
            .join(" ")
    )
}
fn integral_curve(cs: [i32; 5]) -> String {
    format!(
        "(#pt-construct integer-weierstrass-curve () () coefficients ({}))",
        cs.into_iter().map(signed).collect::<Vec<_>>().join(" ")
    )
}
fn fixture(prelude: &str, statement: &str, proof: &str, valid: bool) {
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let directory = std::env::temp_dir().join(format!(
        "lim-finite-enumeration-{}-{}",
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
    let mut modules: Vec<_> = fs::read_dir(&root)
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| {
            p.extension().is_some_and(|s| s == "lim")
                && (p
                    .file_stem()
                    .unwrap()
                    .to_str()
                    .unwrap()
                    .starts_with("finite-")
                    || [
                        "equality",
                        "logical-connectives",
                        "logic-exists",
                        "logic-false",
                        "natural-discrete-order",
                        "natural-decision",
                        "natural-nonzero",
                        "natural-prime-two",
                        "natural-prime-three",
                        "integer-defs",
                        "integer-weierstrass-defs",
                    ]
                    .contains(&p.file_stem().unwrap().to_str().unwrap()))
        })
        .collect();
    modules.push(root.join("../fermat_statement.lim"));
    modules.sort();
    for module in modules {
        for line in fs::read_to_string(&module).unwrap().lines() {
            for prefix in ["(#theorem ", "(#math-definition ", "(#math-inductive "] {
                if let Some(tail) = line.strip_prefix(prefix) {
                    let name = tail.split_whitespace().next().unwrap();
                    if referenced.contains(name) {
                        source
                            .push_str(&format!("(#alias {name} = {}::{name})\n", module.display()));
                    }
                }
            }
        }
    }
    source.push_str(prelude);
    source.push_str(&format!("(#theorem observed-enumeration (#universes) (#parameters) (#statement {statement}) (#proof {proof}))"));
    fs::write(&path, &source).unwrap();
    let mut config = CompileConfig::default();
    let budget = ProofBudget::default();
    config.set_proof_budget(
        ProofBudget::new(budget.work(), budget.phase_bytes(), 1024 * 1024 * 1024).unwrap(),
    );
    let expected = format!(
        "{}::observed-enumeration",
        path.canonicalize().unwrap().display()
    );
    let result = check_theorem_details_from_path_with_config(
        &source,
        &path,
        &config,
        "observed-enumeration",
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
fn observe_points(actual: &str, expected: usize, valid: bool) {
    observe(actual, expected, valid);
}

#[test]
fn tabulation_computes_the_actual_prefix_and_rejects_the_wrong_length() {
    let identity = "(#pt-lambda ((index #pt-nat)) index)";
    for count in [0, 1, 2, 4] {
        let tab = term("finite-list-tabulate", &["#pt-nat", identity, &n(count)]);
        observe(&term("finite-list-length", &["#pt-nat", &tab]), count, true);
    }
    let tab = term("finite-list-tabulate", &["#pt-nat", identity, &n(4)]);
    observe(&term("finite-list-length", &["#pt-nat", &tab]), 3, false);
}
#[test]
fn residue_enumerations_have_the_modulus_as_size() {
    for q in [1, 2, 3, 5] {
        let e = term("finite-residue-enumeration", &[&n(q), &pos(q)]);
        let ty = term("finite-residue", &[&n(q)]);
        observe(&term("finite-enumeration-size", &[&ty, &e]), q, true);
    }
}
#[test]
fn generic_list_cardinality_is_independent_of_order() {
    let xs = list(&[0, 1]);
    let ys = list(&[1, 0]);
    let hx = distinct_two(0, 1);
    let hy = distinct_two(1, 0);
    let proof = term(
        "finite-list-cardinality-equal",
        &[
            "#pt-nat",
            &xs,
            &ys,
            &hx,
            &hy,
            &swap_inclusion(0, 1),
            &swap_inclusion(1, 0),
        ],
    );
    fixture(
        "",
        &eq(
            &term("finite-list-length", &["#pt-nat", &xs]),
            &term("finite-list-length", &["#pt-nat", &ys]),
        ),
        &proof,
        true,
    );
    fixture(
        "",
        &eq(&term("finite-list-length", &["#pt-nat", &xs]), &n(3)),
        &proof,
        false,
    );
}
#[test]
fn equal_members_without_duplicate_freedom_do_not_determine_length() {
    let xs = list(&[0, 1]);
    let ys = list(&[0, 0, 1]);
    let proof = term(
        "finite-list-cardinality-equal",
        &[
            "#pt-nat",
            &xs,
            &ys,
            &distinct_two(0, 1),
            &distinct_two(1, 0),
            &swap_inclusion(0, 1),
            &swap_inclusion(1, 0),
        ],
    );
    fixture(
        "",
        &eq(
            &term("finite-list-length", &["#pt-nat", &xs]),
            &term("finite-list-length", &["#pt-nat", &ys]),
        ),
        &proof,
        false,
    );
}
#[test]
fn duplicate_freedom_certificates_are_checked() {
    fixture("", &nodup(&list(&[0, 1])), &distinct_two(0, 1), true);
    fixture("", &nodup(&list(&[0, 0, 1])), &distinct_two(0, 1), false);
}
#[test]
fn selection_retains_real_evidence_and_does_not_silently_deduplicate() {
    let pred = "(#pt-lambda ((value #pt-nat)) (#pt-eq #pt-nat value #pt-zero))";
    let chooser =
        "(#pt-lambda ((value #pt-nat)) (#pt-app (#pt-use decide-equality ()) value #pt-zero))";
    let selected = term(
        "finite-list-select",
        &["#pt-nat", pred, chooser, &list(&[0, 1, 0])],
    );
    let ty = term("finite-subtype", &["#pt-nat", pred]);
    observe(&term("finite-list-length", &[&ty, &selected]), 2, true);
    let forged = format!(
        "(#pt-construct finite-subtype () (#pt-nat {pred}) select ({} {}))",
        n(1),
        refl(0)
    );
    observe(
        &format!("(#pt-project finite-subtype 0 {forged})"),
        1,
        false,
    );
}
#[test]
fn a_forged_enumeration_cannot_ignore_coverage() {
    let xs = list(&[0, 1]);
    let head = term("finite-list-member-head", &["#pt-nat", &n(0), &list(&[1])]);
    let coverage = format!("(#pt-lambda ((arbitrary #pt-nat)) {head})");
    let fake = format!(
        "(#pt-construct finite-enumeration () (#pt-nat) enumerate ({xs} {} {coverage}))",
        distinct_two(0, 1)
    );
    observe(
        &term("finite-enumeration-size", &["#pt-nat", &fake]),
        2,
        false,
    );
}
#[test]
fn erase_length_requires_a_real_single_occurrence_deletion() {
    let source = list(&[0, 1]);
    let remaining = list(&[1]);
    let head_case = term(
        "conjunction-introduce",
        &[
            &eq(&n(0), &n(0)),
            &format!("(#pt-eq {} {remaining} {remaining})", list_ty()),
            &refl(0),
            &format!("(#pt-refl {} {remaining})", list_ty()),
        ],
    );
    let tail_pred=format!("(#pt-app (#pt-use exists (0)) {} (#pt-lambda ((earlier {})) (#pt-app (#pt-use conjunction ()) (#pt-app (#pt-use finite-list-erases ()) #pt-nat {} {} earlier) (#pt-eq {} {remaining} (#pt-construct finite-list () (#pt-nat) cons ({} earlier))))))",list_ty(),list_ty(),n(0),remaining,list_ty(),n(0));
    let relation = left(
        &term(
            "conjunction",
            &[
                &eq(&n(0), &n(0)),
                &format!("(#pt-eq {} {remaining} {remaining})", list_ty()),
            ],
        ),
        &tail_pred,
        &head_case,
    );
    let proof = term(
        "finite-list-erasure-length",
        &["#pt-nat", &n(0), &source, &remaining, &relation],
    );
    fixture("", &eq(&n(2), &n(2)), &proof, true);
    let bad = term(
        "finite-list-erasure-length",
        &["#pt-nat", &n(0), &source, &list(&[]), &relation],
    );
    fixture("", &eq(&n(2), &n(1)), &bad, false);
}
#[test]
fn coordinate_space_is_a_real_cartesian_product() {
    for q in [1, 2, 3] {
        let ty = term(
            "finite-pair",
            &[
                &term("finite-residue", &[&n(q)]),
                &term("finite-residue", &[&n(q)]),
            ],
        );
        let space = term("finite-coordinate-space", &[&n(q), &pos(q)]);
        observe(&term("finite-list-length", &[&ty, &space]), q * q, true);
    }
}
#[test]
fn unit_modulus_counts_only_infinity() {
    let w = curve(1, [0, 0, 0, 0, 0]);
    observe(
        &term("finite-weierstrass-card", &[&n(1), &pos(1), &w]),
        1,
        true,
    );
}
#[test]
fn singular_solutions_are_excluded_but_infinity_is_counted_once() {
    for (q, cs, expected) in [
        (2, [0, 0, 0, 0, 0], 2),
        (2, [0, 0, 0, 0, 1], 2),
        (2, [0, 0, 1, 0, 0], 3),
        (3, [0, 0, 0, 0, 1], 3),
    ] {
        let actual = term("finite-weierstrass-card", &[&n(q), &pos(q), &curve(q, cs)]);
        observe_points(&actual, expected, true);
    }
    let actual = term(
        "finite-weierstrass-card",
        &[&n(2), &pos(2), &curve(2, [0, 0, 0, 0, 0])],
    );
    observe_points(&actual, 3, false);
}
#[test]
fn frobenius_trace_is_signed_and_can_be_negative() {
    let iw = integral_curve([0, 0, 0, -1, 1]);
    let actual = term("finite-weierstrass-ap-of-model", &[&n(3), &pos(3), &iw]);
    fixture(
        "",
        &term("integer-equal", &[&actual, &signed(-3)]),
        &refl(7),
        true,
    );
    fixture(
        "",
        &term("integer-equal", &[&actual, &signed(0)]),
        &refl(4),
        false,
    );
}
#[test]
fn prime_api_requires_the_actual_prime_evidence() {
    let iw = integral_curve([0, 0, 0, 0, 0]);
    let actual = term(
        "finite-prime-ap-of-model",
        &[&n(2), &term("prime-two", &[]), &iw],
    );
    fixture(
        "",
        &term("integer-equal", &[&actual, &signed(1)]),
        &refl(3),
        true,
    );
    let actual = term(
        "finite-prime-ap-of-model",
        &[&n(1), &term("prime-two", &[]), &iw],
    );
    fixture(
        "",
        &term("integer-equal", &[&actual, &signed(1)]),
        &refl(2),
        false,
    );
}
#[test]
fn trace_independence_checks_both_enumeration_carriers() {
    let q = 2;
    let w = curve(q, [0, 0, 0, 0, 0]);
    let fe = term("finite-residue-enumeration", &[&n(q), &pos(q)]);
    let pe = term(
        "finite-weierstrass-point-enumeration",
        &[&n(q), &pos(q), &w],
    );
    let proof = term(
        "finite-weierstrass-trace-enumeration-independent",
        &[&n(q), &pos(q), &w, &fe, &pe],
    );
    let actual = term(
        "finite-weierstrass-trace-of-frobenius",
        &[&n(q), &pos(q), &w],
    );
    fixture(
        "",
        &term("integer-equal", &[&integer(3, 2), &actual]),
        &proof,
        true,
    );
    let bad_fe = term("finite-residue-enumeration", &[&n(1), &pos(1)]);
    let proof = term(
        "finite-weierstrass-trace-enumeration-independent",
        &[&n(q), &pos(q), &w, &bad_fe, &pe],
    );
    fixture(
        "",
        &term("integer-equal", &[&integer(3, 2), &actual]),
        &proof,
        false,
    );
}
