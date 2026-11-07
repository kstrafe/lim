//! Regression checks for the native computed extended Euclidean algorithm.
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
fn signed(x: i32) -> String {
    format!(
        "(#pt-construct integer () () difference ({} {}))",
        n(x.max(0) as usize),
        n((-x).max(0) as usize)
    )
}
fn integer_eq(a: &str, b: &str) -> String {
    app("integer-equal", &[a, b])
}
fn integer_left_reflexivity(a: &str, b: &str) -> String {
    format!(
        "(#pt-refl #pt-nat {})",
        app(
            "add",
            &[
                &format!("(#pt-project integer 0 {a})"),
                &format!("(#pt-project integer 1 {b})")
            ]
        )
    )
}
fn natural_eq(a: &str, b: &str) -> String {
    format!("(#pt-eq #pt-nat {a} {b})")
}
fn record(a: usize, b: usize) -> String {
    app("compute-natural-extended-gcd", &[&n(a), &n(b)])
}
fn projection(index: usize, value: &str) -> String {
    format!("(#pt-project natural-extended-gcd-data {index} {value})")
}

fn check(statement: &str, proof: &str, good: bool) {
    check_with_prelude("", statement, proof, good);
}
fn check_with_prelude(prelude: &str, statement: &str, proof: &str, good: bool) {
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let dir = std::env::temp_dir().join(format!(
        "lim-modular-inverses-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir(&dir).unwrap();
    let path = dir.join("fixture.lim");
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("theorems/flt");
    let aliases = [
        ("natural-extended-gcd-data", "natural-extended-gcd-data.lim"),
        ("compute-natural-extended-gcd", "natural-extended-gcd.lim"),
        ("gcd-spec", "natural-gcd.lim"),
        ("integer-equal", "integer-defs.lim"),
        ("integer", "integer-defs.lim"),
        ("add", "../fermat_statement.lim"),
        ("integer-of-natural", "integer-defs.lim"),
        ("integer-bezout-equation", "integer-bezout-defs.lim"),
        ("natural-data-below", "natural-data-recursion.lim"),
        (
            "natural-data-strong-recursion",
            "natural-data-recursion.lim",
        ),
        ("less-than-successor", "natural-order.lim"),
        ("zero-less-successor", "natural-discrete-order.lim"),
        ("successor-not-zero", "natural-nonzero.lim"),
        ("finite-residue", "finite-residue-defs.lim"),
        ("finite-residue-of-natural", "finite-residue-defs.lim"),
        (
            "finite-residue-of-integer",
            "finite-residue-integer-cast.lim",
        ),
        ("finite-residue-multiply", "finite-residue-operations.lim"),
        ("finite-residue-inverse", "finite-residue-inverses.lim"),
        ("finite-residue-unit-data", "finite-residue-unit-data.lim"),
        ("finite-prime-inverse-product", "finite-prime-inverses.lim"),
        ("prime-two", "natural-prime-two.lim"),
        ("prime-three", "natural-prime-three.lim"),
    ];
    let terms = format!("{prelude} {statement} {proof}");
    let used: HashSet<_> = terms
        .split(|c: char| c.is_whitespace() || c == '(' || c == ')')
        .collect();
    let mut source = String::new();
    for (name, module) in aliases {
        if used.contains(name) {
            source.push_str(&format!(
                "(#alias {name} = {}/{module}::{name})\n",
                root.display()
            ));
        }
    }
    source.push_str(prelude);
    source.push_str(&format!(
        "(#theorem observed (#universes) (#parameters) (#statement {statement}) (#proof {proof}))"
    ));
    fs::write(&path, &source).unwrap();
    let mut config = CompileConfig::default();
    let default = ProofBudget::default();
    config.set_proof_budget(
        ProofBudget::new(default.work(), default.phase_bytes(), 1024 * 1024 * 1024).unwrap(),
    );
    let expected = format!("{}::observed", path.canonicalize().unwrap().display());
    let result = check_theorem_details_from_path_with_config(&source, &path, &config, "observed");
    fs::remove_dir_all(dir).unwrap();
    if good {
        let report = result.unwrap_or_else(|e| panic!("{statement}: {}", e.message));
        assert_eq!(report.name, expected);
        assert!(report.foundations.is_empty());
    } else {
        let error = result.expect_err("forged or mismatched proof unexpectedly checked");
        assert_eq!(error.code, DiagnosticCode::Proof);
        assert!(error.message.contains("mismatch"), "{}", error.message);
    }
}

#[test]
fn gcd_and_signed_coefficients_cover_zero_and_euclidean_cases() {
    for (a, b, g, x, y) in [
        (0, 0, 0, 1, 0),
        (5, 0, 5, 1, 0),
        (0, 5, 5, 0, 1),
        (3, 7, 1, -2, 1),
        (17, 5, 1, -2, 7),
        (30, 12, 6, 1, -2),
    ] {
        let r = record(a, b);
        for (field, expected) in [(0, g)] {
            let v = projection(field, &r);
            check(
                &natural_eq(&v, &n(expected)),
                &format!("(#pt-refl #pt-nat {})", v),
                true,
            );
        }
        for (field, expected) in [(1, x), (2, y)] {
            let v = projection(field, &r);
            let statement = integer_eq(&v, &signed(expected));
            check(
                &statement,
                &integer_left_reflexivity(&v, &signed(expected)),
                true,
            );
        }
    }
}

fn positive(q: usize) -> String {
    assert!(q > 0);
    app("zero-less-successor", &[&n(q - 1)])
}
fn residue(q: usize, input: usize) -> String {
    app(
        "finite-residue-of-natural",
        &[&n(q), &positive(q), &n(input)],
    )
}
fn value(x: &str) -> String {
    format!("(#pt-project finite-residue 0 {x})")
}
fn inverse(q: usize, x: &str) -> String {
    app("finite-residue-inverse", &[&n(q), &positive(q), x])
}
fn product(q: usize, x: &str, y: &str) -> String {
    app("finite-residue-multiply", &[&n(q), &positive(q), x, y])
}
fn observe_number(actual: &str, expected: usize, good: bool) {
    check(
        &natural_eq(actual, &n(expected)),
        &format!("(#pt-refl #pt-nat {actual})"),
        good,
    );
}

#[test]
fn actual_modular_inverses_compute_for_prime_and_composite_moduli() {
    for (q, input, expected) in [
        (1, 4, 0),
        (2, 1, 1),
        (3, 2, 2),
        (5, 2, 3),
        (7, 3, 5),
        (8, 3, 3),
        (8, 2, 1),
    ] {
        let actual = inverse(q, &residue(q, input));
        observe_number(&value(&actual), expected, true);
    }
    observe_number(&value(&inverse(5, &residue(5, 2))), 2, false);
}

#[test]
fn composite_nonunit_product_is_the_gcd_and_cannot_be_claimed_one() {
    let x = residue(8, 2);
    let actual = value(&product(8, &x, &inverse(8, &x)));
    observe_number(&actual, 2, true);
    observe_number(&actual, 1, false);
}

#[test]
fn zero_and_one_inverse_include_unit_modulus() {
    for q in [1, 2, 5, 8] {
        for input in [0, 1] {
            observe_number(&value(&inverse(q, &residue(q, input))), input % q, true);
        }
    }
}

#[test]
fn prime_inverse_law_checks_prime_and_nonzero_evidence() {
    for (q, input, prime) in [(2, 1, "prime-two"), (3, 2, "prime-three")] {
        let x = residue(q, input);
        let inv = inverse(q, &x);
        let nz = format!(
            "(#pt-lambda ((zero-value {})) (#pt-app {} zero-value))",
            natural_eq(&value(&x), "#pt-zero"),
            app("successor-not-zero", &[&n(input - 1)])
        );
        let proof = app(
            "finite-prime-inverse-product",
            &[&n(q), &positive(q), &app(prime, &[]), &x, &nz],
        );
        check(
            &natural_eq(&value(&product(q, &x, &inv)), &n(1)),
            &proof,
            true,
        );
    }
    let x = residue(4, 2);
    let nz = format!(
        "(#pt-lambda ((zero-value {})) (#pt-app {} zero-value))",
        natural_eq(&value(&x), "#pt-zero"),
        app("successor-not-zero", &[&n(1)])
    );
    let proof = app(
        "finite-prime-inverse-product",
        &[&n(4), &positive(4), &app("prime-two", &[]), &x, &nz],
    );
    check(
        &natural_eq(&value(&product(4, &x, &inverse(4, &x))), &n(1)),
        &proof,
        false,
    );
    let zero = residue(2, 0);
    let one = residue(2, 1);
    let wrong_owner = format!(
        "(#pt-lambda ((zero-value {})) (#pt-app {} zero-value))",
        natural_eq(&value(&one), "#pt-zero"),
        app("successor-not-zero", &[&n(0)])
    );
    let proof = app(
        "finite-prime-inverse-product",
        &[
            &n(2),
            &positive(2),
            &app("prime-two", &[]),
            &zero,
            &wrong_owner,
        ],
    );
    check(
        &natural_eq(&value(&product(2, &zero, &inverse(2, &zero))), &n(1)),
        &proof,
        false,
    );
}

#[test]
fn signed_and_noncanonical_inputs_have_the_same_actual_inverse() {
    for (p, m, expected) in [(0, 2, 2), (15, 17, 2), (17, 15, 3), (0, 0, 0)] {
        let integer = format!(
            "(#pt-construct integer () () difference ({} {}))",
            n(p),
            n(m)
        );
        let x = app(
            "finite-residue-of-integer",
            &[&n(5), &positive(5), &integer],
        );
        observe_number(&value(&inverse(5, &x)), expected, true);
    }
}

#[test]
fn unit_records_validate_the_actual_inverse_product() {
    let x = residue(5, 2);
    for (inv, good) in [(3, true), (1, false)] {
        let forged=format!("(#pt-construct finite-residue-unit-data () ({} {} {x}) invertible ({} (#pt-refl #pt-nat {})))",n(5),positive(5),residue(5,inv),n(1));
        let actual = value(&format!(
            "(#pt-project finite-residue-unit-data 0 {forged})"
        ));
        check(
            &natural_eq(&actual, &n(inv)),
            &format!("(#pt-refl #pt-nat {})", n(inv)),
            good,
        );
    }
}

#[test]
fn type_valued_strong_recursion_computes_actual_history_entries() {
    let family = "(#pt-lambda ((family-index #pt-nat)) #pt-nat)";
    let below = |stage: &str| app("natural-data-below", &[family, stage]);
    let history_type =
        |stage: &str| format!("(#pt-pi ((earlier-history {})) #pt-nat)", below(stage));
    let motive = format!(
        "(#pt-lambda ((recursion-index #pt-nat)) (#pt-pi ((chosen-prefix {})) #pt-nat))",
        below("recursion-index")
    );
    let base = format!(
        "(#pt-lambda ((empty-history {})) #pt-zero)",
        below("#pt-zero")
    );
    let step=format!("(#pt-lambda ((previous #pt-nat) (unused-recursion {}) (available-history {})) (#pt-succ (#pt-app available-history previous {})))",history_type("previous"),below("(#pt-succ previous)"),app("less-than-successor",&["previous"]));
    let prelude=format!("(#math-definition count-step () (#pt-pi ((stage #pt-nat) (history {})) #pt-nat) (#pt-lambda ((stage #pt-nat) (history {})) (#pt-app (#pt-nat-induct {motive} {base} {step} stage) history)))",below("stage"),below("stage"));
    for bound in [0, 1, 4] {
        let actual = app(
            "natural-data-strong-recursion",
            &[family, "(#pt-use count-step ())", &n(bound)],
        );
        check_with_prelude(
            &prelude,
            &natural_eq(&actual, &n(bound)),
            &format!("(#pt-refl #pt-nat {})", n(bound)),
            true,
        );
    }
}

#[test]
fn computed_record_exposes_well_typed_gcd_and_bezout_certificates() {
    for (a, b) in [(0, 0), (5, 0), (0, 5), (3, 7), (17, 5), (30, 12)] {
        let r = record(a, b);
        let gcd = app("gcd-spec", &[&n(a), &n(b), &projection(0, &r)]);
        let bezout = app(
            "integer-bezout-equation",
            &[
                &app("integer-of-natural", &[&n(a)]),
                &app("integer-of-natural", &[&n(b)]),
                &app("integer-of-natural", &[&projection(0, &r)]),
                &projection(1, &r),
                &projection(2, &r),
            ],
        );
        for (field, ty) in [(3, gcd), (4, bezout)] {
            let cert = projection(field, &r);
            check(&ty, &cert, true);
        }
    }
}

#[test]
fn wrong_gcd_and_coefficient_counts_are_rejected() {
    let r = record(30, 12);
    for (statement, proof) in [
        (
            natural_eq(&projection(0, &r), &n(5)),
            format!("(#pt-refl #pt-nat {})", projection(0, &r)),
        ),
        (
            integer_eq(&projection(1, &r), &signed(2)),
            integer_left_reflexivity(&projection(1, &r), &signed(2)),
        ),
        (
            integer_eq(&projection(2, &r), &signed(2)),
            integer_left_reflexivity(&projection(2, &r), &signed(2)),
        ),
    ] {
        check(&statement, &proof, false);
    }
}

#[test]
fn forged_record_certificates_fail_type_checking() {
    let actual = record(3, 0);
    let proof = format!(
        "(#pt-construct natural-extended-gcd-data () ({} {}) computed ({} {} {} {} {}))",
        n(3),
        n(0),
        n(2),
        signed(1),
        signed(0),
        projection(3, &actual),
        projection(4, &actual)
    );
    let statement = natural_eq(&projection(0, &proof), &n(2));
    check(&statement, &format!("(#pt-refl #pt-nat {})", n(2)), false);
}

#[test]
fn certificates_cannot_be_reused_for_different_inputs() {
    let source = record(30, 12);
    let statement = app("gcd-spec", &[&n(17), &n(5), &projection(0, &source)]);
    check(&statement, &projection(3, &source), false);
    let equation = app(
        "integer-bezout-equation",
        &[
            &app("integer-of-natural", &[&n(17)]),
            &app("integer-of-natural", &[&n(5)]),
            &app("integer-of-natural", &[&projection(0, &source)]),
            &projection(1, &source),
            &projection(2, &source),
        ],
    );
    check(&equation, &projection(4, &source), false);
}
