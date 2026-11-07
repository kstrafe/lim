//! Native finite-residue arithmetic and adversarial division certificates.
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
    "natural-division-data",
    "finite-residue-defs",
    "finite-residue-operations",
    "finite-residue-congruence",
    "finite-residue-polynomials",
    "finite-residue-arithmetic-laws",
    "finite-residue-nested-reduction",
    "finite-residue-semiring",
    "finite-residue-negation",
];

fn config() -> CompileConfig {
    let mut config = CompileConfig::default();
    let budget = ProofBudget::default();
    config.set_proof_budget(
        ProofBudget::new(budget.work(), budget.phase_bytes(), 1024 * 1024 * 1024).unwrap(),
    );
    config
}
fn root() -> std::path::PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("theorems/flt")
}
fn term(name: &str, args: &[&str]) -> String {
    let head = format!("(#pt-use {name} ())");
    if args.is_empty() {
        head
    } else {
        format!("(#pt-app {head} {})", args.join(" "))
    }
}
fn n(value: usize) -> String {
    format!("(#pt-numeral {value})")
}
fn refl(value: usize) -> String {
    format!("(#pt-refl #pt-nat {})", n(value))
}
fn eq(left: &str, right: &str) -> String {
    format!("(#pt-eq #pt-nat {left} {right})")
}
fn positive(modulus: usize) -> String {
    term("zero-less-successor", &[&n(modulus - 1)])
}
fn bound(value: usize, modulus: usize) -> String {
    assert!(value < modulus);
    format!("(#pt-construct exists (0) (#pt-nat (#pt-lambda ((gap #pt-nat)) (#pt-eq #pt-nat {} (#pt-app (#pt-use add ()) (#pt-succ {}) gap)))) introduce ({} {}))", n(modulus), n(value), n(modulus - value - 1), refl(modulus))
}
fn residue(value: usize, modulus: usize) -> String {
    format!(
        "(#pt-construct finite-residue () ({}) representative ({} {}))",
        n(modulus),
        n(value),
        bound(value, modulus)
    )
}
fn value(obj: &str) -> String {
    format!("(#pt-project finite-residue 0 {obj})")
}
fn reduce(modulus: usize, number: usize) -> String {
    term(
        "finite-residue-of-natural",
        &[&n(modulus), &positive(modulus), &n(number)],
    )
}
fn fixture(prelude: &str, statement: &str, proof: &str, valid: bool) {
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let directory = std::env::temp_dir().join(format!(
        "lim-finite-residue-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir(&directory).unwrap();
    let path = directory.join("probe.lim");
    let terms = format!("{prelude} {statement} {proof}");
    let referenced: HashSet<_> = terms
        .split(|c: char| c.is_whitespace() || c == '(' || c == ')')
        .collect();
    let mut source = String::new();
    for module in MODULES.iter().copied().chain([
        "../fermat_statement",
        "logic-exists",
        "natural-discrete-order",
        "logical-connectives",
    ]) {
        let module_path = root().join(format!("{module}.lim"));
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
    source.push_str(&format!("(#theorem observed-residue (#universes) (#parameters) (#statement {statement}) (#proof {proof}))"));
    fs::write(&path, &source).unwrap();
    let result =
        check_theorem_details_from_path_with_config(&source, &path, &config(), "observed-residue");
    let expected_name = format!(
        "{}::observed-residue",
        path.canonicalize().unwrap().display()
    );
    fs::remove_dir_all(&directory).unwrap();
    if valid {
        let report = result.unwrap_or_else(|e| panic!("{}", e.message));
        assert_eq!(report.name, expected_name);
        assert!(report.foundations.is_empty());
    } else {
        let error = result.unwrap_err();
        assert_eq!(error.code, DiagnosticCode::Proof);
        assert!(error.message.contains("mismatch"), "{}", error.message);
    }
}
fn observed(actual: &str, expected: usize, valid: bool) {
    fixture("", &eq(actual, &n(expected)), &refl(expected), valid);
}

#[test]
fn division_computes_both_quotient_and_remainder() {
    let computed = term("compute-natural-division", &[&n(3), &positive(3), &n(8)]);
    observed(
        &format!("(#pt-project natural-division-data 0 {computed})"),
        2,
        true,
    );
    observed(
        &format!("(#pt-project natural-division-data 1 {computed})"),
        2,
        true,
    );
    observed(
        &format!("(#pt-project natural-division-data 0 {computed})"),
        1,
        false,
    );
    observed(
        &format!("(#pt-project natural-division-data 1 {computed})"),
        1,
        false,
    );
}
#[test]
fn reductions_cover_zero_exact_multiples_and_wrap_boundaries() {
    for (modulus, input, expected) in [
        (1, 0, 0),
        (1, 4, 0),
        (2, 0, 0),
        (2, 1, 1),
        (2, 2, 0),
        (2, 5, 1),
        (3, 2, 2),
        (3, 3, 0),
        (3, 8, 2),
        (5, 4, 4),
        (5, 5, 0),
        (5, 11, 1),
        (7, 12, 5),
    ] {
        observed(&value(&reduce(modulus, input)), expected, true);
    }
}
#[test]
fn a_wrong_residue_is_a_mathematical_mismatch() {
    observed(&value(&reduce(5, 11)), 2, false);
}
#[test]
fn addition_and_multiplication_actually_reduce() {
    for (word, expected) in [("add", 2), ("multiply", 2)] {
        let actual = term(
            &format!("finite-residue-{word}"),
            &[&n(5), &positive(5), &residue(3, 5), &residue(4, 5)],
        );
        observed(&value(&actual), expected, true);
        observed(&value(&actual), expected + 1, false);
    }
}
#[test]
fn computed_additive_inverses_include_the_zero_and_unit_modulus_cases() {
    for (modulus, input, expected) in [(1, 0, 0), (2, 1, 1), (3, 1, 2), (5, 0, 0), (5, 2, 3)] {
        let actual = term(
            "finite-residue-negate",
            &[&n(modulus), &positive(modulus), &residue(input, modulus)],
        );
        observed(&value(&actual), expected, true);
    }
    let actual = term(
        "finite-residue-negate",
        &[&n(5), &positive(5), &residue(2, 5)],
    );
    observed(&value(&actual), 2, false);
}
#[test]
fn a_residue_cannot_carry_a_forged_range_certificate() {
    let forged = format!(
        "(#pt-construct finite-residue () ({}) representative ({} {}))",
        n(3),
        n(3),
        bound(0, 3)
    );
    observed(&value(&forged), 3, false);
}
#[test]
fn a_zero_modulus_cannot_be_passed_as_positive() {
    let forged = term("finite-residue-of-natural", &[&n(0), &positive(1), &n(2)]);
    observed(&value(&forged), 0, false);
}
#[test]
fn division_data_cannot_carry_a_forged_equation() {
    let computed = term("compute-natural-division", &[&n(3), &positive(3), &n(8)]);
    let certificate = format!("(#pt-project natural-division-data 2 {computed})");
    let forged = format!(
        "(#pt-construct natural-division-data () ({} {}) computed ({} {} {certificate}))",
        n(8),
        n(3),
        n(1),
        n(2)
    );
    observed(
        &format!("(#pt-project natural-division-data 0 {forged})"),
        1,
        false,
    );
}
#[test]
fn a_division_equation_without_a_range_bound_does_not_choose_the_wrong_residue() {
    // 8 = 1*3+5 is true, but 5 is not the canonical representative modulo 3.
    let proof = term(
        "finite-reduction-equation",
        &[&n(3), &positive(3), &n(8), &n(1), &n(5), &refl(8)],
    );
    fixture(
        "",
        &eq(&value(&reduce(3, 8)), &value(&reduce(3, 5))),
        &proof,
        true,
    );
    fixture("", &eq(&value(&reduce(3, 8)), &n(5)), &proof, false);
}
#[test]
fn sum_and_product_laws_use_the_correct_operation() {
    for (law, first, second, expected) in [("sum", 8, 7, 0), ("product", 8, 7, 1)] {
        let proof = term(
            &format!("finite-reduction-{law}"),
            &[&n(5), &positive(5), &n(first), &n(second)],
        );
        let actual = value(&reduce(
            5,
            if law == "sum" {
                first + second
            } else {
                first * second
            },
        ));
        fixture("", &eq(&actual, &n(expected)), &proof, true);
        fixture("", &eq(&actual, &n(expected + 1)), &proof, false);
    }
}
