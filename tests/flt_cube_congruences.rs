//! Foundation-free checks for the native FLT cube congruence modules.
use lim::{check_theorem_details_from_path_with_config, CompileConfig, ProofBudget};
use std::path::Path;

const CUBE_SCALAR_AND_INTEGER_RESIDUES: &[(&str, &str)] = &[
    (
        "eisenstein-cube-scalar-coordinate-minus-one.lim",
        "eisenstein-cube-scalar-coordinate-minus-one",
    ),
    (
        "eisenstein-cube-scalar-coordinate-plus-one.lim",
        "eisenstein-cube-scalar-coordinate-plus-one",
    ),
    (
        "eisenstein-cube-scalar-factor-omega.lim",
        "eisenstein-cube-scalar-factor-omega",
    ),
    (
        "eisenstein-cube-scalar-factor-real.lim",
        "eisenstein-cube-scalar-factor-real",
    ),
    (
        "eisenstein-cube-scalar-integer-shift-cycle.lim",
        "eisenstein-cube-scalar-integer-shift-cycle",
    ),
    (
        "eisenstein-cube-scalar-shift-omega-omega.lim",
        "eisenstein-cube-scalar-shift-omega-omega",
    ),
    (
        "eisenstein-cube-scalar-shift-omega-real.lim",
        "eisenstein-cube-scalar-shift-omega-real",
    ),
    (
        "eisenstein-cube-scalar-shift-square-omega.lim",
        "eisenstein-cube-scalar-shift-square-omega",
    ),
    (
        "eisenstein-cube-scalar-shift-square-real.lim",
        "eisenstein-cube-scalar-shift-square-real",
    ),
    (
        "eisenstein-cube-scalar-third-residue-shift-omega.lim",
        "eisenstein-cube-scalar-third-residue-shift-omega",
    ),
    (
        "eisenstein-cube-scalar-third-residue-shift-real.lim",
        "eisenstein-cube-scalar-third-residue-shift-real",
    ),
    ("integer-three-residues.lim", "integer-add-subtract-right"),
    ("integer-three-residues.lim", "integer-natural-successor"),
    (
        "integer-three-residues.lim",
        "integer-three-residue-congruent",
    ),
    (
        "integer-three-residues.lim",
        "integer-three-residue-increment",
    ),
    (
        "integer-three-residues.lim",
        "integer-natural-has-three-residue",
    ),
    ("integer-three-residues.lim", "integer-three-residue-negate"),
    (
        "integer-three-residues.lim",
        "integer-has-three-residue-everywhere",
    ),
];

const ADDITIVE_AND_EISENSTEIN_RESIDUES: &[(&str, &str)] = &[
    (
        "eisenstein-additive-divisibility.lim",
        "eisenstein-zero-add",
    ),
    (
        "eisenstein-additive-divisibility.lim",
        "eisenstein-add-after-subtract",
    ),
    (
        "eisenstein-additive-divisibility.lim",
        "eisenstein-divides-negative-target",
    ),
    (
        "eisenstein-additive-divisibility.lim",
        "eisenstein-divides-add",
    ),
    (
        "eisenstein-additive-divisibility.lim",
        "eisenstein-divides-add-cancel-left",
    ),
    (
        "eisenstein-additive-divisibility.lim",
        "eisenstein-divides-add-cancel-right",
    ),
    (
        "eisenstein-additive-divisibility.lim",
        "eisenstein-unit-divisibility-reflect",
    ),
    (
        "eisenstein-additive-divisibility.lim",
        "eisenstein-add-subtract-right",
    ),
    (
        "eisenstein-three-residues.lim",
        "eisenstein-coordinate-sum-plus-one",
    ),
    (
        "eisenstein-three-residues.lim",
        "eisenstein-coordinate-sum-minus-one",
    ),
    (
        "eisenstein-three-residues.lim",
        "eisenstein-lambda-three-residues",
    ),
    (
        "eisenstein-three-residues.lim",
        "eisenstein-lambda-nondivisible-residue-cases",
    ),
];

const CUBE_ALGEBRA_AND_CONGRUENCES: &[(&str, &str)] = &[
    (
        "eisenstein-cube-algebra.lim",
        "eisenstein-cube-factor-product-real",
    ),
    (
        "eisenstein-cube-algebra.lim",
        "eisenstein-cube-factor-product-omega",
    ),
    (
        "eisenstein-cube-algebra.lim",
        "eisenstein-cube-factor-product",
    ),
    ("eisenstein-cube-algebra.lim", "eisenstein-cube-factor"),
    ("eisenstein-cube-algebra.lim", "eisenstein-cube-shift-omega"),
    (
        "eisenstein-cube-algebra.lim",
        "eisenstein-cube-shift-square",
    ),
    (
        "eisenstein-cube-algebra.lim",
        "eisenstein-cube-third-residue-shift",
    ),
    ("eisenstein-cube-algebra.lim", "eisenstein-ring-four-factor"),
    (
        "eisenstein-cube-algebra.lim",
        "eisenstein-three-common-factors",
    ),
    ("eisenstein-cube-algebra.lim", "eisenstein-cube-negate"),
    (
        "eisenstein-cube-algebra.lim",
        "eisenstein-cube-shift-factor",
    ),
    (
        "eisenstein-cube-congruences.lim",
        "eisenstein-lambda-divides-three-factor-product",
    ),
    (
        "eisenstein-cube-congruences.lim",
        "eisenstein-lambda-four-divides-cube-minus-one",
    ),
    (
        "eisenstein-cube-congruences.lim",
        "eisenstein-lambda-four-divides-cube-plus-one",
    ),
    (
        "eisenstein-cube-congruences.lim",
        "eisenstein-lambda-four-cube-congruence",
    ),
];

fn cube_config() -> CompileConfig {
    let mut config = CompileConfig::default();
    let default = ProofBudget::default();
    config.set_proof_budget(
        ProofBudget::new(default.work(), default.phase_bytes(), 1024 * 1024 * 1024).unwrap(),
    );
    config
}

fn check_matrix(targets: &[(&str, &str)]) {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let config = cube_config();
    for &(module, target) in targets {
        let path = root.join("theorems/flt").join(module);
        let source = std::fs::read_to_string(&path)
            .unwrap_or_else(|error| panic!("failed to read {}: {error}", path.display()));
        let report = check_theorem_details_from_path_with_config(&source, &path, &config, target)
            .unwrap_or_else(|error| {
                panic!(
                    "failed to check {target} in {}: {}",
                    path.display(),
                    error.message
                )
            });
        assert!(
            report.name == target || report.name.ends_with(&format!("::{target}")),
            "unexpected canonical target for {}: {}",
            path.display(),
            report.name
        );
        assert!(
            report.foundations.is_empty(),
            "foundations for {target} in {}: {:?}",
            path.display(),
            report.foundations
        );
    }
}

#[test]
fn cube_scalar_and_integer_residue_theorems_are_foundation_free() {
    check_matrix(CUBE_SCALAR_AND_INTEGER_RESIDUES);
}

#[test]
fn additive_and_eisenstein_residue_theorems_are_foundation_free() {
    check_matrix(ADDITIVE_AND_EISENSTEIN_RESIDUES);
}

#[test]
fn cube_algebra_and_congruence_theorems_are_foundation_free() {
    check_matrix(CUBE_ALGEBRA_AND_CONGRUENCES);
}

fn cube_call(name: &str, args: &[&str]) -> String {
    if args.is_empty() {
        format!("(#pt-use {name} ())")
    } else {
        format!("(#pt-app (#pt-use {name} ()) {})", args.join(" "))
    }
}

fn cube_fixture(statement: &str, proof: &str, valid: bool) {
    use std::{
        fs,
        sync::atomic::{AtomicUsize, Ordering},
    };
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let directory = std::env::temp_dir().join(format!(
        "lim-flt-cube-congruence-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir(&directory).unwrap();
    let path = directory.join("probe.lim");
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("theorems/flt");
    let mut source = String::new();
    for (name, module) in [
        ("eisenstein", "eisenstein-defs.lim"),
        ("eisenstein-one", "eisenstein-defs.lim"),
        ("eisenstein-zero", "eisenstein-defs.lim"),
        ("eisenstein-lambda", "eisenstein-defs.lim"),
        ("eisenstein-equal", "eisenstein-defs.lim"),
        ("eisenstein-add", "eisenstein-defs.lim"),
        ("eisenstein-negate", "eisenstein-defs.lim"),
        ("eisenstein-multiply", "eisenstein-defs.lim"),
        ("eisenstein-power", "eisenstein-defs.lim"),
        ("eisenstein-divides", "eisenstein-defs.lim"),
        ("eisenstein-of-integer", "eisenstein-defs.lim"),
        ("integer-of-natural", "integer-defs.lim"),
        ("exists", "logic-exists.lim"),
        ("disjunction", "logical-connectives.lim"),
        ("eisenstein-reflexive", "eisenstein-equality.lim"),
        ("eisenstein-transitive", "eisenstein-equality.lim"),
        ("eisenstein-add-congruent", "eisenstein-equality.lim"),
        ("eisenstein-add-commutative", "eisenstein-ring.lim"),
        ("eisenstein-negate-involution", "eisenstein-ring.lim"),
        (
            "eisenstein-add-subtract-right",
            "eisenstein-additive-divisibility.lim",
        ),
        (
            "eisenstein-divides-negative-target",
            "eisenstein-additive-divisibility.lim",
        ),
        (
            "eisenstein-divides-congruent-target",
            "eisenstein-divisibility.lim",
        ),
        (
            "eisenstein-lambda-not-divides-one",
            "eisenstein-lambda-decision-core.lim",
        ),
        (
            "integer-three-divides-coordinate-sum",
            "eisenstein-lambda-decision-core.lim",
        ),
        (
            "integer-natural-divisibility-reflects",
            "integer-natural-bridge.lim",
        ),
        ("three-not-divides-two", "natural-prime-three.lim"),
        (
            "eisenstein-lambda-four-cube-congruence",
            "eisenstein-cube-congruences.lim",
        ),
        (
            "eisenstein-lambda-four-divides-cube-minus-one",
            "eisenstein-cube-congruences.lim",
        ),
    ] {
        source.push_str(&format!(
            "(#alias {name} = {}::{name})\n",
            root.join(module).display()
        ));
    }
    source.push_str(&format!("(#theorem observed-congruence (#universes) (#parameters) (#statement {statement}) (#proof {proof}))"));
    fs::write(&path, &source).unwrap();
    let result = check_theorem_details_from_path_with_config(
        &source,
        &path,
        &cube_config(),
        "observed-congruence",
    );
    fs::remove_dir_all(&directory).unwrap();
    if valid {
        assert!(result
            .unwrap_or_else(|error| panic!("{}", error.message))
            .foundations
            .is_empty());
    } else {
        let error = result.unwrap_err();
        assert_eq!(error.code, lim::DiagnosticCode::Proof);
        assert!(error.message.contains("mismatch"), "{}", error.message);
    }
}

fn cube_congruence_statement(value: &str) -> String {
    let one = "(#pt-use eisenstein-one ())";
    let cube = cube_call("eisenstein-power", &[value, "(#pt-numeral 3)"]);
    let power = cube_call(
        "eisenstein-power",
        &["(#pt-use eisenstein-lambda ())", "(#pt-numeral 4)"],
    );
    let minus = cube_call(
        "eisenstein-add",
        &[&cube, &cube_call("eisenstein-negate", &[one])],
    );
    let plus = cube_call("eisenstein-add", &[&cube, one]);
    cube_call(
        "disjunction",
        &[
            &cube_call("eisenstein-divides", &[&power, &minus]),
            &cube_call("eisenstein-divides", &[&power, &plus]),
        ],
    )
}

#[test]
fn closed_cube_congruences_cover_both_signs_and_reject_a_divisible_input() {
    let one = "(#pt-use eisenstein-one ())";
    let lambda = "(#pt-use eisenstein-lambda ())";
    let negative_one = cube_call("eisenstein-negate", &[one]);
    let negative_twice = cube_call("eisenstein-negate", &[&negative_one]);
    let negative_div = cube_call(
        "eisenstein-divides-negative-target",
        &[lambda, &negative_one, "given-divisibility"],
    );
    let one_div = cube_call(
        "eisenstein-divides-congruent-target",
        &[
            lambda,
            &negative_twice,
            one,
            &cube_call("eisenstein-negate-involution", &[one]),
            &negative_div,
        ],
    );
    let contradiction =
        format!("(#pt-app (#pt-use eisenstein-lambda-not-divides-one ()) {one_div})");
    let negative_nondiv = format!(
        "(#pt-lambda ((given-divisibility {})) {contradiction})",
        cube_call("eisenstein-divides", &[lambda, &negative_one])
    );
    for (value, evidence) in [
        (
            one.to_owned(),
            "(#pt-use eisenstein-lambda-not-divides-one ())".to_owned(),
        ),
        (negative_one, negative_nondiv),
    ] {
        let proof = cube_call(
            "eisenstein-lambda-four-cube-congruence",
            &[&value, &evidence],
        );
        cube_fixture(&cube_congruence_statement(&value), &proof, true);
    }
    for (n, valid) in [(2, true), (3, false)] {
        let numeral = format!("(#pt-numeral {n})");
        let value = cube_call(
            "eisenstein-of-integer",
            &[&cube_call("integer-of-natural", &[&numeral])],
        );
        let coordinate = cube_call(
            "integer-three-divides-coordinate-sum",
            &[&value, "given-divisibility"],
        );
        let natural = cube_call(
            "integer-natural-divisibility-reflects",
            &["(#pt-numeral 3)", &numeral, &coordinate],
        );
        let contradiction = format!("(#pt-app (#pt-use three-not-divides-two ()) {natural})");
        let nondiv = format!(
            "(#pt-lambda ((given-divisibility {})) {contradiction})",
            cube_call("eisenstein-divides", &[lambda, &value])
        );
        let proof = cube_call("eisenstein-lambda-four-cube-congruence", &[&value, &nondiv]);
        cube_fixture(&cube_congruence_statement(&value), &proof, valid);
    }
}

#[test]
fn cube_congruence_checks_the_actual_shift_factor() {
    let one = "(#pt-use eisenstein-one ())";
    let lambda = "(#pt-use eisenstein-lambda ())";
    let factor = one;
    let product = cube_call("eisenstein-multiply", &[lambda, factor]);
    let value = cube_call("eisenstein-add", &[one, &product]);
    let negative_one = cube_call("eisenstein-negate", &[one]);
    let minus = cube_call("eisenstein-add", &[&value, &negative_one]);
    let swapped = cube_call(
        "eisenstein-add",
        &[
            &cube_call("eisenstein-add", &[&product, one]),
            &negative_one,
        ],
    );
    let first = cube_call(
        "eisenstein-add-congruent",
        &[
            &value,
            &negative_one,
            &cube_call("eisenstein-add", &[&product, one]),
            &negative_one,
            &cube_call("eisenstein-add-commutative", &[one, &product]),
            &cube_call("eisenstein-reflexive", &[&negative_one]),
        ],
    );
    let equation = cube_call(
        "eisenstein-transitive",
        &[
            &minus,
            &swapped,
            &product,
            &first,
            &cube_call("eisenstein-add-subtract-right", &[&product, one]),
        ],
    );
    let predicate = format!(
        "(#pt-lambda ((candidate-factor (#pt-use eisenstein ()))) {})",
        cube_call(
            "eisenstein-equal",
            &[
                &minus,
                &cube_call("eisenstein-multiply", &[lambda, "candidate-factor"])
            ]
        )
    );
    for (witness, valid) in [(factor, true), ("(#pt-use eisenstein-zero ())", false)] {
        let division = format!("(#pt-construct exists (0) ((#pt-use eisenstein ()) {predicate}) introduce ({witness} {equation}))");
        let proof = cube_call(
            "eisenstein-lambda-four-divides-cube-minus-one",
            &[&value, &division],
        );
        let cube = cube_call("eisenstein-power", &[&value, "(#pt-numeral 3)"]);
        let power = cube_call("eisenstein-power", &[lambda, "(#pt-numeral 4)"]);
        let statement = cube_call(
            "eisenstein-divides",
            &[
                &power,
                &cube_call("eisenstein-add", &[&cube, &negative_one]),
            ],
        );
        cube_fixture(&statement, &proof, valid);
    }
}

#[test]
fn the_cube_congruence_cannot_drop_its_nondivisibility_premise() {
    let path =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("theorems/flt/eisenstein-cube-congruences.lim");
    let source = std::fs::read_to_string(&path).unwrap();
    let target = "eisenstein-lambda-four-cube-congruence";
    let start = source.find(&format!("(#theorem {target}")).unwrap();
    let parameter = start
        + source[start..]
            .find("(#parameter lambda-not-divides")
            .unwrap();
    let mut depth = 0usize;
    let mut end = parameter;
    for (index, byte) in source.as_bytes()[parameter..].iter().enumerate() {
        if *byte == b'(' {
            depth += 1;
        } else if *byte == b')' {
            depth -= 1;
            if depth == 0 {
                end = parameter + index + 1;
                break;
            }
        }
    }
    let changed = format!("{}{}", &source[..parameter], &source[end..]);
    lim::parse_program_from_path(&changed, &path)
        .expect("removing a premise preserves source syntax");
    let error =
        check_theorem_details_from_path_with_config(&changed, &path, &cube_config(), target)
            .unwrap_err();
    assert_eq!(error.code, lim::DiagnosticCode::Proof);
    assert!(
        error.message.contains("lambda-not-divides"),
        "{}",
        error.message
    );
}
