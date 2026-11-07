//! Foundation-free checks for the FLT Eisenstein cubic-solution modules.
use lim::{check_theorem_details_from_path_with_config, CompileConfig, ProofBudget};
use std::path::Path;

const CUBIC_SOLUTION_ALGEBRA: &[&str] = &[
    "eisenstein-add-four-interchange",
    "eisenstein-add-opposite-shifts",
    "eisenstein-add-negative-one-shifts",
    "eisenstein-lambda-not-divides-two",
    "eisenstein-lambda-four-divisibility-descends",
    "eisenstein-lambda-same-negative-residues-impossible",
    "eisenstein-lambda-same-positive-residues-impossible",
];

const CUBIC_SOLUTION_CONGRUENCES: &[&str] = &[
    "eisenstein-divides-cube",
    "eisenstein-cubic-solution-sum-divides",
    "eisenstein-cubic-solution-opposite-cube-residues",
    "eisenstein-cubic-solution-fourth-power-divides",
];

fn cubic_solution_config() -> CompileConfig {
    let mut config = CompileConfig::default();
    let default = ProofBudget::default();
    config.set_proof_budget(
        ProofBudget::new(default.work(), default.phase_bytes(), 1024 * 1024 * 1024).unwrap(),
    );
    config
}

fn check_matrix(module: &str, targets: &[&str]) {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let path = root.join("theorems/flt").join(module);
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("failed to read {}: {error}", path.display()));
    let config = cubic_solution_config();

    for &target in targets {
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
fn cubic_solution_algebra_theorems_are_foundation_free() {
    check_matrix(
        "eisenstein-cubic-solution-algebra.lim",
        CUBIC_SOLUTION_ALGEBRA,
    );
}

#[test]
fn cubic_solution_congruence_theorems_are_foundation_free() {
    check_matrix(
        "eisenstein-cubic-solution-congruences.lim",
        CUBIC_SOLUTION_CONGRUENCES,
    );
}

#[test]
fn cubic_solution_order_theorems_are_foundation_free() {
    check_matrix(
        "eisenstein-cubic-solution-order.lim",
        &[
            "eisenstein-cubic-solution-square-divides",
            "eisenstein-cubic-solution-order-at-least-two",
        ],
    );
}

fn term(name: &str, args: &[&str]) -> String {
    if args.is_empty() {
        format!("(#pt-use {name} ())")
    } else {
        format!("(#pt-app (#pt-use {name} ()) {})", args.join(" "))
    }
}

fn fixture(statement: &str, proof: &str, valid: bool) {
    use std::{
        fs,
        sync::atomic::{AtomicUsize, Ordering},
    };
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let directory = std::env::temp_dir().join(format!(
        "lim-flt-cubic-solution-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir(&directory).unwrap();
    let path = directory.join("probe.lim");
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("theorems/flt");
    let mut source = String::new();
    for (module, names) in [
        (
            "eisenstein-defs",
            &[
                "eisenstein",
                "eisenstein-one",
                "eisenstein-zero",
                "eisenstein-lambda",
                "eisenstein-add",
                "eisenstein-negate",
                "eisenstein-multiply",
                "eisenstein-power",
                "eisenstein-divides",
                "eisenstein-equal",
            ][..],
        ),
        ("integer-defs", &["integer-equal"][..]),
        ("eisenstein-equality", &["eisenstein-reflexive"][..]),
        (
            "eisenstein-divisibility",
            &[
                "eisenstein-divides-zero",
                "eisenstein-divides-congruent-target",
            ][..],
        ),
        ("eisenstein-ring", &["eisenstein-negate-involution"][..]),
        ("eisenstein-cubic-bridge", &["eisenstein-one-unit"][..]),
        (
            "eisenstein-additive-divisibility",
            &["eisenstein-divides-negative-target"][..],
        ),
        (
            "eisenstein-lambda-decision-core",
            &["eisenstein-lambda-not-divides-one"][..],
        ),
        ("logical-connectives", &["conjunction-introduce"][..]),
        (
            "eisenstein-cubic-solution-algebra",
            &["eisenstein-add-opposite-shifts"][..],
        ),
        (
            "eisenstein-cubic-solution-congruences",
            &[
                "eisenstein-cubic-solution-fourth-power-divides",
                "eisenstein-cubic-solution-opposite-cube-residues",
            ][..],
        ),
    ] {
        for name in names {
            source.push_str(&format!(
                "(#alias {name} = {}::{name})\n",
                root.join(format!("{module}.lim")).display()
            ));
        }
    }
    source.push_str(&format!("(#theorem observed-solution (#universes) (#parameters) (#statement {statement}) (#proof {proof}))"));
    fs::write(&path, &source).unwrap();
    let result = check_theorem_details_from_path_with_config(
        &source,
        &path,
        &cubic_solution_config(),
        "observed-solution",
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

fn nondivisible_negative_one() -> String {
    let one = term("eisenstein-one", &[]);
    let lambda = term("eisenstein-lambda", &[]);
    let negative = term("eisenstein-negate", &[&one]);
    let twice = term("eisenstein-negate", &[&negative]);
    let premise = term("eisenstein-divides", &[&lambda, &negative]);
    let negated = term(
        "eisenstein-divides-negative-target",
        &[&lambda, &negative, "divides-negative-one"],
    );
    let corrected = term(
        "eisenstein-divides-congruent-target",
        &[
            &lambda,
            &twice,
            &one,
            &term("eisenstein-negate-involution", &[&one]),
            &negated,
        ],
    );
    format!(
        "(#pt-lambda ((divides-negative-one {premise})) {})",
        term("eisenstein-lambda-not-divides-one", &[&corrected])
    )
}

fn solution_application(reverse: bool, second_positive: bool, unit_zero: bool) -> (String, String) {
    let one = term("eisenstein-one", &[]);
    let zero = term("eisenstein-zero", &[]);
    let lambda = term("eisenstein-lambda", &[]);
    let negative = term("eisenstein-negate", &[&one]);
    let (first, second) = if reverse {
        (&negative, &one)
    } else if second_positive {
        (&one, &one)
    } else {
        (&one, &negative)
    };
    let first_not = if reverse {
        nondivisible_negative_one()
    } else {
        term("eisenstein-lambda-not-divides-one", &[])
    };
    let second_not = if reverse || second_positive {
        term("eisenstein-lambda-not-divides-one", &[])
    } else {
        nondivisible_negative_one()
    };
    let cube = |x: &str| term("eisenstein-power", &[x, "(#pt-numeral 3)"]);
    let sum = term("eisenstein-add", &[&cube(first), &cube(second)]);
    let unit = if unit_zero { &zero } else { &one };
    let product = term("eisenstein-multiply", &[unit, &cube(&zero)]);
    let component = |index: usize| {
        term(
            "integer-equal",
            &[
                &format!("(#pt-project eisenstein {index} {sum})"),
                &format!("(#pt-project eisenstein {index} {product})"),
            ],
        )
    };
    let equation = term(
        "conjunction-introduce",
        &[
            &component(0),
            &component(1),
            "(#pt-refl #pt-nat (#pt-numeral 1))",
            "(#pt-refl #pt-nat #pt-zero)",
        ],
    );
    let proof = term(
        "eisenstein-cubic-solution-fourth-power-divides",
        &[
            first,
            second,
            &zero,
            unit,
            &term("eisenstein-one-unit", &[]),
            &first_not,
            &second_not,
            &term("eisenstein-divides-zero", &[&lambda]),
            &equation,
        ],
    );
    let fourth = term("eisenstein-power", &[&lambda, "(#pt-numeral 4)"]);
    let statement = term("eisenstein-divides", &[&fourth, &cube(&zero)]);
    (statement, proof)
}

#[test]
fn solution_congruence_accepts_both_opposite_signs_and_zero_third_coordinate() {
    for reverse in [false, true] {
        let (statement, proof) = solution_application(reverse, false, false);
        fixture(&statement, &proof, true);
    }
}

#[test]
fn solution_congruence_rejects_a_false_equation_and_a_nonunit() {
    for (second_positive, unit_zero) in [(true, false), (false, true)] {
        let (statement, proof) = solution_application(false, second_positive, unit_zero);
        fixture(&statement, &proof, false);
    }
}

#[test]
fn solution_congruence_cannot_discard_its_required_evidence() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("theorems/flt/eisenstein-cubic-solution-congruences.lim");
    let source = std::fs::read_to_string(&path).unwrap();
    let target = "eisenstein-cubic-solution-fourth-power-divides";
    let start = source.find(&format!("(#theorem {target}")).unwrap();
    for name in [
        "unit-proof",
        "first-not-divides",
        "second-not-divides",
        "third-divides",
        "solution-equation",
    ] {
        let parameter = start
            + source[start..]
                .find(&format!("(#parameter {name} "))
                .unwrap();
        let mut depth = 0usize;
        let mut end = parameter;
        for (index, byte) in source.as_bytes()[parameter..].iter().enumerate() {
            match byte {
                b'(' => depth += 1,
                b')' => {
                    depth -= 1;
                    if depth == 0 {
                        end = parameter + index + 1;
                        break;
                    }
                }
                _ => {}
            }
        }
        let changed = format!("{}{}", &source[..parameter], &source[end..]);
        lim::parse_program_from_path(&changed, &path)
            .expect("removing evidence keeps the source well formed");
        let error = check_theorem_details_from_path_with_config(
            &changed,
            &path,
            &cubic_solution_config(),
            target,
        )
        .unwrap_err();
        assert_eq!(error.code, lim::DiagnosticCode::Proof);
        assert!(
            error
                .message
                .contains(&format!("unbound proof-term name '{name}'")),
            "{}",
            error.message
        );
    }
}
