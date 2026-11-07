//! Foundation-free checks for the FLT Eisenstein cubic-orientation modules.
use lim::{check_theorem_details_from_path_with_config, CompileConfig, ProofBudget};
use std::path::Path;

const CUBIC_FACTOR_CHOICE: &[&str] = &[
    "eisenstein-lambda-square-divides-of-large-order",
    "eisenstein-lambda-small-order-of-not-square",
    "eisenstein-lambda-four-not-divides-three-small-factors",
    "eisenstein-lambda-square-divides-one-of-three-factors",
    "eisenstein-cubic-solution-square-divides-a-factor",
];

const CUBIC_UNIT_ROTATION: &[&str] = &[
    "eisenstein-unit-product-not-divides",
    "eisenstein-unit-coprime-right",
];

const CUBIC_ORIENTATION: &[&str] = &[
    "eisenstein-cubic-solution-rotate-omega",
    "eisenstein-cubic-solution-rotate-omega-square",
    "eisenstein-cubic-solution-has-oriented-pair",
];

fn cubic_orientation_config() -> CompileConfig {
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
    let config = cubic_orientation_config();

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
fn cubic_factor_choice_theorems_are_foundation_free() {
    check_matrix("eisenstein-cubic-factor-choice.lim", CUBIC_FACTOR_CHOICE);
}

#[test]
fn cubic_unit_rotation_theorems_are_foundation_free() {
    check_matrix("eisenstein-cubic-unit-rotation.lim", CUBIC_UNIT_ROTATION);
}

#[test]
fn cubic_orientation_theorems_are_foundation_free() {
    check_matrix("eisenstein-cubic-orientation.lim", CUBIC_ORIENTATION);
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
        "lim-flt-cubic-orientation-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir(&directory).unwrap();
    let path = directory.join("probe.lim");
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("theorems/flt");
    // Keep unrelated proof libraries out of a fixture's import closure.
    let terms = format!("{statement} {proof}");
    let referenced: std::collections::HashSet<&str> = terms
        .split(|c: char| c.is_whitespace() || c == '(' || c == ')')
        .collect();
    let mut source = String::new();
    for (module, names) in [
        (
            "eisenstein-defs",
            &[
                "eisenstein",
                "eisenstein-one",
                "eisenstein-zero",
                "eisenstein-omega",
                "eisenstein-lambda",
                "eisenstein-equal",
                "eisenstein-add",
                "eisenstein-multiply",
                "eisenstein-negate",
                "eisenstein-power",
                "eisenstein-divides",
                "eisenstein-coprime",
            ][..],
        ),
        ("integer-defs", &["integer-equal"][..]),
        ("../fermat_statement", &["add"][..]),
        ("logic-exists", &["exists"][..]),
        ("logic-false", &["false-elimination"][..]),
        (
            "logical-connectives",
            &[
                "conjunction",
                "conjunction-introduce",
                "conjunction-left",
                "disjunction",
                "disjunction-eliminate",
            ][..],
        ),
        (
            "eisenstein-equality",
            &[
                "eisenstein-reflexive",
                "eisenstein-symmetric",
                "eisenstein-transitive",
                "eisenstein-multiply-congruent",
            ][..],
        ),
        (
            "eisenstein-ring",
            &["eisenstein-multiply-one", "eisenstein-negate-involution"][..],
        ),
        (
            "eisenstein-divisibility",
            &[
                "eisenstein-divides-reflexive",
                "eisenstein-divides-zero",
                "eisenstein-divides-congruent-target",
            ][..],
        ),
        (
            "eisenstein-additive-divisibility",
            &["eisenstein-divides-negative-target"][..],
        ),
        ("eisenstein-cubic-bridge", &["eisenstein-one-unit"][..]),
        (
            "eisenstein-constants",
            &["eisenstein-omega-unit", "eisenstein-omega-cube"][..],
        ),
        (
            "eisenstein-power-divisibility",
            &["eisenstein-power-add"][..],
        ),
        (
            "eisenstein-lambda-decision-core",
            &["eisenstein-lambda-not-divides-one"][..],
        ),
        (
            "eisenstein-lambda-order",
            &[
                "eisenstein-lambda-order",
                "eisenstein-lambda-order-one",
                "eisenstein-lambda-order-step",
                "eisenstein-lambda-order-excludes-higher",
            ][..],
        ),
        (
            "eisenstein-cubic-factorization",
            &[
                "eisenstein-sum-cubes-factor",
                "eisenstein-cube-product",
                "eisenstein-omega-square-unit",
                "eisenstein-omega-product-cube",
                "eisenstein-omega-square-product-cube",
            ][..],
        ),
        (
            "eisenstein-cubic-factor-choice",
            &["eisenstein-lambda-square-divides-one-of-three-factors"][..],
        ),
        (
            "eisenstein-cubic-unit-rotation",
            &["eisenstein-unit-coprime-right"][..],
        ),
        (
            "eisenstein-cubic-orientation",
            &[
                "eisenstein-oriented-cubic-pair",
                "eisenstein-cubic-solution-has-oriented-pair",
            ][..],
        ),
    ] {
        for name in names {
            if !referenced.contains(name) {
                continue;
            }
            source.push_str(&format!(
                "(#alias {name} = {}::{name})\n",
                root.join(format!("{module}.lim")).display()
            ));
        }
    }
    source.push_str(&format!("(#theorem observed-cubic (#universes) (#parameters) (#statement {statement}) (#proof {proof}))"));
    fs::write(&path, &source).unwrap();
    let result = check_theorem_details_from_path_with_config(
        &source,
        &path,
        &cubic_orientation_config(),
        "observed-cubic",
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

fn power(x: &str, n: usize) -> String {
    term("eisenstein-power", &[x, &format!("(#pt-numeral {n})")])
}
fn product(x: &str, y: &str) -> String {
    term("eisenstein-multiply", &[x, y])
}
fn equal(x: &str, y: &str) -> String {
    term("eisenstein-equal", &[x, y])
}
fn reflexive(x: &str) -> String {
    term("eisenstein-reflexive", &[x])
}

#[test]
fn cubic_ring_identities_handle_nonreal_signed_values_and_reject_a_wrong_power() {
    let one = term("eisenstein-one", &[]);
    let omega = term("eisenstein-omega", &[]);
    let a = term("eisenstein-add", &[&one, &omega]);
    let b = term("eisenstein-negate", &[&omega]);
    let factor = product(
        &product(
            &term("eisenstein-add", &[&a, &b]),
            &term("eisenstein-add", &[&a, &product(&omega, &b)]),
        ),
        &term("eisenstein-add", &[&a, &product(&power(&omega, 2), &b)]),
    );
    let sum = term("eisenstein-add", &[&power(&a, 3), &power(&b, 3)]);
    fixture(
        &equal(&sum, &factor),
        &term("eisenstein-sum-cubes-factor", &[&a, &b]),
        true,
    );
    for (unit, name) in [
        (&omega, "eisenstein-omega-product-cube"),
        (&power(&omega, 2), "eisenstein-omega-square-product-cube"),
    ] {
        fixture(
            &equal(&power(&product(unit, &b), 3), &power(&b, 3)),
            &term(name, &[&b]),
            true,
        );
    }
    // Replacing the cube by the square would claim omega^2 = 1.
    // Its real-coordinate equation is 0 = 2 because omega^2 = -1-omega.
    // Project the actual cube proof and reject that false scalar claim.
    let scalar_proof = "(#pt-project conjunction 0 (#pt-use eisenstein-omega-cube ()))";
    fixture(
        "(#pt-eq #pt-nat #pt-zero (#pt-numeral 2))",
        scalar_proof,
        false,
    );
}

fn lambda_order_one() -> String {
    term(
        "eisenstein-lambda-order-step",
        &[
            &term("eisenstein-one", &[]),
            "#pt-zero",
            &term("eisenstein-lambda-order-one", &[]),
        ],
    )
}
fn lambda_first_power_not_square() -> String {
    let lambda = term("eisenstein-lambda", &[]);
    let higher = "(#pt-construct exists (0) (#pt-nat (#pt-lambda ((gap #pt-nat)) (#pt-eq #pt-nat (#pt-numeral 2) (#pt-app (#pt-use add ()) (#pt-numeral 2) gap)))) introduce (#pt-zero (#pt-refl #pt-nat (#pt-numeral 2))))";
    term(
        "eisenstein-lambda-order-excludes-higher",
        &[
            &power(&lambda, 1),
            "(#pt-numeral 1)",
            "(#pt-numeral 2)",
            &lambda_order_one(),
            higher,
        ],
    )
}

#[test]
fn fourth_power_divisibility_selects_each_square_factor_and_rejects_an_incorrect_order() {
    let lambda = term("eisenstein-lambda", &[]);
    let fourth = power(&lambda, 4);
    for selected in 0..3 {
        let exponents: Vec<usize> = (0..3)
            .map(|index| if index == selected { 2 } else { 1 })
            .collect();
        let xs: Vec<String> = exponents.iter().map(|&n| power(&lambda, n)).collect();
        let pair = product(&xs[0], &xs[1]);
        let all = product(&pair, &xs[2]);
        let pair_power = power(&lambda, exponents[0] + exponents[1]);
        let pair_equivalence = term(
            "eisenstein-symmetric",
            &[
                &pair_power,
                &pair,
                &term(
                    "eisenstein-power-add",
                    &[
                        &lambda,
                        &format!("(#pt-numeral {})", exponents[0]),
                        &format!("(#pt-numeral {})", exponents[1]),
                    ],
                ),
            ],
        );
        let middle = product(&pair_power, &xs[2]);
        let step = term(
            "eisenstein-multiply-congruent",
            &[
                &pair,
                &xs[2],
                &pair_power,
                &xs[2],
                &pair_equivalence,
                &reflexive(&xs[2]),
            ],
        );
        let last = term(
            "eisenstein-symmetric",
            &[
                &fourth,
                &middle,
                &term(
                    "eisenstein-power-add",
                    &[
                        &lambda,
                        &format!("(#pt-numeral {})", exponents[0] + exponents[1]),
                        &format!("(#pt-numeral {})", exponents[2]),
                    ],
                ),
            ],
        );
        let relation = term(
            "eisenstein-transitive",
            &[&all, &middle, &fourth, &step, &last],
        );
        let divides = term(
            "eisenstein-divides-congruent-target",
            &[
                &fourth,
                &fourth,
                &all,
                &term("eisenstein-symmetric", &[&all, &fourth, &relation]),
                &term("eisenstein-divides-reflexive", &[&fourth]),
            ],
        );
        let ps: Vec<String> = xs
            .iter()
            .map(|x| term("eisenstein-divides", &[&power(&lambda, 2), x]))
            .collect();
        let choice = term(
            "eisenstein-lambda-square-divides-one-of-three-factors",
            &[&xs[0], &xs[1], &xs[2], &divides],
        );
        let selected_prop = &ps[selected];
        let branch = |index: usize| {
            let binding = format!("square-{index}");
            let body = if index == selected {
                binding.clone()
            } else {
                term(
                    "false-elimination",
                    &[
                        selected_prop,
                        &format!("(#pt-app {} {binding})", lambda_first_power_not_square()),
                    ],
                )
            };
            format!("(#pt-lambda (({binding} {})) {body})", ps[index])
        };
        let rest = term("disjunction", &[&ps[1], &ps[2]]);
        let second = term(
            "disjunction-eliminate",
            &[
                &ps[1],
                &ps[2],
                selected_prop,
                &branch(1),
                &branch(2),
                "remaining",
            ],
        );
        let proof = term(
            "disjunction-eliminate",
            &[
                &ps[0],
                &rest,
                selected_prop,
                &branch(0),
                &format!("(#pt-lambda ((remaining {rest})) {second})"),
                &choice,
            ],
        );
        fixture(selected_prop, &proof, true);
    }
    let wrong = term(
        "eisenstein-lambda-order",
        &[&power(&lambda, 1), "(#pt-numeral 2)"],
    );
    fixture(&wrong, &lambda_order_one(), false);
}

fn coprime_with_one(first: &str, second: &str) -> String {
    let one = term("eisenstein-one", &[]);
    let zero = term("eisenstein-zero", &[]);
    let right = format!(
        "(#pt-lambda ((right-factor (#pt-use eisenstein ()))) {})",
        equal(
            &one,
            &term(
                "eisenstein-add",
                &[&product(&one, first), &product("right-factor", second)]
            )
        )
    );
    let left = format!("(#pt-lambda ((left-factor (#pt-use eisenstein ()))) (#pt-app (#pt-use exists (0)) (#pt-use eisenstein ()) (#pt-lambda ((right-factor (#pt-use eisenstein ()))) {})))",
        equal(&one,&term("eisenstein-add", &[&product("left-factor",first),&product("right-factor",second)])));
    let right_proof = format!(
        "(#pt-construct exists (0) ((#pt-use eisenstein ()) {right}) introduce ({zero} {}))",
        reflexive(&one)
    );
    format!("(#pt-construct exists (0) ((#pt-use eisenstein ()) {left}) introduce ({one} {right_proof}))")
}

#[test]
fn unit_rotation_checks_its_actual_bezout_witness() {
    let one = term("eisenstein-one", &[]);
    let zero = term("eisenstein-zero", &[]);
    let omega = term("eisenstein-omega", &[]);
    for (unit, certificate) in [
        (&omega, term("eisenstein-omega-unit", &[])),
        (&power(&omega, 2), term("eisenstein-omega-square-unit", &[])),
    ] {
        let proof = term(
            "eisenstein-unit-coprime-right",
            &[
                &one,
                &one,
                unit,
                &certificate,
                &coprime_with_one(&one, &one),
            ],
        );
        fixture(
            &term("eisenstein-coprime", &[&one, &product(unit, &one)]),
            &proof,
            true,
        );
    }
    let proof = term(
        "eisenstein-unit-coprime-right",
        &[
            &zero,
            &zero,
            &omega,
            &term("eisenstein-omega-unit", &[]),
            &coprime_with_one(&zero, &zero),
        ],
    );
    fixture(
        &term("eisenstein-coprime", &[&zero, &product(&omega, &zero)]),
        &proof,
        false,
    );
}

#[test]
fn solution_orientation_constructs_a_pair_with_the_actual_equation_and_coprimality() {
    let one = term("eisenstein-one", &[]);
    let zero = term("eisenstein-zero", &[]);
    let lambda = term("eisenstein-lambda", &[]);
    let negative = term("eisenstein-negate", &[&one]);
    let premise = term("eisenstein-divides", &[&lambda, &negative]);
    let negated = term(
        "eisenstein-divides-negative-target",
        &[&lambda, &negative, "negative-divides"],
    );
    let corrected = term(
        "eisenstein-divides-congruent-target",
        &[
            &lambda,
            &term("eisenstein-negate", &[&negative]),
            &one,
            &term("eisenstein-negate-involution", &[&one]),
            &negated,
        ],
    );
    let nondiv = format!(
        "(#pt-lambda ((negative-divides {premise})) {})",
        term("eisenstein-lambda-not-divides-one", &[&corrected])
    );
    let sum = term("eisenstein-add", &[&power(&one, 3), &power(&negative, 3)]);
    let rhs = product(&one, &power(&zero, 3));
    let coordinate = |index: usize| {
        term(
            "integer-equal",
            &[
                &format!("(#pt-project eisenstein {index} {sum})"),
                &format!("(#pt-project eisenstein {index} {rhs})"),
            ],
        )
    };
    let equation = term(
        "conjunction-introduce",
        &[
            &coordinate(0),
            &coordinate(1),
            "(#pt-refl #pt-nat (#pt-numeral 1))",
            "(#pt-refl #pt-nat #pt-zero)",
        ],
    );
    let statement = format!("(#pt-app (#pt-use exists (0)) (#pt-use eisenstein ()) (#pt-lambda ((candidate-first (#pt-use eisenstein ()))) (#pt-app (#pt-use exists (0)) (#pt-use eisenstein ()) (#pt-lambda ((candidate-second (#pt-use eisenstein ()))) {}))))",
        term("eisenstein-oriented-cubic-pair", &["candidate-first","candidate-second",&zero,&one]));
    let proof = term(
        "eisenstein-cubic-solution-has-oriented-pair",
        &[
            &one,
            &negative,
            &zero,
            &one,
            &term("eisenstein-one-unit", &[]),
            &term("eisenstein-lambda-not-divides-one", &[]),
            &nondiv,
            &term("eisenstein-divides-zero", &[&lambda]),
            &equation,
            &coprime_with_one(&one, &negative),
        ],
    );
    fixture(&statement, &proof, true);
}

#[test]
fn orientation_cannot_drop_equation_or_coprimality_evidence() {
    let path =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("theorems/flt/eisenstein-cubic-orientation.lim");
    let source = std::fs::read_to_string(&path).unwrap();
    let target = "eisenstein-cubic-solution-has-oriented-pair";
    let start = source.find(&format!("(#theorem {target}")).unwrap();
    for name in ["solution-equation", "coprime-proof"] {
        let parameter = start
            + source[start..]
                .find(&format!("(#parameter {name} "))
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
            .expect("removing evidence keeps source syntax valid");
        let error = check_theorem_details_from_path_with_config(
            &changed,
            &path,
            &cubic_orientation_config(),
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
