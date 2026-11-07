//! Foundation-free checks for Eisenstein divisibility and lambda multiplicity.
use lim::{
    check_theorem_details_from_path_with_config, CompileConfig, DiagnosticCode, ProofBudget,
};
use std::path::{Path, PathBuf};

const INFRASTRUCTURE: &[(&str, &str)] = &[
    (
        "eisenstein-divisibility.lim",
        "eisenstein-divides-reflexive",
    ),
    ("eisenstein-divisibility.lim", "eisenstein-one-divides"),
    ("eisenstein-divisibility.lim", "eisenstein-divides-zero"),
    (
        "eisenstein-divisibility.lim",
        "eisenstein-divides-congruent-target",
    ),
    (
        "eisenstein-divisibility.lim",
        "eisenstein-divides-congruent-divisor",
    ),
    (
        "eisenstein-divisibility.lim",
        "eisenstein-divides-transitive",
    ),
    (
        "eisenstein-divisibility.lim",
        "eisenstein-divides-product-left",
    ),
    (
        "eisenstein-divisibility.lim",
        "eisenstein-divides-product-right",
    ),
    ("eisenstein-divisibility.lim", "eisenstein-divisor-nonzero"),
    ("eisenstein-power-divisibility.lim", "eisenstein-power-one"),
    ("eisenstein-power-divisibility.lim", "eisenstein-power-add"),
    ("eisenstein-domain-powers.lim", "eisenstein-power-nonzero"),
    (
        "eisenstein-power-divisibility.lim",
        "eisenstein-power-divisor",
    ),
    (
        "eisenstein-power-divisibility.lim",
        "eisenstein-power-divides-add",
    ),
    (
        "eisenstein-power-divisibility.lim",
        "eisenstein-power-divides-product-raise",
    ),
    (
        "eisenstein-domain-powers.lim",
        "eisenstein-power-divides-product-cancel",
    ),
    (
        "eisenstein-power-divisibility.lim",
        "eisenstein-power-divides-step",
    ),
];

const MULTIPLICITY: &[(&str, &str)] = &[
    (
        "eisenstein-lambda-power-decision.lim",
        "eisenstein-lambda-power-divisibility-decided",
    ),
    (
        "eisenstein-lambda-order.lim",
        "eisenstein-lambda-order-exists",
    ),
    (
        "eisenstein-lambda-order.lim",
        "eisenstein-lambda-order-excludes-higher",
    ),
    (
        "eisenstein-lambda-order.lim",
        "eisenstein-lambda-order-unique",
    ),
    (
        "eisenstein-lambda-order.lim",
        "eisenstein-lambda-order-congruent",
    ),
    (
        "eisenstein-lambda-order.lim",
        "eisenstein-lambda-order-nonzero",
    ),
    ("eisenstein-lambda-order.lim", "eisenstein-lambda-order-one"),
    (
        "eisenstein-lambda-order.lim",
        "eisenstein-lambda-order-step",
    ),
];

fn order_config() -> CompileConfig {
    let mut config = CompileConfig::default();
    let default = ProofBudget::default();
    config.set_proof_budget(
        ProofBudget::new(default.work(), default.phase_bytes(), 512 * 1024 * 1024).unwrap(),
    );
    config
}

fn check_matrix(targets: &[(&str, &str)], config: &CompileConfig) {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    for &(module, target) in targets {
        let path = root.join("theorems/flt").join(module);
        let source = std::fs::read_to_string(&path)
            .unwrap_or_else(|error| panic!("failed to read {}: {error}", path.display()));
        let report = check_theorem_details_from_path_with_config(&source, &path, config, target)
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
fn infrastructure_theorems_are_foundation_free() {
    check_matrix(INFRASTRUCTURE, &CompileConfig::default());
}

#[test]
fn multiplicity_theorems_are_foundation_free() {
    check_matrix(MULTIPLICITY, &order_config());
}

fn changed_statement_rejected(file: &str, target: &str, statement: &str) {
    let path: PathBuf = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("theorems/flt")
        .join(file);
    let source = std::fs::read_to_string(&path).unwrap();
    let marker = format!("(#theorem {target}");
    let theorem = source.find(&marker).unwrap();
    let start = source[theorem..].find("(#statement").unwrap() + theorem;
    let end = end_of_form(&source, start);
    let changed = format!("{}{}{}", &source[..start], statement, &source[end..]);
    lim::parse_program_from_path(&changed, &path).expect("mutation remains valid Lim source");
    let error =
        check_theorem_details_from_path_with_config(&changed, &path, &order_config(), target)
            .unwrap_err();
    assert_eq!(
        error.code,
        DiagnosticCode::Proof,
        "unexpected rejection for {target}: {}",
        error.message
    );
    assert!(error.message.contains("mismatch"), "{}", error.message);
}

fn end_of_form(source: &str, start: usize) -> usize {
    let bytes = source.as_bytes();
    let mut depth = 0usize;
    for (offset, byte) in bytes[start..].iter().enumerate() {
        match byte {
            b'(' => depth += 1,
            b')' => {
                depth -= 1;
                if depth == 0 {
                    return start + offset + 1;
                }
            }
            _ => {}
        }
    }
    panic!("unterminated form")
}

#[test]
fn order_excludes_strictly_higher_exponents_only() {
    let one = "(#pt-use eisenstein-one ())";
    let evidence = order_call("less-than-successor", &["#pt-zero"]);
    for (higher, valid) in [("(#pt-succ #pt-zero)", true), ("#pt-zero", false)] {
        // The same known proof 0<1 is valid only for the higher exponent.
        // It cannot discharge the impossible strictness premise 0<0.
        let proof = order_call(
            "eisenstein-lambda-order-excludes-higher",
            &[
                one,
                "#pt-zero",
                higher,
                "(#pt-use eisenstein-lambda-order-one ())",
                &evidence,
            ],
        );
        let divisor = order_call(
            "eisenstein-power",
            &["(#pt-use eisenstein-lambda ())", higher],
        );
        let division = order_call("eisenstein-divides", &[&divisor, one]);
        let statement = format!("(#pt-pi ((denied-proof {division})) #pt-false)");
        numeric_order_fixture(&statement, &proof, valid);
    }
}

#[test]
fn the_unit_one_does_not_have_order_one() {
    changed_statement_rejected(
        "eisenstein-lambda-order.lim",
        "eisenstein-lambda-order-one",
        "(#statement (#pt-app (#pt-use eisenstein-lambda-order ()) (#pt-use eisenstein-one ()) (#pt-succ #pt-zero)))",
    );
}

#[test]
fn product_cancellation_requires_a_nonzero_base() {
    let path: PathBuf =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("theorems/flt/eisenstein-domain-powers.lim");
    let source = std::fs::read_to_string(&path).unwrap();
    let target = "eisenstein-power-divides-product-cancel";
    let theorem = source.find(&format!("(#theorem {target}")).unwrap();
    let parameter = theorem + source[theorem..].find("(#parameter base-nonzero").unwrap();
    let end = end_of_form(&source, parameter);
    let changed = format!("{}{}", &source[..parameter], &source[end..]);
    lim::parse_program_from_path(&changed, &path)
        .expect("weakened cancellation declaration parses");
    let error =
        check_theorem_details_from_path_with_config(&changed, &path, &order_config(), target)
            .unwrap_err();
    assert_eq!(error.code, DiagnosticCode::Proof);
    assert!(error.message.contains("base-nonzero"), "{}", error.message);
}

const FOCUSED_ARITHMETIC: &[(&str, &str)] = &[
    (
        "eisenstein-lambda-cancellation.lim",
        "eisenstein-scalar-multiply-real",
    ),
    (
        "eisenstein-lambda-cancellation.lim",
        "eisenstein-scalar-multiply-omega",
    ),
    (
        "eisenstein-lambda-cancellation.lim",
        "eisenstein-natural-multiply-cancel",
    ),
    (
        "eisenstein-lambda-cancellation.lim",
        "eisenstein-natural-divisor-cancel",
    ),
    (
        "eisenstein-lambda-cancellation.lim",
        "eisenstein-lambda-multiply-cancel",
    ),
    (
        "eisenstein-lambda-cancellation.lim",
        "eisenstein-lambda-power-divides-product-cancel",
    ),
    (
        "eisenstein-lambda-cancellation.lim",
        "eisenstein-lambda-power-nonzero",
    ),
    (
        "eisenstein-lambda-decision-core.lim",
        "eisenstein-coordinate-sum-congruent",
    ),
    (
        "eisenstein-lambda-decision-core.lim",
        "integer-three-divides-coordinate-sum",
    ),
    (
        "eisenstein-lambda-decision-core.lim",
        "eisenstein-lambda-divides-of-coordinate-sum",
    ),
    (
        "eisenstein-lambda-decision-core.lim",
        "eisenstein-lambda-not-divides-one",
    ),
    (
        "eisenstein-lambda-decision-core.lim",
        "eisenstein-lambda-divisibility-decided",
    ),
    (
        "eisenstein-lambda-norm-descent.lim",
        "eisenstein-lambda-norm-multiply",
    ),
    (
        "eisenstein-lambda-norm-descent.lim",
        "eisenstein-nonzero-natural-norm",
    ),
    (
        "eisenstein-lambda-norm-descent.lim",
        "eisenstein-lambda-quotient-nonzero",
    ),
    (
        "eisenstein-lambda-norm-descent.lim",
        "eisenstein-lambda-quotient-norm-equation",
    ),
    (
        "eisenstein-lambda-norm-descent.lim",
        "eisenstein-lambda-quotient-norm-less",
    ),
    (
        "eisenstein-norm-scalar-lambda-multiply.lim",
        "eisenstein-norm-scalar-lambda-multiply",
    ),
];

#[test]
fn focused_lambda_arithmetic_is_foundation_free() {
    check_matrix(FOCUSED_ARITHMETIC, &order_config());
}

fn order_call(name: &str, args: &[&str]) -> String {
    format!("(#pt-app (#pt-use {name} ()) {})", args.join(" "))
}

fn numeric_order_fixture(statement: &str, proof: &str, valid: bool) {
    use std::{
        fs,
        sync::atomic::{AtomicUsize, Ordering},
    };
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let directory = std::env::temp_dir().join(format!(
        "lim-flt-order-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir(&directory).unwrap();
    let path = directory.join("probe.lim");
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("theorems/flt");
    let mut source = String::new();
    for (name, module) in [
        ("eisenstein", "eisenstein-defs.lim"),
        ("integer", "integer-defs.lim"),
        ("eisenstein-equal", "eisenstein-defs.lim"),
        ("eisenstein-divides", "eisenstein-defs.lim"),
        ("less-than-successor", "natural-order.lim"),
        (
            "eisenstein-lambda-order-excludes-higher",
            "eisenstein-lambda-order.lim",
        ),
        ("eisenstein-zero", "eisenstein-defs.lim"),
        ("eisenstein-one", "eisenstein-defs.lim"),
        ("eisenstein-lambda", "eisenstein-defs.lim"),
        ("eisenstein-power", "eisenstein-defs.lim"),
        ("eisenstein-multiply", "eisenstein-defs.lim"),
        ("integer-equal", "integer-defs.lim"),
        ("conjunction-introduce", "logical-connectives.lim"),
        ("successor-not-zero", "natural-nonzero.lim"),
        ("eisenstein-lambda-order", "eisenstein-lambda-order.lim"),
        ("eisenstein-lambda-order-one", "eisenstein-lambda-order.lim"),
        (
            "eisenstein-lambda-order-step",
            "eisenstein-lambda-order.lim",
        ),
        (
            "eisenstein-lambda-order-congruent",
            "eisenstein-lambda-order.lim",
        ),
        (
            "eisenstein-lambda-order-exists",
            "eisenstein-lambda-order.lim",
        ),
        ("exists", "logic-exists.lim"),
    ] {
        source.push_str(&format!(
            "(#alias {name} = {}::{name})\n",
            root.join(module).display()
        ));
    }
    source.push_str(&format!("(#theorem observed-order (#universes) (#parameters) (#statement {statement}) (#proof {proof}))"));
    fs::write(&path, &source).unwrap();
    let result = check_theorem_details_from_path_with_config(
        &source,
        &path,
        &order_config(),
        "observed-order",
    );
    fs::remove_dir_all(&directory).unwrap();
    if valid {
        assert!(result
            .unwrap_or_else(|error| panic!("{}", error.message))
            .foundations
            .is_empty());
    } else {
        let error = result.unwrap_err();
        assert_eq!(error.code, DiagnosticCode::Proof);
        assert!(error.message.contains("mismatch"), "{}", error.message);
    }
}

#[test]
fn lambda_steps_have_exact_orders_and_reject_off_by_one_orders() {
    let lambda = "(#pt-use eisenstein-lambda ())";
    let mut value = "(#pt-use eisenstein-one ())".to_owned();
    let mut proof = "(#pt-use eisenstein-lambda-order-one ())".to_owned();
    for exponent in 0..3 {
        let index = format!("(#pt-numeral {exponent})");
        let wrong = format!("(#pt-numeral {})", exponent + 1);
        numeric_order_fixture(
            &order_call("eisenstein-lambda-order", &[&value, &index]),
            &proof,
            true,
        );
        numeric_order_fixture(
            &order_call("eisenstein-lambda-order", &[&value, &wrong]),
            &proof,
            false,
        );
        proof = order_call("eisenstein-lambda-order-step", &[&value, &index, &proof]);
        value = order_call("eisenstein-multiply", &[lambda, &value]);
    }
}

#[test]
fn order_transfers_through_equivalent_noncanonical_integer_coordinates() {
    let one = "(#pt-use eisenstein-one ())";
    let other = "(#pt-construct eisenstein () () pair ((#pt-construct integer () () difference ((#pt-numeral 2) (#pt-numeral 1))) (#pt-construct integer () () difference (#pt-zero #pt-zero))))";
    let coordinate =
        |index: usize, value: &str| format!("(#pt-project eisenstein {index} {value})");
    let real_equal = order_call(
        "integer-equal",
        &[&coordinate(0, one), &coordinate(0, other)],
    );
    let omega_equal = order_call(
        "integer-equal",
        &[&coordinate(1, one), &coordinate(1, other)],
    );
    let equal = order_call(
        "conjunction-introduce",
        &[
            &real_equal,
            &omega_equal,
            "(#pt-refl #pt-nat (#pt-numeral 2))",
            "(#pt-refl #pt-nat #pt-zero)",
        ],
    );
    let proof = order_call(
        "eisenstein-lambda-order-congruent",
        &[
            one,
            other,
            "#pt-zero",
            &equal,
            "(#pt-use eisenstein-lambda-order-one ())",
        ],
    );
    numeric_order_fixture(
        &order_call("eisenstein-lambda-order", &[other, "#pt-zero"]),
        &proof,
        true,
    );
}

#[test]
fn zero_cannot_supply_the_nonzero_premise_for_order_existence() {
    let zero = "(#pt-use eisenstein-zero ())";
    let equal = order_call("eisenstein-equal", &[zero, zero]);
    let fake_nonzero = format!("(#pt-lambda ((zero-proof {equal})) (#pt-app (#pt-use successor-not-zero ()) #pt-zero (#pt-refl #pt-nat #pt-zero)))");
    let proof = order_call("eisenstein-lambda-order-exists", &[zero, &fake_nonzero]);
    let candidate = order_call("eisenstein-lambda-order", &[zero, "candidate-order"]);
    let statement = format!("(#pt-app (#pt-use exists (0)) #pt-nat (#pt-lambda ((candidate-order #pt-nat)) {candidate}))");
    numeric_order_fixture(&statement, &proof, false);
}
