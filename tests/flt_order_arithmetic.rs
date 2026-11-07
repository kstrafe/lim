//! Foundation-free checks for lambda order arithmetic and its numeric laws.
use lim::{
    check_theorem_details_from_path_with_config, CompileConfig, DiagnosticCode, ProofBudget,
};
use std::path::Path;

const ORDER_ARITHMETIC: &[(&str, &str)] = &[
    (
        "eisenstein-lambda-factor.lim",
        "eisenstein-lambda-power-multiply-cancel",
    ),
    (
        "eisenstein-lambda-factor.lim",
        "eisenstein-lambda-next-power-of-residual",
    ),
    (
        "eisenstein-lambda-factor.lim",
        "eisenstein-lambda-residual-of-next-power",
    ),
    (
        "eisenstein-lambda-factor.lim",
        "eisenstein-lambda-order-residual-not-divides",
    ),
    (
        "eisenstein-lambda-factor.lim",
        "eisenstein-lambda-order-of-residual",
    ),
    (
        "eisenstein-lambda-factor.lim",
        "eisenstein-lambda-order-residual-exists",
    ),
    (
        "eisenstein-lambda-order-arithmetic.lim",
        "eisenstein-lambda-not-divides-product",
    ),
    (
        "eisenstein-lambda-order-arithmetic.lim",
        "eisenstein-lambda-order-multiply",
    ),
    (
        "eisenstein-lambda-order-arithmetic.lim",
        "eisenstein-lambda-order-power",
    ),
    (
        "eisenstein-lambda-order-arithmetic.lim",
        "eisenstein-lambda-order-unit",
    ),
    (
        "eisenstein-lambda-order-arithmetic.lim",
        "eisenstein-lambda-order-unit-multiply",
    ),
    (
        "eisenstein-lambda-order-bounds.lim",
        "eisenstein-lambda-order-divides-below",
    ),
    (
        "eisenstein-lambda-order-bounds.lim",
        "eisenstein-lambda-order-divisibility-upper",
    ),
    (
        "eisenstein-lambda-order-bounds.lim",
        "eisenstein-lambda-order-divisibility-lower",
    ),
    (
        "eisenstein-lambda-cubic-divisibility.lim",
        "eisenstein-lambda-order-at-least-two-from-cube",
    ),
    (
        "eisenstein-lambda-cubic-divisibility.lim",
        "eisenstein-lambda-square-divides-from-cube",
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

#[test]
fn order_arithmetic_theorems_are_foundation_free() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let config = order_config();
    for &(module, target) in ORDER_ARITHMETIC {
        let path = root.join("theorems/flt").join(module);
        let source = std::fs::read_to_string(&path)
            .unwrap_or_else(|error| panic!("failed to read {}: {error}", path.display()));
        let report = check_theorem_details_from_path_with_config(&source, &path, &config, target)
            .unwrap_or_else(|error| panic!("failed to check {target}: {}", error.message));
        assert!(
            report.name == target || report.name.ends_with(&format!("::{target}")),
            "unexpected canonical target for {}: {}",
            path.display(),
            report.name
        );
        assert!(
            report.foundations.is_empty(),
            "foundations for {target}: {:?}",
            report.foundations
        );
    }
}

fn order_call(name: &str, args: &[&str]) -> String {
    format!("(#pt-app (#pt-use {name} ()) {})", args.join(" "))
}

fn numeric_fixture(statement: &str, proof: &str, valid: bool) {
    use std::{
        fs,
        sync::atomic::{AtomicUsize, Ordering},
    };
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let directory = std::env::temp_dir().join(format!(
        "lim-flt-order-arithmetic-{}-{}",
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
        ("eisenstein-equal", "eisenstein-defs.lim"),
        ("eisenstein-divides", "eisenstein-defs.lim"),
        ("eisenstein-negate", "eisenstein-defs.lim"),
        ("eisenstein-minus-one-unit", "eisenstein-constants.lim"),
        (
            "eisenstein-lambda-order-unit-multiply",
            "eisenstein-lambda-order-arithmetic.lim",
        ),
        (
            "eisenstein-lambda-order-nonzero",
            "eisenstein-lambda-order.lim",
        ),
        (
            "eisenstein-lambda-order-divisibility-lower",
            "eisenstein-lambda-order-bounds.lim",
        ),
        (
            "eisenstein-lambda-square-divides-from-cube",
            "eisenstein-lambda-cubic-divisibility.lim",
        ),
        ("eisenstein-divides-zero", "eisenstein-divisibility.lim"),
        ("not-less-than-addition", "natural-discrete-order.lim"),
        ("successor-not-zero", "natural-nonzero.lim"),
        ("eisenstein-lambda", "eisenstein-defs.lim"),
        ("eisenstein-multiply", "eisenstein-defs.lim"),
        ("eisenstein-power", "eisenstein-defs.lim"),
        ("eisenstein-lambda-order", "eisenstein-lambda-order.lim"),
        ("eisenstein-lambda-order-one", "eisenstein-lambda-order.lim"),
        (
            "eisenstein-lambda-order-step",
            "eisenstein-lambda-order.lim",
        ),
        (
            "eisenstein-lambda-order-multiply",
            "eisenstein-lambda-order-arithmetic.lim",
        ),
        (
            "eisenstein-lambda-order-power",
            "eisenstein-lambda-order-arithmetic.lim",
        ),
        ("add", "../fermat_statement.lim"),
        ("multiply", "../fermat_statement.lim"),
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
fn products_add_the_orders_and_reject_wrong_indices() {
    let one = "(#pt-use eisenstein-one ())";
    let order_one = "(#pt-use eisenstein-lambda-order-one ())";
    let lambda = "(#pt-use eisenstein-lambda ())";
    let step = order_call(
        "eisenstein-lambda-order-step",
        &[one, "#pt-zero", order_one],
    );
    let lambda_one = order_call("eisenstein-multiply", &[lambda, one]);
    let product = order_call(
        "eisenstein-multiply",
        &[lambda_one.as_str(), lambda_one.as_str()],
    );
    let product_proof = order_call(
        "eisenstein-lambda-order-multiply",
        &[
            lambda_one.as_str(),
            lambda_one.as_str(),
            "(#pt-succ #pt-zero)",
            "(#pt-succ #pt-zero)",
            step.as_str(),
            step.as_str(),
        ],
    );
    let expected = "(#pt-numeral 2)";
    numeric_fixture(
        &order_call("eisenstein-lambda-order", &[product.as_str(), expected]),
        &product_proof,
        true,
    );
    numeric_fixture(
        &order_call(
            "eisenstein-lambda-order",
            &[product.as_str(), "(#pt-numeral 3)"],
        ),
        &product_proof,
        false,
    );
}

#[test]
fn arbitrary_power_preserves_zero_and_scales_positive_order() {
    let (base, certificate) = lambda_squared_parts();
    let zero_power = order_call("eisenstein-power", &[&base, "#pt-zero"]);
    let zero_proof = order_call(
        "eisenstein-lambda-order-power",
        &[&base, "(#pt-numeral 2)", "#pt-zero", &certificate],
    );
    numeric_fixture(
        &order_call("eisenstein-lambda-order", &[&zero_power, "#pt-zero"]),
        &zero_proof,
        true,
    );
    let square = order_call("eisenstein-power", &[&base, "(#pt-numeral 2)"]);
    let square_proof = order_call(
        "eisenstein-lambda-order-power",
        &[&base, "(#pt-numeral 2)", "(#pt-numeral 2)", &certificate],
    );
    numeric_fixture(
        &order_call("eisenstein-lambda-order", &[&square, "(#pt-numeral 4)"]),
        &square_proof,
        true,
    );
    numeric_fixture(
        &order_call("eisenstein-lambda-order", &[&square, "(#pt-numeral 2)"]),
        &square_proof,
        false,
    );
}

fn lambda_squared_parts() -> (String, String) {
    let one = "(#pt-use eisenstein-one ())";
    let lambda = "(#pt-use eisenstein-lambda ())";
    let first = order_call("eisenstein-multiply", &[lambda, one]);
    let first_certificate = order_call(
        "eisenstein-lambda-order-step",
        &[one, "#pt-zero", "(#pt-use eisenstein-lambda-order-one ())"],
    );
    let second = order_call("eisenstein-multiply", &[lambda, &first]);
    let certificate = order_call(
        "eisenstein-lambda-order-step",
        &[&first, "(#pt-numeral 1)", &first_certificate],
    );
    (second, certificate)
}

#[test]
fn units_preserve_the_order_of_an_actual_value() {
    let (value, certificate) = lambda_squared_parts();
    let negative_one = order_call("eisenstein-negate", &["(#pt-use eisenstein-one ())"]);
    let product = order_call("eisenstein-multiply", &[&negative_one, &value]);
    let proof = order_call(
        "eisenstein-lambda-order-unit-multiply",
        &[
            &negative_one,
            &value,
            "(#pt-numeral 2)",
            "(#pt-use eisenstein-minus-one-unit ())",
            &certificate,
        ],
    );
    numeric_fixture(
        &order_call("eisenstein-lambda-order", &[&product, "(#pt-numeral 2)"]),
        &proof,
        true,
    );
}

#[test]
fn cubic_orders_supply_the_real_fourth_power_premise() {
    let (value, certificate) = lambda_squared_parts();
    let cube = order_call("eisenstein-power", &[&value, "(#pt-numeral 3)"]);
    let cube_certificate = order_call(
        "eisenstein-lambda-order-power",
        &[&value, "(#pt-numeral 2)", "(#pt-numeral 3)", &certificate],
    );
    let bounded = order_call(
        "not-less-than-addition",
        &["(#pt-numeral 4)", "(#pt-numeral 2)"],
    );
    let fourth_divides = order_call(
        "eisenstein-lambda-order-divisibility-lower",
        &[
            &cube,
            "(#pt-numeral 6)",
            "(#pt-numeral 4)",
            &cube_certificate,
            &bounded,
        ],
    );
    let nonzero = order_call(
        "eisenstein-lambda-order-nonzero",
        &[&value, "(#pt-numeral 2)", &certificate],
    );
    let proof = order_call(
        "eisenstein-lambda-square-divides-from-cube",
        &[&value, &nonzero, &fourth_divides],
    );
    let square = order_call(
        "eisenstein-power",
        &["(#pt-use eisenstein-lambda ())", "(#pt-numeral 2)"],
    );
    numeric_fixture(
        &order_call("eisenstein-divides", &[&square, &value]),
        &proof,
        true,
    );
    // A cube of order six cannot use the same bound to certify power seven.
    let false_division = order_call(
        "eisenstein-lambda-order-divisibility-lower",
        &[
            &cube,
            "(#pt-numeral 6)",
            "(#pt-numeral 7)",
            &cube_certificate,
            &bounded,
        ],
    );
    let seventh = order_call(
        "eisenstein-power",
        &["(#pt-use eisenstein-lambda ())", "(#pt-numeral 7)"],
    );
    numeric_fixture(
        &order_call("eisenstein-divides", &[&seventh, &cube]),
        &false_division,
        false,
    );
}

#[test]
fn cubic_divisibility_does_not_accept_forged_nonzero_evidence() {
    let zero = "(#pt-use eisenstein-zero ())";
    let equal = order_call("eisenstein-equal", &[zero, zero]);
    let fake = format!("(#pt-lambda ((zero-proof {equal})) (#pt-app (#pt-use successor-not-zero ()) #pt-zero (#pt-refl #pt-nat #pt-zero)))");
    let fourth = order_call(
        "eisenstein-power",
        &["(#pt-use eisenstein-lambda ())", "(#pt-numeral 4)"],
    );
    let division = order_call("eisenstein-divides-zero", &[&fourth]);
    let proof = order_call(
        "eisenstein-lambda-square-divides-from-cube",
        &[zero, &fake, &division],
    );
    let square = order_call(
        "eisenstein-power",
        &["(#pt-use eisenstein-lambda ())", "(#pt-numeral 2)"],
    );
    numeric_fixture(
        &order_call("eisenstein-divides", &[&square, zero]),
        &proof,
        false,
    );
}
