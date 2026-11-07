mod support;

use lim::{check_theorem_details_from_path_with_config, CompileConfig, DiagnosticCode};
use std::{fs, path::PathBuf, process::Command, time::Duration};

fn module(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("theorems/flt")
        .join(name)
}

#[test]
fn source_port_arithmetic_is_universally_checked_without_global_axioms() {
    let modules: &[(&str, &[&str])] = &[
        (
            "equality.lim",
            &["symmetry", "transitivity", "congruence", "substitution"],
        ),
        (
            "logical-connectives.lim",
            &[
                "conjunction-introduce",
                "conjunction-left",
                "conjunction-right",
                "disjunction-left",
                "disjunction-right",
                "disjunction-eliminate",
            ],
        ),
        ("decidable-logic.lim", &["decision-evidence"]),
        ("natural-decision.lim", &["natural-equality-decided"]),
        (
            "bounded-existence.lim",
            &["any-up-to-grow", "any-up-to-here"],
        ),
        (
            "bounded-search.lim",
            &[
                "any-up-to-has-witness",
                "any-up-to-with-gap",
                "bounded-existence-decided",
            ],
        ),
        (
            "decidable-divisibility.lim",
            &[
                "positive-divisor-bounded",
                "zero-divisor-equation",
                "zero-divisor-witness",
                "natural-divisibility-decided",
            ],
        ),
        (
            "decidable-order.lim",
            &[
                "less-than-bounded",
                "natural-order-decided",
                "any-up-to-from-less-successor",
            ],
        ),
        (
            "least-witness.lim",
            &[
                "bounded-minimum",
                "least-witness",
                "minimum-holds",
                "minimum-excludes-earlier",
            ],
        ),
        ("least-divisor.lim", &["least-nontrivial-divisor"]),
        (
            "natural-prime.lim",
            &[
                "least-divisor-is-prime",
                "exists-prime-divisor",
                "prime-larger-than-one",
                "prime-excludes-proper-divisor",
            ],
        ),
        (
            "natural-multiplication-commutative.lim",
            &[
                "add-left-commutative",
                "multiply-successor-right",
                "multiply-commutative",
            ],
        ),
        (
            "natural-small-cases.lim",
            &[
                "zero-one-or-large",
                "successor-below-double",
                "less-than-upper-nonzero",
            ],
        ),
        (
            "two-factor-classification.lim",
            &[
                "factor-two-divides-multiple",
                "two-power-or-prime-double",
                "classify-two-multiple",
                "classify-large-number",
                "classify-one-step",
                "classify-positive-number",
            ],
        ),
        (
            "natural-parity.lim",
            &[
                "even-or-odd",
                "prime-not-two-above-two",
                "prime-not-two-is-odd",
            ],
        ),
        (
            "divisor-dichotomy.lim",
            &[
                "non-two-prime-is-odd-divisor",
                "four-divides-or-odd-prime-divides",
            ],
        ),
        (
            "odd-prime-reduction.lim",
            &[
                "fermat-for-from-odd-primes",
                "fermat-statement-from-four-and-odd-primes",
            ],
        ),
        (
            "infinite-descent.lim",
            &["no-infinite-descent", "descent-refutes-existence"],
        ),
        (
            "natural-discrete-order.lim",
            &[
                "zero-less-successor",
                "successor-less-successor",
                "successor-less-reflect",
                "less-than-discrete-step",
                "natural-trichotomy",
                "not-less-than-addition",
            ],
        ),
        (
            "natural-multiplication-order.lim",
            &[
                "multiply-add-right",
                "multiply-less-right-successor",
                "multiply-less-left-successor",
                "multiply-cancel-right-successor",
                "multiply-cancel-left-successor",
            ],
        ),
        ("natural-division.lim", &["division-exists"]),
        (
            "natural-divisibility-addition.lim",
            &[
                "divides-add",
                "divides-add-cancel-successor",
                "divides-add-cancel-left",
            ],
        ),
        (
            "natural-divisibility-bounds.lim",
            &[
                "divisor-nonzero",
                "divisor-not-above",
                "divides-antisymmetric",
                "divides-one",
            ],
        ),
        (
            "natural-gcd.lim",
            &[
                "gcd-zero-right",
                "gcd-euclidean-step",
                "gcd-induction-step",
                "gcd-exists",
            ],
        ),
        (
            "natural-coprime.lim",
            &[
                "gcd-unique",
                "gcd-one-of-coprime",
                "coprime-of-gcd-one",
                "coprime-symmetric",
                "coprime-one-left",
                "coprime-add-left",
                "coprime-add-right",
                "coprime-euclidean-remainder",
                "coprime-euclidean-reconstruct",
            ],
        ),
        (
            "natural-gcd-scaling.lim",
            &[
                "gcd-euclidean-reverse",
                "gcd-scale-induction-step",
                "gcd-scale-right-successor",
                "gcd-scale-right",
            ],
        ),
        (
            "natural-euclid.lim",
            &[
                "coprime-gcd-one",
                "coprime-divides-product-left",
                "coprime-divisor-right",
                "coprime-multiply-left",
                "coprime-multiply-right",
                "coprime-power-left",
                "coprime-power-right",
                "coprime-square-sum",
                "coprime-square-sum-product",
            ],
        ),
        (
            "natural-prime-divisibility.lim",
            &[
                "prime-divisor-one-or-self",
                "prime-not-one",
                "prime-coprime-of-not-divides",
                "prime-divides-product",
                "prime-divides-power",
                "prime-divides-square",
            ],
        ),
        (
            "natural-square-arithmetic.lim",
            &[
                "multiply-left-commutative",
                "square-product",
                "multiply-less-right-nonzero",
                "multiply-cancel-left-nonzero",
                "nonunit-multiple-above",
            ],
        ),
        (
            "natural-square-factors.lim",
            &[
                "square-remove-first-factor",
                "square-remove-second-factor",
                "square-restore-double-prime-factor",
                "square-factor-prime-step",
                "square-factor-induction-step",
                "coprime-product-square",
            ],
        ),
        (
            "integer-addition.lim",
            &[
                "integer-add-commutative",
                "integer-add-associative",
                "integer-add-zero",
                "integer-add-inverse",
                "integer-negate-involution",
                "integer-negate-add",
                "integer-add-cancel-left",
            ],
        ),
        (
            "integer-cross-identities.lim",
            &[
                "sum-four-interchange",
                "sum-three-permutation",
                "product-cross-group",
            ],
        ),
        (
            "integer-cube-identities.lim",
            &[
                "cube-positive-positive-component",
                "cube-positive-negative-component",
                "cube-negative-positive-component",
                "cube-negative-negative-component",
            ],
        ),
        (
            "integer-cube-normalization.lim",
            &[
                "integer-cube-normal-positive",
                "integer-cube-normal-negative",
                "integer-cube-equation-transport",
                "integer-power-three-as-cube",
            ],
        ),
        (
            "integer-divisibility.lim",
            &[
                "integer-multiply-negative-second",
                "integer-multiply-two-negatives",
                "integer-divides-zero",
                "integer-divides-reflexive",
                "integer-divides-multiple",
                "integer-divides-congruent-target",
                "integer-divides-congruent-divisor",
                "integer-divides-transitive",
                "integer-divides-negative-target",
                "integer-divides-negative-divisor",
                "integer-divides-of-natural",
            ],
        ),
        (
            "integer-embedding-identities.lim",
            &[
                "natural-product-positive-component",
                "natural-product-negative-component",
            ],
        ),
        (
            "integer-equality.lim",
            &[
                "integer-reflexive",
                "integer-symmetric",
                "integer-transitive",
                "integer-negate-congruent",
                "integer-add-congruent",
                "integer-multiply-congruent-first",
                "integer-of-natural-injective",
                "integer-negative-natural-injective",
            ],
        ),
        (
            "integer-multiplication.lim",
            &[
                "integer-multiply-commutative",
                "integer-multiply-associative",
                "integer-multiply-distributive",
                "integer-multiply-one",
                "integer-multiply-zero",
                "integer-multiply-negative",
                "integer-multiply-congruent-second",
                "integer-multiply-congruent",
                "integer-cube-congruent",
                "integer-cube-positive",
                "integer-cube-negative",
                "integer-multiply-of-natural",
                "integer-add-of-natural",
            ],
        ),
        (
            "integer-natural-bridge.lim",
            &[
                "natural-zero-sum-first",
                "integer-positive-negative-zero",
                "integer-natural-divisibility-reflects",
            ],
        ),
        ("integer-normal-form.lim", &["integer-normal-form"]),
        (
            "integer-product-associative-identities.lim",
            &[
                "product-associative-positive",
                "product-associative-negative",
            ],
        ),
        (
            "integer-product-commutative-identities.lim",
            &[
                "product-commutative-positive",
                "product-commutative-negative",
            ],
        ),
        (
            "integer-product-distributive-identities.lim",
            &[
                "product-distributive-positive",
                "product-distributive-negative",
            ],
        ),
        (
            "integer-product-negative-identities.lim",
            &["product-negative-positive", "product-negative-negative"],
        ),
        (
            "integer-product-one-identities.lim",
            &["product-one-positive", "product-one-negative"],
        ),
        (
            "integer-product-zero-identities.lim",
            &["product-zero-positive", "product-zero-negative"],
        ),
        (
            "integer-signed-sum-identities.lim",
            &[
                "signed-sum-ppp-left",
                "signed-sum-ppp-right",
                "signed-sum-ppn-left",
                "signed-sum-ppn-right",
                "signed-sum-pnp-left",
                "signed-sum-pnp-right",
                "signed-sum-pnn-left",
                "signed-sum-pnn-right",
                "signed-sum-npp-left",
                "signed-sum-npp-right",
                "signed-sum-npn-left",
                "signed-sum-npn-right",
                "signed-sum-nnp-left",
                "signed-sum-nnp-right",
                "signed-sum-nnn-left",
                "signed-sum-nnn-right",
            ],
        ),
        (
            "integer-three-sign-cases.lim",
            &[
                "natural-nonmultiple-three-nonzero",
                "natural-nonmultiple-three-cube-nonzero",
                "natural-cube-equation-impossible",
                "integer-three-sign-ppp",
                "integer-three-sign-ppn",
                "integer-three-sign-pnp",
                "integer-three-sign-pnn",
                "integer-three-sign-npp",
                "integer-three-sign-npn",
                "integer-three-sign-nnp",
                "integer-three-sign-nnn",
            ],
        ),
        (
            "fermat-three-first-case-integers.lim",
            &[
                "integer-nonmultiple-positive-magnitude",
                "integer-nonmultiple-negative-magnitude",
                "fermat-three-first-case-integer-coordinates",
                "integer-nondivisor-product-left",
                "integer-nondivisor-product-right",
                "fermat-three-first-case-integers-cubes",
                "fermat-three-first-case-integers",
            ],
        ),
        (
            "natural-division-unique.lim",
            &[
                "small-remainder-excludes-positive-quotient",
                "quotient-remainder-unique",
                "division-unique",
            ],
        ),
        (
            "natural-cube-identities.lim",
            &[
                "cube-three-multiple",
                "cube-three-plus-one",
                "cube-three-plus-two",
                "ninth-residues-one-one",
                "ninth-residues-one-eight",
                "ninth-residues-eight-eight",
            ],
        ),
        (
            "natural-small-remainders.lim",
            &[
                "less-than-one-is-zero",
                "less-than-two-cases",
                "less-than-three-cases",
            ],
        ),
        (
            "natural-ninth-residues.lim",
            &[
                "power-three-as-cube",
                "ninth-residue-certificate",
                "ninth-residue-unique",
                "cube-residue-of-thirds-one",
                "cube-residue-of-thirds-two",
                "thirds-division-equation",
                "nonmultiple-three-cube-residue",
            ],
        ),
        (
            "natural-ninth-exclusion.lim",
            &[
                "ninth-sum-one-one",
                "ninth-sum-one-eight",
                "ninth-sum-eight-eight",
                "ninth-sum-eight-one",
                "ninth-zero-excludes-cube-residues",
                "ninth-two-excludes-cube-residues",
                "ninth-seven-excludes-cube-residues",
                "ninth-cube-residues-exclude-sum",
            ],
        ),
        (
            "fermat-three-first-case.lim",
            &[
                "nondivisor-product-left",
                "nondivisor-product-right",
                "fermat-three-first-case-at-coordinates",
                "fermat-three-first-case",
            ],
        ),
        (
            "natural-semiring-identities.lim",
            &[
                "double-as-sum",
                "double-square",
                "odd-square",
                "two-odd-residues-add",
                "two-odd-values-add",
                "double-product",
                "square-add",
                "square-gap-product",
                "square-double-gap",
                "add-one-is-successor",
            ],
        ),
        (
            "natural-prime-two.lim",
            &["prime-two", "two-not-divides-one"],
        ),
        (
            "natural-parity-arithmetic.lim",
            &[
                "two-divides-four",
                "four-not-divides-two",
                "odd-even-exclusion",
                "odd-nonzero",
                "four-divides-even-square",
                "odd-square-residue",
                "odd-square-is-odd",
                "odd-plus-odd-is-even",
                "odd-square-sum-residue",
                "odd-squares-not-square",
                "pythagorean-odd-leg-even-other",
                "pythagorean-odd-leg-odd-hypotenuse",
            ],
        ),
        (
            "natural-square-order.lim",
            &[
                "zero-less-nonzero",
                "square-strict-monotone",
                "square-injective",
                "square-order-reflect",
                "pythagorean-leg-below-hypotenuse",
                "positive-summand-above",
            ],
        ),
        (
            "natural-pythagorean-halves.lim",
            &[
                "pythagorean-coprime-hypotenuse",
                "odd-increasing-even-gap",
                "pythagorean-halves-coprime",
                "pythagorean-half-product",
                "pythagorean-coprime-from-hypotenuse",
            ],
        ),
        (
            "natural-pythagorean-classification.lim",
            &[
                "pythagorean-parameter-opposite-parity",
                "pythagorean-parameters-from-halves",
                "primitive-pythagorean-classification",
            ],
        ),
        (
            "natural-descent-bounds.lim",
            &[
                "square-has-self-gap",
                "less-than-lower-addend",
                "square-root-below-square-sum",
                "nonzero-square-root",
            ],
        ),
        (
            "fermat-four-defs.lim",
            &[
                "quartic-nonzero",
                "four-two-hypotenuse-nonzero",
                "four-two-swap",
                "power-two-as-square",
                "power-four-as-quartic",
            ],
        ),
        (
            "fermat-four-primitive-descent.lim",
            &[
                "four-two-primitive-from-parameters",
                "four-two-primitive-descends",
            ],
        ),
        (
            "fermat-four-factor-descent.lim",
            &[
                "quartic-product",
                "four-two-remove-first-prime-square",
                "four-two-remove-second-prime-square",
                "four-two-common-prime-descends",
            ],
        ),
        (
            "fermat-four.lim",
            &[
                "four-two-coprime-descends",
                "four-two-descends",
                "four-two-counterexample-descends",
                "no-four-two-counterexample",
                "fermat-for-four",
                "fermat-statement-from-odd-primes",
            ],
        ),
        (
            "natural-addition.lim",
            &[
                "add-zero-right",
                "add-successor-right",
                "add-commutative",
                "add-associative",
            ],
        ),
        (
            "natural-multiplication.lim",
            &[
                "multiply-one-left",
                "multiply-add-left",
                "multiply-associative",
            ],
        ),
        ("natural-powers.lim", &["power-add", "power-multiply"]),
        ("logic-false.lim", &["false-elimination"]),
        ("natural-successor.lim", &["successor-injective"]),
        (
            "natural-cancellation.lim",
            &["add-cancel-left", "add-cancel-right"],
        ),
        (
            "natural-multiplication-right.lim",
            &["multiply-zero-right", "multiply-one-right"],
        ),
        (
            "natural-strong-induction.lim",
            &["below-zero", "below-successor", "strong-induction-with-gap"],
        ),
        (
            "natural-order.lim",
            &[
                "less-than-successor",
                "not-less-than-zero",
                "not-less-than-self",
                "less-than-transitive",
                "strong-induction",
            ],
        ),
        (
            "natural-divisibility.lim",
            &[
                "divides-reflexive",
                "one-divides",
                "divides-zero",
                "divides-multiple",
                "divides-transitive",
            ],
        ),
        (
            "two-power-reduction.lim",
            &["four-divides-two-power", "four-divides-large-two-power"],
        ),
        (
            "natural-nonzero.lim",
            &[
                "successor-not-zero",
                "add-nonzero-left",
                "multiply-nonzero",
                "power-nonzero",
            ],
        ),
        ("exponent-reduction.lim", &["regroup-power-equation"]),
        (
            "fermat-for.lim",
            &["fermat-for-factor", "fermat-for-monotone"],
        ),
    ];
    check_native_modules_without_foundations(modules);
}

fn check_native_modules_without_foundations(modules: &[(&str, &[&str])]) {
    for &(file, targets) in modules {
        let path = module(file);
        let source = fs::read_to_string(&path).unwrap();
        for &target in targets {
            let checked = check_theorem_details_from_path_with_config(
                &source,
                &path,
                &CompileConfig::default(),
                target,
            )
            .unwrap_or_else(|why| panic!("{file}::{target}: {}", why.message));
            assert!(
                checked.name == target || checked.name.ends_with(&format!("::{target}")),
                "unexpected checked identity: {}",
                checked.name
            );
            assert!(
                checked.foundations.is_empty(),
                "{file}::{target}: {:?}",
                checked.foundations
            );
        }
    }
}

#[test]
fn bezout_and_eisenstein_source_port_theorems_are_kernel_checked() {
    let modules: &[(&str, &[&str])] = &[
        (
            "integer-bezout-algebra.lim",
            &[
                "integer-one-multiply",
                "integer-zero-multiply",
                "integer-add-three-rotate",
                "integer-add-opposite-cancel-four",
                "integer-of-natural-congruent",
                "integer-natural-division-equation",
                "integer-bezout-euclidean-update",
            ],
        ),
        (
            "integer-bezout.lim",
            &[
                "integer-bezout-reflexive-left",
                "integer-bezout-target-congruent",
                "integer-bezout-arguments-congruent",
                "integer-bezout-negative-first",
                "integer-bezout-negative-second",
                "integer-bezout-euclidean-step",
                "integer-bezout-common-divisor",
            ],
        ),
        (
            "natural-bezout.lim",
            &["natural-bezout-induction-step", "natural-gcd-bezout"],
        ),
        (
            "integer-gcd-bezout.lim",
            &[
                "integer-bezout-from-magnitudes",
                "integer-gcd-bezout",
                "integer-coprime-of-gcd-one",
                "integer-gcd-one-of-coprime",
                "integer-coprime-negative-first",
                "integer-coprime-negative-second",
                "integer-coprime-congruent",
            ],
        ),
        (
            "eisenstein-equality.lim",
            &[
                "eisenstein-reflexive",
                "eisenstein-symmetric",
                "eisenstein-transitive",
                "eisenstein-negate-congruent",
                "eisenstein-add-congruent",
                "eisenstein-multiply-congruent",
                "eisenstein-of-integer-congruent",
                "eisenstein-of-integer-injective",
            ],
        ),
        (
            "eisenstein-embedding.lim",
            &[
                "eisenstein-of-integer-add",
                "eisenstein-of-integer-negate",
                "eisenstein-of-integer-multiply",
                "eisenstein-of-integer-power",
                "eisenstein-of-natural-injective",
                "eisenstein-embedded-nonzero",
                "eisenstein-one-nonzero",
                "eisenstein-divides-of-integer",
            ],
        ),
        (
            "eisenstein-bezout.lim",
            &[
                "eisenstein-coprime-of-integer",
                "eisenstein-coprime-of-integer-gcd-one",
            ],
        ),
        (
            "eisenstein-cubic-bridge.lim",
            &[
                "eisenstein-one-multiply",
                "eisenstein-one-unit",
                "integer-fermat-three-residual-of-eisenstein",
                "integer-fermat-three-residual-gcd-of-eisenstein",
            ],
        ),
        (
            "eisenstein-constants.lim",
            &[
                "eisenstein-omega-polynomial",
                "eisenstein-omega-square",
                "eisenstein-omega-cube",
                "eisenstein-lambda-square",
                "eisenstein-omega-not-one",
                "eisenstein-omega-square-not-one",
                "eisenstein-lambda-nonzero",
                "eisenstein-lambda-divides-three",
                "eisenstein-omega-unit",
                "eisenstein-minus-one-unit",
            ],
        ),
        (
            "integer-linear-identities.lim",
            &[
                "integer-minus-one-multiply",
                "integer-two-multiply-sum",
                "integer-three-multiply-sum",
                "integer-zero-sum-negative",
                "integer-zero-difference",
                "integer-negate-three-sum",
            ],
        ),
    ];
    check_native_modules_without_foundations(modules);
}

#[test]
fn eisenstein_lambda_source_port_theorems_are_kernel_checked() {
    check_native_modules_without_foundations(&[(
        "eisenstein-lambda.lim",
        &[
            "eisenstein-lambda-multiply-normal",
            "integer-three-divides-of-lambda",
            "eisenstein-lambda-divides-of-three",
            "eisenstein-lambda-not-divides-of-integer",
        ],
    )]);
}

fn bezout_aliases() -> &'static [(&'static str, &'static str)] {
    &[
        ("integer", "integer-defs.lim"),
        ("integer-of-natural", "integer-defs.lim"),
        ("integer-add", "integer-defs.lim"),
        ("integer-multiply", "integer-defs.lim"),
        ("integer-equal", "integer-defs.lim"),
        ("integer-negate", "integer-defs.lim"),
        ("integer-bezout-equation", "integer-bezout-defs.lim"),
        ("integer-has-bezout", "integer-bezout-defs.lim"),
        ("natural-gcd-bezout", "natural-bezout.lim"),
        ("integer-coprime", "integer-gcd-bezout.lim"),
        ("integer-coprime-of-gcd-one", "integer-gcd-bezout.lim"),
    ]
}

fn explicit_bezout_certificate(
    first: (usize, usize),
    second: (usize, usize),
    target: (usize, usize),
    left: (usize, usize),
    right: (usize, usize),
) -> String {
    let equation = |l: String, r: String| {
        proof_call(
            "integer-bezout-equation",
            [
                integer_pair(first.0, first.1),
                integer_pair(second.0, second.1),
                integer_pair(target.0, target.1),
                l,
                r,
            ],
        )
    };
    let right_predicate = |l: String| {
        format!(
            "(#pt-lambda ((candidate-right (#pt-use integer ()))) {})",
            equation(l, "candidate-right".to_owned()),
        )
    };
    let left_predicate = format!(
        "(#pt-lambda ((candidate-left (#pt-use integer ())))
            (#pt-app (#pt-use exists (0)) (#pt-use integer ()) {}))",
        right_predicate("candidate-left".to_owned()),
    );
    let l = integer_pair(left.0, left.1);
    let r = integer_pair(right.0, right.1);
    // Only a candidate equality term: the kernel independently reduces both
    // cross sums. Incorrect coefficients therefore cannot pass this fixture.
    let negative_sum =
        left.0 * first.1 + left.1 * first.0 + right.0 * second.1 + right.1 * second.0;
    let proof = reflexivity(target.0 + negative_sum);
    let inner = format!(
        "(#pt-construct exists (0) ((#pt-use integer ()) {}) introduce ({r} {proof}))",
        right_predicate(l.clone())
    );
    format!("(#pt-construct exists (0) ((#pt-use integer ()) {left_predicate}) introduce ({l} {inner}))")
}

#[test]
fn bezout_explicit_coefficients_cover_negative_zero_and_noncanonical_inputs() {
    for (a, b, g, l, r) in [
        ((30, 0), (12, 0), (6, 0), (1, 0), (0, 2)),
        ((84, 0), (30, 0), (6, 0), (0, 1), (3, 0)),
        ((0, 7), (12, 0), (1, 0), (5, 0), (3, 0)),
        ((7, 2), (0, 3), (1, 0), (2, 0), (3, 0)),
        ((0, 0), (0, 0), (0, 0), (0, 0), (0, 0)),
        ((0, 0), (5, 0), (5, 0), (0, 0), (1, 0)),
        ((5, 0), (0, 0), (5, 0), (1, 0), (0, 0)),
    ] {
        let statement = proof_call(
            "integer-has-bezout",
            [
                integer_pair(a.0, a.1),
                integer_pair(b.0, b.1),
                integer_pair(g.0, g.1),
            ],
        );
        expect_native_fixture(
            bezout_aliases(),
            "",
            &statement,
            &explicit_bezout_certificate(a, b, g, l, r),
            true,
        );
    }
    let statement = proof_call(
        "integer-has-bezout",
        [integer_pair(30, 0), integer_pair(12, 0), integer_pair(6, 0)],
    );
    expect_native_fixture(
        bezout_aliases(),
        "",
        &statement,
        &explicit_bezout_certificate((30, 0), (12, 0), (6, 0), (1, 0), (2, 0)),
        false,
    );
}

#[test]
fn bezout_euclidean_induction_requires_the_actual_gcd_certificate() {
    for (a, b) in [(0, 0), (0, 5), (5, 0), (30, 12)] {
        let (g, certificate) = gcd_certificate(a, b);
        let proof = proof_call(
            "natural-gcd-bezout",
            [numeral(a), numeral(b), numeral(g), certificate],
        );
        let embedded = |n| proof_call("integer-of-natural", [numeral(n)]);
        expect_native_fixture(
            bezout_aliases(),
            "",
            &proof_call(
                "integer-has-bezout",
                [embedded(a), embedded(b), embedded(g)],
            ),
            &proof,
            true,
        );
        if a == 30 {
            expect_native_fixture(
                bezout_aliases(),
                "",
                &proof_call(
                    "integer-has-bezout",
                    [embedded(a), embedded(b), embedded(1)],
                ),
                &proof,
                false,
            );
        }
    }
}

#[test]
fn bezout_update_and_gcd_one_reject_changed_equations() {
    let product = proof_call(
        "integer-multiply",
        [
            "old-right-coefficient".to_owned(),
            "quotient-value".to_owned(),
        ],
    );
    // Addition instead of subtraction is the tempting but incorrect update.
    let coefficient = proof_call("integer-add", ["old-left-coefficient".to_owned(), product]);
    let wrong = proof_call(
        "integer-add",
        [
            proof_call(
                "integer-multiply",
                [
                    "old-right-coefficient".to_owned(),
                    "dividend-value".to_owned(),
                ],
            ),
            proof_call(
                "integer-multiply",
                [coefficient, "divisor-value".to_owned()],
            ),
        ],
    );
    let old = proof_call(
        "integer-add",
        [
            proof_call(
                "integer-multiply",
                [
                    "old-left-coefficient".to_owned(),
                    "divisor-value".to_owned(),
                ],
            ),
            proof_call(
                "integer-multiply",
                [
                    "old-right-coefficient".to_owned(),
                    "remainder-value".to_owned(),
                ],
            ),
        ],
    );
    reject_changed_statement(
        "integer-bezout-algebra.lim",
        "integer-bezout-euclidean-update",
        &format!("(#statement {})", integer_equivalent(wrong, old)),
    );
    let mut aliases = magnitude_aliases().to_vec();
    aliases.extend([
        ("integer-coprime", "integer-gcd-bezout.lim"),
        ("integer-coprime-of-gcd-one", "integer-gcd-bezout.lim"),
    ]);
    let (_, gcd) = signed_gcd_certificate((6, 0), (4, 0));
    let a = integer_pair(6, 0);
    let b = integer_pair(4, 0);
    let proof = proof_call("integer-coprime-of-gcd-one", [a.clone(), b.clone(), gcd]);
    expect_native_fixture(
        &aliases,
        "",
        &proof_call("integer-coprime", [a, b]),
        &proof,
        false,
    );
}

fn end_of_form(source: &str, start: usize) -> usize {
    let mut depth = 0usize;
    for (offset, byte) in source.bytes().enumerate().skip(start) {
        match byte {
            b'(' => depth += 1,
            b')' => {
                depth -= 1;
                if depth == 0 {
                    return offset + 1;
                }
            }
            _ => {}
        }
    }
    panic!("unclosed fixture form")
}

#[test]
fn source_port_rejects_a_false_unbounded_power_identity() {
    let path = module("natural-powers.lim");
    let source = fs::read_to_string(&path).unwrap();
    let theorem = source.find("(#theorem power-multiply").unwrap();
    let start = source[theorem..].find("(#statement").unwrap() + theorem;
    let end = end_of_form(&source, start);
    // Incorrectly repeat the outer exponent in place of the inner one.
    let false_statement = "(#statement (#pt-eq #pt-nat
      (#pt-app (#pt-use power ()) base
        (#pt-app (#pt-use multiply ()) outer-exponent inner-exponent))
      (#pt-app (#pt-use power ())
        (#pt-app (#pt-use power ()) base outer-exponent) outer-exponent)))";
    let changed = format!("{}{}{}", &source[..start], false_statement, &source[end..]);
    lim::parse_program_from_path(&changed, &path).expect("mutation remains valid source");
    let why = check_theorem_details_from_path_with_config(
        &changed,
        &path,
        &CompileConfig::default(),
        "power-multiply",
    )
    .unwrap_err();
    assert_eq!(why.code, DiagnosticCode::Proof);
    assert!(why.message.contains("mismatch"), "{}", why.message);
}

#[test]
fn regrouping_requires_the_counterexample_equation_as_evidence() {
    let path = module("exponent-reduction.lim");
    let source = fs::read_to_string(&path).unwrap();
    assert_eq!(source.matches("(#parameter equation ").count(), 1);
    let changed = source.replacen("(#parameter equation ", "(#parameter unused-equation ", 1);
    lim::parse_program_from_path(&changed, &path).expect("mutation remains valid source");
    assert!(check_theorem_details_from_path_with_config(
        &changed,
        &path,
        &CompileConfig::default(),
        "regroup-power-equation",
    )
    .is_err());
}

#[test]
fn monotonicity_does_not_prove_an_unrelated_exponent_or_reverse_divisibility() {
    let path = module("fermat-for.lim");
    let source = fs::read_to_string(&path).unwrap();
    let theorem = source.find("(#theorem fermat-for-monotone").unwrap();
    let start = source[theorem..].find("(#statement").unwrap() + theorem;
    let end = end_of_form(&source, start);
    let wrong_exponent = format!(
        "{}(#statement (#pt-app (#pt-use fermat-for ()) (#pt-succ multiple))){}",
        &source[..start],
        &source[end..]
    );
    assert_eq!(
        source
            .matches("(#pt-app (#pt-use divides ()) divisor multiple)")
            .count(),
        1
    );
    let wrong_divisibility = source.replacen(
        "(#pt-app (#pt-use divides ()) divisor multiple)",
        "(#pt-app (#pt-use divides ()) multiple divisor)",
        1,
    );
    for changed in [wrong_exponent, wrong_divisibility] {
        lim::parse_program_from_path(&changed, &path).expect("mutation remains valid source");
        let why = check_theorem_details_from_path_with_config(
            &changed,
            &path,
            &CompileConfig::default(),
            "fermat-for-monotone",
        )
        .unwrap_err();
        assert_eq!(why.code, DiagnosticCode::Proof);
    }
}

fn reject_changed_statement(file: &str, target: &str, statement: &str) {
    let path = module(file);
    let source = fs::read_to_string(&path).unwrap();
    let theorem = source.find(&format!("(#theorem {target}")).unwrap();
    let start = source[theorem..].find("(#statement").unwrap() + theorem;
    let end = end_of_form(&source, start);
    let changed = format!("{}{}{}", &source[..start], statement, &source[end..]);
    lim::parse_program_from_path(&changed, &path).expect("negative control remains valid source");
    let why = check_theorem_details_from_path_with_config(
        &changed,
        &path,
        &CompileConfig::default(),
        target,
    )
    .unwrap_err();
    assert_eq!(why.code, DiagnosticCode::Proof);
}

#[test]
fn four_divisibility_requires_the_power_to_exceed_two() {
    reject_changed_statement(
        "two-power-reduction.lim",
        "four-divides-large-two-power",
        "(#statement (#pt-app (#pt-use divides ())
          (#pt-succ (#pt-succ (#pt-succ (#pt-succ #pt-zero))))
          (#pt-app (#pt-use power ()) (#pt-succ (#pt-succ #pt-zero)) exponent)))",
    );
}

#[test]
fn transitivity_cannot_reverse_order_or_divisibility() {
    reject_changed_statement(
        "natural-order.lim",
        "less-than-transitive",
        "(#statement (#pt-app (#pt-use less-than ()) third first))",
    );
    reject_changed_statement(
        "natural-divisibility.lim",
        "divides-transitive",
        "(#statement (#pt-app (#pt-use divides ()) third first))",
    );
}

#[test]
fn strong_induction_cannot_assume_its_own_current_case_in_the_history() {
    let path = module("natural-strong-induction.lim");
    let source = fs::read_to_string(&path).unwrap();
    let start = source.find("(#math-definition below").unwrap();
    let end = end_of_form(&source, start);
    let definition = &source[start..end];
    assert_eq!(definition.matches("(#pt-succ earlier)").count(), 1);
    let changed = format!(
        "{}{}{}",
        &source[..start],
        definition.replacen("(#pt-succ earlier)", "earlier", 1),
        &source[end..],
    );
    lim::parse_program_from_path(&changed, &path).expect("negative control remains valid source");
    let why = check_theorem_details_from_path_with_config(
        &changed,
        &path,
        &CompileConfig::default(),
        "strong-induction-with-gap",
    )
    .unwrap_err();
    assert_eq!(why.code, DiagnosticCode::Proof);
}

fn natural(value: usize) -> String {
    (0..value).fold("#pt-zero".to_owned(), |term, _| {
        format!("(#pt-succ {term})")
    })
}

#[test]
fn constructive_arithmetic_decisions_compute_both_answers() {
    let cases = [
        ("equality", 0, 0, true),
        ("equality", 0, 1, false),
        ("equality", 1, 0, false),
        ("equality", 2, 2, true),
        ("equality", 2, 3, false),
        ("divides", 0, 0, true),
        ("divides", 0, 1, false),
        ("divides", 1, 0, true),
        ("divides", 1, 3, true),
        ("divides", 2, 4, true),
        ("divides", 2, 3, false),
        ("divides", 3, 12, true),
        ("divides", 4, 2, false),
        ("less", 0, 0, false),
        ("less", 0, 1, true),
        ("less", 1, 0, false),
        ("less", 2, 3, true),
        ("less", 3, 2, false),
    ];
    for (kind, a, b, yes) in cases {
        let (file, decide, relation) = match kind {
            "equality" => ("natural-decision.lim", "decide-equality", "#pt-eq #pt-nat"),
            "divides" => (
                "decidable-divisibility.lim",
                "decide-divides",
                "#pt-app (#pt-use divides ())",
            ),
            "less" => (
                "decidable-order.lim",
                "decide-less-than",
                "#pt-app (#pt-use less-than ())",
            ),
            _ => unreachable!(),
        };
        let path = module(file);
        let source = fs::read_to_string(&path).unwrap();
        let a = natural(a);
        let b = natural(b);
        let expected = natural(usize::from(yes));
        // Observe the data constructor, not just an excluded-middle proposition.
        // Refl must reduce the actual decision algorithm to the expected tag.
        let observation = format!(
            "
            (#math-definition observation-proposition () #pt-prop ({relation} {a} {b}))
            (#math-definition observation-tag () #pt-nat
              (#pt-induct decision () ((#pt-use observation-proposition ()))
                (#pt-lambda ((answer
                  (#pt-app (#pt-use decision ()) (#pt-use observation-proposition ()))))
                  #pt-nat)
                ((#pt-lambda ((refutation
                    (#pt-pi ((proof (#pt-use observation-proposition ()))) #pt-false)))
                    #pt-zero)
                 (#pt-lambda ((evidence (#pt-use observation-proposition ())))
                    (#pt-succ #pt-zero)))
                (#pt-app (#pt-use {decide} ()) {a} {b})))
            (#theorem observed-result (#universes) (#parameters)
              (#statement (#pt-eq #pt-nat (#pt-use observation-tag ()) {expected}))
              (#proof (#pt-refl #pt-nat {expected})))"
        );
        let changed = format!("{source}\n{observation}");
        let checked = check_theorem_details_from_path_with_config(
            &changed,
            &path,
            &CompileConfig::default(),
            "observed-result",
        )
        .unwrap_or_else(|why| panic!("{kind}({a}, {b}): {}", why.message));
        assert!(checked.foundations.is_empty());

        let wrong = natural(usize::from(!yes));
        let false_observation = observation.replace(
            &format!("(#pt-use observation-tag ()) {expected})"),
            &format!("(#pt-use observation-tag ()) {wrong})"),
        );
        let why = check_theorem_details_from_path_with_config(
            &format!("{source}\n{false_observation}"),
            &path,
            &CompileConfig::default(),
            "observed-result",
        )
        .unwrap_err();
        assert_eq!(why.code, DiagnosticCode::Proof);
    }
}

#[test]
fn a_prefix_witness_does_not_make_its_upper_bound_the_minimum() {
    reject_changed_statement(
        "least-witness.lim",
        "bounded-minimum",
        "(#statement (#pt-app (#pt-use minimum ()) property limit))",
    );
}

#[test]
fn a_prime_factor_does_not_make_the_original_number_prime() {
    reject_changed_statement(
        "natural-prime.lim",
        "exists-prime-divisor",
        "(#statement (#pt-app (#pt-use prime ()) multiple))",
    );
}

#[test]
fn bounded_search_cannot_replace_its_bound_with_zero() {
    reject_changed_statement(
        "bounded-search.lim",
        "any-up-to-with-gap",
        "(#statement (#pt-app (#pt-use any-up-to ()) property #pt-zero))",
    );
}

#[test]
fn the_divisor_dichotomy_cannot_discard_either_alternative() {
    reject_changed_statement(
        "divisor-dichotomy.lim",
        "four-divides-or-odd-prime-divides",
        "(#statement (#pt-app (#pt-use divides ())
          (#pt-succ (#pt-succ (#pt-succ (#pt-succ #pt-zero)))) number))",
    );
    reject_changed_statement(
        "divisor-dichotomy.lim",
        "four-divides-or-odd-prime-divides",
        "(#statement (#pt-app (#pt-use odd-prime-divisor ()) number))",
    );
}

#[test]
fn parity_does_not_prove_that_every_natural_has_the_same_parity() {
    reject_changed_statement(
        "natural-parity.lim",
        "even-or-odd",
        "(#statement (#pt-app (#pt-use odd ()) number))",
    );
    reject_changed_statement(
        "natural-parity.lim",
        "even-or-odd",
        "(#statement (#pt-app (#pt-use divides ())
          (#pt-succ (#pt-succ #pt-zero)) number))",
    );
}

#[test]
fn the_odd_prime_reduction_requires_both_unproved_exponent_cases() {
    let path = module("odd-prime-reduction.lim");
    let source = fs::read_to_string(&path).unwrap();
    for parameter in ["four-case", "odd-prime-cases"] {
        // Renaming the binder removes that evidence from the proof's scope.
        let changed = source.replace(
            &format!("(#parameter {parameter} "),
            &format!("(#parameter missing-{parameter} "),
        );
        assert_ne!(changed, source);
        lim::parse_program_from_path(&changed, &path).expect("mutation remains valid source");
        let why = check_theorem_details_from_path_with_config(
            &changed,
            &path,
            &CompileConfig::default(),
            "fermat-statement-from-four-and-odd-primes",
        )
        .unwrap_err();
        assert_eq!(why.code, DiagnosticCode::Proof);
    }
}

#[test]
fn infinite_descent_requires_a_strictly_smaller_witness() {
    let path = module("infinite-descent.lim");
    let source = fs::read_to_string(&path).unwrap();
    let start = source.find("(#parameter descend ").unwrap();
    let end = end_of_form(&source, start);
    let hypothesis = &source[start..end];
    // The weakened hypothesis admits returning the very same witness.
    let weakened = hypothesis.replace("#pt-app (#pt-use less-than ())", "#pt-eq #pt-nat");
    assert_ne!(weakened, hypothesis);
    let changed = format!("{}{}{}", &source[..start], weakened, &source[end..]);
    lim::parse_program_from_path(&changed, &path).expect("mutation remains valid source");
    let why = check_theorem_details_from_path_with_config(
        &changed,
        &path,
        &CompileConfig::default(),
        "no-infinite-descent",
    )
    .unwrap_err();
    assert_eq!(why.code, DiagnosticCode::Proof);
}

fn proof_call(name: &str, arguments: impl IntoIterator<Item = String>) -> String {
    format!(
        "(#pt-app (#pt-use {name} ()) {})",
        arguments.into_iter().collect::<Vec<_>>().join(" ")
    )
}

fn natural_equation(left: &str, right: &str) -> String {
    format!("(#pt-eq #pt-nat {left} {right})")
}

fn numeral(value: usize) -> String {
    assert!(value <= 128);
    format!("(#pt-numeral {value})")
}

fn reflexivity(number: usize) -> String {
    format!("(#pt-refl #pt-nat {})", numeral(number))
}

fn division_certificate(n: usize, d: usize, q: usize, r: usize, gap: usize) -> String {
    let sum = proof_call(
        "add",
        [proof_call("multiply", [numeral(q), numeral(d)]), numeral(r)],
    );
    let predicate = format!(
        "(#pt-lambda ((gap #pt-nat))
          (#pt-eq #pt-nat {} (#pt-app (#pt-use add ()) (#pt-succ {}) gap)))",
        numeral(d),
        numeral(r),
    );
    let bound = format!(
        "(#pt-construct exists (0) (#pt-nat {predicate}) introduce ({} {}))",
        numeral(gap),
        reflexivity(d),
    );
    proof_call(
        "conjunction-introduce",
        [
            natural_equation(&numeral(n), &sum),
            proof_call("less-than", [numeral(r), numeral(d)]),
            reflexivity(n),
            bound,
        ],
    )
}

fn gcd_certificate(a: usize, b: usize) -> (usize, String) {
    if b == 0 {
        return (a, proof_call("gcd-zero-right", [numeral(a)]));
    }
    let q = a / b;
    let r = a % b;
    let (g, smaller) = gcd_certificate(b, r);
    // Rust builds a candidate proof only. The kernel checks every arithmetic
    // equation and strict bound, independently of these integer calculations.
    (
        g,
        proof_call(
            "gcd-euclidean-step",
            [
                numeral(a),
                numeral(b),
                numeral(q),
                numeral(r),
                division_certificate(a, b, q, r, b - r - 1),
                numeral(g),
                smaller,
            ],
        ),
    )
}

fn expect_euclidean_fixture(parameters: &str, statement: &str, proof: &str, valid: bool) {
    expect_native_fixture(&[], parameters, statement, proof, valid);
}

fn expect_native_fixture(
    extra_aliases: &[(&str, &str)],
    parameters: &str,
    statement: &str,
    proof: &str,
    valid: bool,
) {
    let scratch = support::Scratch::new("flt-euclidean-source");
    let path = scratch.path().join("probe.lim");
    let mut source = String::new();
    for (name, file) in [
        ("add", "../fermat_statement.lim"),
        ("multiply", "../fermat_statement.lim"),
        ("exists", "logic-exists.lim"),
        ("less-than", "natural-order.lim"),
        ("division-spec", "natural-division.lim"),
        ("gcd-spec", "natural-gcd.lim"),
        ("gcd-zero-right", "natural-gcd.lim"),
        ("gcd-euclidean-step", "natural-gcd.lim"),
        ("gcd-unique", "natural-coprime.lim"),
        ("coprime-of-gcd-one", "natural-coprime.lim"),
        ("conjunction-introduce", "logical-connectives.lim"),
        ("coprime-product-square", "natural-square-factors.lim"),
        ("is-square", "natural-square-factors.lim"),
    ]
    .into_iter()
    .chain(extra_aliases.iter().copied())
    {
        source.push_str(&format!(
            "(#alias {name} = {}::{name})\n",
            module(file).display()
        ));
    }
    source.push_str(&format!(
        "(#theorem observed-result (#universes) (#parameters {parameters})
           (#statement {statement}) (#proof {proof}))"
    ));
    fs::write(&path, &source).unwrap();
    lim::parse_program_from_path(&source, &path).expect("fixture remains valid source");
    let checked = check_theorem_details_from_path_with_config(
        &source,
        &path,
        &CompileConfig::default(),
        "observed-result",
    );
    if valid {
        let checked = checked.unwrap_or_else(|why| panic!("{}", why.message));
        assert!(checked.foundations.is_empty());
    } else {
        let why = checked.unwrap_err();
        assert_eq!(why.code, DiagnosticCode::Proof);
        assert!(why.message.contains("mismatch"), "{}", why.message);
    }
}

#[test]
fn euclidean_division_rejects_wrong_equations_and_non_strict_remainders() {
    for (n, d, q, r, gap, valid) in [
        (7, 3, 2, 1, 1, true),
        (7, 3, 3, 1, 1, false),
        (9, 3, 2, 3, 0, false),
        (0, 0, 0, 0, 0, false),
    ] {
        expect_euclidean_fixture(
            "",
            &proof_call(
                "division-spec",
                [numeral(n), numeral(d), numeral(q), numeral(r)],
            ),
            &division_certificate(n, d, q, r, gap),
            valid,
        );
    }
}

#[test]
fn checked_euclidean_certificates_determine_the_unique_gcd() {
    for (a, b, expected) in [(0, 0, 0), (8, 0, 8), (0, 8, 8), (84, 30, 6), (6, 15, 3)] {
        let (g, certificate) = gcd_certificate(a, b);
        assert_eq!(g, expected);
        let parameters = format!(
            "(#parameter candidate #pt-nat)
             (#parameter certificate {})",
            proof_call("gcd-spec", [numeral(a), numeral(b), "candidate".to_owned()]),
        );
        let proof = proof_call(
            "gcd-unique",
            [
                numeral(a),
                numeral(b),
                "candidate".to_owned(),
                numeral(g),
                "certificate".to_owned(),
                certificate,
            ],
        );
        expect_euclidean_fixture(
            &parameters,
            &natural_equation("candidate", &numeral(g)),
            &proof,
            true,
        );
        expect_euclidean_fixture(
            &parameters,
            &natural_equation("candidate", &numeral(g + 1)),
            &proof,
            false,
        );
    }
}

#[test]
fn square_extraction_checks_zero_unit_and_nontrivial_coprime_factors() {
    for (a, b, root) in [(0, 1, 0), (1, 0, 0), (4, 9, 6), (9, 4, 6), (2, 2, 2)] {
        let (g, certificate) = gcd_certificate(a, b);
        let coprime = proof_call(
            "coprime-of-gcd-one",
            [
                numeral(a),
                numeral(b),
                numeral(g),
                certificate,
                reflexivity(1),
            ],
        );
        let proof = proof_call(
            "coprime-product-square",
            [
                numeral(a),
                numeral(b),
                numeral(root),
                coprime,
                reflexivity(a * b),
            ],
        );
        // 2*2 = 2² is the counterexample if coprimality were dropped.
        expect_euclidean_fixture("", &proof_call("is-square", [numeral(a)]), &proof, g == 1);
    }
}

fn odd_certificate(number: usize) -> String {
    let half = (number - 1) / 2;
    format!(
        "(#pt-construct exists (0) (#pt-nat
           (#pt-lambda ((candidate-half #pt-nat))
             (#pt-eq #pt-nat {} (#pt-succ
               (#pt-app (#pt-use multiply ()) {} candidate-half)))))
           introduce ({} {}))",
        numeral(number),
        numeral(2),
        numeral(half),
        reflexivity(number),
    )
}

#[test]
fn primitive_pythagorean_classification_requires_its_real_hypotheses() {
    let aliases = [
        ("odd", "natural-parity.lim"),
        ("successor-not-zero", "natural-nonzero.lim"),
        (
            "primitive-pythagorean-classification",
            "natural-pythagorean-classification.lim",
        ),
        (
            "pythagorean-parameters",
            "natural-pythagorean-classification.lim",
        ),
    ];
    for (a, b, c, valid) in [
        (3, 4, 5, true),
        (5, 12, 13, true),
        (9, 12, 15, false),
        (3, 4, 6, false),
        (4, 3, 5, false),
    ] {
        let (g, certificate) = gcd_certificate(a, b);
        let coprime = proof_call(
            "coprime-of-gcd-one",
            [
                numeral(a),
                numeral(b),
                numeral(g),
                certificate,
                reflexivity(1),
            ],
        );
        let statement = format!(
            "(#pt-app (#pt-use exists (0)) #pt-nat
              (#pt-lambda ((candidate-larger #pt-nat))
                (#pt-app (#pt-use exists (0)) #pt-nat
                  (#pt-lambda ((candidate-smaller #pt-nat))
                    (#pt-app (#pt-use pythagorean-parameters ())
                      {} {} {} candidate-larger candidate-smaller)))))",
            numeral(a),
            numeral(b),
            numeral(c),
        );
        let lhs = proof_call(
            "add",
            [
                proof_call("multiply", [numeral(a), numeral(a)]),
                proof_call("multiply", [numeral(b), numeral(b)]),
            ],
        );
        let proof = proof_call(
            "primitive-pythagorean-classification",
            [
                numeral(a),
                numeral(b),
                numeral(c),
                odd_certificate(a),
                proof_call("successor-not-zero", [numeral(b - 1)]),
                coprime,
                format!("(#pt-refl #pt-nat {lhs})"),
            ],
        );
        expect_native_fixture(&aliases, "", &statement, &proof, valid);
    }
}

#[test]
fn exponent_four_is_a_closed_case_and_cannot_prove_exponent_two() {
    let path = module("fermat-four.lim");
    let source = fs::read_to_string(&path).unwrap();
    let theorem = source.find("(#theorem fermat-for-four").unwrap();
    let parameters = source[theorem..].find("(#parameters").unwrap() + theorem;
    assert_eq!(
        &source[parameters..end_of_form(&source, parameters)],
        "(#parameters)",
        "the exponent-four case must not assume an unproved exponent case"
    );
    let checked = check_theorem_details_from_path_with_config(
        &source,
        &path,
        &CompileConfig::default(),
        "fermat-for-four",
    )
    .unwrap_or_else(|why| panic!("{}", why.message));
    assert!(checked.foundations.is_empty());
    // 3² + 4² = 5² makes this a false replacement for the proved case.
    reject_changed_statement(
        "fermat-four.lim",
        "fermat-for-four",
        "(#statement (#pt-app (#pt-use fermat-for ()) (#pt-numeral 2)))",
    );
}

#[test]
fn odd_square_identity_cannot_drop_its_residue_one() {
    let value = proof_call("multiply", [numeral(2), "first".to_owned()]);
    let lhs = proof_call(
        "multiply",
        [format!("(#pt-succ {value})"), format!("(#pt-succ {value})")],
    );
    let rhs = proof_call(
        "multiply",
        [
            numeral(4),
            proof_call(
                "add",
                [
                    proof_call("multiply", ["first".to_owned(), "first".to_owned()]),
                    "first".to_owned(),
                ],
            ),
        ],
    );
    reject_changed_statement(
        "natural-semiring-identities.lim",
        "odd-square",
        &format!("(#statement {})", natural_equation(&lhs, &rhs)),
    );
}

#[test]
fn overdeep_unary_numerals_in_aliased_proofs_return_a_diagnostic() {
    let scratch = support::Scratch::new("flt-proof-spine-limit");
    let path = scratch.path().join("probe.lim");
    let unary = natural(84);
    // The alias selects contextual file resolution, where the old large
    // recursive dispatch frame overflowed the ordinary test-worker stack.
    let source = format!(
        "(#alias symmetry = {}::symmetry)
         (#theorem observed-result (#universes) (#parameters)
           (#statement (#pt-eq #pt-nat {unary} {unary}))
           (#proof (#pt-refl #pt-nat {unary})))",
        module("equality.lim").display(),
    );
    fs::write(&path, &source).unwrap();
    let why = check_theorem_details_from_path_with_config(
        &source,
        &path,
        &CompileConfig::default(),
        "observed-result",
    )
    .unwrap_err();
    assert_eq!(why.code, DiagnosticCode::Proof);
    assert!(why
        .message
        .contains("kernel syntax resource limit exceeded"));
}

#[test]
fn direct_source_port_cli_works_without_lean_or_an_export() {
    for (file, target) in [
        ("fermat-for.lim", "fermat-for-monotone"),
        ("natural-prime.lim", "exists-prime-divisor"),
        (
            "odd-prime-reduction.lim",
            "fermat-statement-from-four-and-odd-primes",
        ),
        ("natural-square-factors.lim", "coprime-product-square"),
        ("fermat-four.lim", "fermat-for-four"),
        ("fermat-three-first-case.lim", "fermat-three-first-case"),
        (
            "fermat-three-first-case-integers.lim",
            "fermat-three-first-case-integers",
        ),
    ] {
        let path = module(file);
        let mut command = Command::new(env!("CARGO_BIN_EXE_lim"));
        command
            .env("PATH", "")
            .args(["--check-theorem", path.to_str().unwrap(), target]);
        let (status, stdout, stderr) =
            support::run(&mut command, Duration::from_secs(15), 1024 * 1024).unwrap();
        assert!(status.success(), "{}", String::from_utf8_lossy(&stderr));
        assert_eq!(stdout, format!("checked theorem {target}\n").as_bytes());
        assert!(stderr.is_empty(), "{}", String::from_utf8_lossy(&stderr));
    }
}

#[test]
fn division_uniqueness_covers_zero_exact_and_last_remainders() {
    let aliases = [
        ("division-unique", "natural-division-unique.lim"),
        ("conjunction", "logical-connectives.lim"),
    ];
    for (n, d, q, r) in [(0, 1, 0, 0), (18, 9, 2, 0), (17, 9, 1, 8), (128, 9, 14, 2)] {
        let certificate = division_certificate(n, d, q, r, d - r - 1);
        let proof = proof_call(
            "division-unique",
            [
                numeral(n),
                numeral(d),
                numeral(q),
                numeral(r),
                numeral(q),
                numeral(r),
                certificate.clone(),
                certificate,
            ],
        );
        for (claimed_quotient, valid) in [(q, true), (q + 1, false)] {
            let statement = proof_call(
                "conjunction",
                [
                    natural_equation(&numeral(q), &numeral(claimed_quotient)),
                    natural_equation(&numeral(r), &numeral(r)),
                ],
            );
            expect_native_fixture(&aliases, "", &statement, &proof, valid);
        }
    }
}

#[test]
fn cube_residue_constructors_check_the_equation_and_the_residue() {
    let aliases = [
        ("cube", "natural-ninth-residues.lim"),
        ("ninth-residue", "natural-ninth-residues.lim"),
        ("cube-residue-of-thirds-one", "natural-ninth-residues.lim"),
        ("cube-residue-of-thirds-two", "natural-ninth-residues.lim"),
    ];
    for (n, digit, residue, valid) in [
        (1, 1, 1, true),
        (2, 2, 8, true),
        (4, 1, 1, true),
        (5, 2, 8, true),
        (7, 1, 1, true),
        (8, 2, 8, true),
        (3, 1, 1, false),
        (4, 1, 8, false),
    ] {
        let quotient = n / 3;
        let name = if digit == 1 {
            "cube-residue-of-thirds-one"
        } else {
            "cube-residue-of-thirds-two"
        };
        let proof = proof_call(name, [numeral(n), numeral(quotient), reflexivity(n)]);
        let statement = proof_call(
            "ninth-residue",
            [proof_call("cube", [numeral(n)]), numeral(residue)],
        );
        expect_native_fixture(&aliases, "", &statement, &proof, valid);
    }
}

fn ninth_residue_witness(n: usize, q: usize, r: usize) -> String {
    let total = proof_call(
        "add",
        [
            proof_call("multiply", [numeral(9), "quotient".to_owned()]),
            numeral(r),
        ],
    );
    let predicate = format!(
        "(#pt-lambda ((quotient #pt-nat)) {})",
        natural_equation(&numeral(n), &total)
    );
    format!(
        "(#pt-construct exists (0) (#pt-nat {predicate}) introduce ({} {}))",
        numeral(q),
        reflexivity(n)
    )
}

fn ninth_remainder_bound(r: usize) -> String {
    let total = proof_call(
        "add",
        [format!("(#pt-succ {})", numeral(r)), "gap".to_owned()],
    );
    let predicate = format!(
        "(#pt-lambda ((gap #pt-nat)) {})",
        natural_equation(&numeral(9), &total)
    );
    // r=9 deliberately proposes the false bound 9<9; Lim must reject it.
    let gap = 8usize.saturating_sub(r);
    format!(
        "(#pt-construct exists (0) (#pt-nat {predicate}) introduce ({} {}))",
        numeral(gap),
        reflexivity(9)
    )
}

#[test]
fn residue_uniqueness_requires_strict_remainder_bounds() {
    let aliases = [("ninth-residue-unique", "natural-ninth-residues.lim")];
    for (n, q1, r1, q2, r2, valid) in [(17, 1, 8, 1, 8, true), (9, 0, 9, 1, 0, false)] {
        let proof = proof_call(
            "ninth-residue-unique",
            [
                numeral(n),
                numeral(r1),
                numeral(r2),
                ninth_remainder_bound(r1),
                ninth_remainder_bound(r2),
                ninth_residue_witness(n, q1, r1),
                ninth_residue_witness(n, q2, r2),
            ],
        );
        expect_native_fixture(
            &aliases,
            "",
            &natural_equation(&numeral(r1), &numeral(r2)),
            &proof,
            valid,
        );
    }
}

#[test]
fn cube_identities_and_residue_sums_reject_wrong_constants() {
    let third = proof_call("multiply", [numeral(3), "first".to_owned()]);
    let value = proof_call("add", [third, numeral(2)]);
    let cube = proof_call(
        "multiply",
        [
            value.clone(),
            proof_call("multiply", [value.clone(), value]),
        ],
    );
    let square = proof_call("multiply", ["first".to_owned(), "first".to_owned()]);
    let old_cube = proof_call("multiply", ["first".to_owned(), square.clone()]);
    let quotient = proof_call(
        "add",
        [
            proof_call(
                "add",
                [
                    proof_call("multiply", [numeral(3), old_cube]),
                    proof_call("multiply", [numeral(6), square]),
                ],
            ),
            proof_call("multiply", [numeral(4), "first".to_owned()]),
        ],
    );
    let wrong = proof_call("multiply", [numeral(9), quotient]);
    reject_changed_statement(
        "natural-cube-identities.lim",
        "cube-three-plus-two",
        &format!("(#statement {})", natural_equation(&cube, &wrong)),
    );
    let sum = proof_call("add", ["first".to_owned(), "second".to_owned()]);
    let wrong_residue = proof_call("ninth-residue", [sum, numeral(1)]);
    reject_changed_statement(
        "natural-ninth-exclusion.lim",
        "ninth-sum-one-one",
        &format!("(#statement {wrong_residue})"),
    );
}

fn integer_pair(positive: usize, negative: usize) -> String {
    format!(
        "(#pt-construct integer () () difference ({} {}))",
        numeral(positive),
        numeral(negative)
    )
}

fn integer_equivalent(first: String, second: String) -> String {
    proof_call("integer-equal", [first, second])
}

#[test]
fn integer_equivalence_accepts_representations_without_collapsing_record_identity() {
    let aliases = [
        ("integer", "integer-defs.lim"),
        ("integer-equal", "integer-defs.lim"),
        ("integer-transitive", "integer-equality.lim"),
    ];
    let first = integer_pair(5, 3);
    let second = integer_pair(4, 2);
    let third = integer_pair(3, 1);
    let proof = proof_call(
        "integer-transitive",
        [
            first.clone(),
            second,
            third.clone(),
            reflexivity(7),
            reflexivity(5),
        ],
    );
    expect_native_fixture(
        &aliases,
        "",
        &integer_equivalent(first.clone(), third.clone()),
        &proof,
        true,
    );
    let record_identity = format!("(#pt-eq (#pt-use integer ()) {first} {third})");
    // Equal integer values can have different pair representations. The kernel
    // must never interpret that relation as identity of the records themselves.
    expect_native_fixture(&aliases, "", &record_identity, &proof, false);
    let wrong = integer_pair(4, 1);
    let proof = proof_call(
        "integer-transitive",
        [
            first.clone(),
            integer_pair(4, 2),
            wrong.clone(),
            reflexivity(7),
            reflexivity(5),
        ],
    );
    expect_native_fixture(
        &aliases,
        "",
        &integer_equivalent(first, wrong),
        &proof,
        false,
    );
}

#[test]
fn signed_cube_normalization_handles_noncanonical_and_zero_representations() {
    let aliases = [
        ("integer", "integer-defs.lim"),
        ("integer-equal", "integer-defs.lim"),
        ("integer-cube", "integer-defs.lim"),
        (
            "integer-cube-normal-positive",
            "integer-cube-normalization.lim",
        ),
        (
            "integer-cube-normal-negative",
            "integer-cube-normalization.lim",
        ),
    ];
    for (p, n, magnitude, negative, valid) in [
        (3, 1, 2, false, true),
        (1, 3, 2, true, true),
        (0, 0, 0, false, true),
        (2, 2, 0, true, true),
        (3, 1, 3, false, false),
        (1, 3, 2, false, false),
    ] {
        let value = integer_pair(p, n);
        let cross = if negative { p + magnitude } else { p };
        let name = if negative {
            "integer-cube-normal-negative"
        } else {
            "integer-cube-normal-positive"
        };
        let proof = proof_call(
            name,
            [value.clone(), numeral(magnitude), reflexivity(cross)],
        );
        let cube = magnitude * magnitude * magnitude;
        let expected = if negative {
            integer_pair(0, cube)
        } else {
            integer_pair(cube, 0)
        };
        let statement = integer_equivalent(proof_call("integer-cube", [value]), expected);
        expect_native_fixture(&aliases, "", &statement, &proof, valid);
    }
}

fn signed_divisibility_witness(d: usize, n: usize, positive: usize, negative: usize) -> String {
    let factor = integer_pair(positive, negative);
    let product = proof_call(
        "integer-multiply",
        [integer_pair(d, 0), "factor".to_owned()],
    );
    let predicate = format!(
        "(#pt-lambda ((factor (#pt-use integer ()))) {})",
        integer_equivalent(integer_pair(n, 0), product)
    );
    format!(
        "(#pt-construct exists (0) ((#pt-use integer ()) {predicate}) introduce ({factor} {}))",
        reflexivity(n + d * negative)
    )
}

#[test]
fn natural_divisibility_reflection_accepts_zero_and_rejects_false_signed_factors() {
    let aliases = [
        ("divides", "natural-divisibility-defs.lim"),
        ("integer", "integer-defs.lim"),
        ("integer-equal", "integer-defs.lim"),
        ("integer-multiply", "integer-defs.lim"),
        (
            "integer-natural-divisibility-reflects",
            "integer-natural-bridge.lim",
        ),
    ];
    for (d, n, p, m, valid) in [
        (3, 6, 2, 0, true),
        (3, 6, 5, 3, true),
        (0, 0, 3, 7, true),
        (3, 0, 0, 0, true),
        (3, 6, 0, 2, false),
        (3, 0, 0, 2, false),
        (3, 7, 2, 0, false),
    ] {
        let proof = proof_call(
            "integer-natural-divisibility-reflects",
            [
                numeral(d),
                numeral(n),
                signed_divisibility_witness(d, n, p, m),
            ],
        );
        expect_native_fixture(
            &aliases,
            "",
            &proof_call("divides", [numeral(d), numeral(n)]),
            &proof,
            valid,
        );
    }
}

fn small_natural_not_divisible_by_three(n: usize) -> String {
    assert!(n == 1 || n == 2);
    let hypothesis = proof_call("divides", [numeral(3), numeral(n)]);
    let nonzero = proof_call("successor-not-zero", [numeral(n - 1)]);
    let predicate = format!(
        "(#pt-lambda ((gap #pt-nat)) {})",
        natural_equation(
            &numeral(3),
            &proof_call(
                "add",
                [format!("(#pt-succ {})", numeral(n)), "gap".to_owned()]
            )
        )
    );
    let less = format!(
        "(#pt-construct exists (0) (#pt-nat {predicate}) introduce ({} {}))",
        numeral(2 - n),
        reflexivity(3)
    );
    let forbidden = proof_call(
        "divisor-not-above",
        [
            numeral(3),
            numeral(n),
            nonzero,
            "natural-divides-proof".to_owned(),
        ],
    );
    format!("(#pt-lambda ((natural-divides-proof {hypothesis})) (#pt-app {forbidden} {less}))")
}

fn integer_not_divisible_by_three(p: usize, n: usize, magnitude: usize) -> String {
    let negative = n > p;
    let value = integer_pair(p, n);
    let canonical = if negative {
        integer_pair(0, magnitude)
    } else {
        integer_pair(magnitude, 0)
    };
    let equivalence = reflexivity(if negative { p + magnitude } else { p });
    let premise = proof_call("integer-divides", [integer_pair(3, 0), value.clone()]);
    let mut transferred = proof_call(
        "integer-divides-congruent-target",
        [
            integer_pair(3, 0),
            value,
            canonical.clone(),
            equivalence,
            "integer-divides-proof".to_owned(),
        ],
    );
    if negative {
        transferred = proof_call(
            "integer-divides-negative-target",
            [integer_pair(3, 0), canonical, transferred],
        );
    }
    let reflected = proof_call(
        "integer-natural-divisibility-reflects",
        [numeral(3), numeral(magnitude), transferred],
    );
    format!(
        "(#pt-lambda ((integer-divides-proof {premise})) (#pt-app {} {reflected}))",
        small_natural_not_divisible_by_three(magnitude)
    )
}

#[test]
fn signed_first_case_covers_every_sign_with_actual_nondivisibility_evidence() {
    let aliases = [
        ("divides", "natural-divisibility-defs.lim"),
        ("integer", "integer-defs.lim"),
        ("integer-equal", "integer-defs.lim"),
        ("integer-add", "integer-defs.lim"),
        ("integer-multiply", "integer-defs.lim"),
        ("integer-power", "integer-defs.lim"),
        ("integer-divides", "integer-defs.lim"),
        (
            "integer-divides-congruent-target",
            "integer-divisibility.lim",
        ),
        (
            "integer-divides-negative-target",
            "integer-divisibility.lim",
        ),
        (
            "integer-natural-divisibility-reflects",
            "integer-natural-bridge.lim",
        ),
        ("divisor-not-above", "natural-divisibility-bounds.lim"),
        ("successor-not-zero", "natural-nonzero.lim"),
        (
            "fermat-three-first-case-integers",
            "fermat-three-first-case-integers.lim",
        ),
    ];
    for signs in 0..8 {
        let values: Vec<(usize, usize)> = [1, 2, 1]
            .into_iter()
            .enumerate()
            .map(|(i, m)| {
                if signs & (1 << i) == 0 {
                    (m + 1, 1)
                } else {
                    (1, m + 1)
                }
            })
            .collect();
        let multiply = |(ap, an): (usize, usize), (bp, bn): (usize, usize)| {
            (ap * bp + an * bn, ap * bn + an * bp)
        };
        let (p, n) = multiply(multiply(values[0], values[1]), values[2]);
        let terms: Vec<String> = values.iter().map(|&(p, n)| integer_pair(p, n)).collect();
        let proof = proof_call(
            "fermat-three-first-case-integers",
            terms
                .clone()
                .into_iter()
                .chain([integer_not_divisible_by_three(p, n, 2)]),
        );
        let powers: Vec<String> = terms
            .into_iter()
            .map(|t| proof_call("integer-power", [t, numeral(3)]))
            .collect();
        let equation = integer_equivalent(
            proof_call("integer-add", [powers[0].clone(), powers[1].clone()]),
            powers[2].clone(),
        );
        let statement = format!("(#pt-pi ((forbidden-equation {equation})) #pt-false)");
        expect_native_fixture(&aliases, "", &statement, &proof, true);
    }
    // 0³+1³=1³: a fabricated nondivisibility proof for the zero product must fail.
    let proof = proof_call(
        "fermat-three-first-case-integers",
        [
            integer_pair(0, 0),
            integer_pair(1, 0),
            integer_pair(1, 0),
            integer_not_divisible_by_three(0, 0, 2),
        ],
    );
    let zero = proof_call("integer-power", [integer_pair(0, 0), numeral(3)]);
    let one = proof_call("integer-power", [integer_pair(1, 0), numeral(3)]);
    let equation = integer_equivalent(proof_call("integer-add", [zero, one.clone()]), one);
    expect_native_fixture(
        &aliases,
        "",
        &format!("(#pt-pi ((forbidden-equation {equation})) #pt-false)"),
        &proof,
        false,
    );
}

#[test]
fn signed_multiplication_cannot_discard_negation() {
    let negative = proof_call("integer-negate", ["first".to_owned()]);
    let left = proof_call("integer-multiply", [negative, "second".to_owned()]);
    let wrong = proof_call(
        "integer-multiply",
        ["first".to_owned(), "second".to_owned()],
    );
    reject_changed_statement(
        "integer-multiplication.lim",
        "integer-multiply-negative",
        &format!("(#statement {})", integer_equivalent(left, wrong)),
    );
}

#[test]
fn magnitude_gcd_and_prime_proofs_are_universally_checked() {
    let modules: &[(&str, &[&str])] = &[
        (
            "integer-magnitude.lim",
            &[
                "integer-natural-magnitude",
                "integer-negative-magnitude",
                "integer-magnitude-exists",
                "integer-magnitude-congruent",
                "integer-magnitude-negate",
                "integer-opposite-magnitudes-equal",
                "integer-magnitude-unique",
                "integer-zero-of-magnitude-zero",
                "integer-zero-forces-magnitude-zero",
                "integer-nonzero-magnitude",
                "integer-nonzero-of-magnitude",
                "integer-divides-magnitude",
                "integer-divides-of-magnitude",
                "integer-divides-magnitude-divisor",
                "integer-divides-from-magnitude-divisor",
            ],
        ),
        (
            "integer-gcd.lim",
            &[
                "integer-gcd-divides-first",
                "integer-gcd-divides-second",
                "integer-gcd-universal",
                "integer-gcd-from-magnitudes",
                "integer-gcd-magnitudes",
                "integer-gcd-exists",
                "integer-gcd-of-naturals",
                "integer-gcd-unique",
                "integer-gcd-symmetric",
                "integer-gcd-congruent",
                "integer-gcd-negative-first",
                "integer-gcd-negative-second",
                "integer-gcd-zero-right",
                "integer-gcd-one-common-divisor",
            ],
        ),
        (
            "integer-gcd-three.lim",
            &[
                "integer-gcd-three-divides-first",
                "integer-gcd-three-divides-second",
                "integer-gcd-three-divides-third",
                "integer-gcd-three-universal",
                "integer-gcd-three-from-pairs",
                "integer-gcd-three-exists",
                "integer-gcd-three-unique",
                "integer-gcd-three-swap-first",
                "integer-gcd-three-rotate",
                "integer-gcd-three-negative-first",
                "integer-gcd-three-negative-second",
                "integer-gcd-three-negative-third",
                "integer-gcd-three-congruent",
                "integer-gcd-three-one-common-divisor",
                "integer-gcd-associative",
            ],
        ),
        (
            "natural-prime-three.lim",
            &[
                "two-not-divides-three",
                "prime-three",
                "three-not-divides-one",
                "three-not-divides-two",
            ],
        ),
        (
            "integer-magnitude-products.lim",
            &[
                "integer-magnitude-multiply",
                "integer-magnitude-cube",
                "integer-magnitude-power",
            ],
        ),
        (
            "integer-divisibility-addition.lim",
            &[
                "integer-multiply-distribute-second",
                "integer-zero-add",
                "integer-add-negative-cancel",
                "integer-divides-add",
                "integer-divides-add-cancel-left",
                "integer-divides-add-cancel-right",
                "integer-divides-zero-sum-other",
                "integer-zero-divisor-equivalence",
                "integer-divisor-nonzero",
                "integer-cube-negate",
            ],
        ),
        (
            "integer-prime-divisibility.lim",
            &[
                "integer-prime-divides-product",
                "integer-prime-divides-power",
                "integer-prime-divides-cube",
                "integer-prime-common-cubes-third",
            ],
        ),
        (
            "integer-cubic-gcd.lim",
            &[
                "integer-primitive-cubic-common-prime-impossible",
                "integer-primitive-cubic-first-excludes-second-prime",
                "integer-cubic-pair-gcd-is-one",
                "integer-cubic-gcd-one-first-pair",
                "integer-three-sum-zero-rotate",
                "integer-cubic-gcd-one-third-pair",
                "integer-cubic-gcd-one-second-pair",
            ],
        ),
    ];
    check_native_modules_without_foundations(modules);
}

fn magnitude_aliases() -> &'static [(&'static str, &'static str)] {
    &[
        ("divides", "natural-divisibility-defs.lim"),
        ("integer", "integer-defs.lim"),
        ("integer-equal", "integer-defs.lim"),
        ("integer-zero", "integer-defs.lim"),
        ("integer-one", "integer-defs.lim"),
        ("integer-add", "integer-defs.lim"),
        ("integer-multiply", "integer-defs.lim"),
        ("integer-cube", "integer-defs.lim"),
        ("integer-power", "integer-defs.lim"),
        ("integer-divides", "integer-defs.lim"),
        ("integer-magnitude", "integer-magnitude.lim"),
        ("integer-magnitude-unique", "integer-magnitude.lim"),
        ("integer-magnitude-congruent", "integer-magnitude.lim"),
        ("integer-nonzero-of-magnitude", "integer-magnitude.lim"),
        ("integer-gcd-spec", "integer-gcd.lim"),
        ("integer-gcd-from-magnitudes", "integer-gcd.lim"),
        ("integer-gcd-three-spec", "integer-gcd-three.lim"),
        ("integer-gcd-three-from-pairs", "integer-gcd-three.lim"),
        ("integer-cubic-gcd-one-first-pair", "integer-cubic-gcd.lim"),
        ("prime-three", "natural-prime-three.lim"),
        (
            "integer-prime-divides-product",
            "integer-prime-divisibility.lim",
        ),
        (
            "integer-prime-divides-power",
            "integer-prime-divisibility.lim",
        ),
        (
            "integer-prime-common-cubes-third",
            "integer-prime-divisibility.lim",
        ),
        ("disjunction", "logical-connectives.lim"),
        ("disjunction-left", "logical-connectives.lim"),
        ("disjunction-right", "logical-connectives.lim"),
        ("successor-not-zero", "natural-nonzero.lim"),
    ]
}

fn magnitude_evidence((p, n): (usize, usize), m: usize, negative: bool) -> String {
    let value = integer_pair(p, n);
    let positive = integer_equivalent(value.clone(), integer_pair(m, 0));
    let negated = integer_equivalent(value, integer_pair(0, m));
    proof_call(
        if negative {
            "disjunction-right"
        } else {
            "disjunction-left"
        },
        [
            positive,
            negated,
            reflexivity(if negative { p + m } else { p }),
        ],
    )
}

fn signed_gcd_certificate(a: (usize, usize), b: (usize, usize)) -> (usize, String) {
    let am = a.0.abs_diff(a.1);
    let bm = b.0.abs_diff(b.1);
    let (g, natural) = gcd_certificate(am, bm);
    let proof = proof_call(
        "integer-gcd-from-magnitudes",
        [
            integer_pair(a.0, a.1),
            integer_pair(b.0, b.1),
            numeral(am),
            numeral(bm),
            numeral(g),
            magnitude_evidence(a, am, a.1 > a.0),
            magnitude_evidence(b, bm, b.1 > b.0),
            natural,
        ],
    );
    (g, proof)
}

fn signed_triple_gcd_certificate(
    a: (usize, usize),
    b: (usize, usize),
    c: (usize, usize),
) -> (usize, String) {
    let (h, first) = signed_gcd_certificate(a, b);
    let (g, outer) = signed_gcd_certificate((h, 0), c);
    (
        g,
        proof_call(
            "integer-gcd-three-from-pairs",
            [
                integer_pair(a.0, a.1),
                integer_pair(b.0, b.1),
                integer_pair(c.0, c.1),
                numeral(h),
                numeral(g),
                first,
                outer,
            ],
        ),
    )
}

#[test]
fn magnitude_uniqueness_checks_signs_zero_and_equivalent_representations() {
    for value in [(5usize, 3usize), (1, 4), (2, 2), (0, 0)] {
        let m = value.0.abs_diff(value.1);
        for (claimed, valid) in [(m, true), (m + 1, false)] {
            let proof = proof_call(
                "integer-magnitude-unique",
                [
                    integer_pair(value.0, value.1),
                    numeral(m),
                    numeral(claimed),
                    magnitude_evidence(value, m, value.1 > value.0),
                    magnitude_evidence(
                        value,
                        claimed,
                        if m == 0 { true } else { value.1 > value.0 },
                    ),
                ],
            );
            expect_native_fixture(
                magnitude_aliases(),
                "",
                &natural_equation(&numeral(m), &numeral(claimed)),
                &proof,
                valid,
            );
        }
    }
    for (other, valid) in [((2, 0), true), ((3, 0), false)] {
        let proof = proof_call(
            "integer-magnitude-congruent",
            [
                integer_pair(5, 3),
                integer_pair(other.0, other.1),
                numeral(2),
                reflexivity(5),
                magnitude_evidence((5, 3), 2, false),
            ],
        );
        let statement = proof_call(
            "integer-magnitude",
            [integer_pair(other.0, other.1), numeral(2)],
        );
        expect_native_fixture(magnitude_aliases(), "", &statement, &proof, valid);
    }
}

#[test]
fn magnitude_signed_gcd_certificates_cover_zero_and_noncanonical_signs() {
    for (a, b, expected) in [
        ((6, 0), (0, 10), 2),
        ((7, 1), (1, 11), 2),
        ((0, 0), (2, 7), 5),
        ((0, 0), (0, 0), 0),
    ] {
        let (g, proof) = signed_gcd_certificate(a, b);
        assert_eq!(g, expected);
        for (claimed, valid) in [(g, true), (g + 1, false)] {
            let statement = proof_call(
                "integer-gcd-spec",
                [
                    integer_pair(a.0, a.1),
                    integer_pair(b.0, b.1),
                    numeral(claimed),
                ],
            );
            expect_native_fixture(magnitude_aliases(), "", &statement, &proof, valid);
        }
    }
}

#[test]
fn magnitude_triple_gcd_and_cubic_pairs_require_primitive_evidence() {
    for (a, b, c, expected) in [
        ((7, 1), (1, 11), (16, 1), 1),
        ((6, 0), (0, 10), (14, 0), 2),
        ((0, 0), (0, 0), (0, 0), 0),
    ] {
        let (g, proof) = signed_triple_gcd_certificate(a, b, c);
        assert_eq!(g, expected);
        let statement = proof_call(
            "integer-gcd-three-spec",
            [
                integer_pair(a.0, a.1),
                integer_pair(b.0, b.1),
                integer_pair(c.0, c.1),
                numeral(g),
            ],
        );
        expect_native_fixture(magnitude_aliases(), "", &statement, &proof, true);
        if g != 1 {
            let wrong = proof_call(
                "integer-gcd-three-spec",
                [
                    integer_pair(a.0, a.1),
                    integer_pair(b.0, b.1),
                    integer_pair(c.0, c.1),
                    numeral(1),
                ],
            );
            expect_native_fixture(magnitude_aliases(), "", &wrong, &proof, false);
        }
    }
    // a³ + 0³ + (-a)³ = 0, but the triple is primitive only when a=1.
    for (a, valid) in [(1, true), (2, false)] {
        let (_, triple) = signed_triple_gcd_certificate((a, 0), (0, 0), (0, a));
        let nonzero = proof_call(
            "integer-nonzero-of-magnitude",
            [
                integer_pair(a, 0),
                numeral(a),
                magnitude_evidence((a, 0), a, false),
                proof_call("successor-not-zero", [numeral(a - 1)]),
            ],
        );
        let proof = proof_call(
            "integer-cubic-gcd-one-first-pair",
            [
                integer_pair(a, 0),
                integer_pair(0, 0),
                integer_pair(0, a),
                triple,
                reflexivity(a * a * a),
                nonzero,
            ],
        );
        let statement = proof_call(
            "integer-gcd-spec",
            [integer_pair(a, 0), integer_pair(0, 0), numeral(1)],
        );
        expect_native_fixture(magnitude_aliases(), "", &statement, &proof, valid);
    }
}

fn explicit_signed_factor(
    divisor: usize,
    value: String,
    value_parts: (usize, usize),
    factor: (usize, usize),
) -> String {
    let product = proof_call(
        "integer-multiply",
        [integer_pair(divisor, 0), "factor".to_owned()],
    );
    let predicate = format!(
        "(#pt-lambda ((factor (#pt-use integer ()))) {})",
        integer_equivalent(value, product)
    );
    format!(
        "(#pt-construct exists (0) ((#pt-use integer ()) {predicate}) introduce ({} {}))",
        integer_pair(factor.0, factor.1),
        reflexivity(value_parts.0 + divisor * factor.1)
    )
}

#[test]
fn magnitude_primes_check_signed_products_powers_and_cubic_sums() {
    for (base, exponent, value, factor, valid) in [
        ((3, 0), 1, (3, 0), (1, 0), true),
        ((0, 3), 1, (0, 3), (0, 1), true),
        ((0, 3), 2, (9, 0), (3, 0), true),
        ((0, 3), 3, (0, 27), (0, 9), true),
        ((0, 3), 0, (1, 0), (0, 0), false),
        ((2, 0), 2, (4, 0), (1, 0), false),
    ] {
        let a = integer_pair(base.0, base.1);
        let powered = proof_call("integer-power", [a.clone(), numeral(exponent)]);
        let evidence = explicit_signed_factor(3, powered, value, factor);
        let proof = proof_call(
            "integer-prime-divides-power",
            [
                numeral(3),
                a.clone(),
                numeral(exponent),
                "(#pt-use prime-three ())".to_owned(),
                evidence,
            ],
        );
        expect_native_fixture(
            magnitude_aliases(),
            "",
            &proof_call("integer-divides", [integer_pair(3, 0), a]),
            &proof,
            valid,
        );
    }
    let a = integer_pair(0, 2);
    let b = integer_pair(0, 3);
    let product = proof_call("integer-multiply", [a.clone(), b.clone()]);
    let proof = proof_call(
        "integer-prime-divides-product",
        [
            numeral(3),
            a.clone(),
            b.clone(),
            "(#pt-use prime-three ())".to_owned(),
            explicit_signed_factor(3, product, (6, 0), (2, 0)),
        ],
    );
    let statement = proof_call(
        "disjunction",
        [
            proof_call("integer-divides", [integer_pair(3, 0), a]),
            proof_call("integer-divides", [integer_pair(3, 0), b]),
        ],
    );
    expect_native_fixture(magnitude_aliases(), "", &statement, &proof, true);
    for (last, valid) in [(3, true), (2, false)] {
        let a = integer_pair(3, 0);
        let b = integer_pair(0, 0);
        let c = integer_pair(0, last);
        let proof = proof_call(
            "integer-prime-common-cubes-third",
            [
                numeral(3),
                a.clone(),
                b.clone(),
                c.clone(),
                "(#pt-use prime-three ())".to_owned(),
                explicit_signed_factor(3, a, (3, 0), (1, 0)),
                explicit_signed_factor(3, b, (0, 0), (0, 0)),
                reflexivity(27),
            ],
        );
        expect_native_fixture(
            magnitude_aliases(),
            "",
            &proof_call("integer-divides", [integer_pair(3, 0), c]),
            &proof,
            valid,
        );
    }
}

#[test]
fn magnitude_negative_controls_reject_wrong_gcd_power_and_prime_conclusions() {
    reject_changed_statement(
        "integer-gcd.lim",
        "integer-gcd-unique",
        "(#statement (#pt-eq #pt-nat greatest-divisor (#pt-succ second-gcd)))",
    );
    reject_changed_statement(
        "natural-prime-three.lim",
        "prime-three",
        "(#statement (#pt-app (#pt-use prime ()) (#pt-numeral 4)))",
    );
    let wrong = proof_call(
        "integer-divides",
        [
            proof_call("integer-of-natural", ["prime-number".to_owned()]),
            "(#pt-use integer-one ())".to_owned(),
        ],
    );
    reject_changed_statement(
        "integer-prime-divisibility.lim",
        "integer-prime-divides-power",
        &format!("(#statement {wrong})"),
    );
}

#[test]
fn magnitude_cli_roots_check_without_external_proof_tools() {
    for (file, target) in [
        ("natural-prime-three.lim", "prime-three"),
        ("integer-gcd-three.lim", "integer-gcd-three-exists"),
        ("integer-cubic-gcd.lim", "integer-cubic-gcd-one-first-pair"),
    ] {
        let path = module(file);
        let mut command = Command::new(env!("CARGO_BIN_EXE_lim"));
        command
            .env("PATH", "")
            .args(["--check-theorem", path.to_str().unwrap(), target]);
        let (status, stdout, stderr) =
            support::run(&mut command, Duration::from_secs(15), 1024 * 1024).unwrap();
        assert!(status.success(), "{}", String::from_utf8_lossy(&stderr));
        assert_eq!(stdout, format!("checked theorem {target}\n").as_bytes());
        assert!(stderr.is_empty(), "{}", String::from_utf8_lossy(&stderr));
    }
}

fn eisenstein_aliases() -> Vec<(&'static str, &'static str)> {
    let mut aliases = bezout_aliases().to_vec();
    aliases.extend([
        ("integer-divides", "integer-defs.lim"),
        ("conjunction", "logical-connectives.lim"),
        ("eisenstein", "eisenstein-defs.lim"),
        ("eisenstein-one", "eisenstein-defs.lim"),
        ("eisenstein-omega", "eisenstein-defs.lim"),
        ("eisenstein-lambda", "eisenstein-defs.lim"),
        ("eisenstein-equal", "eisenstein-defs.lim"),
        ("eisenstein-of-integer", "eisenstein-defs.lim"),
        ("eisenstein-multiply", "eisenstein-defs.lim"),
        ("eisenstein-power", "eisenstein-defs.lim"),
        ("eisenstein-coprime", "eisenstein-defs.lim"),
        ("eisenstein-divides", "eisenstein-defs.lim"),
        ("eisenstein-coprime-of-integer", "eisenstein-bezout.lim"),
        ("integer-three-divides-of-lambda", "eisenstein-lambda.lim"),
        (
            "eisenstein-lambda-divides-of-three",
            "eisenstein-lambda.lim",
        ),
    ]);
    aliases
}

fn eisenstein_pair(real: (usize, usize), imag: (usize, usize)) -> String {
    format!(
        "(#pt-construct eisenstein () () pair ({} {}))",
        integer_pair(real.0, real.1),
        integer_pair(imag.0, imag.1)
    )
}

#[test]
fn eisenstein_coprimality_cast_checks_the_actual_signed_coefficients() {
    let a = (5, 2);
    let b = (0, 2);
    let first = integer_pair(a.0, a.1);
    let second = integer_pair(b.0, b.1);
    let statement = proof_call(
        "eisenstein-coprime",
        [
            proof_call("eisenstein-of-integer", [first.clone()]),
            proof_call("eisenstein-of-integer", [second.clone()]),
        ],
    );
    for (left, valid) in [((1, 0), true), ((2, 0), false)] {
        let coefficient_proof = explicit_bezout_certificate(a, b, (1, 0), left, (1, 0));
        let proof = proof_call(
            "eisenstein-coprime-of-integer",
            [first.clone(), second.clone(), coefficient_proof],
        );
        expect_native_fixture(&eisenstein_aliases(), "", &statement, &proof, valid);
    }
}

#[test]
fn eisenstein_component_equivalence_does_not_imply_record_identity() {
    let a = eisenstein_pair((5, 2), (7, 4));
    let b = eisenstein_pair((3, 0), (3, 0));
    let field = |index, x: &str| format!("(#pt-project eisenstein {index} {x})");
    let real = integer_equivalent(field(0, &a), field(0, &b));
    let imag = integer_equivalent(field(1, &a), field(1, &b));
    let proof = proof_call(
        "conjunction-introduce",
        [real, imag, reflexivity(5), reflexivity(7)],
    );
    expect_native_fixture(
        &eisenstein_aliases(),
        "",
        &proof_call("eisenstein-equal", [a.clone(), b.clone()]),
        &proof,
        true,
    );
    expect_native_fixture(
        &eisenstein_aliases(),
        "",
        &format!("(#pt-eq (#pt-use eisenstein ()) {a} {b})"),
        &format!("(#pt-refl (#pt-use eisenstein ()) {b})"),
        false,
    );
}

fn explicit_lambda_factor(n: (usize, usize), u: (usize, usize), v: (usize, usize)) -> String {
    let lambda = "(#pt-use eisenstein-lambda ())".to_owned();
    let dividend = proof_call("eisenstein-of-integer", [integer_pair(n.0, n.1)]);
    let factor = eisenstein_pair(u, v);
    let product = proof_call("eisenstein-multiply", [lambda.clone(), factor.clone()]);
    let field = |index, x: &str| format!("(#pt-project eisenstein {index} {x})");
    let real = integer_equivalent(field(0, &dividend), field(0, &product));
    let imag = integer_equivalent(field(1, &dividend), field(1, &product));
    let equation = proof_call(
        "conjunction-introduce",
        [
            real,
            imag,
            reflexivity(n.0 + u.0 + v.0),
            reflexivity(v.0 + u.1 + v.0),
        ],
    );
    let predicate = format!(
        "(#pt-lambda ((candidate-factor (#pt-use eisenstein ()))) {})",
        proof_call(
            "eisenstein-equal",
            [
                dividend,
                proof_call(
                    "eisenstein-multiply",
                    [lambda, "candidate-factor".to_owned()]
                )
            ]
        )
    );
    format!("(#pt-construct exists (0) ((#pt-use eisenstein ()) {predicate}) introduce ({factor} {equation}))")
}

#[test]
fn eisenstein_lambda_divisibility_checks_both_directions_and_false_factors() {
    for (n, k, u, v, valid) in [
        ((0, 0), (0, 0), (0, 0), (0, 0), true),
        ((3, 0), (1, 0), (0, 2), (0, 1), true),
        ((6, 0), (2, 0), (0, 4), (0, 2), true),
        ((0, 3), (0, 1), (2, 0), (1, 0), true),
        ((8, 2), (2, 0), (0, 4), (0, 2), true),
        ((1, 0), (0, 0), (0, 0), (0, 0), false),
        ((2, 0), (0, 0), (0, 0), (0, 0), false),
        ((3, 0), (1, 0), (2, 0), (1, 0), false),
    ] {
        let value = integer_pair(n.0, n.1);
        let three = integer_pair(3, 0);
        let source = explicit_signed_factor(3, value.clone(), n, k);
        let target = proof_call(
            "eisenstein-divides",
            [
                "(#pt-use eisenstein-lambda ())".to_owned(),
                proof_call("eisenstein-of-integer", [value.clone()]),
            ],
        );
        // The final case intentionally supplies the correct integer factor
        // but the wrong Eisenstein sign; only the reflection must reject it.
        if n != (3, 0) || u != (2, 0) {
            let proof = proof_call(
                "eisenstein-lambda-divides-of-three",
                [value.clone(), source],
            );
            expect_native_fixture(&eisenstein_aliases(), "", &target, &proof, valid);
        }
        let reflected = proof_call(
            "integer-three-divides-of-lambda",
            [value.clone(), explicit_lambda_factor(n, u, v)],
        );
        expect_native_fixture(
            &eisenstein_aliases(),
            "",
            &proof_call("integer-divides", [three, value]),
            &reflected,
            valid,
        );
    }
}

#[test]
fn eisenstein_constants_and_residual_bridge_reject_false_claims() {
    let square = proof_call(
        "eisenstein-power",
        ["(#pt-use eisenstein-lambda ())".to_owned(), numeral(2)],
    );
    let wrong = proof_call(
        "eisenstein-multiply",
        [
            proof_call(
                "eisenstein-of-integer",
                [proof_call("integer-of-natural", [numeral(3)])],
            ),
            "(#pt-use eisenstein-omega ())".to_owned(),
        ],
    );
    reject_changed_statement(
        "eisenstein-constants.lim",
        "eisenstein-lambda-square",
        &format!(
            "(#statement {})",
            proof_call("eisenstein-equal", [square, wrong])
        ),
    );
    let path = module("eisenstein-cubic-bridge.lim");
    let source = fs::read_to_string(&path).unwrap();
    let changed = source.replace(
        "(#parameter general-case ",
        "(#parameter missing-general-case ",
    );
    assert_ne!(source, changed);
    let why = check_theorem_details_from_path_with_config(
        &changed,
        &path,
        &CompileConfig::default(),
        "integer-fermat-three-residual-of-eisenstein",
    )
    .unwrap_err();
    assert_eq!(why.code, DiagnosticCode::Proof);
}

#[test]
fn eisenstein_and_bezout_cli_roots_need_no_external_proof_tools() {
    for (file, target) in [
        ("integer-gcd-bezout.lim", "integer-gcd-bezout"),
        ("eisenstein-lambda.lim", "integer-three-divides-of-lambda"),
        (
            "eisenstein-cubic-bridge.lim",
            "integer-fermat-three-residual-gcd-of-eisenstein",
        ),
    ] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_lim"));
        command
            .env("PATH", "")
            .args(["--check-theorem", module(file).to_str().unwrap(), target]);
        let (status, stdout, stderr) =
            support::run(&mut command, Duration::from_secs(30), 1024 * 1024).unwrap();
        assert!(status.success(), "{}", String::from_utf8_lossy(&stderr));
        assert_eq!(stdout, format!("checked theorem {target}\n").as_bytes());
        assert!(stderr.is_empty(), "{}", String::from_utf8_lossy(&stderr));
    }
}

#[test]
fn cubic_port_all_normalization_theorems_are_checked_without_foundations() {
    let modules: &[(&str, &[&str])] = &[
        (
            "fermat-three-factor-descent.lim",
            &[
                "cube-product",
                "natural-factor-nonzero",
                "cubic-common-prime-divides-third",
                "cubic-remove-common-factor",
                "cubic-solution-remove-prime",
                "cubic-common-prime-descends",
            ],
        ),
        (
            "fermat-three-primitive-orientation.lim",
            &[
                "integer-primitive-cubic-divisible-first-impossible",
                "integer-primitive-cubic-refuted-by-residual",
            ],
        ),
        (
            "fermat-three-primitive.lim",
            &[
                "natural-cubic-primitive-induction-step",
                "natural-cubic-has-primitive",
                "natural-cubic-refuted-by-primitive",
                "fermat-for-three-from-primitive",
            ],
        ),
        (
            "fermat-three-residual.lim",
            &[
                "integer-cubic-equation-as-power",
                "integer-cubic-negated-pair",
                "integer-cubic-sum-first-case-impossible",
                "integer-residual-refutes-cubes",
                "integer-residual-of-eisenstein-general",
            ],
        ),
        (
            "fermat-three-signed-bridge.lim",
            &[
                "integer-one-divides",
                "integer-gcd-three-one-of-pair",
                "integer-natural-nonzero",
                "natural-cubic-signed-sum",
                "natural-primitive-cubic-refuted-by-residual",
                "fermat-for-three-from-residual",
                "fermat-for-three-from-eisenstein",
            ],
        ),
        (
            "integer-divisibility-decision.lim",
            &[
                "integer-natural-divisibility-decided",
                "integer-nonzero-of-not-divisible",
                "integer-not-divides-negative-target",
                "integer-negative-nonzero",
            ],
        ),
    ];
    check_native_modules_without_foundations(modules);
}

fn cubic_port_aliases() -> Vec<(&'static str, &'static str)> {
    let mut aliases = magnitude_aliases().to_vec();
    for (name, file) in [
        ("cube", "natural-ninth-residues.lim"),
        ("cube-product", "fermat-three-factor-descent.lim"),
        ("natural-factor-nonzero", "fermat-three-factor-descent.lim"),
        (
            "cubic-remove-common-factor",
            "fermat-three-factor-descent.lim",
        ),
        (
            "cubic-common-prime-divides-third",
            "fermat-three-factor-descent.lim",
        ),
        ("successor-not-zero", "natural-nonzero.lim"),
        ("prime-two", "natural-prime-two.lim"),
        ("integer-negate", "integer-defs.lim"),
        ("integer-cubic-negated-pair", "fermat-three-residual.lim"),
        (
            "integer-gcd-three-one-of-pair",
            "fermat-three-signed-bridge.lim",
        ),
    ] {
        if !aliases.iter().any(|(existing, _)| *existing == name) {
            aliases.push((name, file));
        }
    }
    aliases
}

#[test]
fn cubic_port_factor_cancellation_handles_zero_legs_and_rejects_bad_factors() {
    for (a, b, c, d, u, v, w, valid) in [
        (0, 4, 4, 2usize, 0, 2, 2, true),
        (3, 0, 3, 3, 1, 0, 1, true),
        (0, 0, 0, 1, 0, 0, 0, true),
        (0, 4, 4, 2, 0, 2, 1, false),
        (0, 4, 4, 0, 0, 2, 2, false),
    ] {
        let factor_nonzero = proof_call("successor-not-zero", [numeral(d.saturating_sub(1))]);
        let proof = proof_call(
            "cubic-remove-common-factor",
            [
                numeral(a),
                numeral(b),
                numeral(c),
                numeral(d),
                numeral(u),
                numeral(v),
                numeral(w),
                factor_nonzero,
                reflexivity(a * a * a + b * b * b),
                reflexivity(a),
                reflexivity(b),
                reflexivity(c),
            ],
        );
        let cube = |x| proof_call("cube", [numeral(x)]);
        let statement = natural_equation(&proof_call("add", [cube(u), cube(v)]), &cube(w));
        expect_native_fixture(&cubic_port_aliases(), "", &statement, &proof, valid);
    }
}

#[test]
fn cubic_port_prime_propagation_requires_the_cubic_equation() {
    for (a, b, c, p, qa, qb, valid) in [
        (0, 4, 4, 2, 0, 2, true),
        (3, 0, 3, 3, 1, 0, true),
        (0, 4, 3, 2, 0, 2, false),
        (0, 4, 4, 3, 0, 1, false),
    ] {
        let factor = |n, q| {
            let predicate = format!(
                "(#pt-lambda ((candidate-factor #pt-nat)) {})",
                natural_equation(
                    &numeral(n),
                    &proof_call("multiply", [numeral(p), "candidate-factor".to_owned()])
                )
            );
            format!(
                "(#pt-construct exists (0) (#pt-nat {predicate}) introduce ({} {}))",
                numeral(q),
                reflexivity(n)
            )
        };
        let proof = proof_call(
            "cubic-common-prime-divides-third",
            [
                numeral(a),
                numeral(b),
                numeral(c),
                numeral(p),
                format!(
                    "(#pt-use prime-{} ())",
                    if p == 2 { "two" } else { "three" }
                ),
                reflexivity(a * a * a + b * b * b),
                factor(a, qa),
                factor(b, qb),
            ],
        );
        expect_native_fixture(
            &cubic_port_aliases(),
            "",
            &proof_call("divides", [numeral(p), numeral(c)]),
            &proof,
            valid,
        );
    }
}

#[test]
fn cubic_port_signed_rotation_and_primitive_gcd_keep_real_evidence() {
    // Genuine degenerate signed identities exercise the algebra without
    // pretending to construct a nonzero counterexample to exponent three.
    for (a, b, c, cross_sum) in [
        ((1, 0), (0, 0), (0, 1), 1),
        ((2, 0), (0, 2), (0, 0), 8),
        ((3, 1), (0, 2), (0, 0), 36),
    ] {
        let first = integer_pair(a.0, a.1);
        let second = integer_pair(b.0, b.1);
        let third = integer_pair(c.0, c.1);
        let proof = proof_call(
            "integer-cubic-negated-pair",
            [
                first.clone(),
                second.clone(),
                third.clone(),
                reflexivity(cross_sum),
            ],
        );
        let cube = |x| proof_call("integer-cube", [x]);
        let neg = |x| proof_call("integer-negate", [x]);
        let statement = integer_equivalent(
            proof_call("integer-add", [cube(neg(second)), cube(neg(third))]),
            cube(first),
        );
        expect_native_fixture(&cubic_port_aliases(), "", &statement, &proof, true);
    }
    for (a, b, c, valid) in [
        ((1, 0), (0, 2), (5, 0), true),
        ((2, 0), (4, 0), (1, 0), false),
    ] {
        let (_, pair) = signed_gcd_certificate(a, b);
        let values = [
            integer_pair(a.0, a.1),
            integer_pair(b.0, b.1),
            integer_pair(c.0, c.1),
        ];
        let proof = proof_call(
            "integer-gcd-three-one-of-pair",
            values.clone().into_iter().chain([pair]),
        );
        let statement = proof_call(
            "integer-gcd-three-spec",
            values.into_iter().chain([numeral(1)]),
        );
        expect_native_fixture(&cubic_port_aliases(), "", &statement, &proof, valid);
    }
}

#[test]
fn cubic_port_strict_descent_and_general_case_cannot_be_discarded() {
    let solution = proof_call(
        "natural-cubic-solution",
        [
            "next-first".to_owned(),
            "next-second".to_owned(),
            "next-third".to_owned(),
        ],
    );
    let pair = proof_call(
        "conjunction",
        [solution, natural_equation("next-third", "third")],
    );
    let exists = |binding: &str, body: String| {
        format!("(#pt-app (#pt-use exists (0)) #pt-nat (#pt-lambda (({binding} #pt-nat)) {body}))")
    };
    let wrong = exists(
        "next-first",
        exists("next-second", exists("next-third", pair)),
    );
    reject_changed_statement(
        "fermat-three-factor-descent.lim",
        "cubic-common-prime-descends",
        &format!("(#statement {wrong})"),
    );
    for (file, target, evidence) in [
        (
            "fermat-three-primitive.lim",
            "fermat-for-three-from-primitive",
            "primitive-case",
        ),
        (
            "fermat-three-signed-bridge.lim",
            "fermat-for-three-from-eisenstein",
            "general-case",
        ),
    ] {
        let path = module(file);
        let source = fs::read_to_string(&path).unwrap();
        let changed = source.replace(
            &format!("(#parameter {evidence} "),
            &format!("(#parameter missing-{evidence} "),
        );
        assert_ne!(source, changed);
        let why = check_theorem_details_from_path_with_config(
            &changed,
            &path,
            &CompileConfig::default(),
            target,
        )
        .unwrap_err();
        assert_eq!(why.code, DiagnosticCode::Proof);
    }
}

#[test]
fn cubic_port_cli_normalization_roots_need_no_external_proof_tools() {
    for (file, target) in [
        ("fermat-three-primitive.lim", "natural-cubic-has-primitive"),
        (
            "fermat-three-signed-bridge.lim",
            "fermat-for-three-from-eisenstein",
        ),
    ] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_lim"));
        command
            .env("PATH", "")
            .args(["--check-theorem", module(file).to_str().unwrap(), target]);
        let (status, stdout, stderr) =
            support::run(&mut command, Duration::from_secs(30), 1024 * 1024).unwrap();
        assert!(status.success(), "{}", String::from_utf8_lossy(&stderr));
        assert_eq!(stdout, format!("checked theorem {target}\n").as_bytes());
        assert!(stderr.is_empty(), "{}", String::from_utf8_lossy(&stderr));
    }
}

#[test]
fn eisenstein_ring_port_all_theorems_have_no_global_foundations() {
    let modules: &[(&str, &[&str])] = &[
        (
            "eisenstein-lambda-prime.lim",
            &[
                "eisenstein-coordinate-sum-congruent",
                "integer-three-divides-coordinate-sum",
                "eisenstein-lambda-divides-of-coordinate-sum",
                "eisenstein-lambda-not-divides-one",
                "eisenstein-lambda-not-unit",
                "eisenstein-lambda-divides-product",
                "eisenstein-lambda-prime",
                "eisenstein-lambda-divides-power",
                "eisenstein-lambda-divisibility-decided",
            ],
        ),
        (
            "eisenstein-product-associative-omega.lim",
            &["eisenstein-product-associative-omega"],
        ),
        (
            "eisenstein-product-associative-real.lim",
            &["eisenstein-product-associative-real"],
        ),
        (
            "eisenstein-product-commutative-omega.lim",
            &["eisenstein-product-commutative-omega"],
        ),
        (
            "eisenstein-product-commutative-real.lim",
            &["eisenstein-product-commutative-real"],
        ),
        (
            "eisenstein-product-distributive-omega.lim",
            &["eisenstein-product-distributive-omega"],
        ),
        (
            "eisenstein-product-distributive-real.lim",
            &["eisenstein-product-distributive-real"],
        ),
        (
            "eisenstein-product-negative-omega.lim",
            &["eisenstein-product-negative-omega"],
        ),
        (
            "eisenstein-product-negative-real.lim",
            &["eisenstein-product-negative-real"],
        ),
        (
            "eisenstein-ring.lim",
            &[
                "eisenstein-add-commutative",
                "eisenstein-add-associative",
                "eisenstein-add-zero",
                "eisenstein-add-inverse",
                "eisenstein-negate-involution",
                "eisenstein-negate-add",
                "eisenstein-multiply-commutative",
                "eisenstein-multiply-associative",
                "eisenstein-multiply-distributive",
                "eisenstein-multiply-negative",
                "eisenstein-multiply-one",
                "eisenstein-multiply-zero",
                "eisenstein-multiply-distribute-second",
                "eisenstein-multiply-negative-second",
                "eisenstein-add-cancel-left",
                "eisenstein-power-congruent",
                "eisenstein-power-three-as-cube",
            ],
        ),
        (
            "eisenstein-scalar-coordinate-sum-product.lim",
            &["eisenstein-scalar-coordinate-sum-product"],
        ),
        (
            "eisenstein-scalar-lambda-factor-omega.lim",
            &["eisenstein-scalar-lambda-factor-omega"],
        ),
        (
            "eisenstein-scalar-lambda-factor-real.lim",
            &["eisenstein-scalar-lambda-factor-real"],
        ),
        (
            "eisenstein-scalar-lambda-product-coordinate-sum.lim",
            &["eisenstein-scalar-lambda-product-coordinate-sum"],
        ),
        (
            "eisenstein-scalar-right-difference-cancel.lim",
            &["eisenstein-scalar-right-difference-cancel"],
        ),
    ];
    check_native_modules_without_foundations(modules);
}

fn ring_port_aliases(extra: &[(&'static str, &'static str)]) -> Vec<(&'static str, &'static str)> {
    let mut aliases = vec![
        ("integer", "integer-defs.lim"),
        ("integer-of-natural", "integer-defs.lim"),
        ("integer-add", "integer-defs.lim"),
        ("integer-multiply", "integer-defs.lim"),
        ("integer-equal", "integer-defs.lim"),
        ("integer-negate", "integer-defs.lim"),
        ("integer-divides", "integer-defs.lim"),
        ("exists", "logic-exists.lim"),
        ("conjunction", "logical-connectives.lim"),
        ("conjunction-introduce", "logical-connectives.lim"),
        ("eisenstein", "eisenstein-defs.lim"),
        ("eisenstein-equal", "eisenstein-defs.lim"),
        ("eisenstein-multiply", "eisenstein-defs.lim"),
        ("eisenstein-power", "eisenstein-defs.lim"),
        ("eisenstein-one", "eisenstein-defs.lim"),
        ("eisenstein-lambda", "eisenstein-defs.lim"),
        ("eisenstein-omega", "eisenstein-defs.lim"),
        ("eisenstein-divides", "eisenstein-defs.lim"),
    ];
    aliases.extend_from_slice(extra);
    aliases
}

fn expect_ring_port_fixture(aliases: &[(&str, &str)], statement: &str, proof: &str, valid: bool) {
    let scratch = support::Scratch::new("eisenstein-ring-port");
    let path = scratch.path().join("probe.lim");
    let mut source = String::new();
    for (name, file) in aliases {
        source.push_str(&format!(
            "(#alias {name} = {}::{name})\n",
            module(file).display()
        ));
    }
    source.push_str(&format!("(#theorem observed-result (#universes) (#parameters) (#statement {statement}) (#proof {proof}))"));
    fs::write(&path, &source).unwrap();
    lim::parse_program_from_path(&source, &path).expect("fixture remains valid source");
    let result = check_theorem_details_from_path_with_config(
        &source,
        &path,
        &CompileConfig::default(),
        "observed-result",
    );
    if valid {
        assert!(result
            .unwrap_or_else(|why| panic!("{}", why.message))
            .foundations
            .is_empty());
    } else {
        let why = result.unwrap_err();
        assert_eq!(why.code, DiagnosticCode::Proof);
        assert!(why.message.contains("mismatch"), "{}", why.message);
    }
}

type RingInteger = (usize, usize);
type RingPair = (RingInteger, RingInteger);
fn ring_pair_term(p: RingPair) -> String {
    eisenstein_pair(p.0, p.1)
}
fn ring_integer_add(a: RingInteger, b: RingInteger) -> RingInteger {
    (a.0 + b.0, a.1 + b.1)
}
fn ring_integer_neg(a: RingInteger) -> RingInteger {
    (a.1, a.0)
}
fn ring_integer_mul(a: RingInteger, b: RingInteger) -> RingInteger {
    (a.0 * b.0 + a.1 * b.1, a.0 * b.1 + a.1 * b.0)
}
fn ring_pair_mul(a: RingPair, b: RingPair) -> RingPair {
    let bd = ring_integer_neg(ring_integer_mul(a.1, b.1));
    (
        ring_integer_add(ring_integer_mul(a.0, b.0), bd),
        ring_integer_add(
            ring_integer_add(ring_integer_mul(a.0, b.1), ring_integer_mul(a.1, b.0)),
            bd,
        ),
    )
}
fn ring_pair_equality(left: &str, right: &str, a: RingPair, b: RingPair) -> String {
    let field = |index, x: &str| format!("(#pt-project eisenstein {index} {x})");
    proof_call(
        "conjunction-introduce",
        [
            integer_equivalent(field(0, left), field(0, right)),
            integer_equivalent(field(1, left), field(1, right)),
            reflexivity(a.0 .0 + b.0 .1),
            reflexivity(a.1 .0 + b.1 .1),
        ],
    )
}
fn ring_lambda_factor(dividend: &str, value: RingPair, factor: RingPair) -> String {
    let lambda = "(#pt-use eisenstein-lambda ())".to_owned();
    let factor_term = ring_pair_term(factor);
    let product = proof_call("eisenstein-multiply", [lambda.clone(), factor_term.clone()]);
    let actual = ring_pair_mul(((0, 1), (1, 0)), factor);
    let equation = ring_pair_equality(dividend, &product, value, actual);
    let predicate = format!(
        "(#pt-lambda ((candidate-factor (#pt-use eisenstein ()))) {})",
        proof_call(
            "eisenstein-equal",
            [
                dividend.to_owned(),
                proof_call(
                    "eisenstein-multiply",
                    [lambda, "candidate-factor".to_owned()]
                )
            ]
        )
    );
    format!("(#pt-construct exists (0) ((#pt-use eisenstein ()) {predicate}) introduce ({factor_term} {equation}))")
}

#[test]
fn eisenstein_ring_port_lambda_coordinate_criterion_constructs_real_factors() {
    let aliases = ring_port_aliases(&[
        ("eisenstein-coordinate-sum", "eisenstein-lambda-prime.lim"),
        (
            "eisenstein-lambda-divides-of-coordinate-sum",
            "eisenstein-lambda-prime.lim",
        ),
        (
            "integer-three-divides-coordinate-sum",
            "eisenstein-lambda-prime.lim",
        ),
    ]);
    for (value, k, factor, valid) in [
        (((0, 1), (1, 0)), (0, 0), ((1, 0), (0, 0)), true),
        (((2, 0), (1, 0)), (1, 0), ((0, 1), (0, 1)), true),
        (((1, 0), (2, 0)), (1, 0), ((0, 0), (0, 1)), true),
        (((1, 0), (0, 1)), (0, 0), ((0, 1), (0, 0)), true),
        (((3, 1), (2, 1)), (1, 0), ((0, 1), (0, 1)), true),
        (((1, 0), (0, 0)), (0, 0), ((0, 0), (0, 0)), false),
        (((0, 0), (1, 0)), (0, 0), ((0, 0), (0, 0)), false),
    ] {
        let n = ring_pair_term(value);
        let sigma = proof_call("eisenstein-coordinate-sum", [n.clone()]);
        let sum = ring_integer_add(value.0, value.1);
        let source = explicit_signed_factor(3, sigma.clone(), sum, k);
        let target = proof_call(
            "eisenstein-divides",
            ["(#pt-use eisenstein-lambda ())".to_owned(), n.clone()],
        );
        let proof = proof_call(
            "eisenstein-lambda-divides-of-coordinate-sum",
            [n.clone(), source],
        );
        expect_ring_port_fixture(&aliases, &target, &proof, valid);
        let target = proof_call("integer-divides", [integer_pair(3, 0), sigma]);
        let proof = proof_call(
            "integer-three-divides-coordinate-sum",
            [n.clone(), ring_lambda_factor(&n, value, factor)],
        );
        expect_ring_port_fixture(&aliases, &target, &proof, valid);
    }
}

#[test]
fn eisenstein_ring_port_power_divisibility_includes_zero_exponent_control() {
    let aliases = ring_port_aliases(&[(
        "eisenstein-lambda-divides-power",
        "eisenstein-lambda-prime.lim",
    )]);
    let lambda = "(#pt-use eisenstein-lambda ())".to_owned();
    let lambda_value = ((0, 1), (1, 0));
    for (exponent, factor, valid) in [
        (1, ((1, 0), (0, 0)), true),
        (2, lambda_value, true),
        (0, ((0, 0), (0, 0)), false),
    ] {
        let power = proof_call("eisenstein-power", [lambda.clone(), numeral(exponent)]);
        let value = (0..exponent).fold(((1, 0), (0, 0)), |acc, _| ring_pair_mul(lambda_value, acc));
        let source = ring_lambda_factor(&power, value, factor);
        let proof = proof_call(
            "eisenstein-lambda-divides-power",
            [lambda.clone(), numeral(exponent), source],
        );
        expect_ring_port_fixture(
            &aliases,
            &proof_call("eisenstein-divides", [lambda.clone(), lambda.clone()]),
            &proof,
            valid,
        );
    }
}

#[test]
fn eisenstein_ring_port_ring_and_prime_proofs_compose_at_default_budgets() {
    let aliases = ring_port_aliases(&[
        ("eisenstein-prime", "eisenstein-lambda-prime.lim"),
        ("eisenstein-lambda-prime", "eisenstein-lambda-prime.lim"),
        ("eisenstein-multiply-commutative", "eisenstein-ring.lim"),
    ]);
    let lambda = "(#pt-use eisenstein-lambda ())".to_owned();
    let omega = "(#pt-use eisenstein-omega ())".to_owned();
    let prime = proof_call("eisenstein-prime", [lambda.clone()]);
    let eq = proof_call(
        "eisenstein-equal",
        [
            proof_call("eisenstein-multiply", [lambda.clone(), omega.clone()]),
            proof_call("eisenstein-multiply", [omega.clone(), lambda.clone()]),
        ],
    );
    let proof = proof_call(
        "conjunction-introduce",
        [
            prime.clone(),
            eq.clone(),
            "(#pt-use eisenstein-lambda-prime ())".to_owned(),
            proof_call("eisenstein-multiply-commutative", [lambda, omega]),
        ],
    );
    expect_ring_port_fixture(
        &aliases,
        &proof_call("conjunction", [prime, eq]),
        &proof,
        true,
    );
}

#[test]
fn eisenstein_ring_port_false_identities_and_nonunits_are_rejected() {
    let iadd = |a: String, b: String| proof_call("integer-add", [a, b]);
    let imul = |a: &str, b: &str| proof_call("integer-multiply", [a.to_owned(), b.to_owned()]);
    let minus_bd = proof_call("integer-negate", [imul("first-omega", "second-omega")]);
    let coordinate_sum = iadd(
        iadd(imul("first-real", "second-real"), minus_bd.clone()),
        iadd(
            iadd(
                imul("first-real", "second-omega"),
                imul("first-omega", "second-real"),
            ),
            minus_bd,
        ),
    );
    let wrong_product = proof_call(
        "integer-multiply",
        [
            iadd("first-real".to_owned(), "first-omega".to_owned()),
            iadd("second-real".to_owned(), "second-omega".to_owned()),
        ],
    );
    // The coordinate sum preserves multiplication only modulo three.
    // Removing the -3*b*d term must fail in the generated scalar proof too.
    let path = module("eisenstein-scalar-coordinate-sum-product.lim");
    let source = fs::read_to_string(&path).unwrap();
    let declaration = source
        .find("(#theorem eisenstein-scalar-coordinate-sum-product")
        .unwrap();
    let start = declaration + source[declaration..].find("(#statement").unwrap();
    let end = end_of_form(&source, start);
    let statement = format!(
        "(#statement {})",
        integer_equivalent(coordinate_sum, wrong_product)
    );
    let changed = format!("{}{}{}", &source[..start], statement, &source[end..]);
    lim::parse_program_from_path(&changed, &path).expect("changed identity remains valid syntax");
    let why = check_theorem_details_from_path_with_config(
        &changed,
        &path,
        &CompileConfig::default(),
        "eisenstein-scalar-coordinate-sum-product",
    )
    .unwrap_err();
    assert_eq!(why.code, DiagnosticCode::Proof);
    assert!(why.message.contains("mismatch"), "{}", why.message);
    let wrong = proof_call(
        "eisenstein-equal",
        [
            proof_call(
                "eisenstein-multiply",
                [
                    proof_call(
                        "eisenstein-multiply",
                        ["first".to_owned(), "second".to_owned()],
                    ),
                    "third".to_owned(),
                ],
            ),
            proof_call(
                "eisenstein-multiply",
                [
                    "first".to_owned(),
                    proof_call("eisenstein-add", ["second".to_owned(), "third".to_owned()]),
                ],
            ),
        ],
    );
    reject_changed_statement(
        "eisenstein-ring.lim",
        "eisenstein-multiply-associative",
        &format!("(#statement {wrong})"),
    );
    reject_changed_statement(
        "eisenstein-lambda-prime.lim",
        "eisenstein-lambda-prime",
        "(#statement (#pt-app (#pt-use eisenstein-unit ()) (#pt-use eisenstein-lambda ())))",
    );
}

#[test]
fn eisenstein_ring_port_cli_roots_need_no_external_proof_tools() {
    for (file, target) in [
        ("eisenstein-ring.lim", "eisenstein-multiply-associative"),
        ("eisenstein-lambda-prime.lim", "eisenstein-lambda-prime"),
    ] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_lim"));
        command
            .env("PATH", "")
            .args(["--check-theorem", module(file).to_str().unwrap(), target]);
        let (status, stdout, stderr) =
            support::run(&mut command, Duration::from_secs(30), 1024 * 1024).unwrap();
        assert!(status.success(), "{}", String::from_utf8_lossy(&stderr));
        assert_eq!(stdout, format!("checked theorem {target}\n").as_bytes());
        assert!(stderr.is_empty());
    }
}

fn norm_port_aliases(extra: &[(&'static str, &'static str)]) -> Vec<(&'static str, &'static str)> {
    let mut aliases = vec![
        ("eisenstein-norm", "eisenstein-norm-defs.lim"),
        ("eisenstein-conjugate", "eisenstein-norm-defs.lim"),
        ("eisenstein-natural-norm", "eisenstein-norm-defs.lim"),
        ("eisenstein-zero", "eisenstein-defs.lim"),
    ];
    aliases.extend_from_slice(extra);
    ring_port_aliases(&aliases)
}
fn ring_norm_value(value: RingPair) -> RingInteger {
    ring_integer_add(
        ring_integer_add(
            ring_integer_mul(value.0, value.0),
            ring_integer_neg(ring_integer_mul(value.0, value.1)),
        ),
        ring_integer_mul(value.1, value.1),
    )
}
fn natural_norm_certificate(value: RingPair) -> String {
    reflexivity(ring_norm_value(value).0)
}
fn nonnegative_integer_witness(value: &str, n: usize, positive_component: usize) -> String {
    let predicate = format!(
        "(#pt-lambda ((candidate-natural #pt-nat)) {})",
        integer_equivalent(
            value.to_owned(),
            proof_call("integer-of-natural", ["candidate-natural".to_owned()])
        )
    );
    format!(
        "(#pt-construct exists (0) (#pt-nat {predicate}) introduce ({} {}))",
        numeral(n),
        reflexivity(positive_component)
    )
}
fn ring_nonzero_component(value: RingPair, component: usize) -> String {
    let selected = if component == 0 { value.0 } else { value.1 };
    assert!(selected.0 > 0 && selected.1 == 0);
    ring_nonzero_component_claim(value, component, selected.0)
}
fn ring_nonzero_component_claim(
    value: RingPair,
    component: usize,
    claimed_positive: usize,
) -> String {
    let term = ring_pair_term(value);
    let zero = "(#pt-use eisenstein-zero ())".to_owned();
    let field = |index| format!("(#pt-project eisenstein {index} {term})");
    let r = integer_equivalent(field(0), integer_pair(0, 0));
    let i = integer_equivalent(field(1), integer_pair(0, 0));
    let projected = proof_call(
        if component == 0 {
            "conjunction-left"
        } else {
            "conjunction-right"
        },
        [r, i, "zero-proof".to_owned()],
    );
    let contradiction = format!(
        "(#pt-app {} {projected})",
        proof_call("successor-not-zero", [numeral(claimed_positive - 1)])
    );
    format!(
        "(#pt-lambda ((zero-proof {})) {contradiction})",
        proof_call("eisenstein-equal", [term, zero])
    )
}

#[test]
fn norm_port_certificates_cover_signs_noncanonical_values_and_zero() {
    let aliases = norm_port_aliases(&[(
        "eisenstein-norm-zero-implies-zero",
        "eisenstein-norm-nondegenerate.lim",
    )]);
    for (value, expected) in [
        (((0, 0), (0, 0)), 0),
        (((1, 0), (0, 0)), 1),
        (((0, 0), (1, 0)), 1),
        (((1, 0), (1, 0)), 1),
        (((0, 1), (1, 0)), 3),
        (((2, 0), (1, 0)), 3),
        (((3, 1), (2, 1)), 3),
        (((0, 1), (0, 1)), 1),
        (((2, 2), (1, 1)), 0),
    ] {
        let n = ring_pair_term(value);
        let proof = natural_norm_certificate(value);
        expect_ring_port_fixture(
            &aliases,
            &proof_call("eisenstein-natural-norm", [n.clone(), numeral(expected)]),
            &proof,
            true,
        );
        expect_ring_port_fixture(
            &aliases,
            &proof_call(
                "eisenstein-natural-norm",
                [n.clone(), numeral(expected + 1)],
            ),
            &proof,
            false,
        );
        if expected == 0 {
            let proof = proof_call(
                "eisenstein-norm-zero-implies-zero",
                [n.clone(), natural_norm_certificate(value)],
            );
            expect_ring_port_fixture(
                &aliases,
                &proof_call(
                    "eisenstein-equal",
                    [n, "(#pt-use eisenstein-zero ())".to_owned()],
                ),
                &proof,
                true,
            );
        }
    }
    let value = ((1, 0), (0, 0));
    let n = ring_pair_term(value);
    expect_ring_port_fixture(
        &aliases,
        &proof_call(
            "eisenstein-equal",
            [n.clone(), "(#pt-use eisenstein-zero ())".to_owned()],
        ),
        &proof_call(
            "eisenstein-norm-zero-implies-zero",
            [n, natural_norm_certificate(value)],
        ),
        false,
    );
}

#[test]
fn norm_port_nonnegative_reflection_requires_a_nonzero_scale() {
    let aliases = norm_port_aliases(&[
        ("integer-nonnegative", "integer-nonnegative.lim"),
        (
            "integer-nonnegative-scale-reflect",
            "integer-nonnegative.lim",
        ),
        ("integer-square-nonnegative", "integer-nonnegative.lim"),
        ("successor-not-zero", "natural-nonzero.lim"),
    ]);
    for (value, n, valid) in [((2, 2), 0, true), ((0, 1), 0, false)] {
        let x = integer_pair(value.0, value.1);
        expect_ring_port_fixture(
            &aliases,
            &proof_call("integer-nonnegative", [x.clone()]),
            &nonnegative_integer_witness(&x, n, value.0),
            valid,
        );
    }
    for (scale, value, witness, valid) in [
        (4, (2, 1), 4, true),
        (4, (0, 0), 0, true),
        (0, (0, 1), 0, false),
    ] {
        let x = integer_pair(value.0, value.1);
        let product = proof_call("integer-multiply", [integer_pair(scale, 0), x.clone()]);
        let nonnegative = nonnegative_integer_witness(&product, witness, scale * value.0);
        let positive = proof_call(
            "successor-not-zero",
            [numeral(if scale == 0 { 0 } else { scale - 1 })],
        );
        let proof = proof_call(
            "integer-nonnegative-scale-reflect",
            [numeral(scale), x.clone(), positive, nonnegative],
        );
        expect_ring_port_fixture(
            &aliases,
            &proof_call("integer-nonnegative", [x]),
            &proof,
            valid,
        );
    }
}

#[test]
fn norm_port_multiplicative_cancellation_preserves_equivalence_and_checks_zero() {
    let aliases = norm_port_aliases(&[
        ("eisenstein-multiply-cancel-first", "eisenstein-domain.lim"),
        ("conjunction-left", "logical-connectives.lim"),
        ("conjunction-right", "logical-connectives.lim"),
        ("successor-not-zero", "natural-nonzero.lim"),
    ]);
    for (factor, which, a, b, valid) in [
        (
            ((1, 0), (1, 0)),
            0,
            ((3, 1), (1, 0)),
            ((2, 0), (2, 1)),
            true,
        ),
        (
            ((0, 0), (1, 0)),
            1,
            ((1, 0), (0, 0)),
            ((2, 1), (0, 0)),
            true,
        ),
        (
            ((0, 0), (0, 0)),
            0,
            ((1, 0), (0, 0)),
            ((2, 0), (0, 0)),
            false,
        ),
        (
            ((1, 0), (1, 0)),
            0,
            ((1, 0), (0, 0)),
            ((2, 0), (0, 0)),
            false,
        ),
    ] {
        let f = ring_pair_term(factor);
        let x = ring_pair_term(a);
        let y = ring_pair_term(b);
        let left = proof_call("eisenstein-multiply", [f.clone(), x.clone()]);
        let right = proof_call("eisenstein-multiply", [f.clone(), y.clone()]);
        let equality = ring_pair_equality(
            &left,
            &right,
            ring_pair_mul(factor, a),
            ring_pair_mul(factor, b),
        );
        let nonzero = if factor == ((0, 0), (0, 0)) {
            ring_nonzero_component_claim(factor, which, 1)
        } else {
            ring_nonzero_component(factor, which)
        };
        let proof = proof_call(
            "eisenstein-multiply-cancel-first",
            [f, x.clone(), y.clone(), nonzero, equality],
        );
        expect_ring_port_fixture(
            &aliases,
            &proof_call("eisenstein-equal", [x, y]),
            &proof,
            valid,
        );
    }
}

#[test]
fn norm_port_extended_units_have_norm_one_and_conjugate_inverses() {
    let aliases = norm_port_aliases(&[
        ("eisenstein-unit", "eisenstein-defs.lim"),
        (
            "eisenstein-unit-natural-norm-one",
            "eisenstein-norm-unit.lim",
        ),
        (
            "eisenstein-unit-of-natural-norm-one",
            "eisenstein-norm-unit.lim",
        ),
    ]);
    for value in [
        ((1, 0), (0, 0)),
        ((0, 1), (0, 0)),
        ((0, 0), (1, 0)),
        ((0, 0), (0, 1)),
        ((1, 0), (1, 0)),
        ((0, 1), (0, 1)),
        ((2, 1), (0, 0)),
    ] {
        let x = ring_pair_term(value);
        let cert = natural_norm_certificate(value);
        let unit = proof_call(
            "eisenstein-unit-of-natural-norm-one",
            [x.clone(), cert.clone()],
        );
        expect_ring_port_fixture(
            &aliases,
            &proof_call("eisenstein-unit", [x.clone()]),
            &unit,
            true,
        );
        let proof = proof_call(
            "eisenstein-unit-natural-norm-one",
            [x, numeral(1), unit, cert],
        );
        expect_ring_port_fixture(
            &aliases,
            &natural_equation(&numeral(1), &numeral(1)),
            &proof,
            true,
        );
    }
    for value in [((0, 0), (0, 0)), ((2, 0), (0, 0)), ((0, 1), (1, 0))] {
        let x = ring_pair_term(value);
        let proof = proof_call(
            "eisenstein-unit-of-natural-norm-one",
            [x.clone(), natural_norm_certificate(value)],
        );
        expect_ring_port_fixture(&aliases, &proof_call("eisenstein-unit", [x]), &proof, false);
    }
}

#[test]
fn norm_port_extended_power_and_product_certificates_keep_exact_natural_values() {
    let aliases = norm_port_aliases(&[
        (
            "eisenstein-natural-norm-power",
            "eisenstein-natural-norm-properties.lim",
        ),
        (
            "eisenstein-natural-norm-multiply",
            "eisenstein-natural-norm-multiply.lim",
        ),
    ]);
    let lambda = ((0, 1), (1, 0));
    let l = ring_pair_term(lambda);
    for (exponent, expected) in [(0, 1), (1, 3), (2, 9), (3, 27)] {
        let power = proof_call("eisenstein-power", [l.clone(), numeral(exponent)]);
        let proof = proof_call(
            "eisenstein-natural-norm-power",
            [
                l.clone(),
                numeral(3),
                numeral(exponent),
                natural_norm_certificate(lambda),
            ],
        );
        expect_ring_port_fixture(
            &aliases,
            &proof_call(
                "eisenstein-natural-norm",
                [power.clone(), numeral(expected)],
            ),
            &proof,
            true,
        );
        expect_ring_port_fixture(
            &aliases,
            &proof_call("eisenstein-natural-norm", [power, numeral(expected + 1)]),
            &proof,
            false,
        );
    }
    let omega = ((0, 0), (1, 0));
    let w = ring_pair_term(omega);
    let proof = proof_call(
        "eisenstein-natural-norm-multiply",
        [
            l.clone(),
            w.clone(),
            numeral(3),
            numeral(1),
            natural_norm_certificate(lambda),
            natural_norm_certificate(omega),
        ],
    );
    let product = proof_call("eisenstein-multiply", [l, w]);
    expect_ring_port_fixture(
        &aliases,
        &proof_call("eisenstein-natural-norm", [product, numeral(3)]),
        &proof,
        true,
    );
}

#[test]
fn norm_port_false_square_identities_and_unit_norm_claims_are_rejected() {
    let two = integer_pair(2, 0);
    let three = integer_pair(3, 0);
    let x = "number".to_owned();
    let r = format!("(#pt-project eisenstein 0 {x})");
    let i = format!("(#pt-project eisenstein 1 {x})");
    let d = proof_call(
        "integer-add",
        [
            proof_call("integer-multiply", [two, r]),
            proof_call("integer-negate", [i.clone()]),
        ],
    );
    let rhs = proof_call(
        "integer-add",
        [
            proof_call("integer-multiply", [d.clone(), d]),
            proof_call(
                "integer-multiply",
                [three, proof_call("integer-multiply", [i.clone(), i])],
            ),
        ],
    );
    let wrong = integer_equivalent(proof_call("eisenstein-norm", [x]), rhs);
    reject_changed_statement(
        "eisenstein-norm-squares.lim",
        "eisenstein-norm-four-squares",
        &format!("(#statement {wrong})"),
    );
    reject_changed_statement(
        "eisenstein-norm-nondegenerate.lim",
        "eisenstein-norm-zero-implies-zero",
        "(#statement (#pt-app (#pt-use eisenstein-equal ()) number (#pt-use eisenstein-one ())))",
    );
    reject_changed_statement(
        "eisenstein-norm-unit.lim",
        "eisenstein-unit-natural-norm-one",
        "(#statement (#pt-eq #pt-nat natural-norm (#pt-numeral 2)))",
    );
}

#[test]
fn norm_port_extended_cli_roots_check_without_external_proof_tools() {
    for (file, target) in [
        ("eisenstein-domain.lim", "eisenstein-multiply-cancel-first"),
        (
            "eisenstein-norm-nonnegative.lim",
            "eisenstein-natural-norm-exists",
        ),
        (
            "eisenstein-norm-unit.lim",
            "eisenstein-unit-natural-norm-one",
        ),
    ] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_lim"));
        command
            .env("PATH", "")
            .args(["--check-theorem", module(file).to_str().unwrap(), target]);
        let (status, stdout, stderr) =
            support::run(&mut command, Duration::from_secs(30), 1024 * 1024).unwrap();
        assert!(status.success(), "{}", String::from_utf8_lossy(&stderr));
        assert_eq!(stdout, format!("checked theorem {target}\n").as_bytes());
        assert!(stderr.is_empty());
    }
}

#[test]
fn lambda_multiplicity_port_norm_divisibility_handles_zero_and_rejects_wrong_norms() {
    let aliases = norm_port_aliases(&[
        ("divides", "natural-divisibility-defs.lim"),
        ("eisenstein-reflexive", "eisenstein-equality.lim"),
        (
            "eisenstein-natural-norm-divides",
            "eisenstein-norm-divisibility.lim",
        ),
    ]);
    let zero = ((0, 0), (0, 0));
    let one = ((1, 0), (0, 0));
    let lambda = ((0, 1), (1, 0));
    let omega = ((0, 0), (1, 0));
    for (divisor, factor, claimed_norm, valid) in [
        (zero, one, 0, true),
        (one, zero, 1, true),
        (lambda, omega, 3, true),
        (lambda, omega, 1, false),
    ] {
        let d = ring_pair_term(divisor);
        let q = ring_pair_term(factor);
        let x = proof_call("eisenstein-multiply", [d.clone(), q.clone()]);
        let predicate = format!(
            "(#pt-lambda ((candidate-factor (#pt-use eisenstein ()))) {})",
            proof_call(
                "eisenstein-equal",
                [
                    x.clone(),
                    proof_call(
                        "eisenstein-multiply",
                        [d.clone(), "candidate-factor".to_owned()]
                    )
                ]
            )
        );
        let equality = proof_call("eisenstein-reflexive", [x.clone()]);
        let division = format!("(#pt-construct exists (0) ((#pt-use eisenstein ()) {predicate}) introduce ({q} {equality}))");
        let value = ring_pair_mul(divisor, factor);
        let norm = ring_norm_value(value);
        let proof = proof_call(
            "eisenstein-natural-norm-divides",
            [
                d,
                x,
                numeral(claimed_norm),
                numeral(norm.0 - norm.1),
                natural_norm_certificate(divisor),
                natural_norm_certificate(value),
                division,
            ],
        );
        expect_ring_port_fixture(
            &aliases,
            &proof_call("divides", [numeral(claimed_norm), numeral(norm.0 - norm.1)]),
            &proof,
            valid,
        );
    }
}

#[test]
fn lambda_multiplicity_port_bound_and_existence_require_a_real_nonzero_value() {
    let aliases = norm_port_aliases(&[
        ("successor-not-zero", "natural-nonzero.lim"),
        ("conjunction-left", "logical-connectives.lim"),
        ("conjunction-right", "logical-connectives.lim"),
        (
            "eisenstein-lambda-power-norm-bound",
            "eisenstein-lambda-multiplicity.lim",
        ),
        (
            "eisenstein-lambda-finite-multiplicity",
            "eisenstein-lambda-multiplicity.lim",
        ),
    ]);
    for (value, component, claimed_norm, valid) in [
        (((1, 0), (0, 0)), 0, 1, true),
        (((0, 1), (1, 0)), 1, 3, true),
        (((0, 1), (1, 0)), 1, 1, false),
        (((0, 0), (0, 0)), 0, 0, false),
    ] {
        let x = ring_pair_term(value);
        let nonzero = if valid || claimed_norm == 1 {
            ring_nonzero_component(value, component)
        } else {
            ring_nonzero_component_claim(value, component, 1)
        };
        let power = proof_call(
            "eisenstein-power",
            [
                "(#pt-use eisenstein-lambda ())".to_owned(),
                numeral(claimed_norm),
            ],
        );
        let no_division = format!(
            "(#pt-pi ((power-divides {})) #pt-false)",
            proof_call("eisenstein-divides", [power, x.clone()])
        );
        let proof = proof_call(
            "eisenstein-lambda-power-norm-bound",
            [
                x.clone(),
                numeral(claimed_norm),
                natural_norm_certificate(value),
                nonzero.clone(),
            ],
        );
        expect_ring_port_fixture(&aliases, &no_division, &proof, valid);
        if claimed_norm == 1 && !valid {
            continue;
        }
        let predicate = format!(
            "(#pt-lambda ((candidate-bound #pt-nat)) (#pt-pi ((power-divides {})) #pt-false))",
            proof_call(
                "eisenstein-divides",
                [
                    proof_call(
                        "eisenstein-power",
                        [
                            "(#pt-use eisenstein-lambda ())".to_owned(),
                            "candidate-bound".to_owned()
                        ]
                    ),
                    x.clone()
                ]
            )
        );
        let statement = format!("(#pt-app (#pt-use exists (0)) #pt-nat {predicate})");
        let proof = proof_call("eisenstein-lambda-finite-multiplicity", [x, nonzero]);
        expect_ring_port_fixture(&aliases, &statement, &proof, valid);
    }
}

#[test]
fn lambda_multiplicity_port_rejects_zero_growth_and_an_off_by_one_bound() {
    let aliases = ring_port_aliases(&[
        ("less-than", "natural-order.lim"),
        ("power", "../fermat_statement.lim"),
        ("exponent-below-three-power", "natural-power-growth.lim"),
    ]);
    for exponent in 0usize..4 {
        let proof = proof_call("exponent-below-three-power", [numeral(exponent)]);
        let upper = proof_call("power", [numeral(3), numeral(exponent)]);
        expect_ring_port_fixture(
            &aliases,
            &proof_call("less-than", [numeral(exponent), upper]),
            &proof,
            true,
        );
    }
    expect_ring_port_fixture(
        &aliases,
        &proof_call("less-than", [numeral(0), numeral(0)]),
        &proof_call("exponent-below-three-power", [numeral(0)]),
        false,
    );
    reject_changed_statement("eisenstein-lambda-multiplicity.lim", "eisenstein-lambda-power-norm-bound", "(#statement (#pt-pi ((power-divides (#pt-app (#pt-use eisenstein-divides ()) (#pt-app (#pt-use eisenstein-power ()) (#pt-use eisenstein-lambda ()) #pt-zero) number))) #pt-false))");
}
