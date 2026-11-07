//! Local mathematical observations of the pinned native string definitions.
//!
//! These theorems are appended to the checked native source. They are not a
//! Lean export and do not change the upstream string producer.
use lim::{CompileConfig, ProofBudget};
use std::path::Path;

const NATIVE: &str = include_str!("../theorems/lean_replay/strings.lim");

fn config() -> CompileConfig {
    let mut config = CompileConfig::default();
    config.set_proof_budget(ProofBudget::new(1_000_000, 128 << 20, 1 << 30).unwrap());
    config
}

fn observation(name: &str, expr: &str, expected: u32) -> String {
    format!(
        "(#theorem {name}\n  (#universes)\n  (#parameters)\n  (#statement (#pt-eq (#pt-use lean-10-Nat ()) {expr} (#pt-nat-literal lean-10-Nat \"{expected}\")))\n  (#proof (#pt-refl (#pt-use lean-10-Nat ()) (#pt-nat-literal lean-10-Nat \"{expected}\"))))\n"
    )
}

fn char_value_observation(name: &str, scalar: u32, expected: u32) -> String {
    let value = format!(
        "(#pt-app (#pt-use lean-93-UInt32-toNat ()) (#pt-app (#pt-use lean-128-Char-val ()) (#pt-app (#pt-use lean-372-Char-ofNat ()) (#pt-nat-literal lean-10-Nat \"{scalar}\"))))"
    );
    observation(name, &value, expected)
}

fn char(scalar: u32) -> String {
    format!("(#pt-app (#pt-use lean-372-Char-ofNat ()) (#pt-nat-literal lean-10-Nat \"{scalar}\"))")
}

fn chars(values: &[u32]) -> String {
    values.iter().rev().fold(
        "(#pt-app (#pt-use lean-4-List-nil (0)) (#pt-use lean-95-Char ()))".to_owned(),
        |tail, scalar| {
            format!(
                "(#pt-app (#pt-app (#pt-app (#pt-use lean-5-List-cons (0)) (#pt-use lean-95-Char ())) {}) {})",
                char(*scalar), tail
            )
        },
    )
}

fn utf8_byte_length(name: &str, text: &str) -> String {
    let scalars = text.chars().map(u32::from).collect::<Vec<_>>();
    let expected = u32::try_from(text.len()).unwrap();
    let string = format!(
        "(#pt-app (#pt-use lean-346-String-ofList ()) {})",
        chars(&scalars)
    );
    let bytes = format!(
        "(#pt-project lean-7-Array 0 (#pt-project lean-75-ByteArray 0 (#pt-project lean-342-String 0 {string})))"
    );
    let list_type = "(#pt-app (#pt-use lean-3-List (0)) (#pt-use lean-72-UInt8 ()))";
    let nil = "(#pt-nat-literal lean-10-Nat \"0\")";
    let cons = "(#pt-lambda ((obs-head (#pt-use lean-72-UInt8 ())) (obs-tail (#pt-app (#pt-use lean-3-List (0)) (#pt-use lean-72-UInt8 ()))) (obs-count (#pt-use lean-10-Nat ()))) (#pt-app (#pt-use lean-12-Nat-succ ()) obs-count))";
    let count = format!(
        "(#pt-induct lean-3-List (0) ((#pt-use lean-72-UInt8 ())) (#pt-lambda ((obs-items {list_type})) (#pt-use lean-10-Nat ())) ({nil} {cons}) {bytes})"
    );
    observation(name, &count, expected)
}

fn appended(theorems: &[String]) -> String {
    let mut source = NATIVE.to_owned();
    source.push('\n');
    for theorem in theorems {
        source.push_str(theorem);
    }
    source
}

#[test]
fn char_uint32_nat_observations() {
    let theorems = [
        char_value_observation("obs-char-ascii", 65, 65),
        char_value_observation("obs-char-unicode", 233, 233),
        char_value_observation("obs-char-surrogate", 55296, 0),
    ];
    let source = appended(&theorems);
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("theorems/lean_replay/strings.lim");
    for name in ["obs-char-ascii", "obs-char-unicode", "obs-char-surrogate"] {
        let checked =
            lim::check_theorem_details_from_path_with_config(&source, &path, &config(), name)
                .unwrap();
        assert!(checked.foundations.is_empty());
    }
}

#[test]
fn string_utf8_byte_length_observations() {
    let theorems = [
        utf8_byte_length("obs-utf8-empty", ""),
        utf8_byte_length("obs-utf8-ascii", "A"),
        utf8_byte_length("obs-utf8-unicode-crab", "é🦀"),
        utf8_byte_length("obs-utf8-nul", "\0"),
    ];
    let source = appended(&theorems);
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("theorems/lean_replay/strings.lim");
    for name in [
        "obs-utf8-empty",
        "obs-utf8-ascii",
        "obs-utf8-unicode-crab",
        "obs-utf8-nul",
    ] {
        let checked =
            lim::check_theorem_details_from_path_with_config(&source, &path, &config(), name)
                .unwrap();
        assert!(checked.foundations.is_empty());
    }
}

#[test]
fn incorrect_scalar_observation_fails_after_valid_context() {
    let valid = char_value_observation("obs-valid-scalar-context", 65, 65);
    let invalid = char_value_observation("obs-invalid-scalar-observation", 65, 66);
    let valid_source = appended(std::slice::from_ref(&valid));
    let source = appended(&[valid, invalid]);
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("theorems/lean_replay/strings.lim");
    lim::check_theorem_details_from_path_with_config(
        &valid_source,
        &path,
        &config(),
        "obs-valid-scalar-context",
    )
    .unwrap();
    let failure = lim::check_theorem_details_from_path_with_config(
        &source,
        &path,
        &config(),
        "obs-invalid-scalar-observation",
    )
    .unwrap_err();
    assert!(
        failure.message.contains("type mismatch"),
        "{}",
        failure.message
    );
    assert!(
        !failure.message.contains("resource limit"),
        "{}",
        failure.message
    );
}

#[test]
fn a_constant_scalar_function_ignores_unequal_structured_inputs() {
    let a = format!(
        "(#pt-app (#pt-use lean-346-String-ofList ()) {})",
        chars(&[65])
    );
    let b = format!(
        "(#pt-app (#pt-use lean-346-String-ofList ()) {})",
        chars(&[66])
    );
    let function = "(#math-definition obs-constant-string ()
      (#pt-pi ((ignored-input (#pt-use lean-342-String ()))) (#pt-use lean-10-Nat ()))
      (#pt-lambda ((ignored-input (#pt-use lean-342-String ()))) (#pt-nat-literal lean-10-Nat \"0\")))";
    let left = format!("(#pt-app (#pt-use obs-constant-string ()) {a})");
    let right = format!("(#pt-app (#pt-use obs-constant-string ()) {b})");
    let theorem = format!(
        "(#theorem obs-constant-string-equality (#universes) (#parameters)
      (#statement (#pt-eq (#pt-use lean-10-Nat ()) {left} {right}))
      (#proof (#pt-refl (#pt-use lean-10-Nat ()) {left})))"
    );
    let source = appended(&[function.to_owned(), theorem]);
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("theorems/lean_replay/strings.lim");
    let checked = lim::check_theorem_details_from_path_with_config(
        &source,
        &path,
        &config(),
        "obs-constant-string-equality",
    )
    .unwrap();
    assert!(checked.foundations.is_empty());
}
