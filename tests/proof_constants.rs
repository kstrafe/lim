mod support;

use lim::{CompileConfig, DiagnosticCode};
use std::{fs, path::Path, process::Command, time::Duration};

fn check(source: &str) -> Result<(), String> {
    let program = lim::parse_program(source)?;
    lim::check_types(&program)
}

fn proves(source: &str) {
    check(source).unwrap_or_else(|error| panic!("{error}\n{source}"));
}

const CONSTANTS: &str = r#"
      (#struct Point () (: x #u8 : y #u8))
      (#enum Choice () (: Choice.None : Choice.Some #u8))
      (#let scalar #u8 7u8)
      (#let values (#array #u8 2) (#array-of (#array #u8 2) 3u8 5u8))
      (#let pair (#tuple #u8 #u8) (#tuple (#tuple #u8 #u8) 11u8 13u8))
      (#let point Point (#struct-literal Point (: x 17u8 : y 19u8)))
      (#let choice Choice (#enum-literal Choice.Some 23u8))
      (#let scalar-copy #u8 (#u8::add-wrap scalar 1u8))
      (#theorem constants
        (#proof-and
          (#proof-eq scalar-copy 8u8)
          (#proof-eq (#index values 1usize) 5u8)
          (#proof-eq (#get pair 0) 11u8)
          (#proof-eq (#get point y) 19u8)
          (#proof-eq choice (#enum-literal Choice.Some 23u8))))
    "#;

#[test]
fn checked_global_initializers_are_symbolic_values() {
    proves(CONSTANTS);
}

#[test]
fn checked_constants_match_native_execution() {
    let scratch = support::Scratch::new("proof-constants-native");
    let source = scratch.path().join("main.lim");
    let binary = scratch.path().join("main");
    fs::write(
        &source,
        format!(
            r#"{CONSTANTS}
      (#fn main () #u64
        (#return (#as (#u8::add-wrap scalar
          (#u8::add-wrap (#get point y)
            (#u8::add-wrap (#get pair 1) (#index values 0usize)))) #u64)))"#
        ),
    )
    .unwrap();
    let (status, _, stderr) = support::run(
        Command::new(env!("CARGO_BIN_EXE_lim"))
            .arg(&source)
            .arg("-o")
            .arg(&binary)
            .env("PATH", ""),
        Duration::from_secs(20),
        1024 * 1024,
    )
    .unwrap();
    assert!(status.success(), "{}", String::from_utf8_lossy(&stderr));
    let (status, _, stderr) = support::run(
        Command::new(&binary).env("PATH", ""),
        Duration::from_secs(5),
        1024 * 1024,
    )
    .unwrap();
    assert_eq!(
        status.code(),
        Some(42),
        "{}",
        String::from_utf8_lossy(&stderr)
    );
}

#[test]
fn user_written_proof_literals_still_require_typed_primitives() {
    let error = check("(#let initialized #u8 1u8) (#theorem invalid (#proof-and (#proof-eq initialized 1u8) (#proof-eq (#literal u8 1) 1u8)))")
        .expect_err("unprefixed numeric literals are invalid in proof syntax");
    assert!(error.contains("must use its '#' prefix"), "{error}");
}

#[test]
fn specification_cannot_mutate_globals() {
    let error = check(
        r#"
      (#let initialized #u8 1u8)
      (#theorem mutation (#proof-for-all (: value (#ref-mut #u8))
        (#proof-and (#proof-eq initialized 1u8)
          (#proof-eq (#deref-set value 2u8) ()))))
    "#,
    )
    .expect_err("proof specification must reject writes");
    assert!(
        error.contains("specifications cannot write through references"),
        "{error}"
    );
}

#[test]
fn imported_private_constant_representation_is_usable_through_facade() {
    let scratch = crate::support::Scratch::new("proof-constants");
    let library = scratch.path().join("library");
    fs::create_dir(&library).unwrap();
    fs::write(
        library.join("impl.lim"),
        r#"
      (#struct Hidden () (: value #u8))
      (#const private-value Hidden (#struct-literal Hidden (: value 31u8)))
      (#fn read () #u8 (#return (#get private-value value)))
    "#,
    )
    .unwrap();
    fs::write(
        library.join("lib.lim"),
        r#"
      (#std)
      (#alias read = ./impl.lim::read)
      (#export read)
    "#,
    )
    .unwrap();
    let source = r#"
      (#std)
      (#alias imported-read = ./library/lib.lim::read)
      (#theorem imported (#proof-contract imported-read true
        (#proof-eq (#proof-result) 31u8)))
    "#;
    let path = scratch.path().join("main.lim");
    let result = lim::check_theorem_details_from_path_with_config(
        source,
        &path,
        &CompileConfig::default(),
        "imported",
    );
    result.unwrap_or_else(|error| panic!("{}", error.message));
}

#[test]
fn invalid_proof_reports_proof_diagnostic() {
    let error = lim::check_theorem_details_from_path_with_config(
        "(#theorem invalid (#proof-eq 1 1))",
        Path::new("proof_constants.lim"),
        &CompileConfig::default(),
        "invalid",
    )
    .expect_err("invalid proof source must fail");
    assert_eq!(error.code, DiagnosticCode::ProofInvalid);
}
