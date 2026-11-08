//! Regression coverage for mutable slice clearing invariants.

use lim::{CompileConfig, Diagnostic, ProofOutcome};
mod support;

fn check(source: &str, theorem: &str) -> Result<lim::CheckedTheorem, Diagnostic> {
    lim::check_theorem_details_from_path_with_config(
        source,
        std::path::Path::new("collection-invariants.lim"),
        &CompileConfig::default(),
        theorem,
    )
}

fn proved(source: &str, theorem: &str) {
    check(source, theorem).unwrap_or_else(|error| panic!("{}\n{source}", error.message));
}

fn induction_failure(source: &str, theorem: &str) {
    let error = check(source, theorem).expect_err("must fail closed");
    assert_eq!(
        error.proof_outcome(),
        Some(ProofOutcome::InductionFailure),
        "{}\n{source}",
        error.message
    );
}

fn program(length: usize, assignment: &str) -> String {
    let cells = (0..length)
        .map(|j| {
            format!(
                "(#proof-implies (#bool::and (#usize::le remaining {j}usize) (#usize::lt {j}usize (#slice-mut-len view))) (#proof-eq (#deref (#slice-mut-idx view {j}usize)) 0u8))"
            )
        })
        .collect::<Vec<_>>()
        .join(" ");
    let cleared = (0..length)
        .map(|j| format!("(#proof-implies (#bool::and (#usize::le start {j}usize) (#usize::lt {j}usize end)) (#proof-eq (#index source {j}usize) 0u8))"))
        .collect::<Vec<_>>()
        .join(" ");
    let preserved = (0..length)
        .map(|j| format!("(#proof-implies (#bool::or (#usize::lt {j}usize start) (#usize::le end {j}usize)) (#proof-eq (#index source {j}usize) (#proof-old (#index source {j}usize))))"))
        .collect::<Vec<_>>()
        .join(" ");
    format!(
        r#"
      (#fn worker (: view (#slice-mut #u8)) #usize
        (#let-mut remaining #usize (#slice-mut-len view))
        (#label again (#while (#usize::gt remaining 0usize)
          (#deref-set (#slice-mut-idx view (#usize::sub-wrap remaining 1usize)) {assignment})
          (#set remaining (#usize::sub-wrap remaining 1usize))))
        (#forget view) (#return remaining))
      (#fn run (: source (#ref-mut (#array #u8 {length})) : start #usize : end #usize) #usize
        (#let whole (#slice-mut #u8) (#slice-mut-of source))
        (#let view (#slice-mut #u8) (#slice-mut-range whole start end))
        (#let result #usize (#call worker (: view view)))
        (#forget whole) (#return result))
      (#theorem claim
        (#proof-loop-limit 1
          (#proof-with-invariants
            ((worker again (#proof-and (#usize::le remaining (#slice-mut-len view)) {cells}) remaining))
            (#proof-contract run (#bool::and (#usize::le start end) (#usize::le end {length}usize))
              (#proof-and (#proof-eq (#proof-result) 0usize) {cleared} {preserved})))))
    "#
    )
}

#[test]
fn bounded_arrays_prove_interior_zeroing_and_frame() {
    for length in 1..=3 {
        let source = program(length, "0u8");
        proved(&source, "claim");
    }
}

#[test]
fn wrong_value_assignment_is_induction_failure_under_negation() {
    let claim = program(3, "1u8");
    let negated = claim.replace("(#proof-contract run", "(#proof-not (#proof-contract run");
    let negated = format!("{negated})");
    induction_failure(&claim, "claim");
    induction_failure(&negated, "claim");
}

#[test]
fn missing_processed_cell_invariant_is_induction_failure_under_negation() {
    let source = program(3, "0u8");
    let source = source.replace(
        "(#proof-implies (#bool::and (#usize::le remaining 2usize) (#usize::lt 2usize (#slice-mut-len view))) (#proof-eq (#deref (#slice-mut-idx view 2usize)) 0u8))",
        "",
    );
    let negated = source.replace("(#proof-contract run", "(#proof-not (#proof-contract run");
    let negated = format!("{negated})");
    induction_failure(&source, "claim");
    induction_failure(&negated, "claim");
}

#[test]
fn repeated_sort_matches_native_for_every_byte_pair_and_representative_counts() {
    use std::{fs, process::Command, time::Duration};
    let scratch = support::Scratch::new("proof-collection-loop-native");
    let mut source = include_str!("../examples/proof_collection_loop.lim").to_owned();
    source.truncate(source.find("(#fn main ").unwrap());
    source.push_str(r#"
      (#fn main () #u64
        (#let counts (#array #u8 4) (#array-of (#array #u8 4) 0u8 1u8 2u8 255u8))
        (#let-mut left-index #u16 0u16)
        (#while (#u16::lt left-index 256u16)
          (#let left #u8 (#as left-index #u8))
          (#let-mut right-index #u16 0u16)
          (#while (#u16::lt right-index 256u16)
            (#let right #u8 (#as right-index #u8))
            (#let-mut count-index #usize 0usize)
            (#while (#usize::lt count-index 4usize)
              (#let count #u8 (#index counts count-index))
              (#let-mut pair (#array #u8 2) (#array-of (#array #u8 2) left right))
              (#call sort-pair-repeat (: values (#borrow-mut pair) : count count))
              (#let preserve #bool (#bool::or (#u8::eq count 0u8) (#u16::le left-index right-index)))
              (#let expected-first #u8 (#if preserve left right))
              (#let expected-second #u8 (#if preserve right left))
              (#if (#u8::ne (#index pair 0usize) expected-first) (#block (#return 1u64)))
              (#if (#u8::ne (#index pair 1usize) expected-second) (#block (#return 2u64)))
              (#set count-index (#usize::add-wrap count-index 1usize)))
            (#set right-index (#u16::add-wrap right-index 1u16)))
          (#set left-index (#u16::add-wrap left-index 1u16)))
        (#return 42u64))
    "#);
    let path = scratch.path().join("main.lim");
    let binary = scratch.path().join("main");
    fs::write(&path, source).unwrap();
    let (status, _, stderr) = support::run(
        Command::new(env!("CARGO_BIN_EXE_lim"))
            .arg(&path)
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
        Duration::from_secs(15),
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
