//! Regression coverage for symbolic slice loop induction.

use lim::{CompileConfig, Diagnostic, ProofOutcome};
mod support;

fn check(source: &str, theorem: &str) -> Result<lim::CheckedTheorem, Diagnostic> {
    lim::check_theorem_details_from_path_with_config(
        source,
        std::path::Path::new("slice-induction.lim"),
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

const WRAPPER: &str = r#"
  (#fn worker (: view (#slice-mut #u8)) #usize
    (#let-mut remaining #usize (#slice-mut-len view))
    (#label again
      (#while (#usize::gt remaining 0usize)
        (#deref-set
          (#slice-mut-idx view (#usize::sub-wrap remaining 1usize)) 0u8)
        (#set remaining (#usize::sub-wrap remaining 1usize))))
    (#forget view) (#return remaining))
  (#fn run (: source (#ref-mut (#array #u8 3)) : start #usize : end #usize) #usize
    (#let whole (#slice-mut #u8) (#slice-mut-of source))
    (#let view (#slice-mut #u8) (#slice-mut-range whole start end))
    (#let result #usize (#call worker (($ view))))
    (#forget whole)
    (#return result))
"#;

const RANGE: &str = "(#bool::and (#usize::le start end) (#usize::le end 3usize))";

fn wrapped_claim(claim: &str) -> String {
    format!(
        r#"{WRAPPER}
      (#theorem run-contract
        (#proof-loop-limit 1
          (#proof-with-invariants
            ((worker again (#usize::le remaining (#slice-mut-len view)) remaining))
            {claim})))"#
    )
}

#[test]
fn bounded_mutable_slice_worker_proves_result_and_guarded_frame() {
    let outside = (0..3)
        .map(|index| {
            format!(
                r#"
      (#proof-implies
        (#bool::or (#usize::lt {index}usize start) (#usize::le end {index}usize))
        (#proof-eq (#index source {index}usize) (#proof-old (#index source {index}usize))))"#
            )
        })
        .collect::<Vec<_>>()
        .join(" ");
    let source = wrapped_claim(&format!(
        "(#proof-contract run {RANGE} (#proof-and (#proof-eq (#proof-result) 0usize) {outside}))"
    ));
    proved(&source, "run-contract");
}

#[test]
fn bounded_mutable_slice_wrapper_accepts_empty_end_boundary() {
    proved(
        r#"
      (#fn worker (: view (#slice-mut #u8)) #usize
        (#let-mut remaining #usize (#slice-mut-len view))
        (#label again (#while (#usize::gt remaining 0usize)
          (#deref-set (#slice-mut-idx view (#usize::sub-wrap remaining 1usize)) 0u8)
          (#set remaining (#usize::sub-wrap remaining 1usize))))
        (#forget view) (#return remaining))
      (#fn empty (: source (#ref-mut (#array #u8 3))) #usize
        (#let whole (#slice-mut #u8) (#slice-mut-of source))
        (#let view (#slice-mut #u8) (#slice-mut-range whole 3usize 3usize))
        (#let result #usize (#call worker (($ view))))
        (#forget whole) (#return result))
      (#theorem empty-contract
        (#proof-loop-limit 1
          (#proof-with-invariants ((worker again (#usize::le remaining (#slice-mut-len view)) remaining))
            (#proof-contract empty true (#proof-eq (#proof-result) 0usize)))))
    "#,
        "empty-contract",
    );
}

#[test]
fn readonly_slice_countdown_repeatedly_reads_and_proves_rank() {
    proved(
        r#"
      (#fn count (: view (#slice #u8)) #usize
        (#let-mut remaining #usize (#slice-len view))
        (#label again (#while (#usize::gt remaining 0usize)
          (#let value #u8 (#deref (#slice-idx view (#usize::sub-wrap remaining 1usize))))
          (#set remaining (#usize::sub-wrap remaining 1usize))))
        (#forget view) (#return remaining))
      (#fn run (: source (#ref (#array #u8 3))) #usize
        (#return (#call count (: view (#slice-of source)))))
      (#theorem count-contract
        (#proof-loop-limit 1
          (#proof-with-invariants ((count again (#usize::le remaining (#slice-len view)) remaining))
            (#proof-contract run true (#proof-eq (#proof-result) 0usize)))))
    "#,
        "count-contract",
    );
}

#[test]
fn missing_slice_length_invariant_is_induction_failure_under_negation() {
    let source = r#"
      (#fn unsafe-count (: view (#slice #u8) : limit #usize) #usize
        (#let-mut remaining #usize limit)
        (#label again (#while (#usize::gt remaining 0usize)
          (#let value #u8 (#deref (#slice-idx view (#usize::sub-wrap remaining 1usize))))
          (#set remaining (#usize::sub-wrap remaining 1usize))))
        (#forget view) (#return remaining))
      (#fn run (: source (#ref (#array #u8 3))) #usize
        (#return (#call unsafe-count (: view (#slice-of source) : limit 3usize))))
      (#theorem unsafe-contract
        (#proof-loop-limit 1
          (#proof-with-invariants ((unsafe-count again true remaining))
            (#proof-not
              (#proof-contract run true
                (#proof-eq (#proof-result) 0usize))))))
    "#;
    induction_failure(source, "unsafe-contract");
}

#[test]
fn weak_interior_slice_frame_is_induction_failure_under_negation() {
    let claim = format!("(#proof-contract run {RANGE} (#proof-eq (#index source 1usize) (#proof-old (#index source 1usize))))");
    for claim in [claim.clone(), format!("(#proof-not {claim})")] {
        induction_failure(&wrapped_claim(&claim), "run-contract");
    }
}

#[test]
fn slice_reference_elements_preserve_their_referents_outside_the_view() {
    let program = r#"
      (#fn worker (: view (#slice-mut (#ref-mut #u8))) #usize
        (#let-mut remaining #usize (#slice-mut-len view))
        (#label again (#while (#usize::gt remaining 0usize)
          (#let slot (#ref-mut (#ref-mut #u8))
            (#slice-mut-idx view (#usize::sub-wrap remaining 1usize)))
          (#deref-set (#borrow-mut (#deref (#deref slot))) 0u8)
          (#set remaining (#usize::sub-wrap remaining 1usize))))
        (#forget view) (#return remaining))
      (#fn run (: left (#ref-mut #u8) : right (#ref-mut #u8) : start #usize : end #usize) #usize
        (#let-mut pointers (#array (#ref-mut #u8) 2)
          (#array-of (#array (#ref-mut #u8) 2) left right))
        (#let view (#slice-mut (#ref-mut #u8)) (#borrow-slice-mut pointers start end))
        (#let result #usize (#call worker (: view view)))
        (#forget pointers) (#return result))"#;
    let pre = "(#bool::and (#usize::le start end) (#usize::le end 2usize))";
    let property = "(#proof-and (#proof-eq (#proof-result) 0usize) (#proof-implies (#usize::gt start 0usize) (#proof-eq (#deref left) (#proof-old (#deref left)))) (#proof-implies (#bool::or (#usize::gt start 1usize) (#usize::le end 1usize)) (#proof-eq (#deref right) (#proof-old (#deref right)))))";
    let source = format!("{program} (#theorem claim (#proof-with-invariants ((worker again (#usize::le remaining (#slice-mut-len view)) remaining)) (#proof-contract run {pre} {property})))");
    proved(&source, "claim");
    let claim = "(#proof-contract run true (#proof-eq (#deref left) (#proof-old (#deref left))))";
    // Restrict the view to its full backing array, so a missing recursive
    // pointee write would incorrectly establish an unchanged-data claim.
    let program = program.replace(
        "#borrow-slice-mut pointers start end",
        "#borrow-slice-mut pointers 0usize 2usize",
    );
    for claim in [claim.to_owned(), format!("(#proof-not {claim})")] {
        let source = format!("{program} (#theorem claim (#proof-with-invariants ((worker again (#usize::le remaining (#slice-mut-len view)) remaining)) {claim}))");
        induction_failure(&source, "claim");
    }
}

#[test]
fn a_temporary_view_can_update_a_loop_carried_owned_array() {
    let source = r#"
      (#fn run (: source (#ref-mut (#array #u8 3))) #u8
        (#let-mut remaining #u8 3u8)
        (#label again (#while (#u8::gt remaining 0u8)
          (#let view (#slice-mut #u8) (#borrow-slice-mut (#deref source) 1usize 2usize))
          (#deref-set (#slice-mut-idx view 0usize) 9u8)
          (#forget view)
          (#set remaining (#u8::sub-wrap remaining 1u8))))
        (#return (#index source 1usize)))
      (#theorem claim (#proof-with-invariants
        ((run again (#proof-or (#u8::eq remaining 3u8) (#proof-eq (#index source 1usize) 9u8)) remaining))
        (#proof-contract run true (#proof-eq (#proof-result) 9u8))))"#;
    proved(source, "claim");
}

#[test]
fn split_views_keep_the_original_outside_range_unchanged() {
    let worker = WRAPPER.split("  (#fn run ").next().unwrap();
    let source = format!(
        r#"{worker}
      (#fn run (: source (#ref-mut (#array #u8 3))) #usize
        (#let whole (#slice-mut #u8) (#borrow-slice-mut (#deref source) 1usize 3usize))
        (#let (#tuple left right) (#tuple (#slice-mut #u8) (#slice-mut #u8))
          (#slice-mut-split whole 1usize))
        (#let first #usize (#call worker (: view left)))
        (#let second #usize (#call worker (: view right)))
        (#return (#usize::add-wrap first second)))
      (#theorem claim (#proof-with-invariants
        ((worker again (#usize::le remaining (#slice-mut-len view)) remaining))
        (#proof-loop-limit 1 (#proof-contract run true
          (#proof-and (#proof-eq (#proof-result) 0usize)
            (#proof-eq (#index source 0usize) (#proof-old (#index source 0usize))))))))"#
    );
    proved(&source, "claim");
}

#[test]
fn ordinary_validation_rejects_replacing_reference_retaining_slice_locals() {
    let program = r#"
      (#fn run (: source (#ref (#array #u8 3)) : count #u8) ()
        (#let-mut cursor (#slice #u8) (#borrow-slice (#deref source) 0usize 3usize))
        (#let-mut remaining #u8 count)
        (#label again (#while (#u8::gt remaining 0u8)
          (#set cursor (#borrow-slice (#deref source) 1usize 3usize))
          (#set remaining (#u8::sub-wrap remaining 1u8))))
        (#forget cursor) (#return ()))"#;
    for claim in [
        "(#proof-contract run true true)",
        "(#proof-not (#proof-contract run true true))",
    ] {
        let source = format!("{program} (#theorem claim (#proof-with-invariants ((run again true remaining)) {claim}))");
        let error =
            check(&source, "claim").expect_err("moving view geometry cannot be assumed stable");
        assert_eq!(error.code, lim::DiagnosticCode::Type);
        assert_eq!(error.proof_outcome(), None);
    }
}

#[test]
fn slice_induction_example_matches_native_for_all_ranges_and_byte_values() {
    use std::{fs, process::Command, time::Duration};
    let scratch = support::Scratch::new("proof-slice-induction-native");
    let mut source = include_str!("../examples/proof_slice_induction.lim").to_owned();
    source.truncate(source.find("(#fn main ").unwrap());
    source.push_str(r#"
      (#fn main () #u64
        (#let-mut input #u16 0u16)
        (#while (#u16::lt input 256u16)
          (#let initial #u8 (#as input #u8))
          (#let-mut start #usize 0usize)
          (#while (#usize::le start 3usize)
            (#let-mut end #usize start)
            (#while (#usize::le end 3usize)
              (#let-mut values (#array #u8 3) (#array-of (#array #u8 3)
                initial (#u8::add-wrap initial 77u8) (#u8::add-wrap initial 155u8)))
              (#let result #usize (#call clear-range (: source (#borrow-mut values) : start start : end end)))
              (#if (#usize::ne result 0usize) (#block (#return 1u64)))"#);
    for (index, offset) in [(0, 0), (1, 77), (2, 155)] {
        source.push_str(&format!(r#"
              (#let expected-{index} #u8
                (#if (#bool::and (#usize::le start {index}usize) (#usize::lt {index}usize end))
                  0u8 (#u8::add-wrap initial {offset}u8)))
              (#if (#u8::ne (#index values {index}usize) expected-{index}) (#block (#return 2u64)))"#));
    }
    source.push_str(
        r#"
              (#set end (#usize::add-wrap end 1usize)))
            (#set start (#usize::add-wrap start 1usize)))
          (#set input (#u16::add-wrap input 1u16)))
        (#return 42u64))"#,
    );
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
