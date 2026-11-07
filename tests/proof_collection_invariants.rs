//! Regression coverage for mutable slice clearing invariants.

use lim::{CompileConfig, Diagnostic, ProofOutcome};

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
