//! Public API regressions for collection predicates in loop invariants.

use lim::{check_theorem_details_from_path_with_config, CompileConfig, Diagnostic, ProofOutcome};
use std::path::Path;

fn check(source: &str) -> Result<lim::CheckedTheorem, Diagnostic> {
    check_theorem_details_from_path_with_config(
        source,
        Path::new("proof-collection-loop-predicates.lim"),
        &CompileConfig::default(),
        "claim",
    )
}

fn proved(source: &str) {
    let checked = check(source).unwrap_or_else(|error| panic!("{}\n{source}", error.message));
    assert_eq!(checked.outcome, ProofOutcome::Proved);
}

fn induction_failure(source: &str) {
    let error = check(source).expect_err("the induction obligation must fail closed");
    assert_eq!(
        error.proof_outcome(),
        Some(ProofOutcome::InductionFailure),
        "{}\n{source}",
        error.message
    );
}

fn unproved(source: &str) {
    let error = check(source).expect_err("unsupported invariant expressions must fail closed");
    assert!(
        matches!(
            error.proof_outcome(),
            Some(
                ProofOutcome::Unsupported
                    | ProofOutcome::ResourceLimit
                    | ProofOutcome::Counterexample
                    | ProofOutcome::InductionFailure
            )
        ),
        "{}\n{source}",
        error.message
    );
}

const LESS: &str = "(#fn less (: left #u8 : right #u8) #bool\n  (#return (#u8::lt left right)))";

const SWAP_LOOP: &str = r#"
  (#fn swap-twice (: values (#ref-mut (#array #u8 3)) : count #u8) ()
    (#let original (#array #u8 3) (#deref values))
    (#let-mut remaining #u8 count)
    (#label again
      (#while (#u8::gt remaining 0u8)
        (#let first #u8 (#index (#deref values) 0usize))
        (#let second #u8 (#index (#deref values) 1usize))
        (#deref-set (#borrow-mut (#index (#deref values) 0usize)) second)
        (#deref-set (#borrow-mut (#index (#deref values) 1usize)) first)
        (#let first-again #u8 (#index (#deref values) 0usize))
        (#let second-again #u8 (#index (#deref values) 1usize))
        (#deref-set (#borrow-mut (#index (#deref values) 0usize)) second-again)
        (#deref-set (#borrow-mut (#index (#deref values) 1usize)) first-again)
        (#set remaining (#u8::sub-wrap remaining 1u8))))
    (#return ()))
"#;

#[test]
fn unique_and_permutation_are_inductive_across_repeated_swaps() {
    proved(&format!(
        r#"{SWAP_LOOP}
      (#theorem claim
        (#proof-loop-limit 1
          (#proof-with-invariants
            ((swap-twice again
              (#proof-and
                (#proof-unique (#deref values))
                (#proof-permutation (#deref values) original))
              remaining))
            (#proof-contract swap-twice
              (#proof-unique (#deref values))
              (#proof-and
                (#proof-unique (#deref values))
                (#proof-permutation (#deref values) (#proof-old (#deref values))))))))"#
    ));
}

#[test]
fn sortedness_is_preserved_by_a_noop_loop_with_a_named_comparator() {
    proved(&format!(
        r#"{LESS}
      (#fn idle (: values (#ref-mut (#array #u8 3)) : count #u8) ()
        (#let-mut remaining #u8 count)
        (#label again
          (#while (#u8::gt remaining 0u8)
            (#set remaining (#u8::sub-wrap remaining 1u8))))
        (#return ()))
      (#theorem claim
        (#proof-loop-limit 1
          (#proof-with-invariants
            ((idle again (#proof-sorted (#deref values) less) remaining))
            (#proof-contract idle
              (#proof-sorted (#deref values) less)
              (#proof-sorted (#deref values) less)))))"#
    ));
}

#[test]
fn empty_mutable_slice_and_empty_array_predicates_are_valid_in_invariants() {
    proved(
        r#"
      (#fn idle (: values (#ref-mut (#array #u8 2)) : count #u8) ()
        (#let-mut remaining #u8 count)
        (#label again
          (#while (#u8::gt remaining 0u8)
            (#set remaining (#u8::sub-wrap remaining 1u8))))
        (#return ()))
      (#theorem claim
        (#proof-loop-limit 1
          (#proof-with-invariants
            ((idle again
              (#proof-and
                (#proof-unique (#array-of (#array #u8 0)))
                (#proof-unique (#slice-mut-range (#slice-mut-of values) 2usize 2usize)))
              remaining))
            (#proof-contract idle true
              (#proof-and
                (#proof-unique (#array-of (#array #u8 0)))
                (#proof-unique (#slice-mut-range (#slice-mut-of values) 2usize 2usize)))))))
    "#,
    );
}

fn symbolic_mutable_range_predicate_is_proved_under_explicit_bounds() {
    proved(
        r#"
      (#fn idle (: values (#ref-mut (#array #u8 3)) : start #usize : end #usize : count #u8) ()
        (#let-mut remaining #u8 count)
        (#label again
          (#while (#u8::gt remaining 0u8)
            (#set remaining (#u8::sub-wrap remaining 1u8))))
        (#return ()))
      (#theorem claim
        (#proof-loop-limit 1
          (#proof-with-invariants
            ((idle again
              (#proof-implies
                (#bool::and (#usize::le start end) (#usize::le end 3usize))
                (#proof-unique
                  (#slice-mut-range (#slice-mut-of values) start end)))
              remaining))
            (#proof-contract idle
              (#if (#bool::and (#usize::le start end) (#usize::le end 3usize))
                (#proof-unique (#slice-mut-range (#slice-mut-of values) start end)) false)
              (#proof-unique
                (#slice-mut-range (#slice-mut-of values) start end))))))
    "#,
    );
}

#[test]
fn borrowed_and_existing_slice_range_builders_work_in_loop_invariants() {
    proved(
        r#"
      (#fn idle (: values (#ref (#array #u8 3)) : start #usize : end #usize : count #u8) ()
        (#let view (#slice #u8) (#slice-of values))
        (#let-mut remaining #u8 count)
        (#label again
          (#while (#u8::gt remaining 0u8)
            (#set remaining (#u8::sub-wrap remaining 1u8))))
        (#return ()))
      (#theorem claim
        (#proof-loop-limit 1
          (#proof-with-invariants
            ((idle again
              (#proof-implies
                (#bool::and (#usize::le start end) (#usize::le end 3usize))
                (#proof-and
                  (#proof-unique (#borrow-slice (#deref values) start end))
                  (#proof-unique (#slice-range view start end))))
              remaining))
            (#proof-contract idle
              (#if (#bool::and (#usize::le start end) (#usize::le end 3usize))
                (#proof-unique (#borrow-slice (#deref values) start end)) false)
              (#proof-and
                (#proof-unique (#borrow-slice (#deref values) start end))
                (#proof-unique (#slice-range (#slice-of values) start end)))))))
    "#,
    );
    symbolic_mutable_range_predicate_is_proved_under_explicit_bounds();
    mutable_range_can_be_proved_unique_when_its_guard_selects_at_most_one_item();
}

fn mutable_range_can_be_proved_unique_when_its_guard_selects_at_most_one_item() {
    proved(
        r#"
      (#fn idle (: values (#ref-mut (#array #u8 4)) : start #usize : end #usize : count #u8) ()
        (#let-mut remaining #u8 count)
        (#label again
          (#while (#u8::gt remaining 0u8)
            (#set remaining (#u8::sub-wrap remaining 1u8))))
        (#return ()))
      (#theorem claim
        (#proof-loop-limit 1
          (#proof-with-invariants
            ((idle again
              (#proof-implies
                (#bool::and
                  (#usize::le start end)
                  (#bool::and (#usize::le end 4usize)
                    (#usize::le (#usize::sub-wrap end start) 1usize)))
                (#proof-unique
                  (#slice-mut-range (#slice-mut-of values) start end)))
              remaining))
            (#proof-contract idle
              (#bool::and
                (#usize::le start end)
                (#bool::and (#usize::le end 4usize)
                  (#usize::le (#usize::sub-wrap end start) 1usize)))
              (#proof-unique
                (#slice-mut-range (#slice-mut-of values) start end))))))
    "#,
    );
}

#[test]
fn invalid_unique_mutation_and_its_negation_fail_the_induction_obligation() {
    let function = r#"
      (#fn corrupt (: values (#ref-mut (#array #u8 3)) : count #u8) ()
        (#let-mut remaining #u8 count)
        (#label again
          (#while (#u8::gt remaining 0u8)
            (#deref-set (#borrow-mut (#index (#deref values) 1usize)) (#index (#deref values) 0usize))
            (#set remaining (#u8::sub-wrap remaining 1u8))))
        (#return ()))
    "#;
    let postcondition =
        "(#proof-contract corrupt (#proof-unique (#deref values)) (#proof-unique (#deref values)))";
    let theorem = |claim: &str| {
        format!(
            "{function} (#theorem claim (#proof-loop-limit 1 (#proof-with-invariants ((corrupt again (#proof-unique (#deref values)) remaining)) {claim})))"
        )
    };
    induction_failure(&theorem(postcondition));
    induction_failure(&theorem(&format!("(#proof-not {postcondition})")));
}

#[test]
fn missing_permutation_invariant_and_its_negation_remain_unproved() {
    let claim = r#"(#proof-contract swap-twice true
      (#proof-permutation (#deref values) (#proof-old (#deref values))))"#;
    let source = format!(
        r#"{SWAP_LOOP}
      (#theorem claim
        (#proof-loop-limit 1
          (#proof-with-invariants ((swap-twice again true remaining)) {claim})))"#
    );
    induction_failure(&source);
    let negated = source.replace(claim, &format!("(#proof-not {claim})"));
    induction_failure(&negated);
}

fn trace_program(body: &str) -> String {
    format!(
        r#"
      (#fn action (: left #u8 : right #u8) #bool (#return true))
      (#fn compare (: left #u8 : right #u8) #bool
        (#let ignored #bool (#call action (: left left : right right)))
        (#return (#u8::lt left right)))
      (#fn prepare () () (#return ()))
      (#fn entry (: count #u8) ()
        (#let values (#array #u8 3) (#array-of (#array #u8 3) 1u8 2u8 3u8))
        (#let-mut remaining #u8 count)
        (#label again
          (#while (#u8::gt remaining 0u8)
            {body}
            (#set remaining (#u8::sub-wrap remaining 1u8))))
        (#return ()))
      (#theorem claim
        (#proof-loop-limit 1
          (#proof-with-invariants
            ((entry again (#proof-sorted values compare) remaining))
            (#proof-calls-before entry prepare action))))
    "#
    )
}

#[test]
fn comparator_only_calls_in_sorted_invariants_do_not_enter_the_execution_trace() {
    proved(&trace_program(""));
}

#[test]
fn a_real_action_in_the_loop_still_violates_call_order_after_specification_calls() {
    let source = trace_program("(#call action (: left 1u8 : right 2u8))");
    induction_failure(&source);
    let negated = source.replace(
        "(#proof-calls-before entry prepare action)",
        "(#proof-not (#proof-calls-before entry prepare action))",
    );
    induction_failure(&negated);
}

#[test]
fn comparator_traps_and_effects_are_errors_even_inside_invariant_checks() {
    let trap = r#"
      (#fn never (: left #u8 : right #u8) #bool (#return (#unreachable)))
      (#fn idle (: values (#ref-mut (#array #u8 2)) : count #u8) ()
        (#let-mut remaining #u8 count)
        (#label again (#while (#u8::gt remaining 0u8)
          (#set remaining (#u8::sub-wrap remaining 1u8))))
        (#return ()))
      (#theorem claim
        (#proof-with-invariants
          ((idle again (#proof-sorted (#deref values) never) remaining))
          (#proof-contract idle true true)))
    "#;
    unproved(trap);

    let effect = r#"
      (#unsafe-fn unsafe-compare (: left #u8 : right #u8) #bool
        (#return (#u8::lt left right)))
      (#fn idle (: values (#ref-mut (#array #u8 2)) : count #u8) ()
        (#let-mut remaining #u8 count)
        (#label again (#while (#u8::gt remaining 0u8)
          (#set remaining (#u8::sub-wrap remaining 1u8))))
        (#return ()))
      (#theorem claim
        (#proof-with-invariants
          ((idle again (#proof-sorted (#deref values) unsafe-compare) remaining))
          (#proof-contract idle true true)))
    "#;
    unproved(effect);
}

#[test]
fn ordinary_calls_and_blocks_remain_forbidden_inside_collection_and_range_inputs() {
    let call_in_element = r#"
      (#fn one () #u8 (#return 1u8))
      (#fn idle (: count #u8) ()
        (#let-mut remaining #u8 count)
        (#label again (#while (#u8::gt remaining 0u8)
          (#set remaining (#u8::sub-wrap remaining 1u8))))
        (#return ()))
      (#theorem claim
        (#proof-with-invariants
          ((idle again (#proof-unique (#array-of (#array #u8 1) (#call one ()))) remaining))
          (#proof-contract idle true true)))
    "#;
    unproved(call_in_element);

    let call_in_range = r#"
      (#fn start () #usize (#return 0usize))
      (#fn idle (: values (#ref (#array #u8 2)) : count #u8) ()
        (#let-mut remaining #u8 count)
        (#label again (#while (#u8::gt remaining 0u8)
          (#set remaining (#u8::sub-wrap remaining 1u8))))
        (#return ()))
      (#theorem claim
        (#proof-with-invariants
          ((idle again
            (#proof-unique (#borrow-slice (#deref values) (#call start ()) 2usize))
            remaining))
          (#proof-contract idle true true)))
    "#;
    unproved(call_in_range);

    let block_in_range = r#"
      (#fn idle (: values (#ref (#array #u8 2)) : count #u8) ()
        (#let-mut remaining #u8 count)
        (#label again (#while (#u8::gt remaining 0u8)
          (#set remaining (#u8::sub-wrap remaining 1u8))))
        (#return ()))
      (#theorem claim
        (#proof-with-invariants
          ((idle again
            (#proof-unique (#borrow-slice (#deref values) (#block (#let local #usize 0usize) local) 2usize))
            remaining))
          (#proof-contract idle true true)))
    "#;
    unproved(block_in_range);
}

#[test]
fn recursive_comparator_specifications_exhaust_a_typed_budget_under_negation() {
    let prefix = r#"
      (#fn compare (: left #u8 : right #u8) #bool
        (#let-mut remaining #u8 left)
        (#label again (#while (#u8::gt remaining 0u8)
          (#set remaining (#u8::sub-wrap remaining 1u8))))
        (#return (#u8::lt left right)))
    "#;
    let contract = "(#proof-contract compare true true)";
    for claim in [contract.to_string(), format!("(#proof-not {contract})")] {
        let source = format!(
            r#"{prefix}
          (#theorem claim (#proof-with-invariants
            ((compare again (#proof-sorted (#array-of (#array #u8 2) 1u8 2u8) compare) remaining))
            {claim}))"#
        );
        let error = check(&source).expect_err("cyclic specifications cannot establish a claim");
        assert_eq!(
            error.proof_outcome(),
            Some(ProofOutcome::ResourceLimit),
            "{}",
            error.message
        );
    }
}

#[test]
fn nested_comparator_specifications_have_an_explicit_stack_bound() {
    fn chain(length: usize, negate: bool) -> String {
        let mut source = String::new();
        let mut invariants = Vec::new();
        for index in 0..length {
            source.push_str(&format!(
                "(#fn compare-{index} (: left #u8 : right #u8) #bool"
            ));
            if index + 1 != length {
                source.push_str("(#let-mut remaining #u8 1u8) (#label again (#while (#u8::gt remaining 0u8) (#set remaining (#u8::sub-wrap remaining 1u8))))");
                invariants.push(format!("(compare-{index} again (#proof-sorted (#array-of (#array #u8 2) 1u8 2u8) compare-{}) remaining)", index + 1));
            }
            source.push_str("(#return (#u8::lt left right)))");
        }
        let claim = "(#proof-sorted (#array-of (#array #u8 2) 1u8 2u8) compare-0)";
        let claim = if negate {
            format!("(#proof-not {claim})")
        } else {
            claim.into()
        };
        source.push_str(&format!(
            "(#theorem claim (#proof-with-invariants ({}) {claim}))",
            invariants.join(" ")
        ));
        source
    }
    proved(&chain(4, false));
    for negate in [false, true] {
        let error = check(&chain(5, negate))
            .expect_err("deep specifications must not overflow the host stack");
        assert_eq!(
            error.proof_outcome(),
            Some(ProofOutcome::ResourceLimit),
            "{}",
            error.message
        );
        assert!(
            error.message.contains("nesting exceeds 4"),
            "{}",
            error.message
        );
    }
}

#[test]
fn a_safe_comparator_cannot_hide_unmodeled_unsafe_memory_behind_a_helper() {
    let prefix = r#"
      (#unsafe-fn read-byte (: pointer (#ptr #u8)) #u8
        (#return (#unsafe (#ptr-read pointer))))
      (#fn compare (: left #u8 : right #u8) #bool
        (#return (#unsafe
          (#u8::eq (#unsafe-call read-byte (: pointer (#ptr-null (#ptr #u8)))) left))))
      (#fn idle (: values (#ref (#array #u8 2)) : count #u8) ()
        (#let-mut remaining #u8 count)
        (#label again (#while (#u8::gt remaining 0u8)
          (#set remaining (#u8::sub-wrap remaining 1u8))))
        (#return ()))
    "#;
    for claim in [
        "(#proof-contract idle true true)",
        "(#proof-not (#proof-contract idle true true))",
    ] {
        let source = format!("{prefix} (#theorem claim (#proof-with-invariants ((idle again (#proof-sorted (#deref values) compare) remaining)) {claim}))");
        let error = check(&source).expect_err("unsafe memory has no symbolic model");
        assert_eq!(
            error.proof_outcome(),
            Some(ProofOutcome::Unsupported),
            "{}",
            error.message
        );
    }
}
