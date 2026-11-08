use lim::{check_theorem_details_from_path_with_config, CompileConfig, ProofOutcome};
use std::path::Path;

fn check(source: &str) -> Result<lim::CheckedTheorem, lim::Diagnostic> {
    check_theorem_details_from_path_with_config(
        source,
        Path::new("proof-collection-views.lim"),
        &CompileConfig::default(),
        "claim",
    )
}

fn proved(source: &str) {
    let checked = check(source).unwrap_or_else(|error| panic!("{}\n{source}", error.message));
    assert_eq!(checked.outcome, ProofOutcome::Proved);
}

fn outcome(source: &str, expected: ProofOutcome) -> String {
    let error = check(source).expect_err("the theorem should not be certified");
    assert_eq!(
        error.proof_outcome(),
        Some(expected),
        "{}\n{source}",
        error.message
    );
    error.message
}

const LESS_U8: &str = "(#fn less (: left #u8 : right #u8) #bool
  (#return (#u8::lt left right)))";

#[test]
fn unique_is_true_for_empty_and_pairwise_distinct_fixed_arrays() {
    proved(&format!(
        "{LESS_U8}
        (#theorem claim
          (#proof-and
            (#proof-unique (#array-of (#array #u8 0)))
            (#proof-unique (#array-of (#array #u8 4) 1u8 2u8 3u8 4u8))
            (#proof-sorted (#array-of (#array #u8 0)) less)))"
    ));
}

#[test]
fn duplicate_values_disprove_unique_and_negation_proves_the_counterclaim() {
    let sequence = "(#array-of (#array #u8 4) 1u8 2u8 1u8 3u8)";
    let message = outcome(
        &format!("(#theorem claim (#proof-unique {sequence}))"),
        ProofOutcome::Counterexample,
    );
    assert!(message.contains("disproved"), "{message}");
    proved(&format!(
        "(#theorem claim (#proof-not (#proof-unique {sequence})))"
    ));
}

#[test]
fn immutable_slice_properties_ignore_values_outside_the_selected_range() {
    proved(&format!(
        "{LESS_U8}
        (#theorem claim
          (#proof-for-all (: values (#array #u8 4))
            (#proof-implies
              (#bool::and
                (#u8::eq (#index values 0usize) (#index values 3usize))
                (#bool::not (#u8::eq (#index values 1usize) (#index values 2usize))))
              (#proof-and
                (#proof-unique (#borrow-slice values 1usize 3usize))
                (#proof-not (#proof-unique values))))))"
    ));
}

#[test]
fn sortedness_holds_for_every_guarded_symbolic_subrange_of_a_sorted_array() {
    proved(&format!(
        "{LESS_U8}
        (#theorem claim
          (#proof-for-all (: values (#array #u8 4) : start #usize : end #usize)
            (#proof-implies
              (#bool::and
                (#usize::le start end)
                (#bool::and
                  (#usize::le end 4usize)
                  (#bool::and
                    (#u8::le (#index values 0usize) (#index values 1usize))
                    (#bool::and
                      (#u8::le (#index values 1usize) (#index values 2usize))
                      (#u8::le (#index values 2usize) (#index values 3usize))))))
              (#proof-sorted
                (#borrow-slice values start end)
                less))))"
    ));
}

#[test]
fn unique_is_proved_for_every_guarded_empty_or_single_element_subrange() {
    proved(
        "(#theorem claim
          (#proof-for-all (: values (#array #u16 4) : start #usize : end #usize)
            (#proof-implies
              (#bool::and
                (#usize::le start end)
                (#bool::and
                  (#usize::le end 4usize)
                  (#usize::le (#usize::sub-wrap end start) 1usize)))
              (#proof-unique (#borrow-slice values start end)))))",
    );
}

#[test]
fn permutation_accepts_same_type_empty_array_and_empty_slice() {
    proved(
        "(#theorem claim
          (#proof-for-all (: backing (#array #u8 3))
            (#proof-permutation
              (#array-of (#array #u8 0))
              (#borrow-slice backing 2usize 2usize))))",
    );
}

#[test]
fn permutation_compares_arrays_with_immutable_slices_and_preserves_multiplicity() {
    proved(
        "(#theorem claim
          (#proof-for-all (: backing (#array #u8 4))
            (#proof-implies
              (#bool::and
                (#u8::eq (#index backing 1usize) 2u8)
                (#bool::and
                  (#u8::eq (#index backing 2usize) 1u8)
                  (#u8::eq (#index backing 3usize) 1u8)))
              (#proof-and
                (#proof-permutation
                  (#array-of (#array #u8 3) 1u8 2u8 1u8)
                  (#borrow-slice backing 1usize 4usize))
                (#proof-not
                  (#proof-permutation
                    (#array-of (#array #u8 3) 1u8 2u8 2u8)
                    (#borrow-slice backing 1usize 4usize)))))))",
    );
}

#[test]
fn mutable_slice_is_a_supported_collection_view() {
    proved(
        "(#theorem claim
          (#proof-for-all (: source (#ref-mut (#array #u8 3))
                           : start #usize : end #usize)
            (#proof-and
              (#proof-implies
                (#bool::and
                  (#usize::le start end)
                  (#bool::and
                    (#usize::le end 3usize)
                    (#usize::le (#usize::sub-wrap end start) 1usize)))
                (#proof-unique
                  (#slice-mut-range (#slice-mut-of source) start end)))
              (#proof-permutation
                (#deref source)
                (#slice-mut-of source)))))",
    );
}

#[test]
fn proof_old_snapshots_array_contents_but_an_old_slice_handle_reads_current_storage() {
    let source = "(#fn duplicate-second (: values (#ref-mut (#array #u8 2))) ()
        (#let whole (#slice-mut #u8) (#slice-mut-of values))
        (#let first #u8 (#deref (#slice-mut-idx whole 0usize)))
        (#deref-set (#slice-mut-idx whole 1usize) first)
        (#forget whole)
        (#return ()))
      (#theorem claim
        (#proof-contract duplicate-second
          (#u8::ne (#index values 0usize) (#index values 1usize))
          (#proof-and
            (#proof-old (#proof-unique (#deref values)))
            (#proof-old (#proof-unique (#slice-mut-of values)))
            (#proof-not (#proof-unique (#deref values)))
            (#proof-not (#proof-unique (#proof-old (#slice-mut-of values)))))))";
    proved(source);
}

#[test]
fn sorted_comparator_is_not_called_for_empty_singleton_or_guarded_short_views() {
    let never = "(#fn never (: left #u8 : right #u8) #bool (#return (#unreachable)))";
    let marker = "(#fn marker (: left #u8 : right #u8) #bool
        (#return (#u8::eq left 99u8)))";
    proved(&format!(
        "{never}
        {marker}
        (#theorem claim
          (#proof-and
            (#proof-sorted (#array-of (#array #u8 0)) never)
            (#proof-sorted (#array-of (#array #u8 1) 7u8) never)
            (#proof-for-all (: values (#array #u8 3) : start #usize : end #usize)
              (#proof-implies
                (#bool::and
                  (#usize::le start end)
                  (#bool::and
                    (#usize::le end 3usize)
                    (#usize::le (#usize::sub-wrap end start) 1usize)))
                (#proof-sorted (#borrow-slice values start end) never)))
            (#proof-for-all (: values (#array #u8 3))
              (#proof-implies
                (#bool::and
                  (#u8::eq (#index values 0usize) 1u8)
                  (#bool::and
                    (#u8::eq (#index values 1usize) 2u8)
                    (#u8::eq (#index values 2usize) 99u8)))
                (#proof-sorted (#borrow-slice values 0usize 2usize) marker)))))"
    ));

    let mismatch = "(#fn wrong (: left #u64 : right #u64) #bool
        (#return (#u64::lt left right)))
      (#theorem claim
        (#proof-not
          (#proof-sorted (#array-of (#array #u8 0)) wrong)))";
    let error = check(mismatch).expect_err("empty input must still typecheck its comparator");
    assert!(
        error.message.contains("parameter types"),
        "{}",
        error.message
    );
}

#[test]
fn comparator_traps_remain_errors_and_selected_contracts_still_work() {
    let source = "(#fn never (: left #u8 : right #u8) #bool (#return (#unreachable)))
      (#theorem claim
        (#proof-not
          (#proof-sorted (#array-of (#array #u8 2) 1u8 2u8) never)))";
    outcome(source, ProofOutcome::Counterexample);

    proved(
        "(#fn less (: left #u8 : right #u8) #bool
          (#return (#u8::lt left right)))
        (#theorem less-contract
          (#proof-contract less true
            (#proof-eq (#proof-result) (#u8::lt left right))))
        (#theorem claim
          (#proof-using (less-contract)
            (#proof-sorted (#array-of (#array #u8 3) 1u8 2u8 3u8) less)))",
    );
}

#[test]
fn collection_limits_and_malformed_unique_remain_errors_under_negation() {
    let values = std::iter::repeat_n("0u8", 65).collect::<Vec<_>>().join(" ");
    let oversized = format!(
        "(#theorem claim
          (#proof-not
            (#proof-unique (#array-of (#array #u8 65) {values}))))"
    );
    outcome(&oversized, ProofOutcome::ResourceLimit);

    let malformed = "(#theorem claim
      (#proof-not
        (#proof-unique (#array-of (#array #u8 1) 0u8) 1u8)))";
    let error = check(malformed).expect_err("malformed unique form must remain an error");
    assert_ne!(error.proof_outcome(), Some(ProofOutcome::Proved));

    let source = "(#theorem claim
      (#proof-not
        (#proof-for-all (: values (#array (#ref #u8) 2))
          (#proof-unique values))))";
    outcome(source, ProofOutcome::Unsupported);
}

#[test]
fn unsafe_and_external_comparators_are_rejected_even_for_empty_arrays() {
    for declaration in [
        "(#unsafe-fn compare (: left #u8 : right #u8) #bool (#return (#u8::lt left right)))",
        "(#extern-fn #abi-c compare (: left #u8 : right #u8) #bool)",
    ] {
        for length in [0, 2] {
            let elements = if length == 0 { "" } else { "1u8 2u8" };
            let source = format!("{declaration} (#theorem claim (#proof-not (#proof-sorted (#array-of (#array #u8 {length}) {elements}) compare)))");
            let message = outcome(&source, ProofOutcome::Unsupported);
            assert!(message.contains("safe checked implementation"), "{message}");
        }
    }
}
