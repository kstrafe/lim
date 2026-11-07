use lim::{check_types, parse_program};

fn accepts(source: &str) {
    check_types(&parse_program(source).expect("valid Lim source"))
        .expect("symbolic slice contract should be proved");
}

fn disproved(source: &str) {
    let error = check_types(&parse_program(source).expect("valid Lim source"))
        .expect_err("symbolic slice contract should be disproved");
    assert!(error.contains("disproved"), "{error}");
}

fn proof_error(source: &str, expected: &str) {
    let error = check_types(&parse_program(source).expect("valid Lim source"))
        .expect_err("invalid symbolic slice proof should fail");
    assert!(
        error.starts_with("theorem '"),
        "ordinary program validation failed: {error}"
    );
    assert!(
        error.contains(expected),
        "expected {expected:?}, got: {error}"
    );
}

const REF_ARRAY: &str = "(#ref (#array #u64 4))";
const MUT_REF_ARRAY: &str = "(#ref-mut (#array #u64 4))";

#[test]
fn symbolic_range_index_contract_tracks_array_reference_contents() {
    accepts(&format!(
        "(#fn select ((source {REF_ARRAY}) (start #usize) (end #usize) (index #usize)) #u64
      (#let view (#slice #u64) (#slice-range (#slice-of source) start end))
      (#let item (#ref #u64) (#slice-idx view index))
      (#let result #u64 (#deref item)) (#forget item) (#forget view) (#return result))
      (#theorem select-contract
        (#proof-contract select
          (#bool::and (#usize::le start end)
            (#bool::and (#usize::le end 4usize) (#usize::lt index (#usize::sub-wrap end start))))
          (#proof-eq (#proof-result)
            (#proof-old (#index (#deref source) (#usize::add-wrap start index))))))"
    ));
}

#[test]
fn false_result_claim_exposes_symbolic_counterexample_for_slice_read() {
    disproved(&format!(
        "(#fn select ((source {REF_ARRAY}) (start #usize) (end #usize) (index #usize)) #u64
      (#let view (#slice #u64) (#slice-range (#slice-of source) start end))
      (#let result #u64 (#deref (#slice-idx view index)))
      (#forget view) (#return result))
      (#theorem wrong-result
        (#proof-contract select
          (#bool::and (#usize::le start end)
            (#bool::and (#usize::le end 4usize) (#usize::lt index (#usize::sub-wrap end start))))
          (#proof-eq (#proof-result) 0u64)))"
    ));
}

#[test]
fn mutable_slice_update_changes_selected_array_element() {
    accepts(&format!(
        "(#fn update ((source {MUT_REF_ARRAY}) (start #usize) (end #usize) (index #usize)) #u64
      (#let whole (#slice-mut #u64) (#slice-mut-of source))
      (#let view (#slice-mut #u64) (#slice-mut-range whole start end))
      (#let item (#ref-mut #u64) (#slice-mut-idx view index))
      (#deref-set item 77u64) (#forget item) (#forget view) (#forget whole)
      (#return (#index source (#usize::add-wrap start index))))
      (#theorem update-contract
        (#proof-contract update
          (#bool::and (#usize::le start end)
            (#bool::and (#usize::le end 4usize) (#usize::lt index (#usize::sub-wrap end start))))
          (#proof-eq (#proof-result) 77u64)))"
    ));
}

#[test]
fn symbolic_mutation_false_old_state_claim_is_disproved() {
    disproved(&format!(
        "(#fn update ((source {MUT_REF_ARRAY}) (start #usize) (end #usize) (index #usize)) #u64
      (#let whole (#slice-mut #u64) (#slice-mut-of source))
      (#let view (#slice-mut #u64) (#slice-mut-range whole start end))
      (#deref-set (#slice-mut-idx view index) 77u64)
      (#forget view) (#forget whole)
      (#return (#index source (#usize::add-wrap start index))))
      (#theorem unchanged
        (#proof-contract update
          (#bool::and (#usize::le start end)
            (#bool::and (#usize::le end 4usize) (#usize::lt index (#usize::sub-wrap end start))))
          (#proof-eq (#proof-result)
            (#proof-old (#index (#deref source) (#usize::add-wrap start index))))))"
    ));
}

#[test]
fn nested_ranges_preserve_composed_offset() {
    accepts(&format!(
        "(#fn nested ((source {REF_ARRAY}) (start #usize) (end #usize)) #u64
      (#let whole (#slice #u64) (#slice-of source))
      (#let outer (#slice #u64) (#slice-range whole start end))
      (#let inner (#slice #u64) (#slice-range outer 0usize (#usize::sub-wrap end start)))
      (#let result #u64 (#deref (#slice-idx inner 0usize)))
      (#forget inner) (#forget outer) (#forget whole) (#return result))
      (#theorem nested-contract
        (#proof-contract nested
          (#bool::and (#usize::lt start end) (#usize::le end 4usize))
          (#proof-eq (#proof-result) (#proof-old (#index (#deref source) start)))))"
    ));
}

#[test]
fn empty_range_at_end_boundary_has_zero_length() {
    accepts(&format!(
        "(#fn empty ((source {REF_ARRAY})) #usize
      (#let view (#slice #u64) (#borrow-slice (#deref source) 4usize 4usize))
      (#let length #usize (#slice-len view)) (#forget view) (#return length))
      (#theorem empty-contract
        (#proof-contract empty true (#proof-eq (#proof-result) 0usize)))"
    ));
}

#[test]
fn guarded_symbolic_range_is_safe_under_branch_condition() {
    accepts(&format!(
        "(#fn guarded ((source {REF_ARRAY}) (start #usize) (end #usize)) #usize
      (#if (#bool::and (#usize::le start end) (#usize::le end 4usize))
        (#block
          (#let view (#slice #u64) (#borrow-slice (#deref source) start end))
          (#let length #usize (#slice-len view))
          (#forget view)
          (#return length)))
      (#return 0usize))
      (#theorem guarded-contract
        (#proof-contract guarded true
          (#proof-eq (#proof-result)
            (#if (#bool::and (#usize::le start end) (#usize::le end 4usize))
              (#usize::sub-wrap end start) 0usize))))"
    ));
}

#[test]
fn reversed_and_too_large_ranges_fail_with_slice_bounds_reason() {
    let reversed = format!(
        "(#fn invalid ((source {REF_ARRAY})) #usize
      (#let view (#slice #u64) (#borrow-slice (#deref source) 3usize 2usize))
      (#let length #usize (#slice-len view)) (#forget view) (#return length))
      (#theorem invalid-range (#proof-contract invalid true
        (#proof-eq (#proof-result) 0usize)))"
    );
    proof_error(&reversed, "a slice range can be out of bounds or reversed");

    let too_large = format!(
        "(#fn invalid ((source {REF_ARRAY})) #usize
      (#let view (#slice #u64) (#borrow-slice (#deref source) 0usize 5usize))
      (#let length #usize (#slice-len view)) (#forget view) (#return length))
      (#theorem invalid-range (#proof-contract invalid true
        (#proof-eq (#proof-result) 0usize)))"
    );
    proof_error(&too_large, "a slice range can be out of bounds or reversed");
}

#[test]
fn index_equal_to_slice_length_fails_with_bounds_reason() {
    let source = format!(
        "(#fn invalid ((source {REF_ARRAY})) #u64
      (#let view (#slice #u64) (#borrow-slice (#deref source) 1usize 3usize))
      (#let result #u64 (#deref (#slice-idx view 2usize)))
      (#forget view) (#return result))
      (#theorem invalid-index (#proof-contract invalid true
        (#proof-eq (#proof-result) 0u64)))"
    );
    proof_error(&source, "a slice index can be out of bounds");
}

#[test]
fn split_mutation_updates_both_halves_and_preserves_other_elements() {
    accepts(&format!(
        "(#fn split ((source {MUT_REF_ARRAY})) #u64
      (#let whole (#slice-mut #u64) (#borrow-slice-mut (#deref source)))
      (#let (#tuple left right) (#tuple (#slice-mut #u64) (#slice-mut #u64))
        (#slice-mut-split whole 2usize))
      (#deref-set (#slice-mut-idx left 1usize) 51u64)
      (#deref-set (#slice-mut-idx right 0usize) 91u64)
      (#forget left) (#forget right)
      (#return (#u64::add-wrap
        (#deref (#borrow (#index (#deref source) 1usize)))
        (#deref (#borrow (#index (#deref source) 2usize))))))
      (#theorem split-contract
        (#proof-contract split true
          (#proof-and
            (#proof-eq (#proof-result) 142u64)
            (#proof-eq (#index source 0usize) (#proof-old (#index source 0usize)))
            (#proof-eq (#index source 3usize) (#proof-old (#index source 3usize))))))"
    ));
}

#[test]
fn wrapping_usize_endpoints_cannot_bypass_slice_bounds() {
    for (start, end) in [
        ("18446744073709551615usize", "18446744073709551615usize"),
        ("18446744073709551615usize", "0usize"),
    ] {
        proof_error(
            &format!(
                "(#fn invalid (: source {REF_ARRAY}) #usize
            (#let view (#slice #u64) (#borrow-slice (#deref source) {start} {end}))
            (#return (#slice-len view)))
          (#theorem no-wrapping-bypass (#proof-contract invalid true true))"
            ),
            "a slice range can be out of bounds or reversed",
        );
    }
}

#[test]
fn pure_slice_helpers_preserve_existing_views_and_read_their_backing_storage() {
    accepts(
        "(#fn last (: view (#slice #u8)) #u8
        (#return (#deref (#slice-idx view 1usize))))
      (#fn read (: source (#ref (#array #u8 3))) #u8
        (#let view (#slice #u8) (#borrow-slice (#deref source) 1usize 3usize))
        (#return (#call last (($ view)))))
      (#theorem helpers
        (#proof-for-all (: values (#array #u8 3))
          (#proof-eq (#call read (: source (#borrow values))) (#index values 2usize))))",
    );
}

#[test]
fn a_specification_cannot_hide_a_write_through_a_slice() {
    proof_error(
        "(#fn change (: view (#slice-mut #u8)) ()
        (#deref-set (#slice-mut-idx view 0usize) 7u8)
        (#forget view) (#return ()))
      (#theorem writes-are-observable
        (#proof-for-all (: source (#ref-mut (#array #u8 1)))
          (#proof-eq (#call change (: view (#slice-mut-of source))) ())))",
        "may have global-write effects",
    );
}

#[test]
fn returned_views_keep_the_original_array_and_composed_offset() {
    accepts(
        "(#fn suffix (: source (#ref (#array #u8 3))) (#slice #u8)
        (#return (#borrow-slice (#deref source) 1usize 3usize)))
      (#fn read (: source (#ref (#array #u8 3))) #u8
        (#let view (#slice #u8) (#call suffix (($ source))))
        (#return (#deref (#slice-idx view 1usize))))
      (#theorem returned-view
        (#proof-contract read true
          (#proof-eq (#proof-result) (#proof-old (#index source 2usize)))))",
    );
}

#[test]
fn arbitrary_slice_inputs_remain_unproved_without_a_backing_bound() {
    proof_error(
        "(#fn length (: source (#slice #u8)) #usize
        (#return (#slice-len source)))
      (#theorem all-lengths (#proof-contract length true true))",
        "unsupported",
    );
}
