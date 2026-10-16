use lim::{check_types, parse_program};

#[test]
fn bound_mutable_slice_element_suspends_parent_until_release() {
    let source = "(#fn main () #usize
      (#let-mut values (#array #u64 2)
        (#array-of (#array #u64 2) 1u64 2u64))
      (#let view (#slice-mut #u64) (#slice-mut-of (#borrow-mut values)))
      (#let item (#ref-mut #u64) (#slice-mut-idx view 0usize))
      (#deref-set item 7u64)
      (#forget item)
      (#let count #usize (#slice-mut-len view))
      (#forget view)
      (#return count))";
    check_types(&parse_program(source).unwrap()).unwrap();
}

#[test]
fn parent_slice_cannot_be_used_while_element_reborrow_is_live() {
    let source = "(#fn main () #usize
      (#let-mut values (#array #u64 2)
        (#array-of (#array #u64 2) 1u64 2u64))
      (#let view (#slice-mut #u64) (#slice-mut-of (#borrow-mut values)))
      (#let item (#ref-mut #u64) (#slice-mut-idx view 0usize))
      (#let count #usize (#slice-mut-len view))
      (#forget item)
      (#forget view)
      (#return count))";
    let error = check_types(&parse_program(source).unwrap()).unwrap_err();
    assert!(
        error.contains("derived field reference is active"),
        "{error}"
    );
}

#[test]
fn shared_borrow_cannot_overlap_mutable_slice() {
    let source = "(#fn main () ()
      (#let-mut values (#array #u64 2)
        (#array-of (#array #u64 2) 1u64 2u64))
      (#let view (#slice-mut #u64) (#slice-mut-of (#borrow-mut values)))
      (#let shared (#ref (#array #u64 2)) (#borrow values))
      (#forget shared)
      (#forget view)
      (#return ()))";
    let error = check_types(&parse_program(source).unwrap()).unwrap_err();
    assert!(error.contains("borrow"), "{error}");
}

#[test]
fn mutable_slice_can_be_reborrowed_again_after_element_release() {
    let source = "(#fn main () #u64
      (#let-mut values (#array #u64 2)
        (#array-of (#array #u64 2) 1u64 2u64))
      (#let view (#slice-mut #u64) (#slice-mut-of (#borrow-mut values)))
      (#let first (#ref-mut #u64) (#slice-mut-idx view 0usize))
      (#deref-set first 7u64)
      (#forget first)
      (#let second (#ref-mut #u64) (#slice-mut-idx view 1usize))
      (#deref-set second 8u64)
      (#forget second)
      (#let answer #u64 (#deref (#slice-mut-idx view 1usize)))
      (#forget view)
      (#return answer))";
    check_types(&parse_program(source).unwrap()).unwrap();
}

#[test]
fn same_slice_cannot_have_two_live_mutable_element_reborrows() {
    let source = "(#fn main () ()
      (#let-mut values (#array #u64 2)
        (#array-of (#array #u64 2) 1u64 2u64))
      (#let view (#slice-mut #u64) (#slice-mut-of (#borrow-mut values)))
      (#let first (#ref-mut #u64) (#slice-mut-idx view 0usize))
      (#let second (#ref-mut #u64) (#slice-mut-idx view 0usize))
      (#deref-set first 10u64) (#deref-set second 20u64)
      (#forget first) (#forget second) (#forget view) (#return ()))";
    let error = check_types(&parse_program(source).unwrap()).unwrap_err();
    assert!(error.contains("borrow"), "{error}");
}

#[test]
fn dynamic_indices_may_alias_and_cannot_hold_two_live_mutable_reborrows() {
    let source = "(#fn main () ()
      (#let-mut values (#array #u64 2)
        (#array-of (#array #u64 2) 1u64 2u64))
      (#let view (#slice-mut #u64) (#slice-mut-of (#borrow-mut values)))
      (#let index #usize 0usize)
      (#let first (#ref-mut #u64) (#slice-mut-idx view index))
      (#let second (#ref-mut #u64) (#slice-mut-idx view index))
      (#deref-set first 10u64) (#deref-set second 20u64)
      (#forget first) (#forget second) (#forget view) (#return ()))";
    let error = check_types(&parse_program(source).unwrap()).unwrap_err();
    assert!(error.contains("borrow"), "{error}");
}

#[test]
fn dynamic_indices_on_an_incoming_slice_remain_may_aliases() {
    let source = "(#fn conflict (: view (#slice-mut #u64) : index #usize) ()
        (#let first (#ref-mut #u64) (#slice-mut-idx view index))
        (#let second (#ref-mut #u64) (#slice-mut-idx view index))
        (#deref-set first 10u64) (#deref-set second 20u64)
        (#forget first) (#forget second) (#forget view) (#return ()))
      (#fn main () () (#return ()))";
    let error = check_types(&parse_program(source).unwrap()).unwrap_err();
    assert!(error.contains("borrow"), "{error}");
}

#[test]
fn returned_element_reference_retains_its_parameter_borrow() {
    let source = "(#fn pick (: target (#ref-mut (#array #u64 2))) (#ref-mut #u64)
        (#return (#borrow-mut (#index target 0usize))))
      (#fn main () ()
        (#let-mut values (#array #u64 2)
          (#array-of (#array #u64 2) 1u64 2u64))
        (#let element (#ref-mut #u64)
          (#call pick (: target (#borrow-mut values))))
        (#deref-set element 10u64)
        (#forget element) (#forget values) (#return ()))";
    check_types(&parse_program(source).unwrap()).unwrap();

    // The returned loan retains element zero, not the entire array. A write
    // to the disjoint second element remains valid while the reference is live.
    let disjoint = source.replace(
        "(#deref-set element 10u64)",
        "(#set-index values 1usize 20u64) (#deref-set element 10u64)",
    );
    check_types(&parse_program(&disjoint).unwrap()).unwrap();
    let conflict = source.replace(
        "(#deref-set element 10u64)",
        "(#set-index values 0usize 20u64) (#deref-set element 10u64)",
    );
    let error = check_types(&parse_program(&conflict).unwrap()).unwrap_err();
    assert!(error.contains("borrow"), "{error}");
}

#[test]
fn returned_element_reference_can_relinquish_its_mutable_slice_parent() {
    let source = "(#fn pick (: view (#slice-mut #u64)) (#ref-mut #u64)
        (#let element (#ref-mut #u64) (#slice-mut-idx view 0usize))
        (#forget view)
        (#return element))
      (#fn main () ()
        (#let-mut values (#array #u64 1) (#array-of (#array #u64 1) 1u64))
        (#let view (#slice-mut #u64) (#slice-mut-of (#borrow-mut values)))
        (#let element (#ref-mut #u64) (#call pick (: view view)))
        (#deref-set element 2u64)
        (#forget element) (#forget values) (#return ()))";
    check_types(&parse_program(source).unwrap()).unwrap();

    let conflict = source.replace(
        "(#deref-set element 2u64)",
        "(#set-index values 0usize 2u64)",
    );
    let error = check_types(&parse_program(&conflict).unwrap()).unwrap_err();
    assert!(error.contains("borrow"), "{error}");
}

#[test]
fn returned_field_reference_can_relinquish_its_mutable_reference_parent() {
    let source = "(#struct Pair () (: left #u64 : right #u64))
      (#fn pick (: target (#ref-mut Pair)) (#ref-mut #u64)
        (#let child (#ref-mut #u64) (#borrow-mut (#get target left)))
        (#forget target)
        (#return child))
      (#fn main () ()
        (#let-mut pair Pair (#struct-literal Pair (: left 1u64 : right 2u64)))
        (#let child (#ref-mut #u64)
          (#call pick (: target (#borrow-mut pair))))
        (#deref-set child 3u64)
        (#forget child) (#forget pair) (#return ()))";
    check_types(&parse_program(source).unwrap()).unwrap();

    let conflict = source.replace("(#deref-set child 3u64)", "(#set-field pair left 3u64)");
    let error = check_types(&parse_program(&conflict).unwrap()).unwrap_err();
    assert!(error.contains("borrow"), "{error}");
}

#[test]
fn returned_aggregate_reference_can_relinquish_its_mutable_parent() {
    let source = "(#struct Pair () (: left #u64 : right #u64))
      (#struct View () (: selected (#ref-mut #u64)))
      (#fn pick (: target (#ref-mut Pair)) View
        (#let child (#ref-mut #u64) (#borrow-mut (#get target left)))
        (#forget target)
        (#return (#struct-literal View (: selected child))))
      (#fn main () ()
        (#let-mut pair Pair (#struct-literal Pair (: left 1u64 : right 2u64)))
        (#let view View (#call pick (: target (#borrow-mut pair))))
        (#set-field pair right 5u64)
        (#let child (#ref-mut #u64) (#get view selected))
        (#deref-set child 3u64)
        (#forget child) (#forget view) (#forget pair) (#return ()))";
    check_types(&parse_program(source).unwrap()).unwrap();

    let conflict = source.replace("(#deref-set child 3u64)", "(#set-field pair left 3u64)");
    let error = check_types(&parse_program(&conflict).unwrap()).unwrap_err();
    assert!(error.contains("borrow"), "{error}");
}

#[test]
fn returned_reference_from_owned_reference_container_keeps_its_referent() {
    let source = "(#struct Pair () (: value #u64))
      (#struct Holder () (: view (#ref-mut #u64)))
      (#fn take (: holder Holder) (#ref-mut #u64)
        (#let child (#ref-mut #u64) (#get holder view))
        (#forget holder)
        (#return child))
      (#fn main () ()
        (#let-mut pair Pair (#struct-literal Pair (: value 1u64)))
        (#let holder Holder
          (#struct-literal Holder (: view (#borrow-mut (#get pair value)))))
        (#let child (#ref-mut #u64) (#call take (: holder holder)))
        (#deref-set child 3u64)
        (#forget child) (#forget pair) (#return ()))";
    check_types(&parse_program(source).unwrap()).unwrap();

    let conflict = source.replace("(#deref-set child 3u64)", "(#set-field pair value 3u64)");
    let error = check_types(&parse_program(&conflict).unwrap()).unwrap_err();
    assert!(error.contains("borrow"), "{error}");
}

#[test]
fn parent_handle_release_does_not_transfer_an_unreturned_sibling_loan() {
    let source = "(#struct Pair () (: left #u64 : right #u64))
      (#fn pick (: target (#ref-mut Pair)) (#ref-mut #u64)
        (#let selected (#ref-mut #u64) (#borrow-mut (#get target left)))
        (#let other (#ref-mut #u64) (#borrow-mut (#get target right)))
        (#forget target)
        (#drop other)
        (#return selected))";
    let error = check_types(&parse_program(source).unwrap()).unwrap_err();
    assert!(error.contains("derived reference"), "{error}");
}

#[test]
fn range_relative_slice_index_retains_the_selected_base_element_loan() {
    let source = "(#fn pick (: range (#slice #u64)) (#ref #u64)
        (#let selected (#ref #u64) (#slice-idx range 0usize))
        (#forget range)
        (#return selected))
      (#fn main () ()
      (#let-mut values (#array #u64 3)
        (#array-of (#array #u64 3) 1u64 2u64 3u64))
      (#let base (#slice #u64) (#slice-of (#borrow values)))
      (#let range (#slice #u64) (#slice-range base 1usize 2usize))
      (#let selected (#ref #u64) (#call pick (: range range)))
      (#set-index values 1usize 20u64)
      (#forget selected) (#forget values) (#return ()))";
    let error = check_types(&parse_program(&source).unwrap()).unwrap_err();
    assert!(error.contains("borrow"), "{error}");

    let disjoint = source.replace(
        "(#set-index values 1usize 20u64)",
        "(#set-index values 0usize 20u64)",
    );
    check_types(&parse_program(&disjoint).unwrap()).unwrap();
}

#[test]
fn ranged_slice_offsets_survive_a_reference_parameter_return() {
    let source = "(#fn pick (: view (#slice #u64)) (#ref #u64)
        (#let range (#slice #u64)
          (#slice-range (#slice-range view 1usize 3usize) 1usize 2usize))
        (#let selected (#ref #u64) (#slice-idx range 0usize))
        (#forget range)
        (#return selected))
      (#fn main () ()
      (#let-mut values (#array #u64 4)
        (#array-of (#array #u64 4) 1u64 2u64 3u64 4u64))
      (#let base (#slice #u64) (#slice-of (#borrow values)))
      (#let selected (#ref #u64) (#call pick (: view base)))
      (#forget base)
      (#set-index values 2usize 20u64)
      (#forget selected) (#forget values) (#return ()))";
    let error = check_types(&parse_program(source).unwrap()).unwrap_err();
    assert!(error.contains("cannot mutate"), "{error}");

    let disjoint = source.replace(
        "(#set-index values 2usize 20u64)",
        "(#set-index values 1usize 20u64)",
    );
    check_types(&parse_program(&disjoint).unwrap()).unwrap();
}

#[test]
fn projected_reborrow_conflicts_follow_multiple_reference_bindings() {
    let source = "(#struct Inner () (: value #u64))
      (#struct Outer () (: inner Inner))
      (#fn main () ()
        (#let-mut owner Outer (#struct-literal Outer
          (: inner (#struct-literal Inner (: value 1u64)))))
        (#let outer-ref (#ref-mut Outer) (#borrow-mut owner))
        (#let inner-ref (#ref-mut Inner) (#borrow-mut (#get outer-ref inner)))
        (#let shared (#ref #u64) (#borrow (#get inner-ref value)))
        (#let conflicting (#ref-mut #u64)
          (#borrow-mut (#get inner-ref value)))
        (#forget conflicting) (#forget shared) (#forget inner-ref)
        (#forget outer-ref) (#forget owner) (#return ()))";
    let error = check_types(&parse_program(source).unwrap()).unwrap_err();
    assert!(
        error.contains("already borrowed") || error.contains("live reference"),
        "expected an overlapping-loan diagnostic, got: {error}"
    );

    let disjoint = source
        .replace(
            "(#struct Inner () (: value #u64))",
            "(#struct Inner () (: value #u64 : other #u64))",
        )
        .replace(
            "(: inner (#struct-literal Inner (: value 1u64)))",
            "(: inner (#struct-literal Inner (: value 1u64 : other 2u64)))",
        )
        .replace(
            "(#get inner-ref value)))\n        (#forget conflicting)",
            "(#get inner-ref other)))\n        (#forget conflicting)",
        );
    check_types(&parse_program(&disjoint).unwrap()).unwrap();
}

#[test]
fn live_element_reborrows_from_disjoint_split_halves_are_allowed() {
    let source = "(#fn main () ()
      (#let-mut values (#array #u64 4)
        (#array-of (#array #u64 4) 1u64 2u64 3u64 4u64))
      (#let whole (#slice-mut #u64) (#slice-mut-of (#borrow-mut values)))
      (#let (#tuple left right) (#tuple (#slice-mut #u64) (#slice-mut #u64))
        (#slice-mut-split whole 2usize))
      (#let first (#ref-mut #u64) (#slice-mut-idx left 0usize))
      (#let second (#ref-mut #u64) (#slice-mut-idx right 0usize))
      (#deref-set first 10u64) (#deref-set second 20u64)
      (#forget first) (#forget second)
      (#forget left) (#forget right) (#return ()))";
    check_types(&parse_program(source).unwrap()).unwrap();
}

#[test]
fn distinct_constant_indices_in_one_mutable_slice_are_disjoint() {
    let source = "(#fn main () ()
      (#let-mut values (#array #u64 2)
        (#array-of (#array #u64 2) 1u64 2u64))
      (#let view (#slice-mut #u64) (#slice-mut-of (#borrow-mut values)))
      (#let first (#ref-mut #u64) (#slice-mut-idx view 0usize))
      (#let second (#ref-mut #u64) (#slice-mut-idx view 1usize))
      (#deref-set first 10u64) (#deref-set second 20u64)
      (#forget first) (#forget second) (#forget view) (#return ()))";
    check_types(&parse_program(source).unwrap()).unwrap();
}

#[test]
fn distinct_constant_indices_in_an_incoming_mutable_slice_are_disjoint() {
    let source = "(#fn touch (: view (#slice-mut #u64)) ()
        (#let first (#ref-mut #u64) (#slice-mut-idx view 0usize))
        (#let second (#ref-mut #u64) (#slice-mut-idx view 1usize))
        (#deref-set first 10u64) (#deref-set second 20u64)
        (#forget first) (#forget second) (#forget view) (#return ()))
      (#fn main () ()
        (#let-mut values (#array #u64 2)
          (#array-of (#array #u64 2) 1u64 2u64))
        (#let view (#slice-mut #u64) (#slice-mut-of (#borrow-mut values)))
        (#call touch (: view view))
        (#forget values) (#return ()))";
    check_types(&parse_program(source).unwrap()).unwrap();
}
