use lim::{check_types, parse_program};

#[test]
fn bound_mutable_slice_element_suspends_parent_until_release() {
    let source = "(#fn main () usize
      (#let-mut values (#array u64 2)
        (#array-of (#array u64 2) 1u64 2u64))
      (#let view (#slice-mut u64) (#slice-mut-of (#borrow-mut values)))
      (#let item (#ref-mut u64) (#slice-mut-idx view 0usize))
      (#deref-set item 7u64)
      (#forget item)
      (#let count usize (#slice-mut-len view))
      (#forget view)
      (#return count))";
    check_types(&parse_program(source).unwrap()).unwrap();
}

#[test]
fn parent_slice_cannot_be_used_while_element_reborrow_is_live() {
    let source = "(#fn main () usize
      (#let-mut values (#array u64 2)
        (#array-of (#array u64 2) 1u64 2u64))
      (#let view (#slice-mut u64) (#slice-mut-of (#borrow-mut values)))
      (#let item (#ref-mut u64) (#slice-mut-idx view 0usize))
      (#let count usize (#slice-mut-len view))
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
      (#let-mut values (#array u64 2)
        (#array-of (#array u64 2) 1u64 2u64))
      (#let view (#slice-mut u64) (#slice-mut-of (#borrow-mut values)))
      (#let shared (#ref (#array u64 2)) (#borrow values))
      (#forget shared)
      (#forget view)
      (#return ()))";
    let error = check_types(&parse_program(source).unwrap()).unwrap_err();
    assert!(error.contains("borrow"), "{error}");
}

#[test]
fn mutable_slice_can_be_reborrowed_again_after_element_release() {
    let source = "(#fn main () u64
      (#let-mut values (#array u64 2)
        (#array-of (#array u64 2) 1u64 2u64))
      (#let view (#slice-mut u64) (#slice-mut-of (#borrow-mut values)))
      (#let first (#ref-mut u64) (#slice-mut-idx view 0usize))
      (#deref-set first 7u64)
      (#forget first)
      (#let second (#ref-mut u64) (#slice-mut-idx view 1usize))
      (#deref-set second 8u64)
      (#forget second)
      (#let answer u64 (#deref (#slice-mut-idx view 1usize)))
      (#forget view)
      (#return answer))";
    check_types(&parse_program(source).unwrap()).unwrap();
}
