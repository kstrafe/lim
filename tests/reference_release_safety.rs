use lim::{check_types, parse_program};

#[test]
fn forgotten_reference_cannot_be_used_after_owner_mutation() {
    let source = "(#fn main () #u64
      (#let-mut owner #u64 1u64)
      (#let view (#ref #u64) (#borrow owner))
      (#forget view)
      (#set owner 2u64)
      (#return (#deref view)))";
    let error = check_types(&parse_program(source).unwrap()).unwrap_err();
    assert!(
        error.contains("consumed") || error.contains("borrowed"),
        "{error}"
    );
}

#[test]
fn dropped_reference_cannot_be_reused_by_read_clone_or_reborrow() {
    for use_after in [
        "(#return (#deref view))",
        "(#let again (#ref #u64) (#clone view)) (#return 0u64)",
        "(#let again (#ref #u64) view) (#return 0u64)",
    ] {
        let source = format!(
            "(#fn main () #u64
              (#let owner #u64 1u64)
              (#let view (#ref #u64) (#borrow owner))
              (#drop view)
              {use_after})"
        );
        let error = check_types(&parse_program(&source).unwrap()).unwrap_err();
        assert!(
            error.contains("consumed") || error.contains("moved"),
            "{use_after}: {error}"
        );
    }
}

#[test]
fn released_reference_field_cannot_be_read_or_reborrowed() {
    for use_after in [
        "(#return (#deref (#index values 0u64)))",
        "(#let again (#ref #u64) (#clone (#index values 0u64))) (#return 0u64)",
    ] {
        let source = format!(
            "(#fn main () #u64
              (#let owner #u64 1u64)
              (#let values (#array (#ref #u64) 1)
                (#array-repeat (#borrow owner)))
              (#forget (#index values 0u64))
              {use_after})"
        );
        let error = check_types(&parse_program(&source).unwrap()).unwrap_err();
        assert!(
            error.contains("consumed") || error.contains("moved"),
            "{use_after}: {error}"
        );
    }
}

#[test]
fn forgetting_a_copy_scalar_does_not_invalidate_it() {
    let source = "(#fn main () #u64
      (#let value #u64 7u64)
      (#forget value)
      (#return value))";
    check_types(&parse_program(source).unwrap()).unwrap();
}

#[test]
fn dropped_copy_aggregate_with_references_cannot_be_reused() {
    let source = "(#fn main () #u64
      (#let owner #u64 1u64)
      (#let values (#array (#ref #u64) 1)
        (#array-repeat (#borrow owner)))
      (#drop values)
      (#return (#deref (#index values 0u64))))";
    let error = check_types(&parse_program(source).unwrap()).unwrap_err();
    assert!(error.contains("consumed"), "{error}");
}

#[test]
fn destructured_reference_cannot_be_reused_after_drop() {
    let source = "(#fn main () #u64
      (#let-mut owner #u64 1u64)
      (#let pair (#tuple (#ref #u64)) (#tuple (#borrow owner)))
      (#let (#tuple view) (#tuple (#ref #u64)) pair)
      (#drop view)
      (#set owner 2u64)
      (#return (#deref view)))";
    let error = check_types(&parse_program(source).unwrap()).unwrap_err();
    assert!(error.contains("consumed"), "{error}");
}

#[test]
fn a_mutable_reference_cannot_be_moved_into_two_aggregate_fields() {
    let source = "(#struct Pair ((left (#ref-mut #u64)) (right (#ref-mut #u64))))
      (#fn main () #u64
        (#let-mut owner #u64 1u64)
        (#let reference (#ref-mut #u64) (#borrow-mut owner))
        (#let pair Pair
          (#struct-literal Pair ((left reference) (right reference))))
        (#forget pair)
        (#return 0u64))";
    let error = check_types(&parse_program(source).unwrap()).unwrap_err();
    assert!(
        error.contains("consumed") || error.contains("moved") || error.contains("borrow"),
        "{error}"
    );
}
