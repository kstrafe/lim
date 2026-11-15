use lim::{check_types, parse_program};

#[test]
fn releasing_only_repeated_mutable_reference_unblocks_owner() {
    let source = "#fn main () #u64
        (#let-mut owner #u64 7u64)
        (#let aggregate (#array (#ref-mut #u64) 1)
          (#array-repeat (#borrow-mut owner)))
        (#forget (#index aggregate 0u64))
        (#return owner)\n";
    check_types(&parse_program(source).unwrap()).unwrap();
}

#[test]
fn releasing_one_shared_reference_does_not_end_the_other() {
    let source = "#fn main () #u64
        (#let-mut owner #u64 7u64)
        (#let aggregate (#array (#ref #u64) 2)
          (#array-of (#array (#ref #u64) 2)
            (#borrow owner) (#borrow owner)))
        (#forget (#index aggregate 0u64))
        (#set owner 9u64)
        (#forget (#index aggregate 1u64))
        (#return owner)\n";
    let error = check_types(&parse_program(source).unwrap()).unwrap_err();
    assert!(error.contains("immutably borrowed"), "{error}");
}

#[test]
fn releasing_a_field_keeps_its_copied_reference_alias_live() {
    let source = "#fn main () #u64
        (#let-mut owner #u64 7u64)
        (#let aggregate (#array (#ref #u64) 1)
          (#array-repeat (#borrow owner)))
        (#let alias (#ref #u64) (#index aggregate 0u64))
        (#forget (#index aggregate 0u64))
        (#set owner 9u64)
        (#forget alias)
        (#return owner)\n";
    let error = check_types(&parse_program(source).unwrap()).unwrap_err();
    assert!(error.contains("immutably borrowed"), "{error}");
}

#[test]
fn releasing_every_shared_field_unblocks_owner() {
    let source = "#fn main () #u64
        (#let-mut owner #u64 7u64)
        (#let aggregate (#array (#ref #u64) 2)
          (#array-of (#array (#ref #u64) 2)
            (#borrow owner) (#borrow owner)))
        (#forget (#index aggregate 0u64))
        (#forget (#index aggregate 1u64))
        (#set owner 9u64)
        (#return owner)\n";
    check_types(&parse_program(source).unwrap()).unwrap();
}

#[test]
fn dropping_partially_released_aggregate_does_not_end_alias_loan() {
    let source = "#fn main () #u64
        (#let-mut owner #u64 7u64)
        (#let aggregate (#array (#ref #u64) 1)
          (#array-repeat (#borrow owner)))
        (#let alias (#ref #u64) (#index aggregate 0u64))
        (#forget (#index aggregate 0u64))
        (#forget aggregate)
        (#set owner 9u64)
        (#forget alias)
        (#return owner)\n";
    let error = check_types(&parse_program(source).unwrap()).unwrap_err();
    assert!(error.contains("immutably borrowed"), "{error}");
}
