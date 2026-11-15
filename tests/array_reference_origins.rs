use lim::{check_types, parse_program};

fn accepts(source: &str) {
    check_types(&parse_program(source).expect("valid Lim source"))
        .expect("source should pass type and borrow checking");
}

fn rejects(source: &str) -> String {
    check_types(&parse_program(source).expect("valid Lim source"))
        .expect_err("source should be rejected")
}

#[test]
fn mutable_and_shared_borrows_of_distinct_literal_elements_are_disjoint() {
    accepts(
        "#fn main {
  #params = ();
  #returns = ();
  #body = (
        (#let-mut values (#array #u64 2) (#array-of (#array #u64 2) 10u64 20u64))
        (#let first (#ref-mut #u64) (#borrow-mut (#index values 0usize)))
        (#let second (#ref #u64) (#borrow (#index values 1usize)))
        (#deref-set first 11u64)
        (#forget first) (#forget second) (#forget values)
        (#return ())\n  );\n}\n",
    );
}

#[test]
fn mutable_and_shared_borrows_of_distinct_typed_literal_elements_are_disjoint() {
    accepts(
        "#fn main {
  #params = ();
  #returns = ();
  #body = (
        (#let-mut values (#array #u64 2) (#array-of (#array #u64 2) 10u64 20u64))
        (#let first (#ref-mut #u64) (#borrow-mut (#index values (#literal #usize 0))))
        (#let second (#ref #u64) (#borrow (#index values (#literal #usize 1))))
        (#deref-set first 11u64)
        (#forget first) (#forget second) (#forget values)
        (#return ())\n  );\n}\n",
    );
}

#[test]
fn same_suffixed_array_index_rejects_mutable_and_shared_borrows() {
    let error = rejects(
        "#fn main {
  #params = ();
  #returns = ();
  #body = (
        (#let-mut values (#array #u64 2) (#array-of (#array #u64 2) 10u64 20u64))
        (#let first (#ref-mut #u64) (#borrow-mut (#index values 0usize)))
        (#let second (#ref #u64) (#borrow (#index values 0usize)))
        (#forget first) (#forget second) (#forget values)
        (#return ())\n  );\n}\n",
    );
    assert!(error.contains("borrow"), "{error}");
}

#[test]
fn same_typed_literal_array_index_rejects_two_mutable_borrows() {
    let error = rejects(
        "#fn main {
  #params = ();
  #returns = ();
  #body = (
        (#let-mut values (#array #u64 2) (#array-of (#array #u64 2) 10u64 20u64))
        (#let first (#ref-mut #u64) (#borrow-mut (#index values (#literal #usize 1))))
        (#let second (#ref-mut #u64) (#borrow-mut (#index values (#literal #usize 1))))
        (#forget first) (#forget second) (#forget values)
        (#return ())\n  );\n}\n",
    );
    assert!(error.contains("borrow"), "{error}");
}

#[test]
fn reference_to_local_array_element_cannot_escape() {
    let error = rejects(
        "#fn escape {
  #params = ();
  #returns = (#ref #u64);
  #body = (
        (#let-mut values (#array #u64 2) (#array-of (#array #u64 2) 10u64 20u64))
        (#return (#borrow (#index values (#literal #usize 0))))\n  );\n}\n",
    );
    assert!(
        error.contains("reference") || error.contains("borrow"),
        "{error}"
    );
}
