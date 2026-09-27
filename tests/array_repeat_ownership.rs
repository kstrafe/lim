use lim::{check_types, parse_program};

#[test]
fn repeating_a_linear_element_requires_exactly_one_slot() {
    for (length, allowed) in [(0, false), (1, true), (2, false)] {
        let source = format!(
            "(#struct Token ((value u64)))
             (#linear Token)
             (#fn main () ()
               (#let values (#array Token {length})
                 (#array-repeat (#struct-literal Token ((value 1u64)))))
               (#forget values)
               (#return ()))"
        );
        let program = parse_program(&source).unwrap();
        let result = check_types(&program);
        if allowed {
            result.unwrap_or_else(|error| panic!("length {length}: {error}"));
        } else {
            let error = result.unwrap_err();
            assert!(
                error.contains("#array-repeat requires a Copy element"),
                "{error}"
            );
        }
    }
}

#[test]
fn repeating_exclusive_references_is_rejected_even_without_linear_cleanup() {
    let source = "(#struct Holder ((view (#ref-mut u64))))
      (#fn main () ()
        (#let-mut owner u64 1u64)
        (#let holder Holder (#struct-literal Holder ((view (#borrow-mut owner)))))
        (#let values (#array Holder 2) (#array-repeat holder))
        (#forget values)
        (#return ()))";
    let program = parse_program(source).unwrap();
    let error = check_types(&program).unwrap_err();
    assert!(
        error.contains("#array-repeat requires a Copy element"),
        "{error}"
    );

    let source = "(#fn main () ()
      (#let-mut owner u64 1u64)
      (#let views (#array (#ref-mut u64) 2) (#array-repeat (#borrow-mut owner)))
      (#forget views)
      (#return ()))";
    let program = parse_program(source).unwrap();
    let error = check_types(&program).unwrap_err();
    assert!(
        error.contains("#array-repeat requires a Copy element"),
        "{error}"
    );
}

#[test]
fn repeating_copy_elements_and_shared_references_remains_valid() {
    let copy = "(#fn main () ()
      (#let values (#array u64 3) (#array-repeat 7u64))
      (#return ()))";
    check_types(&parse_program(copy).unwrap()).unwrap();

    let shared = "(#fn main () ()
      (#let owner u64 1u64)
      (#let views (#array (#ref u64) 2) (#array-repeat (#borrow owner)))
      (#forget views)
      (#return ()))";
    check_types(&parse_program(shared).unwrap()).unwrap();
}

#[test]
fn contextual_single_slot_repeat_consumes_the_linear_source() {
    let source = "(#struct Token ((value u64)))
      (#linear Token)
      (#fn main () ()
        (#let token Token (#struct-literal Token ((value 7u64))))
        (#let values (#array Token 1) (#array-repeat token))
        (#forget token)
        (#forget values)
        (#return ()))";
    let program = parse_program(source).unwrap();
    let error = check_types(&program).unwrap_err();
    assert!(error.contains("already consumed"), "{error}");
}
