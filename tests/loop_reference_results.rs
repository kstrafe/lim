//! Loop results retain loans and actual enum payload bounds through blocks.

#[test]
fn block_wrapped_loop_references_keep_their_source_borrow() {
    for (ty, value, read) in [
        ("(#ref #u64)", "(#borrow owner)", "(#deref saved)"),
        ("(#ref-mut #u64)", "(#borrow-mut owner)", "(#deref saved)"),
        (
            "Holder",
            "(#struct-literal Holder (: view (#borrow owner)))",
            "(#deref (#get saved view))",
        ),
    ] {
        let source = format!(
            "(#struct Holder (: view (#ref #u64)))
          (#fn main () #u64
            (#let-mut owner #u64 42u64)
            (#let saved {ty} (#block (#block (#label result (#loop
              (#break-to result {value}))))))
            (#return {read}))"
        );
        let program = lim::parse_program(&source).unwrap();
        lim::check_types(&program).unwrap();
        lim::generate_assembly(&program).unwrap();
        let invalid = source.replace("(#return", "(#set owner 1u64) (#return");
        let error = lim::check_types(&lim::parse_program(&invalid).unwrap()).unwrap_err();
        assert!(
            error.contains("borrow") || error.contains("access"),
            "{error}"
        );
    }
}

#[test]
fn block_wrapped_loop_cannot_return_a_reference_to_its_local_owner() {
    let source = "(#fn escape () (#ref #u64)
      (#return (#block (#let owner #u64 42u64)
        (#label result (#loop (#break-to result (#borrow owner)))))))";
    let error = lim::check_types(&lim::parse_program(source).unwrap()).unwrap_err();
    assert!(
        error.contains("local") || error.contains("outlive") || error.contains("borrow"),
        "{error}"
    );
}

#[test]
fn loop_payload_bounds_do_not_invent_missing_reference_slots() {
    for result in [
        "(#loop (#break (Present (Second (#borrow owner)))))",
        "(#block (#label result (#loop (#break-to result (Present (Second (#borrow owner)))))))",
    ] {
        let source = format!(
            "(#enum Inner (: First (#ref #u64) : Second (#ref #u64)))
          (#enum Outer (: Present Inner : Absent #u64))
          (#fn use-value (: input Outer) #u64
            (#return (#match input
              (#case (Present child) (#match child
                (#case (First view) (#deref view))
                (#case (Second view) (#deref view))))
              (#case (Absent value) value))))
          (#fn main () #u64 (#let owner #u64 42u64)
            (#let packet Outer {result})
            (#return (#call use-value (: input packet))))"
        );
        let program = lim::parse_program(&source).unwrap();
        lim::check_types(&program).unwrap();
        lim::generate_assembly(&program).unwrap();
    }
}

#[test]
fn loop_result_bounds_keep_unknown_alternatives_conservative() {
    let source = "(#enum Choice (: Borrowed (#ref #u64) : Value #u64))
      (#fn select (: input Choice : choose #bool) Choice
        (#return (#block (#label result (#loop
          (#if choose (#block (#break-to result input))
            (#block (#forget input) (#break-to result (Value 42u64)))))))))
      (#fn main () #u64 (#let-mut owner #u64 1u64)
        (#let saved Choice (#call select (: input (Borrowed (#borrow owner)) : choose true)))
        (#set owner 2u64)
        (#return (#match saved
          (#case (Borrowed view) (#deref view)) (#case (Value value) value))))";
    let error = lim::check_types(&lim::parse_program(source).unwrap()).unwrap_err();
    assert!(
        error.contains("borrow") || error.contains("access"),
        "{error}"
    );
}
