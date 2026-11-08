use lim::{CompileConfig, Diagnostic, ProofOutcome};
mod support;

fn check(source: &str, theorem: &str) -> Result<lim::CheckedTheorem, Diagnostic> {
    lim::check_theorem_details_from_path_with_config(
        source,
        std::path::Path::new("dynamic-reference-arrays.lim"),
        &CompileConfig::default(),
        theorem,
    )
}

fn proved(source: &str, theorem: &str) {
    check(source, theorem).unwrap_or_else(|error| panic!("{}\n{source}", error.message));
}

fn contract_failure(source: &str, theorem: &str) {
    let error =
        check(source, theorem).expect_err("the invalid dynamic-index claim must fail closed");
    assert_eq!(
        error.proof_outcome(),
        Some(ProofOutcome::ContractFailure),
        "{error:?}"
    );
}

#[test]
fn dynamic_store_updates_the_selected_slot_and_preserves_the_other() {
    proved(
        r#"
      (#struct Slot () (: reference (#ref #u8)))
      (#fn replace (: slots (#ref-mut (#array Slot 2)) : index #usize : next (#ref #u8)) ()
        (#deref-set (#borrow-mut (#index (#deref slots) index))
          (#struct-literal Slot (: reference next)))
        (#return ()))
      (#theorem replace-contract (#proof-contract replace
        (#usize::lt index 2usize) true))
      (#fn caller (: slots (#ref-mut (#array Slot 2)) : index #usize : next (#ref #u8)) ()
        (#call replace (: slots slots : index index : next next))
        (#return ()))
      (#theorem selected (#proof-using (replace-contract)
        (#proof-contract caller (#usize::lt index 2usize)
          (#proof-and
            (#proof-eq (#deref (#get (#index (#deref slots) index) reference)) (#deref next))
            (#proof-implies (#usize::ne index 0usize)
              (#proof-eq
                (#deref (#get (#index (#deref slots) 0usize) reference))
                (#proof-old (#deref (#get (#index (#deref slots) 0usize) reference)))))
            (#proof-implies (#usize::ne index 1usize)
              (#proof-eq
                (#deref (#get (#index (#deref slots) 1usize) reference))
                (#proof-old (#deref (#get (#index (#deref slots) 1usize) reference)))))))))
    "#,
        "selected",
    );
}

#[test]
fn symbolic_index_read_selects_the_referent_stored_at_that_position() {
    proved(
        r#"
      (#struct Slot () (: reference (#ref #u8)))
      (#fn read (: slots (#array Slot 2) : index #usize) #u8
        (#return (#deref (#get (#index slots index) reference))))
      (#theorem read-contract (#proof-contract read
        (#usize::lt index 2usize)
        (#proof-eq (#proof-result)
          (#if (#usize::eq index 0usize)
            (#deref (#get (#index slots 0usize) reference))
            (#deref (#get (#index slots 1usize) reference))))))
    "#,
        "read-contract",
    );
}

#[test]
fn dynamic_store_preserves_enum_variant_and_payload_condition() {
    proved(
        r#"
      (#enum Maybe () (: Maybe.None : Maybe.Some (#ref #u8)))
      (#fn replace (: values (#ref-mut (#array Maybe 2)) : index #usize
          : next (#ref #u8) : present #bool) ()
        (#if present
          (#deref-set (#borrow-mut (#index (#deref values) index))
            (#enum-literal Maybe.Some next))
          (#deref-set (#borrow-mut (#index (#deref values) index))
            (#enum-literal Maybe.None)))
        (#return ()))
      (#theorem replace-contract (#proof-contract replace
        (#usize::lt index 2usize) true))
      (#fn caller (: values (#ref-mut (#array Maybe 2)) : index #usize
          : next (#ref #u8) : present #bool) ()
        (#call replace (: values values : index index : next next : present present))
        (#return ()))
      (#theorem selected (#proof-using (replace-contract)
        (#proof-contract caller (#usize::lt index 2usize)
          (#proof-eq
            (#match (#index (#deref values) index)
              (#case Maybe.None 0u8)
              (#case (Maybe.Some payload) (#deref payload)))
            (#if present (#deref next) 0u8)))))
    "#,
        "selected",
    );
}

#[test]
fn two_symbolically_indexed_writes_to_the_same_slot_keep_last_write_order() {
    proved(
        r#"
      (#struct Slot () (: reference (#ref #u8)))
      (#fn replace-twice (: slots (#ref-mut (#array Slot 2)) : index #usize
          : first (#ref #u8) : second (#ref #u8)) ()
        (#deref-set (#borrow-mut (#index (#deref slots) index))
          (#struct-literal Slot (: reference first)))
        (#deref-set (#borrow-mut (#index (#deref slots) index))
          (#struct-literal Slot (: reference second)))
        (#return ()))
      (#theorem replace-twice-contract (#proof-contract replace-twice
        (#usize::lt index 2usize) true))
      (#fn caller (: slots (#ref-mut (#array Slot 2)) : index #usize
          : first (#ref #u8) : second (#ref #u8)) ()
        (#call replace-twice (: slots slots : index index : first first : second second))
        (#return ()))
      (#theorem last-write (#proof-using (replace-twice-contract)
        (#proof-contract caller (#usize::lt index 2usize)
          (#proof-eq
            (#deref (#get (#index (#deref slots) index) reference))
            (#deref second)))))
    "#,
        "last-write",
    );
}

#[test]
fn writes_at_distinct_symbolic_indices_preserve_both_selected_values() {
    proved(
        r#"
      (#struct Slot () (: reference (#ref #u8)))
      (#fn replace-two (: slots (#ref-mut (#array Slot 2)) : first-index #usize
          : second-index #usize : first (#ref #u8) : second (#ref #u8)) ()
        (#deref-set (#borrow-mut (#index (#deref slots) first-index))
          (#struct-literal Slot (: reference first)))
        (#deref-set (#borrow-mut (#index (#deref slots) second-index))
          (#struct-literal Slot (: reference second)))
        (#return ()))
      (#theorem replace-two-contract (#proof-contract replace-two
        (#proof-and (#usize::lt first-index 2usize) (#usize::lt second-index 2usize)) true))
      (#fn caller (: slots (#ref-mut (#array Slot 2)) : first-index #usize
          : second-index #usize : first (#ref #u8) : second (#ref #u8)) ()
        (#call replace-two (: slots slots : first-index first-index : second-index second-index
          : first first : second second))
        (#return ()))
      (#theorem selected (#proof-using (replace-two-contract)
        (#proof-contract caller
          (#proof-and (#usize::lt first-index 2usize) (#usize::lt second-index 2usize))
          (#proof-and
            (#proof-eq
              (#deref (#get (#index (#deref slots) first-index) reference))
              (#if (#usize::eq first-index second-index)
                (#deref second) (#deref first)))
            (#proof-eq
              (#deref (#get (#index (#deref slots) second-index) reference))
              (#deref second))))))
    "#,
        "selected",
    );
}

#[test]
fn nested_symbolic_indices_select_and_update_the_inner_slot() {
    proved(
        r#"
      (#struct Slot () (: reference (#ref #u8)))
      (#fn replace (: grid (#ref-mut (#array (#array Slot 2) 2))
          : row #usize : column #usize : next (#ref #u8)) ()
        (#deref-set
          (#borrow-mut (#index (#index (#deref grid) row) column))
          (#struct-literal Slot (: reference next)))
        (#return ()))
      (#theorem replace-contract (#proof-contract replace
        (#proof-and (#usize::lt row 2usize) (#usize::lt column 2usize)) true))
      (#fn caller (: grid (#ref-mut (#array (#array Slot 2) 2))
          : row #usize : column #usize : next (#ref #u8)) ()
        (#call replace (: grid grid : row row : column column : next next))
        (#return ()))
      (#theorem selected (#proof-using (replace-contract)
        (#proof-contract caller
          (#proof-and (#usize::lt row 2usize) (#usize::lt column 2usize))
          (#proof-eq
            (#deref (#get (#index (#index (#deref grid) row) column) reference))
            (#deref next)))))
    "#,
        "selected",
    );
}

#[test]
fn helper_contract_replays_symbolic_indexed_borrowed_target() {
    proved(
        r#"
      (#struct Slot () (: reference (#ref #u8)))
      (#fn replace-one (: slot (#ref-mut Slot) : next (#ref #u8)) ()
        (#deref-set slot (#struct-literal Slot (: reference next)))
        (#return ()))
      (#theorem replace-one-contract (#proof-contract replace-one true true))
      (#fn replace-at (: slots (#ref-mut (#array Slot 2)) : index #usize
          : next (#ref #u8)) ()
        (#call replace-one
          (: slot (#borrow-mut (#index (#deref slots) index)) : next next))
        (#return ()))
      (#theorem replace-at-contract (#proof-using (replace-one-contract)
        (#proof-contract replace-at (#usize::lt index 2usize) true)))
      (#fn caller (: slots (#ref-mut (#array Slot 2)) : index #usize
          : next (#ref #u8)) ()
        (#call replace-at (: slots slots : index index : next next))
        (#return ()))
      (#theorem selected (#proof-using (replace-at-contract)
        (#proof-contract caller (#usize::lt index 2usize)
          (#proof-eq
            (#deref (#get (#index (#deref slots) index) reference))
            (#deref next)))))
    "#,
        "selected",
    );
}

#[test]
fn provider_contract_replays_conditional_dynamic_index_store() {
    proved(
        r#"
      (#struct Slot () (: reference (#ref #u8)))
      (#fn replace (: slots (#ref-mut (#array Slot 2)) : index #usize
          : condition #bool : next (#ref #u8)) ()
        (#if condition
          (#deref-set (#borrow-mut (#index (#deref slots) index))
            (#struct-literal Slot (: reference next)))
          ())
        (#return ()))
      (#theorem replace-contract (#proof-contract replace
        (#usize::lt index 2usize) true))
      (#fn caller (: slots (#ref-mut (#array Slot 2)) : index #usize
          : condition #bool : next (#ref #u8)) ()
        (#call replace (: slots slots : index index : condition condition : next next))
        (#return ()))
      (#theorem selected (#proof-using (replace-contract)
        (#proof-contract caller (#usize::lt index 2usize)
          (#proof-eq
            (#deref (#get (#index (#deref slots) index) reference))
            (#if condition
              (#deref next)
              (#proof-old (#deref (#get (#index (#deref slots) index) reference))))))))
    "#,
        "selected",
    );
}

#[test]
fn out_of_bounds_dynamic_access_is_not_discharged_by_negating_the_claim() {
    let source = r#"
      (#struct Slot () (: reference (#ref #u8)))
      (#fn read (: slots (#array Slot 2) : index #usize) #u8
        (#return (#deref (#get (#index slots index) reference))))
      (#theorem read-contract (#proof-contract read true
        (#proof-eq (#proof-result)
          (#if (#usize::eq index 0usize)
            (#deref (#get (#index slots 0usize) reference))
            (#deref (#get (#index slots 1usize) reference))))))
      (#theorem negated-read-contract
        (#proof-not (#proof-contract read true
          (#proof-eq (#proof-result)
            (#if (#usize::eq index 0usize)
              (#deref (#get (#index slots 0usize) reference))
              (#deref (#get (#index slots 1usize) reference)))))))
    "#;

    for theorem in ["read-contract", "negated-read-contract"] {
        let error =
            check(source, theorem).expect_err("unbounded indices must not erase executions");
        assert_eq!(
            error.proof_outcome(),
            Some(ProofOutcome::Counterexample),
            "{error:?}"
        );
        assert!(error.message.contains("out of bounds"), "{}", error.message);
    }
}

#[test]
fn wrong_sibling_claim_and_negation_of_selected_value_fail_closed() {
    let source = r#"
      (#struct Slot () (: reference (#ref #u8)))
      (#fn replace (: slots (#ref-mut (#array Slot 2)) : index #usize : next (#ref #u8)) ()
        (#deref-set (#borrow-mut (#index (#deref slots) index))
          (#struct-literal Slot (: reference next)))
        (#return ()))
      (#theorem replace-contract (#proof-contract replace (#usize::lt index 2usize) true))
      (#fn caller (: slots (#ref-mut (#array Slot 2)) : index #usize : next (#ref #u8)) ()
        (#call replace (: slots slots : index index : next next)) (#return ()))
      (#theorem wrong-sibling (#proof-using (replace-contract)
        (#proof-contract caller (#usize::lt index 2usize)
          (#proof-eq (#deref (#get (#index (#deref slots) 0usize) reference)) (#deref next)))))
      (#theorem wrong-selected (#proof-using (replace-contract)
        (#proof-contract caller (#usize::lt index 2usize)
          (#proof-not (#proof-eq (#deref (#get (#index (#deref slots) index) reference)) (#deref next))))))
    "#;
    contract_failure(source, "wrong-sibling");
    contract_failure(source, "wrong-selected");
}

#[test]
fn symbolic_index_preserves_the_selected_slice_backing_and_geometry() {
    proved(
        r#"
      (#fn read (: index #usize : left #u8 : right #u8) #u8
        (#let first (#array #u8 1) (#array-of (#array #u8 1) left))
        (#let second (#array #u8 2) (#array-of (#array #u8 2) right 0u8))
        (#let views (#array (#slice #u8) 2)
          (#array-of (#array (#slice #u8) 2)
            (#borrow-slice first) (#borrow-slice second)))
        (#let selected (#slice #u8) (#index views index))
        (#return (#deref (#slice-idx selected 0usize))))
      (#theorem selected (#proof-contract read (#usize::lt index 2usize)
        (#proof-eq (#proof-result) (#if (#usize::eq index 0usize) left right))))
    "#,
        "selected",
    );
}

#[test]
fn indexed_reference_replacement_revokes_validation_of_the_selected_slot() {
    let source = r#"
      (#struct Slot () (: reference (#ref #u8)))
      (#fn validate (: user (#ref Slot)) #bool
        (#return (#u8::eq (#deref (#get user reference)) 1u8)))
      (#fn perform (: user (#ref Slot)) () (#return ()))
      (#fn entry (: index #usize : left #u8 : right #u8 : replacement #u8) ()
        (#let-mut slots (#array Slot 2) (#array-of (#array Slot 2)
          (#struct-literal Slot (: reference (#borrow left)))
          (#struct-literal Slot (: reference (#borrow right)))))
        (#let accepted #bool (#call validate (: user (#borrow (#index slots 0usize)))))
        (#if (#usize::lt index 2usize) (#block
          (#deref-set (#borrow-mut (#index slots index))
            (#struct-literal Slot (: reference (#borrow replacement))))
          (#if accepted (#call perform (: user (#borrow (#index slots 0usize)))))))
        (#return ()))
      (#theorem selected (#proof-requires-validation entry
        (#parameter-of validate user) (#parameter-of perform user)))
    "#;
    let error = check(source, "selected").expect_err("a selected slot's old validation is stale");
    assert_eq!(
        error.proof_outcome(),
        Some(ProofOutcome::Counterexample),
        "{error:?}"
    );
    let sibling_only = source.replace(
        "(#if accepted (#call perform",
        "(#if (#bool::and accepted (#usize::eq index 1usize)) (#call perform",
    );
    proved(&sibling_only, "selected");
}

#[test]
fn oversized_handle_arrays_report_a_resource_limit_even_under_negation() {
    let elements = std::iter::repeat_n("(#borrow input)", 65)
        .collect::<Vec<_>>()
        .join(" ");
    for negate in [false, true] {
        let claim = "(#proof-contract read true (#proof-eq (#proof-result) input))";
        let claim = if negate {
            format!("(#proof-not {claim})")
        } else {
            claim.into()
        };
        let source = format!(
            r#"
          (#fn read (: input #u8) #u8
            (#let values (#array (#ref #u8) 65)
              (#array-of (#array (#ref #u8) 65) {elements}))
            (#return (#deref (#index values 0usize))))
          (#theorem selected {claim})
        "#
        );
        let error =
            check(&source, "selected").expect_err("oversized array cannot bypass proof limits");
        assert_eq!(
            error.proof_outcome(),
            Some(ProofOutcome::ResourceLimit),
            "{error:?}"
        );
    }
}

#[test]
fn dynamic_store_example_matches_native_for_byte_pairs_indices_and_branches() {
    use std::{fs, process::Command, time::Duration};
    let scratch = support::Scratch::new("proof-dynamic-reference-array-native");
    let mut source = include_str!("../examples/proof_dynamic_reference_arrays.lim").to_owned();
    source.truncate(source.find("(#fn main ").unwrap());
    source.push_str(r#"
      (#fn main () #u64
        (#let-mut left-index #u16 0u16)
        (#while (#u16::lt left-index 256u16)
          (#let-mut right-index #u16 0u16)
          (#while (#u16::lt right-index 256u16)
            (#let-mut index #usize 0usize)
            (#while (#usize::lt index 2usize)
              (#let-mut selector #u8 0u8)
              (#while (#u8::lt selector 2u8)
                (#let replace #bool (#u8::eq selector 1u8))
                (#let left #u8 (#as left-index #u8))
                (#let right #u8 (#as right-index #u8))
                (#let result (#tuple #u8 #u8)
                  (#call read-updated (: index index : replace replace
                    : left left : right right : next 9u8)))
                (#let expected-left #u8 (#if (#bool::and replace (#usize::eq index 0usize)) 9u8 left))
                (#let expected-right #u8 (#if (#bool::and replace (#usize::eq index 1usize)) 9u8 right))
                (#if (#u8::ne (#get result 0) expected-left) (#block (#return 1u64)))
                (#if (#u8::ne (#get result 1) expected-right) (#block (#return 2u64)))
                (#set selector (#u8::add-wrap selector 1u8)))
              (#set index (#usize::add-wrap index 1usize)))
            (#set right-index (#u16::add-wrap right-index 1u16)))
          (#set left-index (#u16::add-wrap left-index 1u16)))
        (#return 42u64))
    "#);
    let path = scratch.path().join("main.lim");
    let binary = scratch.path().join("main");
    fs::write(&path, source).unwrap();
    let (status, _, stderr) = support::run(
        Command::new(env!("CARGO_BIN_EXE_lim"))
            .arg(&path)
            .arg("-o")
            .arg(&binary)
            .env("PATH", ""),
        Duration::from_secs(20),
        1024 * 1024,
    )
    .unwrap();
    assert!(status.success(), "{}", String::from_utf8_lossy(&stderr));
    let (status, _, stderr) = support::run(
        Command::new(&binary).env("PATH", ""),
        Duration::from_secs(10),
        1024 * 1024,
    )
    .unwrap();
    assert_eq!(
        status.code(),
        Some(42),
        "{}",
        String::from_utf8_lossy(&stderr)
    );
}
