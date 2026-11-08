use lim::{CompileConfig, Diagnostic, ProofOutcome};
mod support;

fn check(source: &str, theorem: &str) -> Result<lim::CheckedTheorem, Diagnostic> {
    lim::check_theorem_details_from_path_with_config(
        source,
        std::path::Path::new("projected-origins.lim"),
        &CompileConfig::default(),
        theorem,
    )
}

fn proved(source: &str, theorem: &str) {
    check(source, theorem).unwrap_or_else(|error| panic!("{}\n{source}", error.message));
}

fn contract_failure(source: &str, theorem: &str) {
    let error = check(source, theorem).expect_err("the projected-origin claim must fail closed");
    assert_eq!(
        error.proof_outcome(),
        Some(ProofOutcome::ContractFailure),
        "{error:?}"
    );
}

#[test]
fn weak_provider_preserves_dynamic_mutable_projection_identity() {
    proved(
        r#"
      (#fn at (: values (#ref-mut (#array #u8 2)) : index #usize) (#ref-mut #u8)
        (#return (#borrow-mut (#index (#deref values) index))))
      (#theorem at-contract (#proof-contract at (#usize::lt index 2usize) true))
      (#fn caller (: index #usize : left #u8 : right #u8) (#tuple #u8 #u8)
        (#let-mut values (#array #u8 2) (#array-of (#array #u8 2) left right))
        (#let selected (#ref-mut #u8)
          (#call at (: values (#borrow-mut values) : index index)))
        (#deref-set selected 9u8)
        (#forget selected)
        (#return (#tuple (#tuple #u8 #u8) (#index values 0usize) (#index values 1usize))))
      (#theorem selected (#proof-using (at-contract)
        (#proof-contract caller (#usize::lt index 2usize)
          (#proof-eq (#proof-result)
            (#if (#usize::eq index 0usize)
              (#tuple (#tuple #u8 #u8) 9u8 right)
              (#tuple (#tuple #u8 #u8) left 9u8))))))
    "#,
        "selected",
    );
}

#[test]
fn equal_array_elements_do_not_collapse_projected_origin_identity() {
    proved(
        r#"
      (#fn at (: values (#ref-mut (#array #u8 2)) : index #usize) (#ref-mut #u8)
        (#return (#borrow-mut (#index (#deref values) index))))
      (#theorem at-contract (#proof-contract at (#usize::lt index 2usize) true))
      (#fn caller (: index #usize) (#tuple #u8 #u8)
        (#let-mut values (#array #u8 2) (#array-of (#array #u8 2) 4u8 4u8))
        (#let selected (#ref-mut #u8)
          (#call at (: values (#borrow-mut values) : index index)))
        (#deref-set selected 9u8)
        (#forget selected)
        (#return (#tuple (#tuple #u8 #u8) (#index values 0usize) (#index values 1usize)))
      )
      (#theorem selected (#proof-using (at-contract)
        (#proof-contract caller (#usize::lt index 2usize)
          (#proof-eq (#proof-result)
            (#if (#usize::eq index 0usize) (#tuple (#tuple #u8 #u8) 9u8 4u8)
              (#tuple (#tuple #u8 #u8) 4u8 9u8))))))
    "#,
        "selected",
    );
}

#[test]
fn nested_two_by_two_projection_tracks_both_indices() {
    proved(
        r#"
      (#fn at (: values (#ref-mut (#array (#array #u8 2) 2)) : row #usize : column #usize)
          (#ref-mut #u8)
        (#return (#borrow-mut (#index (#index (#deref values) row) column))))
      (#theorem at-contract (#proof-contract at (#proof-and (#usize::lt row 2usize) (#usize::lt column 2usize)) true))
      (#fn caller (: row #usize : column #usize : value #u8) (#array (#array #u8 2) 2)
        (#let-mut values (#array (#array #u8 2) 2)
          (#array-of (#array (#array #u8 2) 2)
            (#array-of (#array #u8 2) 1u8 2u8)
            (#array-of (#array #u8 2) 3u8 4u8)))
        (#let selected (#ref-mut #u8)
          (#call at (: values (#borrow-mut values) : row row : column column)))
        (#deref-set selected value)
        (#forget selected)
        (#return values))
      (#theorem selected (#proof-using (at-contract)
        (#proof-contract caller
          (#proof-and (#usize::lt row 2usize) (#usize::lt column 2usize))
          (#proof-eq (#proof-result)
            (#if (#usize::eq row 0usize)
              (#if (#usize::eq column 0usize)
                (#array-of (#array (#array #u8 2) 2) (#array-of (#array #u8 2) value 2u8) (#array-of (#array #u8 2) 3u8 4u8))
                (#array-of (#array (#array #u8 2) 2) (#array-of (#array #u8 2) 1u8 value) (#array-of (#array #u8 2) 3u8 4u8)))
              (#if (#usize::eq column 0usize)
                (#array-of (#array (#array #u8 2) 2) (#array-of (#array #u8 2) 1u8 2u8) (#array-of (#array #u8 2) value 4u8))
                (#array-of (#array (#array #u8 2) 2) (#array-of (#array #u8 2) 1u8 2u8) (#array-of (#array #u8 2) 3u8 value))))))))
    "#,
        "selected",
    );
}

#[test]
fn selecting_an_input_array_of_references_retains_each_actual_reference() {
    proved(
        r#"
      (#fn at (: values (#array (#ref #u8) 2) : index #usize) (#ref #u8)
        (#return (#index values index)))
      (#theorem at-contract (#proof-contract at (#usize::lt index 2usize) true))
      (#fn caller (: index #usize : left #u8 : right #u8) #u8
        (#let values (#array (#ref #u8) 2)
          (#array-of (#array (#ref #u8) 2) (#borrow left) (#borrow right)))
        (#let selected (#ref #u8) (#call at (: values values : index index)))
        (#return (#deref selected)))
      (#theorem selected (#proof-using (at-contract)
        (#proof-contract caller (#usize::lt index 2usize)
          (#proof-eq (#proof-result) (#if (#usize::eq index 0usize) left right)))))
    "#,
        "selected",
    );
}

#[test]
fn returned_struct_payload_keeps_projected_origin() {
    proved(
        r#"
      (#struct Borrowed () (: value (#ref #u8)))
      (#fn at (: values (#array (#ref #u8) 2) : index #usize) Borrowed
        (#return (#struct-literal Borrowed (: value (#index values index)))))
      (#theorem at-contract (#proof-contract at (#usize::lt index 2usize) true))
      (#fn caller (: index #usize : left #u8 : right #u8) #u8
        (#let values (#array (#ref #u8) 2)
          (#array-of (#array (#ref #u8) 2) (#borrow left) (#borrow right)))
        (#let wrapped Borrowed (#call at (: values values : index index)))
        (#return (#deref (#get wrapped value))))
      (#theorem selected (#proof-using (at-contract)
        (#proof-contract caller (#usize::lt index 2usize)
          (#proof-eq (#proof-result) (#if (#usize::eq index 0usize) left right)))))
    "#,
        "selected",
    );
}

#[test]
fn returned_enum_payload_keeps_projected_origin() {
    proved(
        r#"
      (#enum MaybeRef () (: MaybeRef.None : MaybeRef.Some (#ref #u8)))
      (#fn at (: values (#array (#ref #u8) 2) : index #usize) MaybeRef
        (#return (#enum-literal MaybeRef.Some (#index values index))))
      (#theorem at-contract (#proof-contract at (#usize::lt index 2usize) true))
      (#fn caller (: index #usize : left #u8 : right #u8) #u8
        (#let values (#array (#ref #u8) 2)
          (#array-of (#array (#ref #u8) 2) (#borrow left) (#borrow right)))
        (#let wrapped MaybeRef (#call at (: values values : index index)))
        (#return (#match wrapped
          (#case MaybeRef.None 0u8)
          (#case (MaybeRef.Some value) (#deref value)))))
      (#theorem selected (#proof-using (at-contract)
        (#proof-contract caller (#usize::lt index 2usize)
          (#proof-eq (#proof-result) (#if (#usize::eq index 0usize) left right)))))
    "#,
        "selected",
    );
}

#[test]
fn repeated_computed_indices_keep_distinct_projection_guards() {
    proved(
        r#"
      (#fn at (: values (#array (#ref #u8) 2) : index #usize) (#ref #u8)
        (#return (#index values index)))
      (#theorem at-contract (#proof-contract at (#usize::lt index 2usize) true))
      (#fn caller (: index #usize : left #u8 : right #u8) (#tuple #u8 #u8)
        (#let first (#ref #u8) (#call at (: values (#array-of (#array (#ref #u8) 2) (#borrow left) (#borrow right)) : index index)))
        (#let second-index #usize (#usize::rem-wrap (#usize::add-wrap index 1usize) 2usize))
        (#let second (#ref #u8) (#call at (: values (#array-of (#array (#ref #u8) 2) (#borrow left) (#borrow right)) : index second-index)))
        (#return (#tuple (#tuple #u8 #u8) (#deref first) (#deref second))))
      (#theorem selected (#proof-using (at-contract)
        (#proof-contract caller (#usize::lt index 2usize)
          (#proof-eq (#proof-result)
            (#if (#usize::eq index 0usize) (#tuple (#tuple #u8 #u8) left right)
              (#tuple (#tuple #u8 #u8) right left))))))
    "#,
        "selected",
    );
}

#[test]
fn transitive_wrapper_preserves_dynamic_projection_summary() {
    proved(
        r#"
      (#fn at (: values (#array (#ref #u8) 2) : index #usize) (#ref #u8)
        (#return (#index values index)))
      (#theorem at-contract (#proof-contract at (#usize::lt index 2usize) true))
      (#fn forward (: values (#array (#ref #u8) 2) : index #usize) (#ref #u8)
        (#return (#call at (: values values : index index))))
      (#theorem forward-contract (#proof-using (at-contract)
        (#proof-contract forward (#usize::lt index 2usize) true)))
      (#fn caller (: index #usize : left #u8 : right #u8) #u8
        (#let values (#array (#ref #u8) 2)
          (#array-of (#array (#ref #u8) 2) (#borrow left) (#borrow right)))
        (#let selected (#ref #u8)
          (#call forward (: values values : index index)))
        (#return (#deref selected)))
      (#theorem selected (#proof-using (forward-contract)
        (#proof-contract caller (#usize::lt index 2usize)
          (#proof-eq (#proof-result) (#if (#usize::eq index 0usize) left right)))))
    "#,
        "selected",
    );
}

#[test]
fn conditional_source_index_keeps_selector_and_projection_correlated() {
    proved(
        r#"
      (#fn at (: values (#array (#ref #u8) 2) : index #usize) (#ref #u8)
        (#return (#index values index)))
      (#theorem at-contract (#proof-contract at (#usize::lt index 2usize) true))
      (#fn choose (: values (#array (#ref #u8) 2) : condition #bool : index #usize) (#ref #u8)
        (#let selected-index #usize (#if condition index 1usize))
        (#return (#call at (: values values : index selected-index))))
      (#theorem choose-contract (#proof-using (at-contract)
        (#proof-contract choose
          (#proof-implies condition (#usize::lt index 2usize)) true)))
      (#fn caller (: condition #bool : index #usize : left #u8 : right #u8) #u8
        (#let values (#array (#ref #u8) 2)
          (#array-of (#array (#ref #u8) 2) (#borrow left) (#borrow right)))
        (#let selected (#ref #u8)
          (#call choose (: values values : condition condition : index index)))
        (#return (#deref selected)))
      (#theorem selected (#proof-using (choose-contract)
        (#proof-contract caller
          (#proof-implies condition (#usize::lt index 2usize))
          (#proof-eq (#proof-result)
            (#if condition (#if (#usize::eq index 0usize) left right) right)))))
    "#,
        "selected",
    );
}

#[test]
fn incorrect_target_and_negated_abstract_summary_fail_closed() {
    let source = r#"
      (#fn at (: values (#array (#ref #u8) 2) : index #usize) (#ref #u8)
        (#return (#index values index)))
      (#theorem at-contract (#proof-contract at (#usize::lt index 2usize) true))
      (#fn caller (: index #usize : left #u8 : right #u8) #u8
        (#let values (#array (#ref #u8) 2)
          (#array-of (#array (#ref #u8) 2) (#borrow left) (#borrow right)))
        (#let selected (#ref #u8) (#call at (: values values : index index)))
        (#return (#deref selected)))
      (#theorem selected (#proof-using (at-contract)
        (#proof-contract caller (#usize::lt index 2usize)
          (#proof-eq (#proof-result) left))))
    "#;
    contract_failure(source, "selected");
    contract_failure(
        &source.replace(
            "(#proof-eq (#proof-result) left)",
            "(#proof-not (#proof-eq (#proof-result) (#if (#usize::eq index 0usize) left right)))",
        ),
        "selected",
    );
}

#[test]
fn missing_index_bounds_are_not_invented_for_a_weak_provider_contract() {
    let source = r#"
      (#fn at (: values (#array (#ref #u8) 2) : index #usize) (#ref #u8)
        (#return (#index values index)))
      (#theorem at-contract (#proof-contract at true true))
    "#;
    let error = check(source, "at-contract").expect_err("unchecked indexing must retain its bound");
    assert_eq!(error.proof_outcome(), Some(ProofOutcome::Counterexample));
    assert!(error.message.contains("out of bounds"), "{}", error.message);
}

#[test]
fn dynamic_input_slot_choices_survive_a_stored_reference_summary() {
    proved(
        r#"
      (#struct Slot () (: reference (#ref #u8)))
      (#fn install (: slot (#ref-mut Slot) : choices (#array (#ref #u8) 2) : index #usize) ()
        (#let selected (#ref #u8) (#index choices index))
        (#deref-set slot (#struct-literal Slot (: reference selected)))
        (#return ()))
      (#theorem install-origins (#proof-contract install (#usize::lt index 2usize) true))
      (#fn caller (: index #usize : left #u8 : right #u8) #u8
        (#let choices (#array (#ref #u8) 2)
          (#array-of (#array (#ref #u8) 2) (#borrow left) (#borrow right)))
        (#let-mut slot Slot (#struct-literal Slot (: reference (#borrow left))))
        (#call install (: slot (#borrow-mut slot) : choices choices : index index))
        (#return (#deref (#get slot reference))))
      (#theorem selected (#proof-using (install-origins)
        (#proof-contract caller (#usize::lt index 2usize)
          (#proof-eq (#proof-result) (#if (#usize::eq index 0usize) left right)))))
    "#,
        "selected",
    );
}

#[test]
fn dynamic_slice_range_and_index_keep_the_physical_returned_element() {
    proved(
        r#"
      (#fn at (: values (#ref-mut (#array #u8 4)) : start #usize : end #usize : index #usize) (#ref-mut #u8)
        (#let view (#slice-mut #u8) (#borrow-slice-mut (#deref values) start end))
        (#let selected (#ref-mut #u8) (#slice-mut-idx view index))
        (#forget view)
        (#return selected))
      (#theorem at-origins (#proof-contract at
        (#proof-and (#usize::le start end) (#usize::le end 4usize)
          (#usize::lt index (#usize::sub-wrap end start))) true))
      (#fn caller (: values (#ref-mut (#array #u8 4)) : start #usize : end #usize
          : index #usize : value #u8) ()
        (#let selected (#ref-mut #u8)
          (#call at (: values values : start start : end end : index index)))
        (#deref-set selected value) (#forget selected) (#return ()))
      (#theorem selected (#proof-using (at-origins)
        (#proof-contract caller
          (#proof-and (#usize::le start end) (#usize::le end 4usize)
            (#usize::lt index (#usize::sub-wrap end start)))
          (#proof-and
            (#proof-eq (#index values 0usize)
              (#if (#usize::eq (#usize::add-wrap start index) 0usize) value (#proof-old (#index values 0usize))))
            (#proof-eq (#index values 1usize)
              (#if (#usize::eq (#usize::add-wrap start index) 1usize) value (#proof-old (#index values 1usize))))
            (#proof-eq (#index values 2usize)
              (#if (#usize::eq (#usize::add-wrap start index) 2usize) value (#proof-old (#index values 2usize))))
            (#proof-eq (#index values 3usize)
              (#if (#usize::eq (#usize::add-wrap start index) 3usize) value (#proof-old (#index values 3usize))))))))
    "#,
        "selected",
    );
}

#[test]
fn projected_origin_example_matches_native_for_byte_pairs_indices_and_values() {
    use std::{fs, process::Command, time::Duration};
    let scratch = support::Scratch::new("proof-projected-origin-native");
    let mut source = include_str!("../examples/proof_projected_origins.lim").to_owned();
    source.truncate(source.find("(#fn main ").unwrap());
    source.push_str(
        r#"
      (#fn main () #u64
        (#let-mut left-index #u16 0u16)
        (#while (#u16::lt left-index 256u16)
          (#let-mut right-index #u16 0u16)
          (#while (#u16::lt right-index 256u16)
            (#let-mut index #usize 0usize)
            (#while (#usize::lt index 2usize)
              (#let-mut sample #u8 0u8)
              (#while (#u8::lt sample 3u8)
                (#let value #u8 (#if (#u8::eq sample 0u8) 0u8 (#if (#u8::eq sample 1u8) 9u8 255u8)))
                (#let left #u8 (#as left-index #u8))
                (#let right #u8 (#as right-index #u8))
                (#let-mut values (#array #u8 2) (#array-of (#array #u8 2) left right))
                (#call overwrite (: values (#borrow-mut values) : index index : value value))
                (#let expected-left #u8 (#if (#usize::eq index 0usize) value left))
                (#let expected-right #u8 (#if (#usize::eq index 1usize) value right))
                (#if (#u8::ne (#index values 0usize) expected-left) (#block (#return 1u64)))
                (#if (#u8::ne (#index values 1usize) expected-right) (#block (#return 2u64)))
                (#set sample (#u8::add-wrap sample 1u8)))
              (#set index (#usize::add-wrap index 1usize)))
            (#set right-index (#u16::add-wrap right-index 1u16)))
          (#set left-index (#u16::add-wrap left-index 1u16)))
        (#return 42u64))
    "#,
    );
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
