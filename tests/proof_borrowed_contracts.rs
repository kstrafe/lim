use lim::{CompileConfig, Diagnostic, ProofOutcome};
mod support;

fn check(source: &str, theorem: &str) -> Result<lim::CheckedTheorem, Diagnostic> {
    lim::check_theorem_details_from_path_with_config(
        source,
        std::path::Path::new("borrowed-contracts.lim"),
        &CompileConfig::default(),
        theorem,
    )
}

fn proved(source: &str, theorem: &str) {
    check(source, theorem).unwrap_or_else(|error| panic!("{}\n{source}", error.message));
}

fn rejected(source: &str, theorem: &str) -> Diagnostic {
    check(source, theorem).expect_err("the borrowed contract claim must fail closed")
}

#[test]
fn mutable_reference_contract_updates_target_and_returns_old_value() {
    proved(
        r#"
      (#fn increment (: target (#ref-mut #u8)) #u8
        (#let old #u8 (#deref target))
        (#deref-set target (#u8::add-wrap (#deref target) 1u8))
        (#return old))
      (#theorem increment-contract
        (#proof-contract increment true
          (#proof-and
            (#proof-eq (#proof-result) (#proof-old (#deref target)))
            (#proof-eq (#deref target)
              (#u8::add-wrap (#proof-old (#deref target)) 1u8)))))
      (#fn caller (: input #u8) #u8
        (#let-mut local #u8 input)
        (#let old #u8 (#call increment (: target (#borrow-mut local))))
        (#return old))
      (#theorem caller-contract
        (#proof-using (increment-contract)
          (#proof-contract caller true
            (#proof-eq (#proof-result) (#proof-old input)))))
    "#,
        "caller-contract",
    );
}

#[test]
fn selected_mutation_summary_is_not_a_specification_call() {
    let error = rejected(
        r#"
      (#fn increment (: target (#ref-mut #u8)) #u8
        (#let old #u8 (#deref target))
        (#deref-set target (#u8::add-wrap (#deref target) 1u8))
        (#return old))
      (#theorem increment-contract
        (#proof-contract increment true
          (#proof-eq (#deref target)
            (#u8::add-wrap (#proof-old (#deref target)) 1u8))))
      (#theorem invalid
        (#proof-using (increment-contract)
          (#proof-for-all (: input (#ref-mut #u8))
            (#proof-eq (#call increment (: target input)) 0u8))))
    "#,
        "invalid",
    );
    assert_eq!(
        error.proof_outcome(),
        Some(ProofOutcome::Unsupported),
        "{error:?}"
    );
}

#[test]
fn mutable_field_summary_preserves_unrelated_field() {
    proved(
        r#"
      (#struct Pair () (: first #u8 : second #u8))
      (#fn increment (: target (#ref-mut #u8)) #u8
        (#let old #u8 (#deref target))
        (#deref-set target (#u8::add-wrap (#deref target) 1u8))
        (#return old))
      (#theorem increment-contract
        (#proof-contract increment true
          (#proof-eq (#deref target)
            (#u8::add-wrap (#proof-old (#deref target)) 1u8))))
      (#fn caller (: input (#ref-mut Pair)) #u8
        (#let old #u8
          (#call increment (: target (#borrow-mut (#get (#deref input) first)))))
        (#return (#get input first)))
      (#theorem caller-contract
        (#proof-using (increment-contract)
          (#proof-contract caller true
            (#proof-and
              (#proof-eq (#proof-result)
                (#u8::add-wrap (#proof-old (#get input first)) 1u8))
              (#proof-eq (#get input second) (#proof-old (#get input second)))))))
    "#,
        "caller-contract",
    );
}

#[test]
fn writable_array_summary_requires_explicit_unchanged_index_postcondition() {
    proved(
        r#"
      (#fn update (: values (#ref-mut (#array #u8 2))) ()
        (#deref-set
          (#borrow-mut (#index (#deref values) 0usize))
          9u8)
        (#return ()))
      (#theorem update-contract
        (#proof-contract update true
          (#proof-and
            (#proof-eq (#index values 0usize) 9u8)
            (#proof-eq (#index values 1usize)
              (#proof-old (#index (#deref values) 1usize))))))
      (#fn caller (: input (#array #u8 2)) #u8
        (#let-mut values (#array #u8 2) input)
        (#call update (: values (#borrow-mut values)))
        (#return (#u8::add-wrap (#index values 0usize) (#index values 1usize))))
      (#theorem caller-contract
        (#proof-using (update-contract)
          (#proof-contract caller true
            (#proof-eq (#proof-result)
              (#u8::add-wrap 9u8 (#proof-old (#index input 1usize)))))))
    "#,
        "caller-contract",
    );
}

#[test]
fn weak_mutable_postcondition_does_not_prove_preservation_or_its_negation() {
    let source = r#"
      (#fn update (: target (#ref-mut #u8)) ()
        (#deref-set target 9u8)
        (#return ()))
      (#theorem weak (#proof-contract update true true))
      (#fn caller (: input #u8) #u8
        (#let-mut value #u8 input)
        (#call update (: target (#borrow-mut value)))
        (#return value))
      (#theorem selected
        (#proof-using (weak)
          (#proof-contract caller true (#proof-eq (#proof-result) input))))
    "#;
    let error = rejected(source, "selected");
    assert_eq!(
        error.proof_outcome(),
        Some(ProofOutcome::ContractFailure),
        "{error:?}"
    );
    let negated = source.replace(
        "(#proof-contract caller true (#proof-eq (#proof-result) input))",
        "(#proof-not (#proof-contract caller true (#proof-eq (#proof-result) input)))",
    );
    let negated_error = rejected(&negated, "selected");
    assert_eq!(
        negated_error.proof_outcome(),
        Some(ProofOutcome::ContractFailure),
        "{negated_error:?}"
    );
}

#[test]
fn readonly_reference_contract_can_be_reused() {
    proved(
        r#"
      (#fn read (: source (#ref #u8)) #u8 (#return (#deref source)))
      (#theorem read-contract
        (#proof-contract read true
          (#proof-eq (#proof-result) (#proof-old (#deref source)))))
      (#fn caller (: input #u8) #u8
        (#let result #u8 (#call read (: source (#borrow input))))
        (#return result))
      (#theorem caller-contract
        (#proof-using (read-contract)
          (#proof-contract caller true
            (#proof-eq (#proof-result) input))))
    "#,
        "caller-contract",
    );
}

#[test]
fn mutating_through_a_stored_reference_preserves_its_identity() {
    proved(
        r#"
      (#fn read (: target (#ref-mut (#ref-mut #u8))) ()
        (#deref-set (#borrow-mut (#deref (#deref target))) 9u8)
        (#return ()))
      (#theorem read-contract (#proof-contract read true
        (#proof-eq (#deref (#deref target)) 9u8)))
      (#theorem selected
        (#proof-using (read-contract)
          (#proof-contract read true (#proof-eq (#deref (#deref target)) 9u8))))
    "#,
        "selected",
    );
}

#[test]
fn raw_pointer_contracts_remain_unsupported() {
    let error = rejected(
        r#"
      (#fn identity (: source (#ptr #u8)) (#ptr #u8) (#return source))
      (#theorem identity-contract
        (#proof-contract identity true true))
      (#theorem selected (#proof-using (identity-contract) true))
    "#,
        "selected",
    );
    assert_eq!(
        error.proof_outcome(),
        Some(ProofOutcome::Unsupported),
        "{error:?}"
    );
}

#[test]
fn borrowed_summary_avoids_reexecuting_a_bounded_mutating_loop() {
    let source = r#"
      (#fn bump (: target (#ref-mut #u8) : count #u8) ()
        (#let-mut remaining #u8 count)
        (#while (#u8::gt remaining 0u8)
          (#deref-set target (#u8::add-wrap (#deref target) 1u8))
          (#set remaining (#u8::sub-wrap remaining 1u8)))
        (#return ()))
      (#theorem bump-contract (#proof-loop-limit 4
        (#proof-contract bump (#u8::le count 2u8)
          (#proof-eq (#deref target)
            (#u8::add-wrap (#proof-old (#deref target)) count)))))
      (#fn caller (: target (#ref-mut #u8) : count #u8) #u8
        (#call bump (: target target : count count))
        (#return (#deref target)))
      (#theorem selected (#proof-using (bump-contract)
        (#proof-loop-limit 1 (#proof-contract caller (#u8::le count 2u8)
          (#proof-eq (#proof-result)
            (#u8::add-wrap (#proof-old (#deref target)) count))))))"#;
    proved(source, "selected");
    let no_summary = source.replace("(#proof-using (bump-contract)", "(#proof-using ()");
    assert_eq!(
        rejected(&no_summary, "selected").proof_outcome(),
        Some(ProofOutcome::ResourceLimit)
    );
}

#[test]
fn symbolic_element_borrow_preserves_the_other_array_elements() {
    proved(
        r#"
      (#fn set (: target (#ref-mut #u8)) () (#deref-set target 9u8) (#return ()))
      (#theorem set-contract (#proof-contract set true (#proof-eq (#deref target) 9u8)))
      (#fn caller (: values (#ref-mut (#array #u8 2)) : index #usize) ()
        (#call set (: target (#borrow-mut (#index (#deref values) index))))
        (#return ()))
      (#theorem selected (#proof-using (set-contract)
        (#proof-contract caller (#usize::lt index 2usize)
          (#proof-and
            (#proof-eq (#index values index) 9u8)
            (#proof-implies (#usize::ne index 0usize)
              (#proof-eq (#index values 0usize) (#proof-old (#index values 0usize))))
            (#proof-implies (#usize::ne index 1usize)
              (#proof-eq (#index values 1usize) (#proof-old (#index values 1usize))))))))"#,
        "selected",
    );
}

#[test]
fn summary_writes_merge_enum_tags_and_payloads_at_a_symbolic_index() {
    proved(
        r#"
      (#enum Choice () (: Choice.Empty : Choice.Value #u8))
      (#fn set (: target (#ref-mut Choice)) ()
        (#deref-set target (#enum-literal Choice.Value 9u8)) (#return ()))
      (#theorem set-contract (#proof-contract set true
        (#proof-eq (#deref target) (#enum-literal Choice.Value 9u8))))
      (#fn caller (: values (#ref-mut (#array Choice 2)) : index #usize) ()
        (#call set (: target (#borrow-mut (#index (#deref values) index))))
        (#return ()))
      (#theorem selected (#proof-using (set-contract)
        (#proof-contract caller (#usize::lt index 2usize)
          (#proof-and
            (#proof-eq (#index values index) (#enum-literal Choice.Value 9u8))
            (#proof-implies (#usize::ne index 0usize)
              (#proof-eq (#index values 0usize) (#proof-old (#index values 0usize))))
            (#proof-implies (#usize::ne index 1usize)
              (#proof-eq (#index values 1usize) (#proof-old (#index values 1usize))))))))"#,
        "selected",
    );
}

#[test]
fn aliased_shared_inputs_retain_the_same_referent_values() {
    proved(
        r#"
      (#fn equal (: left (#ref #u8) : right (#ref #u8)) #bool
        (#return (#u8::eq (#deref left) (#deref right))))
      (#theorem equal-contract (#proof-contract equal true
        (#proof-eq (#proof-result) (#u8::eq (#deref left) (#deref right)))))
      (#fn caller (: value #u8) #bool
        (#return (#call equal (: left (#borrow value) : right (#borrow value)))))
      (#theorem selected (#proof-using (equal-contract)
        (#proof-contract caller true (#proof-result))))"#,
        "selected",
    );
}

#[test]
fn references_inside_owned_records_are_included_in_the_write_frame() {
    proved(
        r#"
      (#struct Handle () (: target (#ref-mut #u8)))
      (#fn write (: handle Handle) ()
        (#deref-set (#get handle target) 9u8) (#forget handle) (#return ()))
      (#theorem write-contract (#proof-contract write true
        (#proof-eq (#deref (#get handle target)) 9u8)))
      (#fn caller (: input (#ref-mut #u8)) ()
        (#let handle Handle (#struct-literal Handle (: target input)))
        (#call write (: handle handle)) (#return ()))
      (#theorem selected (#proof-using (write-contract)
        (#proof-contract caller true (#proof-eq (#deref input) 9u8))))"#,
        "selected",
    );
}

#[test]
fn enum_arguments_only_expose_the_active_mutable_payload() {
    proved(
        r#"
      (#enum Destination (#linear) (: Destination.Skip : Destination.Write (#ref-mut #u8)))
      (#fn write (: entry Destination) ()
        (#match entry
          (#case Destination.Skip ())
          (#case (Destination.Write target) (#deref-set target 9u8)))
        (#return ()))
      (#theorem write-contract (#proof-contract write true
        (#match entry
          (#case Destination.Skip true)
          (#case (Destination.Write target) (#proof-eq (#deref target) 9u8)))))
      (#fn caller (: entry Destination : watched (#ref-mut #u8)) #u8
        (#call write (: entry entry)) (#return (#deref watched)))
      (#theorem selected (#proof-using (write-contract)
        (#proof-contract caller true
          (#proof-eq (#proof-result) (#proof-old (#deref watched))))))"#,
        "selected",
    );
}

#[test]
fn enum_updates_preserve_initially_inactive_constructor_payloads() {
    proved(
        r#"
      (#enum Choice () (: Choice.Empty : Choice.Value #u8))
      (#fn set (: target (#ref-mut Choice)) ()
        (#deref-set target (#enum-literal Choice.Value 9u8)) (#return ()))
      (#theorem set-contract (#proof-contract set true
        (#proof-eq (#deref target) (#enum-literal Choice.Value 9u8))))
      (#fn caller (: index #usize) (#array Choice 2)
        (#let-mut values (#array Choice 2) (#array-of (#array Choice 2)
          (#enum-literal Choice.Empty) (#enum-literal Choice.Value 7u8)))
        (#call set (: target (#borrow-mut (#index values index))))
        (#return values))
      (#theorem selected (#proof-using (set-contract)
        (#proof-contract caller (#usize::lt index 2usize)
          (#proof-and
            (#proof-eq (#index (#proof-result) index) (#enum-literal Choice.Value 9u8))
            (#proof-implies (#usize::ne index 0usize)
              (#proof-eq (#index (#proof-result) 0usize) (#enum-literal Choice.Empty)))
            (#proof-implies (#usize::ne index 1usize)
              (#proof-eq (#index (#proof-result) 1usize) (#enum-literal Choice.Value 7u8)))))))"#,
        "selected",
    );
}

#[test]
fn element_borrow_from_a_slice_keeps_the_original_backing_frame() {
    proved(
        r#"
      (#fn set (: target (#ref-mut #u8)) () (#deref-set target 9u8) (#return ()))
      (#theorem set-contract (#proof-contract set true (#proof-eq (#deref target) 9u8)))
      (#fn caller (: values (#ref-mut (#array #u8 4)) : index #usize) ()
        (#let whole (#slice-mut #u8) (#slice-mut-of values))
        (#let middle (#slice-mut #u8) (#slice-mut-range whole 1usize 3usize))
        (#call set (: target (#slice-mut-idx middle index)))
        (#forget middle) (#forget whole) (#return ()))
      (#theorem selected (#proof-using (set-contract)
        (#proof-contract caller (#usize::lt index 2usize)
          (#proof-and
            (#proof-eq (#index values (#usize::add-wrap index 1usize)) 9u8)
            (#proof-eq (#index values 0usize) (#proof-old (#index values 0usize)))
            (#proof-eq (#index values 3usize) (#proof-old (#index values 3usize)))))))"#,
        "selected",
    );
}

#[test]
fn oversized_write_frames_remain_resource_limits_under_negation() {
    let types = vec!["(#ref-mut #u8)"; 257].join(" ");
    for contract in [
        "(#proof-contract touch true true)",
        "(#proof-not (#proof-contract touch true true))",
    ] {
        let source = format!(
            r#"
          (#fn touch (: values (#tuple {types})) ()
            (#deref-set (#get values 0) 9u8) (#forget values) (#return ()))
          (#theorem touch-contract (#proof-contract touch true true))
          (#theorem selected (#proof-using (touch-contract) {contract}))"#
        );
        let error = rejected(&source, "selected");
        assert_eq!(
            error.proof_outcome(),
            Some(ProofOutcome::ResourceLimit),
            "{error:?}"
        );
        assert!(
            error.message.contains("writable-location budget"),
            "{}",
            error.message
        );
    }
}

#[test]
fn a_readonly_function_preserves_a_mutable_argument_in_specifications() {
    proved(
        r#"
      (#fn read (: target (#ref-mut #u8)) #u8 (#return (#deref target)))
      (#theorem read-contract (#proof-contract read true
        (#proof-eq (#proof-result) (#deref target))))
      (#theorem selected (#proof-using (read-contract)
        (#proof-for-all (: target (#ref-mut #u8))
          (#proof-eq (#call read (: target target)) (#deref target)))))"#,
        "selected",
    );
}

#[test]
fn borrowed_example_matches_native_for_every_byte_and_supported_count() {
    use std::{fs, process::Command, time::Duration};
    let scratch = support::Scratch::new("proof-borrowed-native");
    let mut source = fs::read_to_string(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("examples/proof_borrowed_contracts.lim"),
    )
    .unwrap();
    source.truncate(source.find("(#fn main ").unwrap());
    source.push_str(
        r#"
      (#fn main () #u64
        (#let-mut index #u16 0u16)
        (#while (#u16::lt index 256u16)
          (#let initial #u8 (#as index #u8))
          (#let-mut count #u8 0u8)
          (#while (#u8::le count 2u8)
            (#let-mut pair Pair (#struct-literal Pair (: total initial : untouched 7u8)))
            (#let actual #u8 (#call work (: pair (#borrow-mut pair) : count count)))
            (#if (#u8::ne actual (#u8::add-wrap initial count)) (#block (#return 1u64)))
            (#if (#u8::ne (#get pair untouched) 7u8) (#block (#return 2u64)))
            (#set count (#u8::add-wrap count 1u8)))
          (#set index (#u16::add-wrap index 1u16)))
        (#return 42u64))"#,
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
        Duration::from_secs(5),
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
