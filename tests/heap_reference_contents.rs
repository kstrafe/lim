use std::{process::Command, time::Duration};
mod support;

fn compile(source: &str) -> Result<String, lim::Diagnostic> {
    let scratch = support::Scratch::new("heap-reference-check");
    lim::compile_source_to_assembly(
        source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
}

fn run(source: &str) {
    let scratch = support::Scratch::new("heap-reference-run");
    let assembly = compile(source).unwrap_or_else(|e| panic!("{}", e.message));
    let binary = scratch.path().join("program");
    lim::link_native_binary(
        &assembly,
        &binary,
        &[],
        &[],
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    let (status, stdout, stderr) =
        support::run(&mut Command::new(binary), Duration::from_secs(5), 4096).unwrap();
    assert_eq!(status.code(), Some(42), "{stderr:?}");
    assert!(stdout.is_empty() && stderr.is_empty());
}

const PREFIX: &str = r#"
#struct Holder () ((link (#ref #u64)))
#fn make {
  #params = ((pointer (#ptr-mut Holder)) (source (#ref #u64)));
  #returns = (#pin-own Holder);
  #body = (
      (#return (#unsafe (#pin-own-of pointer (#struct-literal Holder ((link source))))))
  );
}
#fn forward {
  #params = ((owner (#pin-own Holder)));
  #returns = (#pin-own Holder);
  #body = ( (#return owner)
  );
}
#fn get {
  #params = ((owner (#ref (#pin-own Holder))));
  #returns = (#ref #u64);
  #body = (
      (#let view (#pin-ref Holder) (#pin-own-borrow owner))
      (#return (#get view link))
  );
}
#fn destroy {
  #params = ((owner (#pin-own Holder)));
  #returns = ();
  #body = (
      (#let pointer (#ptr-mut Holder) (#unsafe (#pin-release owner)))
      (#assert (#i64::eq (#unsafe (#linux-syscall #i64 11usize (pointer 4096usize))) 0i64))
      (#return ())
  );
}
"#;

const OWNER_CELL: &str = r#"
#enum OwnerCell (#linear) ((OwnerCell.Empty ()) (OwnerCell.Full (#pin-own Holder)))

#fn take-owner {
  #params = ((cell (#pin-ref-mut OwnerCell)));
  #returns = (#pin-own Holder);
  #body = (
      (#let previous OwnerCell (#unsafe (#pin-read cell)))
      (#unsafe (#pin-write cell (OwnerCell.Empty ())))
      (#return (#match previous
        (#case (OwnerCell.Empty unit) (#unreachable))
        (#case (OwnerCell.Full owner) owner)))
  );
}
"#;

#[test]
fn a_pinned_cell_extraction_definition_preserves_owned_allocation_slots() {
    compile(&format!("{PREFIX} {OWNER_CELL}")).unwrap_or_else(|error| panic!("{error:?}"));
}

#[test]
fn extracted_heap_owner_can_be_read_by_a_later_call() {
    let source = format!(
        r#"{PREFIX} {OWNER_CELL}
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
          (#let-mut source #u64 42u64)
          (#let pointer (#ptr-mut Holder) (#unsafe (#linux-syscall (#ptr-mut Holder) 9usize
            (0usize 4096usize 3usize 34usize -1i64 0usize))))
          (#let-mut cell OwnerCell (OwnerCell.Full (#call make ((pointer pointer) (source (#borrow source))))))
          (#let view (#pin-ref-mut OwnerCell) (#pin-borrow-mut cell))
          (#let owner (#pin-own Holder) (#call take-owner ((cell view))))
          (#drop view) (#forget cell)
          (#let result (#ref #u64) (#call get ((owner (#borrow owner)))))
          (#call destroy ((owner owner)))
          (#return (#deref result))
  );
}}
"#
    );
    run(&source);
    let invalid = source.replace(
        "(#drop view) (#forget cell)",
        "(#drop view) (#forget cell) (#set source 0u64)",
    );
    let error = compile(&invalid).expect_err("the extracted owner retains its source loan");
    assert_eq!(error.code_string(), "E4100", "{}", error.message);
}

#[test]
fn an_extracted_owner_cannot_outlive_its_external_referent() {
    let source = format!(
        r#"{PREFIX} {OWNER_CELL}
#fn bad {{
  #params = ((pointer (#ptr-mut Holder)));
  #returns = (#pin-own Holder);
  #body = (
          (#let source #u64 42u64)
          (#let-mut cell OwnerCell (OwnerCell.Full (#call make ((pointer pointer) (source (#borrow source))))))
          (#let view (#pin-ref-mut OwnerCell) (#pin-borrow-mut cell))
          (#let owner (#pin-own Holder) (#call take-owner ((cell view))))
          (#drop view) (#forget cell)
          (#return owner)
  );
}}
"#
    );
    let error = compile(&source).expect_err("extraction must not erase the stored lifetime");
    assert_eq!(error.code_string(), "E4100", "{}", error.message);
}

#[test]
fn heap_contents_retain_external_references_through_owner_moves_and_calls() {
    run(&format!(
        r#"{PREFIX}
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
          (#let source #u64 42u64)
          (#let pointer (#ptr-mut Holder) (#unsafe (#linux-syscall (#ptr-mut Holder) 9usize
            (0usize 4096usize 3usize 34usize -1i64 0usize))))
          (#let owner (#pin-own Holder) (#call make ((pointer pointer) (source (#borrow source)))))
          (#let moved (#pin-own Holder) (#call forward ((owner owner))))
          (#let result (#ref #u64) (#call get ((owner (#borrow moved)))))
          (#call destroy ((owner moved)))
          (#return (#deref result))
  );
}}
"#
    ));
}

#[test]
fn owner_cannot_outlive_a_reference_stored_in_its_allocation() {
    let source = format!(
        r#"{PREFIX}
#fn bad {{
  #params = ((pointer (#ptr-mut Holder)));
  #returns = (#pin-own Holder);
  #body = (
          (#let local #u64 42u64)
          (#return (#call make ((pointer pointer) (source (#borrow local)))))
  );
}}
"#
    );
    let error = compile(&source).expect_err("heap allocation does not extend the local lifetime");
    assert_eq!(error.code_string(), "E4100", "{}", error.message);
}

#[test]
fn stored_reference_keeps_source_borrowed_until_the_heap_owner_is_consumed() {
    let source = format!(
        r#"{PREFIX}
#fn bad {{
  #params = ((pointer (#ptr-mut Holder)));
  #returns = ();
  #body = (
          (#let-mut source #u64 42u64)
          (#let owner (#pin-own Holder) (#call make ((pointer pointer) (source (#borrow source)))))
          (#set source 0u64)
          (#let view (#ref #u64) (#call get ((owner (#borrow owner)))))
          (#assert (#u64::eq (#deref view) 42u64))
          (#call destroy ((owner owner))) (#return ())
  );
}}
"#
    );
    let error =
        compile(&source).expect_err("source cannot change while retained in the heap owner");
    assert_eq!(error.code_string(), "E4100", "{}", error.message);
}

#[test]
fn direct_heap_field_writes_track_the_new_source_without_rewriting_it() {
    let source = format!(
        r#"{PREFIX}
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
          (#let first #u64 1u64) (#let-mut second #u64 42u64)
          (#let pointer (#ptr-mut Holder) (#unsafe (#linux-syscall (#ptr-mut Holder) 9usize
            (0usize 4096usize 3usize 34usize -1i64 0usize))))
          (#let-mut owner (#pin-own Holder) (#call make ((pointer pointer) (source (#borrow first)))))
          (#let view (#pin-ref-mut Holder) (#pin-own-borrow-mut owner))
          (#pin-set-field view link (#borrow second))
          (#drop view)
          (#let result (#ref #u64) (#call get ((owner (#borrow owner)))))
          (#call destroy ((owner owner))) (#return (#deref result))
  );
}}
"#
    );
    run(&source);
    let bad = source.replace("(#drop view)", "(#drop view) (#set second 0u64)");
    let error = compile(&bad)
        .err()
        .expect("direct stores retain the replacement source");
    assert_eq!(error.code_string(), "E4100", "{}", error.message);
    assert!(error.message.contains("second"), "{}", error.message);
}

#[test]
fn definite_heap_field_replacement_retires_only_the_old_source_loan() {
    let source = format!(
        r#"{PREFIX}
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
          (#let-mut first #u64 1u64) (#let-mut second #u64 42u64)
          (#let pointer (#ptr-mut Holder) (#unsafe (#linux-syscall (#ptr-mut Holder) 9usize
            (0usize 4096usize 3usize 34usize -1i64 0usize))))
          (#let-mut owner (#pin-own Holder) (#call make ((pointer pointer) (source (#borrow first)))))
          (#let view (#pin-ref-mut Holder) (#pin-own-borrow-mut owner))
          (#pin-set-field view link (#borrow second))
          (#drop view)
          (#set first 0u64)
          (#let result (#ref #u64) (#call get ((owner (#borrow owner)))))
          (#call destroy ((owner owner))) (#return (#deref result))
  );
}}
"#
    );
    run(&source);

    let invalid = source.replace("(#set first 0u64)", "(#set second 0u64)");
    let error = compile(&invalid).expect_err("the replacement reference remains borrowed");
    assert_eq!(error.code_string(), "E4100", "{}", error.message);
    assert!(error.message.contains("second"), "{}", error.message);
}

#[test]
fn replacement_does_not_retire_a_reference_already_loaded_from_the_old_field() {
    let prefix = format!(
        r#"{PREFIX}
#fn replace {{
  #params = ((owner (#ref-mut (#pin-own Holder))) (value (#ref #u64)));
  #returns = ();
  #body = (
          (#let view (#pin-ref-mut Holder) (#pin-own-borrow-mut owner))
          (#pin-set-field view link value) (#return ())
  );
}}
"#
    );
    let invalid = format!(
        r#"{prefix}
#fn bad {{
  #params = ((pointer (#ptr-mut Holder)));
  #returns = ();
  #body = (
          (#let-mut first #u64 1u64) (#let second #u64 42u64)
          (#let-mut owner (#pin-own Holder) (#call make ((pointer pointer) (source (#borrow first)))))
          (#let previous (#ref #u64) (#call get ((owner (#borrow owner)))))
          (#call replace ((owner (#borrow-mut owner)) (value (#borrow second))))
          (#set first 0u64)
          (#call destroy ((owner owner))) (#return ())
  );
}}
"#
    );
    let error = compile(&invalid).expect_err("the extracted reference still borrows first");
    assert_eq!(error.code_string(), "E4100", "{}", error.message);
    assert!(error.message.contains("first"), "{}", error.message);

    let valid = invalid
        .replace("(#set first 0u64)", "(#drop previous) (#set first 0u64)")
        .replace("#fn bad", "#fn main");
    compile(&valid).unwrap_or_else(|error| panic!("{}", error.message));
}

#[test]
fn branch_join_retains_each_possible_heap_field_referent() {
    let source = format!(
        r#"{PREFIX}
#fn exercise {{
  #params = ((pointer (#ptr-mut Holder)) (replace #bool));
  #returns = ();
  #body = (
          (#let-mut first #u64 1u64) (#let-mut second #u64 2u64)
          (#let-mut owner (#pin-own Holder) (#call make ((pointer pointer) (source (#borrow first)))))
          (#if replace
            (#block
              (#let view (#pin-ref-mut Holder) (#pin-own-borrow-mut owner))
              (#pin-set-field view link (#borrow second)) (#drop view))
            ())
          (#set first 0u64)
          (#call destroy ((owner owner))) (#return ())
  );
}}
"#
    );
    let first = compile(&source).expect_err("the non-replacing branch still contains first");
    assert_eq!(first.code_string(), "E4100", "{}", first.message);
    assert!(first.message.contains("first"), "{}", first.message);

    let second = compile(&source.replace("(#set first 0u64)", "(#set second 0u64)"))
        .expect_err("the replacing branch contains second");
    assert_eq!(second.code_string(), "E4100", "{}", second.message);
    assert!(second.message.contains("second"), "{}", second.message);
}

#[test]
fn loop_join_keeps_pre_loop_and_written_heap_field_referents() {
    let source = format!(
        r#"{PREFIX}
#fn exercise {{
  #params = ((pointer (#ptr-mut Holder)) (replace #bool));
  #returns = ();
  #body = (
          (#let-mut first #u64 1u64) (#let-mut second #u64 2u64)
          (#let-mut owner (#pin-own Holder) (#call make ((pointer pointer) (source (#borrow first)))))
          (#while replace
            (#block
              (#let view (#pin-ref-mut Holder) (#pin-own-borrow-mut owner))
              (#pin-set-field view link (#borrow second)) (#drop view)))
          (#set first 0u64)
          (#call destroy ((owner owner))) (#return ())
  );
}}
"#
    );
    let first = compile(&source).expect_err("the loop may execute zero times");
    assert_eq!(first.code_string(), "E4100", "{}", first.message);
    assert!(first.message.contains("first"), "{}", first.message);

    let second = compile(&source.replace("(#set first 0u64)", "(#set second 0u64)"))
        .expect_err("the loop may execute and leave second stored");
    assert_eq!(second.code_string(), "E4100", "{}", second.message);
    assert!(second.message.contains("second"), "{}", second.message);
}

#[test]
fn uncertain_heap_destination_keeps_all_candidate_contents() {
    let source = r#"#struct Holder () ((link (#ref #u64)))
#fn make {
  #params = ((pointer (#ptr-mut Holder)) (source (#ref #u64)));
  #returns = (#pin-own Holder);
  #body = (
          (#return (#unsafe (#pin-own-of pointer (#struct-literal Holder ((link source))))))
  );
}
#fn destroy {
  #params = ((owner (#pin-own Holder)));
  #returns = ();
  #body = ( (#forget owner) (#return ())
  );
}
#fn exercise {
  #params = ((first-pointer (#ptr-mut Holder)) (second-pointer (#ptr-mut Holder)) (choose #bool));
  #returns = ();
  #body = (
          (#let-mut first #u64 1u64) (#let-mut second #u64 2u64)
          (#let-mut first-owner (#pin-own Holder) (#call make ((pointer first-pointer) (source (#borrow first)))))
          (#let-mut second-owner (#pin-own Holder) (#call make ((pointer second-pointer) (source (#borrow second)))))
          (#let view (#pin-ref-mut Holder)
            (#if choose (#pin-own-borrow-mut first-owner) (#pin-own-borrow-mut second-owner)))
          (#let replacement (#ref #u64) (#if choose (#borrow second) (#borrow first)))
          (#pin-set-field view link replacement)
          (#drop view) (#drop replacement)
          (#set first 0u64)
          (#call destroy ((owner first-owner))) (#call destroy ((owner second-owner)))
          (#return ())
  );
}
"#;
    let first = compile(source).expect_err("either owner may still contain first");
    assert_eq!(first.code_string(), "E4100", "{}", first.message);
    assert!(first.message.contains("first"), "{}", first.message);

    let second = compile(&source.replace("(#set first 0u64)", "(#set second 0u64)"))
        .expect_err("either owner may still contain second");
    assert_eq!(second.code_string(), "E4100", "{}", second.message);
    assert!(second.message.contains("second"), "{}", second.message);
}

#[test]
fn direct_reference_pointees_keep_provenance_after_heap_owner_release() {
    let source = r#"#fn main {
  #params = ();
  #returns = #u64;
  #body = (
        (#let-mut source #u64 42u64)
        (#let pointer (#ptr-mut (#ref #u64)) (#unsafe (#linux-syscall (#ptr-mut (#ref #u64)) 9usize
          (0usize 4096usize 3usize 34usize -1i64 0usize))))
        (#let owner (#pin-own (#ref #u64)) (#unsafe (#pin-own-of pointer (#borrow source))))
        (#let view (#pin-ref (#ref #u64)) (#pin-own-borrow owner))
        (#let result (#ref #u64) (#deref view))
        (#drop view)
        (#let raw (#ptr-mut (#ref #u64)) (#unsafe (#pin-release owner)))
        (#assert (#i64::eq (#unsafe (#linux-syscall #i64 11usize (raw 4096usize))) 0i64))
        (#return (#deref result))
  );
}
"#;
    run(source);
    let bad = source.replace(
        "(#return (#deref result))",
        "(#set source 0u64) (#return (#deref result))",
    );
    let error = compile(&bad)
        .expect_err("loaded reference remains anchored to source, not freed pointer storage");
    assert_eq!(error.code_string(), "E4100", "{}", error.message);
}

#[test]
fn heap_reference_replacement_does_not_lose_a_new_borrow() {
    let source = format!(
        r#"{PREFIX}
#fn replace {{
  #params = ((owner (#ref-mut (#pin-own Holder))) (value (#ref #u64)));
  #returns = ();
  #body = (
          (#let view (#pin-ref-mut Holder) (#pin-own-borrow-mut owner))
          (#pin-set-field view link value)
          (#return ())
  );
}}
#fn bad {{
  #params = ((pointer (#ptr-mut Holder)));
  #returns = ();
  #body = (
          (#let first #u64 1u64)
          (#let-mut second #u64 2u64)
          (#let-mut owner (#pin-own Holder) (#call make ((pointer pointer) (source (#borrow first)))))
          (#call replace ((owner (#borrow-mut owner)) (value (#borrow second))))
          (#set second 3u64)
          (#let result (#ref #u64) (#call get ((owner (#borrow owner)))))
          (#assert (#u64::eq (#deref result) 2u64))
          (#call destroy ((owner owner))) (#return ())
  );
}}
"#
    );
    let error =
        compile(&source).expect_err("replacement must retain its new source or fail closed");
    assert_eq!(error.code_string(), "E4100", "{}", error.message);
    assert!(error.message.contains("second"), "{}", error.message);
}

#[test]
fn updated_contents_follow_an_owner_returned_by_a_helper() {
    let source = format!(
        r#"{PREFIX}
#fn replace-owned {{
  #params = ((owner (#pin-own Holder)) (value (#ref #u64)));
  #returns = (#pin-own Holder);
  #body = (
          (#let-mut moved (#pin-own Holder) owner)
          (#let view (#pin-ref-mut Holder) (#pin-own-borrow-mut moved))
          (#pin-set-field view link value)
          (#drop view)
          (#return moved)
  );
}}
#fn bad {{
  #params = ((pointer (#ptr-mut Holder)));
  #returns = ();
  #body = (
          (#let first #u64 1u64)
          (#let-mut second #u64 2u64)
          (#let owner (#pin-own Holder) (#call make ((pointer pointer) (source (#borrow first)))))
          (#let updated (#pin-own Holder) (#call replace-owned ((owner owner) (value (#borrow second)))))
          (#set second 3u64)
          (#let result (#ref #u64) (#call get ((owner (#borrow updated)))))
          (#assert (#u64::eq (#deref result) 2u64))
          (#call destroy ((owner updated))) (#return ())
  );
}}
"#
    );
    let error = compile(&source)
        .err()
        .expect("returned owner must retain the replacement source");
    assert_eq!(error.code_string(), "E4100", "{}", error.message);
    assert!(error.message.contains("second"), "{}", error.message);
    compile(&source.replace("(#set second 3u64)", "()"))
        .unwrap_or_else(|e| panic!("{}", e.message));
}

#[test]
fn definite_helper_replacement_retires_the_old_heap_field_loan() {
    let source = format!(
        r#"{PREFIX}
#fn replace-owned {{
  #params = ((owner (#pin-own Holder)) (value (#ref #u64)));
  #returns = (#pin-own Holder);
  #body = (
          (#let-mut moved (#pin-own Holder) owner)
          (#let view (#pin-ref-mut Holder) (#pin-own-borrow-mut moved))
          (#pin-set-field view link value)
          (#drop view)
          (#return moved)
  );
}}
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
          (#let-mut first #u64 1u64) (#let second #u64 42u64)
          (#let pointer (#ptr-mut Holder) (#unsafe (#linux-syscall (#ptr-mut Holder) 9usize
            (0usize 4096usize 3usize 34usize -1i64 0usize))))
          (#let owner (#pin-own Holder) (#call make ((pointer pointer) (source (#borrow first)))))
          (#let updated (#pin-own Holder) (#call replace-owned ((owner owner) (value (#borrow second)))))
          (#set first 0u64)
          (#let result (#ref #u64) (#call get ((owner (#borrow updated)))))
          (#call destroy ((owner updated))) (#return (#deref result))
  );
}}
"#
    );
    run(&source);
}

#[test]
fn a_helper_cannot_store_a_shorter_lived_reference_in_a_surviving_owner() {
    let source = format!(
        r#"{PREFIX}
#fn replace {{
  #params = ((owner (#ref-mut (#pin-own Holder))) (value (#ref #u64)));
  #returns = ();
  #body = (
          (#let view (#pin-ref-mut Holder) (#pin-own-borrow-mut owner))
          (#pin-set-field view link value) (#return ())
  );
}}
#fn bad {{
  #params = ((pointer (#ptr-mut Holder)));
  #returns = ();
  #body = (
          (#let first #u64 1u64)
          (#let-mut owner (#pin-own Holder) (#call make ((pointer pointer) (source (#borrow first)))))
          (#block
            (#let short #u64 2u64)
            (#call replace ((owner (#borrow-mut owner)) (value (#borrow short)))))
          (#let result (#ref #u64) (#call get ((owner (#borrow owner)))))
          (#assert (#u64::eq (#deref result) 2u64))
          (#call destroy ((owner owner))) (#return ())
  );
}}
"#
    );
    let error = compile(&source)
        .err()
        .expect("heap storage must not extend the replacement source's lifetime");
    assert_eq!(error.code_string(), "E4100", "{}", error.message);
    assert!(error.message.contains("short"), "{}", error.message);
}

#[test]
fn replaced_contents_are_read_from_the_heap() {
    run(&format!(
        r#"{PREFIX}
#fn replace {{
  #params = ((owner (#ref-mut (#pin-own Holder))) (value (#ref #u64)));
  #returns = ();
  #body = (
          (#let view (#pin-ref-mut Holder) (#pin-own-borrow-mut owner))
          (#pin-set-field view link value) (#return ())
  );
}}
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
          (#let first #u64 1u64) (#let second #u64 42u64)
          (#let pointer (#ptr-mut Holder) (#unsafe (#linux-syscall (#ptr-mut Holder) 9usize
            (0usize 4096usize 3usize 34usize -1i64 0usize))))
          (#let-mut owner (#pin-own Holder) (#call make ((pointer pointer) (source (#borrow first)))))
          (#call replace ((owner (#borrow-mut owner)) (value (#borrow second))))
          (#let result (#ref #u64) (#call get ((owner (#borrow owner)))))
          (#call destroy ((owner owner))) (#return (#deref result))
  );
}}
"#
    ));
}

#[test]
fn nested_heap_owners_keep_all_stored_reference_lifetimes() {
    let prefix = format!(
        r#"{PREFIX}
#struct Outer () ((inner (#pin-own Holder)))
#fn wrap {{
  #params = ((pointer (#ptr-mut Outer)) (inner (#pin-own Holder)));
  #returns = (#pin-own Outer);
  #body = (
          (#return (#unsafe (#pin-own-of pointer (#struct-literal Outer ((inner inner))))))
  );
}}
#fn erase {{
  #params = ((owner (#pin-own Outer)));
  #returns = ();
  #body = ( (#forget owner) (#return ())
  );
}}
"#
    );
    let source = format!(
        r#"{prefix}
#fn bad {{
  #params = ((outer-pointer (#ptr-mut Outer)) (inner-pointer (#ptr-mut Holder)));
  #returns = ();
  #body = (
          (#let-mut source #u64 42u64)
          (#let inner (#pin-own Holder) (#call make ((pointer inner-pointer) (source (#borrow source)))))
          (#let outer (#pin-own Outer) (#call wrap ((pointer outer-pointer) (inner inner))))
          (#set source 0u64)
          (#call erase ((owner outer))) (#return ())
  );
}}
"#
    );
    let error = compile(&source)
        .err()
        .expect("nested owners retain their reference contents");
    assert_eq!(error.code_string(), "E4100", "{}", error.message);
    assert!(error.message.contains("source"), "{}", error.message);
    let escaping = format!(
        r#"{prefix}
#fn bad {{
  #params = ((outer-pointer (#ptr-mut Outer)) (inner-pointer (#ptr-mut Holder)));
  #returns = (#pin-own Outer);
  #body = (
          (#let local #u64 42u64)
          (#let inner (#pin-own Holder) (#call make ((pointer inner-pointer) (source (#borrow local)))))
          (#return (#call wrap ((pointer outer-pointer) (inner inner))))
  );
}}
"#
    );
    let error = compile(&escaping)
        .err()
        .expect("a second allocation cannot extend a local's lifetime");
    assert_eq!(error.code_string(), "E4100", "{}", error.message);
    assert!(error.message.contains("local"), "{}", error.message);
}

#[test]
fn storing_an_exclusive_reference_in_heap_storage_blocks_other_borrows() {
    let prefix = r#"#struct Exclusive () ((link (#ref-mut #u64)))
#fn make {
  #params = ((pointer (#ptr-mut Exclusive)) (source (#ref-mut #u64)));
  #returns = (#pin-own Exclusive);
  #body = (
          (#return (#unsafe (#pin-own-of pointer (#struct-literal Exclusive ((link source))))))
  );
}
#fn erase {
  #params = ((owner (#pin-own Exclusive)));
  #returns = ();
  #body = ( (#forget owner) (#return ())
  );
}
"#;
    for operation in [
        "(#let other (#ref #u64) (#borrow source))",
        "(#let other (#ref-mut #u64) (#borrow-mut source))",
        "(#set source 0u64)",
    ] {
        let source = format!(
            r#"{prefix}
#fn bad {{
  #params = ((pointer (#ptr-mut Exclusive)));
  #returns = ();
  #body = (
              (#let-mut source #u64 42u64)
              (#let owner (#pin-own Exclusive) (#call make ((pointer pointer) (source (#borrow-mut source)))))
              {operation}
              (#call erase ((owner owner))) (#return ())
  );
}}
"#
        );
        let error = compile(&source)
            .err()
            .expect("heap-retained exclusive references cannot be aliased");
        assert_eq!(error.code_string(), "E4100", "{}", error.message);
        assert!(error.message.contains("source"), "{}", error.message);
    }
}

#[test]
fn stored_exclusive_field_blocks_a_later_borrow_of_its_external_referent() {
    let source = r#"#struct Holder () ((link (#ref-mut #u64)))
#fn use-both {
  #params = ((holder (#ref-mut Holder)) (source (#ref #u64)));
  #returns = ();
  #body = ( (#return ())
  );
}
#fn main {
  #params = ();
  #returns = ();
  #body = (
          (#let-mut value #u64 1u64)
          (#let child (#ref-mut #u64) (#borrow-mut value))
          (#let-mut holder Holder (#struct-literal Holder ((link child))))
          (#call use-both ((holder (#borrow-mut holder)) (source (#borrow value))))
          (#forget holder) (#return ())
  );
}
"#;
    let error = compile(source)
        .expect_err("the reference stored in Holder still exclusively borrows value");
    assert_eq!(error.code_string(), "E4100", "{}", error.message);
    assert!(error.message.contains("value"), "{}", error.message);

    let moved = source
        .replace(
            "#params = ((holder (#ref-mut Holder)) (source (#ref #u64)));\n  #returns = ();\n  #body = ( (#return ())",
            "#params = ((holder Holder) (source (#ref #u64)));\n  #returns = Holder;\n  #body = ( (#return holder)",
        )
        .replace(
            "((holder (#borrow-mut holder)) (source (#borrow value)))",
            "((holder holder) (source (#borrow value)))",
        )
        .replace(
            "(#call use-both ((holder holder) (source (#borrow value))))",
            "(#let result Holder (#call use-both ((holder holder) (source (#borrow value))))) (#forget result)",
        )
        .replace("(#forget holder) (#return ())", "(#return ())");
    let error = compile(&moved)
        .expect_err("moving the holder into a call must transfer its nested exclusive loan");
    assert_eq!(error.code_string(), "E4100", "{}", error.message);
    assert!(
        error.message.contains("overlapping borrows"),
        "{}",
        error.message
    );
}
