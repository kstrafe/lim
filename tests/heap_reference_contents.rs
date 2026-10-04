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
  (#struct Holder (: link (#ref u64)))
  (#fn make (: pointer (#ptr-mut Holder) : source (#ref u64)) (#pin-own Holder)
    (#return (#unsafe (#pin-own-of pointer (#struct-literal Holder (: link source))))))
  (#fn forward (: owner (#pin-own Holder)) (#pin-own Holder) (#return owner))
  (#fn get (: owner (#ref (#pin-own Holder))) (#ref u64)
    (#let view (#pin-ref Holder) (#pin-own-borrow owner))
    (#return (#get view link)))
  (#fn destroy (: owner (#pin-own Holder)) ()
    (#let pointer (#ptr-mut Holder) (#unsafe (#pin-release owner)))
    (#assert (#i64.== (#unsafe (#linux-syscall i64 11usize (pointer 4096usize))) 0i64))
    (#return ()))
"#;

#[test]
fn heap_contents_retain_external_references_through_owner_moves_and_calls() {
    run(&format!(
        r#"{PREFIX}
      (#fn main () u64
        (#let source u64 42u64)
        (#let pointer (#ptr-mut Holder) (#unsafe (#linux-syscall (#ptr-mut Holder) 9usize
          (0usize 4096usize 3usize 34usize -1i64 0usize))))
        (#let owner (#pin-own Holder) (#call make (: pointer pointer : source (#borrow source))))
        (#let moved (#pin-own Holder) (#call forward (: owner owner)))
        (#let result (#ref u64) (#call get (: owner (#borrow moved))))
        (#call destroy (: owner moved))
        (#return (#deref result)))"#
    ));
}

#[test]
fn owner_cannot_outlive_a_reference_stored_in_its_allocation() {
    let source = format!(
        r#"{PREFIX}
      (#fn bad (: pointer (#ptr-mut Holder)) (#pin-own Holder)
        (#let local u64 42u64)
        (#return (#call make (: pointer pointer : source (#borrow local)))))"#
    );
    let error = compile(&source).expect_err("heap allocation does not extend the local lifetime");
    assert_eq!(error.code_string(), "E4100", "{}", error.message);
}

#[test]
fn stored_reference_keeps_source_borrowed_until_the_heap_owner_is_consumed() {
    let source = format!(
        r#"{PREFIX}
      (#fn bad (: pointer (#ptr-mut Holder)) ()
        (#let-mut source u64 42u64)
        (#let owner (#pin-own Holder) (#call make (: pointer pointer : source (#borrow source))))
        (#set source 0u64)
        (#let view (#ref u64) (#call get (: owner (#borrow owner))))
        (#assert (#u64.== (#deref view) 42u64))
        (#call destroy (: owner owner)) (#return ()))"#
    );
    let error =
        compile(&source).expect_err("source cannot change while retained in the heap owner");
    assert_eq!(error.code_string(), "E4100", "{}", error.message);
}

#[test]
fn direct_heap_field_writes_track_the_new_source_without_rewriting_it() {
    let source = format!(
        r#"{PREFIX}
      (#fn main () u64
        (#let first u64 1u64) (#let-mut second u64 42u64)
        (#let pointer (#ptr-mut Holder) (#unsafe (#linux-syscall (#ptr-mut Holder) 9usize
          (0usize 4096usize 3usize 34usize -1i64 0usize))))
        (#let-mut owner (#pin-own Holder) (#call make (: pointer pointer : source (#borrow first))))
        (#let view (#pin-ref-mut Holder) (#pin-own-borrow-mut owner))
        (#pin-set-field view link (#borrow second))
        (#drop view)
        (#let result (#ref u64) (#call get (: owner (#borrow owner))))
        (#call destroy (: owner owner)) (#return (#deref result)))"#
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
fn direct_reference_pointees_keep_provenance_after_heap_owner_release() {
    let source = r#"(#fn main () u64
      (#let-mut source u64 42u64)
      (#let pointer (#ptr-mut (#ref u64)) (#unsafe (#linux-syscall (#ptr-mut (#ref u64)) 9usize
        (0usize 4096usize 3usize 34usize -1i64 0usize))))
      (#let owner (#pin-own (#ref u64)) (#unsafe (#pin-own-of pointer (#borrow source))))
      (#let view (#pin-ref (#ref u64)) (#pin-own-borrow owner))
      (#let result (#ref u64) (#deref view))
      (#drop view)
      (#let raw (#ptr-mut (#ref u64)) (#unsafe (#pin-release owner)))
      (#assert (#i64.== (#unsafe (#linux-syscall i64 11usize (raw 4096usize))) 0i64))
      (#return (#deref result)))"#;
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
      (#fn replace (: owner (#ref-mut (#pin-own Holder)) : value (#ref u64)) ()
        (#let view (#pin-ref-mut Holder) (#pin-own-borrow-mut owner))
        (#pin-set-field view link value)
        (#return ()))
      (#fn bad (: pointer (#ptr-mut Holder)) ()
        (#let first u64 1u64)
        (#let-mut second u64 2u64)
        (#let-mut owner (#pin-own Holder) (#call make (: pointer pointer : source (#borrow first))))
        (#call replace (: owner (#borrow-mut owner) : value (#borrow second)))
        (#set second 3u64)
        (#let result (#ref u64) (#call get (: owner (#borrow owner))))
        (#assert (#u64.== (#deref result) 2u64))
        (#call destroy (: owner owner)) (#return ()))"#
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
      (#fn replace-owned (: owner (#pin-own Holder) : value (#ref u64)) (#pin-own Holder)
        (#let-mut moved (#pin-own Holder) owner)
        (#let view (#pin-ref-mut Holder) (#pin-own-borrow-mut moved))
        (#pin-set-field view link value)
        (#drop view)
        (#return moved))
      (#fn bad (: pointer (#ptr-mut Holder)) ()
        (#let first u64 1u64)
        (#let-mut second u64 2u64)
        (#let owner (#pin-own Holder) (#call make (: pointer pointer : source (#borrow first))))
        (#let updated (#pin-own Holder) (#call replace-owned (: owner owner : value (#borrow second))))
        (#set second 3u64)
        (#let result (#ref u64) (#call get (: owner (#borrow updated))))
        (#assert (#u64.== (#deref result) 2u64))
        (#call destroy (: owner updated)) (#return ()))"#
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
fn a_helper_cannot_store_a_shorter_lived_reference_in_a_surviving_owner() {
    let source = format!(
        r#"{PREFIX}
      (#fn replace (: owner (#ref-mut (#pin-own Holder)) : value (#ref u64)) ()
        (#let view (#pin-ref-mut Holder) (#pin-own-borrow-mut owner))
        (#pin-set-field view link value) (#return ()))
      (#fn bad (: pointer (#ptr-mut Holder)) ()
        (#let first u64 1u64)
        (#let-mut owner (#pin-own Holder) (#call make (: pointer pointer : source (#borrow first))))
        (#block
          (#let short u64 2u64)
          (#call replace (: owner (#borrow-mut owner) : value (#borrow short))))
        (#let result (#ref u64) (#call get (: owner (#borrow owner))))
        (#assert (#u64.== (#deref result) 2u64))
        (#call destroy (: owner owner)) (#return ()))"#
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
      (#fn replace (: owner (#ref-mut (#pin-own Holder)) : value (#ref u64)) ()
        (#let view (#pin-ref-mut Holder) (#pin-own-borrow-mut owner))
        (#pin-set-field view link value) (#return ()))
      (#fn main () u64
        (#let first u64 1u64) (#let second u64 42u64)
        (#let pointer (#ptr-mut Holder) (#unsafe (#linux-syscall (#ptr-mut Holder) 9usize
          (0usize 4096usize 3usize 34usize -1i64 0usize))))
        (#let-mut owner (#pin-own Holder) (#call make (: pointer pointer : source (#borrow first))))
        (#call replace (: owner (#borrow-mut owner) : value (#borrow second)))
        (#let result (#ref u64) (#call get (: owner (#borrow owner))))
        (#call destroy (: owner owner)) (#return (#deref result)))"#
    ));
}

#[test]
fn nested_heap_owners_keep_all_stored_reference_lifetimes() {
    let prefix = format!(
        r#"{PREFIX}
      (#struct Outer (: inner (#pin-own Holder)))
      (#fn wrap (: pointer (#ptr-mut Outer) : inner (#pin-own Holder)) (#pin-own Outer)
        (#return (#unsafe (#pin-own-of pointer (#struct-literal Outer (: inner inner))))))
      (#fn erase (: owner (#pin-own Outer)) () (#forget owner) (#return ()))"#
    );
    let source = format!(
        r#"{prefix}
      (#fn bad (: outer-pointer (#ptr-mut Outer) : inner-pointer (#ptr-mut Holder)) ()
        (#let-mut source u64 42u64)
        (#let inner (#pin-own Holder) (#call make (: pointer inner-pointer : source (#borrow source))))
        (#let outer (#pin-own Outer) (#call wrap (: pointer outer-pointer : inner inner)))
        (#set source 0u64)
        (#call erase (: owner outer)) (#return ()))"#
    );
    let error = compile(&source)
        .err()
        .expect("nested owners retain their reference contents");
    assert_eq!(error.code_string(), "E4100", "{}", error.message);
    assert!(error.message.contains("source"), "{}", error.message);
    let escaping = format!(
        r#"{prefix}
      (#fn bad (: outer-pointer (#ptr-mut Outer) : inner-pointer (#ptr-mut Holder)) (#pin-own Outer)
        (#let local u64 42u64)
        (#let inner (#pin-own Holder) (#call make (: pointer inner-pointer : source (#borrow local))))
        (#return (#call wrap (: pointer outer-pointer : inner inner))))"#
    );
    let error = compile(&escaping)
        .err()
        .expect("a second allocation cannot extend a local's lifetime");
    assert_eq!(error.code_string(), "E4100", "{}", error.message);
    assert!(error.message.contains("local"), "{}", error.message);
}

#[test]
fn storing_an_exclusive_reference_in_heap_storage_blocks_other_borrows() {
    let prefix = r#"(#struct Exclusive (: link (#ref-mut u64)))
      (#fn make (: pointer (#ptr-mut Exclusive) : source (#ref-mut u64)) (#pin-own Exclusive)
        (#return (#unsafe (#pin-own-of pointer (#struct-literal Exclusive (: link source))))))
      (#fn erase (: owner (#pin-own Exclusive)) () (#forget owner) (#return ()))"#;
    for operation in [
        "(#let other (#ref u64) (#borrow source))",
        "(#let other (#ref-mut u64) (#borrow-mut source))",
        "(#set source 0u64)",
    ] {
        let source = format!(
            r#"{prefix}
          (#fn bad (: pointer (#ptr-mut Exclusive)) ()
            (#let-mut source u64 42u64)
            (#let owner (#pin-own Exclusive) (#call make (: pointer pointer : source (#borrow-mut source))))
            {operation}
            (#call erase (: owner owner)) (#return ()))"#
        );
        let error = compile(&source)
            .err()
            .expect("heap-retained exclusive references cannot be aliased");
        assert_eq!(error.code_string(), "E4100", "{}", error.message);
        assert!(error.message.contains("source"), "{}", error.message);
    }
}
