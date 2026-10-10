use std::{process::Command, time::Duration};
mod support;

fn run(source: &str, stdout: &[u8]) {
    let scratch = support::Scratch::new("raw-references");
    let assembly = lim::compile_source_to_assembly(
        source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_or_else(|e| panic!("{}", e.message));
    let binary = scratch.path().join("program");
    lim::link_native_binary(
        &assembly,
        &binary,
        &[],
        &[],
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    let (status, out, err) =
        support::run(&mut Command::new(binary), Duration::from_secs(5), 4096).unwrap();
    assert_eq!(status.code(), Some(42), "{err:?}");
    assert_eq!(out, stdout);
    assert!(err.is_empty());
}

#[test]
fn packed_scalar_references_access_exact_width_at_a_guard_page() {
    for (ty, old, new, bytes) in [
        ("#u8", "250u8", "42u8", 1),
        ("#i8", "-7i8", "42i8", 1),
        ("#u16", "65000u16", "42u16", 2),
        ("#i16", "-700i16", "42i16", 2),
        ("#u32", "4294967295u32", "42u32", 4),
        ("#i32", "-70000i32", "42i32", 4),
        ("#char", "#\\🙂", "#\\*", 4),
        ("#bool", "false", "true", 1),
    ] {
        let expected = if ty == "#bool" { "true" } else { new };
        let source = format!(
            r#"
          (#fn read (: view (#ref {ty})) {ty} (#return (#deref view)))
          (#fn write (: view (#ref-mut {ty}) : value {ty}) () (#deref-set view value) (#return ()))
          (#fn main () #u64
            (#let base (#ptr-mut {ty}) (#unsafe (#linux-syscall (#ptr-mut {ty}) 9usize
              (0usize 8192usize 3usize 34usize -1i64 0usize))))
            (#assert (#usize.< (#ptr-address base) 18446744073709547521usize))
            (#let guard (#ptr-mut {ty}) (#unsafe (#ptr-offset base {guard_offset}usize)))
            (#assert (#i64.== (#unsafe (#linux-syscall #i64 10usize (guard 4096usize 0usize))) 0i64))
            (#let last (#ptr-mut {ty}) (#unsafe (#ptr-offset base {offset}usize)))
            (#unsafe (#ptr-write last {old}))
            (#let-mut anchor #u64 0u64)
            (#let view (#ref-mut {ty}) (#unsafe (#ptr-borrow-mut (#borrow-mut anchor) last)))
            (#call write (: view view : value {new}))
            (#assert ({ty}.== (#unsafe (#ptr-read last)) {expected}))
            (#drop view)
            (#let shared (#ref {ty}) (#unsafe (#ptr-borrow (#borrow anchor) last)))
            (#assert ({ty}.== (#call read (: view shared)) {expected}))
            (#drop shared)
            (#assert (#i64.== (#unsafe (#linux-syscall #i64 11usize (base 8192usize))) 0i64))
            (#return 42u64))"#,
            guard_offset = 4096 / bytes,
            offset = (4096 - bytes) / bytes
        );
        run(&source, b"");
    }
}

#[test]
fn odd_byte_references_survive_calls_struct_storage_and_native_boundaries() {
    run(
        r#"(#struct Holder (: byte (#ref #u8)))
      (#fn forward (: byte (#ref #u8)) (#ref #u8) (#return byte))
      (#fn main () #u64
        (#let base (#ptr-mut #u8) (#unsafe (#linux-syscall (#ptr-mut #u8) 9usize
          (0usize 4096usize 3usize 34usize -1i64 0usize))))
        (#assert (#usize.< (#ptr-address base) 18446744073709547521usize))
        (#let odd (#ptr-mut #u8) (#unsafe (#ptr-offset base 1usize)))
        (#unsafe (#ptr-write base 99u8))
        (#unsafe (#ptr-write odd 120u8))
        (#unsafe (#ptr-write (#ptr-offset base 2usize) 100u8))
        (#let anchor #u64 0u64)
        (#let view (#ref #u8) (#call forward (: byte (#unsafe (#ptr-borrow (#borrow anchor) odd)))))
        (#let holder Holder (#struct-literal Holder (: byte view)))
        (#assert (#u8.== (#deref (#get holder byte)) 120u8))
        (#assert (#i64.== (#unsafe (#linux-syscall #i64 1usize (1i64 (#get holder byte) 1usize))) 1i64))
        (#assert (#usize.== (#unsafe (#asm #usize ((rax (#get holder byte))) "")) (#ptr-address odd)))
        (#forget holder)
        (#assert (#u8.== (#unsafe (#ptr-read base)) 99u8))
        (#assert (#u8.== (#unsafe (#ptr-read (#ptr-offset base 2usize))) 100u8))
        (#assert (#i64.== (#unsafe (#linux-syscall #i64 11usize (base 4096usize))) 0i64))
        (#return 42u64))"#,
        b"x",
    );
}

#[test]
fn word_backed_narrow_locals_and_heap_fields_still_store_canonical_words() {
    run(
        r#"(#struct Value (: field #i8))
      (#fn update (: field (#ref-mut #i8)) () (#deref-set field 42i8) (#return ()))
      (#fn main () #u64
        (#let-mut local #i8 -1i8)
        (#call update (: field (#borrow-mut local)))
        (#assert (#i8.== local 42i8))
        (#let pointer (#ptr-mut Value) (#unsafe (#linux-syscall (#ptr-mut Value) 9usize
          (0usize 4096usize 3usize 34usize -1i64 0usize))))
        (#let-mut owner (#pin-own Value) (#unsafe (#pin-own-of pointer (#struct-literal Value (: field -1i8)))))
        (#let view (#pin-ref-mut Value) (#pin-own-borrow-mut owner))
        (#unsafe (#pin-write (#pin-borrow-mut (#get view field)) 42i8))
        (#assert (#i8.== (#get view field) 42i8))
        (#drop view)
        (#let raw (#ptr-mut Value) (#unsafe (#pin-release owner)))
        (#assert (#i64.== (#unsafe (#linux-syscall #i64 11usize (raw 4096usize))) 0i64))
        (#return 42u64))"#,
        b"",
    );
}
