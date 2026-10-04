//! Native regressions for the Linux wrappers that accept safe Lim references.
mod support;

use std::{fs, process::Command, time::Duration};

fn run(source: &str, input: &[u8], expected_stdout: &[u8]) {
    let scratch = support::Scratch::new("linux-reference-io");
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let input_path = scratch.path().join("stdin");
    fs::write(&input_path, input).unwrap();
    let source_path = scratch.path().join("main.lim");
    let source = source.replace(
        "@LINUX@",
        &root.join("library/linux_x86_64.lim").display().to_string(),
    );
    let assembly = lim::compile_source_to_assembly(
        &source,
        &source_path,
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_or_else(|error| panic!("{}", error.message));
    let binary = scratch.path().join("program");
    lim::link_native_binary(
        &assembly,
        &binary,
        &[],
        &[],
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    let (status, stdout, stderr) = support::run(
        Command::new(binary).stdin(fs::File::open(input_path).unwrap()),
        Duration::from_secs(5),
        4096,
    )
    .unwrap();
    assert_eq!(status.code(), Some(42), "{stderr:?}");
    assert!(stderr.is_empty(), "{stderr:?}");
    assert_eq!(stdout, expected_stdout);
}

#[test]
fn odd_raw_byte_references_keep_their_address_through_safe_io_wrappers() {
    run(
        r#"(#import "@LINUX@")
        (#fn main () u64
          (#let base (#ptr-mut u8) (#unsafe (#call linux-mmap (: address (#ptr-null (#ptr-mut u8)) : length 4096usize : protection 3u32 : flags 34u32 : fd -1i64 : offset 0i64))))
          (#let odd (#ptr-mut u8) (#unsafe (#ptr-offset base 1usize)))
          (#unsafe (#ptr-write base 91u8))
          (#unsafe (#ptr-write odd 0u8))
          (#unsafe (#ptr-write (#ptr-offset base 2usize) 92u8))
          (#let-mut anchor u64 0u64)
          (#let view (#ref-mut u8) (#unsafe (#ptr-borrow-mut (#borrow-mut anchor) odd)))
          (#assert (#i64.== (#call linux-read-byte-from (: fd 0i64 : destination view)) 1i64))
          (#assert (#u8.== (#unsafe (#ptr-read base)) 91u8))
          (#assert (#u8.== (#unsafe (#ptr-read (#ptr-offset base 2usize))) 92u8))
          (#drop view)
          (#let shared (#ref u8) (#unsafe (#ptr-borrow (#borrow anchor) odd)))
          (#assert (#i64.== (#call linux-write-byte (: source shared)) 1i64))
          (#drop shared)
          (#assert (#i64.== (#unsafe (#call linux-munmap (: address base : length 4096usize))) 0i64))
          (#return 42u64))"#,
        &[0xa7],
        &[0xa7],
    );
}

#[test]
fn clock_and_nanosleep_marshal_descending_stack_and_ascending_raw_timespecs() {
    run(
        r#"(#import "@LINUX@")
        (#fn main () u64
          (#let-mut stack-time LinuxTimespec (#struct-literal LinuxTimespec ((nanoseconds 0i64) (seconds 0i64))))
          (#assert (#i64.== (#call linux-clock-gettime (: clock-id 1i64 : time (#borrow-mut stack-time))) 0i64))
          (#assert (#i64.<= 0i64 (#get stack-time nanoseconds)))
          (#assert (#i64.< (#get stack-time nanoseconds) 1000000000i64))
          (#assert (#i64.> (#get stack-time seconds) 0i64))
          (#let-mut stack-rem LinuxTimespec (#struct-literal LinuxTimespec ((nanoseconds 123i64) (seconds 456i64))))
          (#let stack-zero LinuxTimespec (#struct-literal LinuxTimespec ((nanoseconds 0i64) (seconds 0i64))))
          (#assert (#i64.== (#call linux-nanosleep (: request (#borrow stack-zero) : remaining (#borrow-mut stack-rem))) 0i64))
          (#assert (#i64.== (#get stack-rem nanoseconds) 123i64))
          (#assert (#i64.== (#get stack-rem seconds) 456i64))
          (#let invalid LinuxTimespec (#struct-literal LinuxTimespec ((nanoseconds 1000000000i64) (seconds 0i64))))
          (#assert (#i64.== (#call linux-nanosleep (: request (#borrow invalid) : remaining (#borrow-mut stack-rem))) -22i64))
          (#let raw (#ptr-mut u8) (#unsafe (#call linux-mmap (: address (#ptr-null (#ptr-mut u8)) : length 4096usize : protection 3u32 : flags 34u32 : fd -1i64 : offset 0i64))))
          ; Lim's ascending raw words hold ns then seconds, unlike Linux's C ABI.
          (#let raw-words (#ptr-mut i64) (#unsafe (#asm (#ptr-mut i64) ((rdi raw)) "mov rax, rdi")))
          (#unsafe (#ptr-write raw-words 0i64))
          (#unsafe (#ptr-write (#ptr-offset raw-words 1usize) 0i64))
          (#let-mut raw-anchor u64 0u64)
          (#let raw-struct (#ptr-mut LinuxTimespec) (#unsafe (#asm (#ptr-mut LinuxTimespec) ((rdi raw)) "mov rax, rdi")))
          (#let raw-time (#ref-mut LinuxTimespec) (#unsafe (#ptr-borrow-mut (#borrow-mut raw-anchor) raw-struct)))
          (#assert (#i64.== (#call linux-clock-gettime (: clock-id 1i64 : time raw-time)) 0i64))
          (#assert (#i64.<= 0i64 (#get raw-time nanoseconds)))
          (#assert (#i64.< (#get raw-time nanoseconds) 1000000000i64))
          (#assert (#i64.> (#get raw-time seconds) 0i64))
          (#drop raw-time)
          (#unsafe (#ptr-write raw-words 0i64))
          (#unsafe (#ptr-write (#ptr-offset raw-words 1usize) 0i64))
          (#let rem-words (#ptr-mut i64) (#unsafe (#ptr-offset raw-words 2usize)))
          (#unsafe (#ptr-write rem-words 123i64))
          (#unsafe (#ptr-write (#ptr-offset rem-words 1usize) 456i64))
          (#let rem-struct (#ptr-mut LinuxTimespec) (#unsafe (#asm (#ptr-mut LinuxTimespec)
            ((rdi rem-words)) "mov rax, rdi")))
          (#let request-anchor u64 0u64)
          (#let-mut remaining-anchor u64 0u64)
          (#let raw-request (#ref LinuxTimespec) (#unsafe (#ptr-borrow (#borrow request-anchor) raw-struct)))
          (#let raw-remaining (#ref-mut LinuxTimespec) (#unsafe (#ptr-borrow-mut (#borrow-mut remaining-anchor) rem-struct)))
          (#assert (#i64.== (#call linux-nanosleep (: request raw-request : remaining raw-remaining)) 0i64))
          (#assert (#i64.== (#get raw-remaining nanoseconds) 123i64))
          (#assert (#i64.== (#get raw-remaining seconds) 456i64))
          (#drop raw-request)
          (#unsafe (#ptr-write raw-words 1000000000i64))
          (#let raw-invalid (#ref LinuxTimespec) (#unsafe (#ptr-borrow (#borrow request-anchor) raw-struct)))
          (#assert (#i64.== (#call linux-nanosleep (: request raw-invalid : remaining raw-remaining)) -22i64))
          (#assert (#i64.== (#get raw-remaining nanoseconds) 123i64))
          (#assert (#i64.== (#get raw-remaining seconds) 456i64))
          (#drop raw-invalid) (#drop raw-remaining)
          (#assert (#i64.== (#unsafe (#call linux-munmap (: address raw : length 4096usize))) 0i64))
          (#return 42u64))"#,
        &[],
        &[],
    );
}
