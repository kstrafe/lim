mod support;

use std::{fs, process::Command, time::Duration};

fn run(source: &str, expected: i32) {
    let scratch = support::Scratch::new("pin-ownership");
    let input = scratch.path().join("main.lim");
    let binary = scratch.path().join("program");
    fs::write(&input, source).unwrap();
    let (status, _, stderr) = support::run(
        Command::new(env!("CARGO_BIN_EXE_lim"))
            .arg(&input)
            .arg("-o")
            .arg(&binary),
        Duration::from_secs(20),
        1024 * 1024,
    )
    .unwrap();
    assert!(status.success(), "{}", String::from_utf8_lossy(&stderr));
    let (status, _, stderr) =
        support::run(&mut Command::new(binary), Duration::from_secs(5), 1024).unwrap();
    assert_eq!(
        status.code(),
        Some(expected),
        "{}",
        String::from_utf8_lossy(&stderr)
    );
}

#[test]
fn stationary_stack_storage_runs_with_explicit_in_place_end() {
    run(include_str!("../examples/stationary_pin.lim"), 42);
}

#[test]
fn movable_heap_owners_initialize_native_scalars_and_large_aggregates() {
    for (ty, value, read) in [
        ("u32", "42u32", "(#as (#deref view) u64)"),
        (
            "(#array u64 8)",
            "(#array-of (#array u64 8) 1u64 2u64 3u64 4u64 5u64 6u64 7u64 42u64)",
            "(#index view 7usize)",
        ),
    ] {
        let source = format!(
            "(#fn forward (: owner (#pin-own {ty})) (#pin-own {ty}) (#return owner))
          (#fn main () u64
          (#let pointer (#ptr-mut {ty}) (#unsafe (#linux-syscall (#ptr-mut {ty}) 9usize
            (0usize (#size-of {ty}) 3usize 34usize -1i64 0usize))))
          (#let owner (#pin-own {ty}) (#unsafe (#pin-own-of pointer {value})))
          (#let view (#pin-ref {ty}) (#pin-own-borrow owner))
          (#let moved (#pin-own {ty}) (#call forward (: owner owner)))
          (#let result u64 {read}) (#forget view)
          (#let raw (#ptr-mut {ty}) (#unsafe (#pin-release moved)))
          (#let status i64 (#unsafe (#linux-syscall i64 11usize (raw (#size-of {ty})))))
          (#assert (#i64.== status 0i64)) (#return result))"
        );
        run(&source, 42);
    }
}
