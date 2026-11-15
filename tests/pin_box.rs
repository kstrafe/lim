mod support;

use std::{fs, process::Command, time::Duration};

fn example_source() -> String {
    include_str!("../examples/pin_box.lim").replace(
        "../library/",
        &format!("{}/library/", env!("CARGO_MANIFEST_DIR")),
    )
}

#[test]
fn allocator_owned_pin_box_runs_and_generated_code_is_inspectable() {
    let scratch = support::Scratch::new("pin-box");
    let input = scratch.path().join("main.lim");
    let binary = scratch.path().join("program");
    let source = example_source();
    assert!(source.contains("(allocator SystemAllocator::Allocator)"));
    assert!(!source.contains("Arena"));
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

    let generated = fs::read_dir(scratch.path().join(".lim/generated"))
        .unwrap()
        .filter_map(Result::ok)
        .filter(|entry| entry.path().extension().is_some_and(|ext| ext == "lim"))
        .map(|entry| fs::read_to_string(entry.path()).unwrap())
        .collect::<Vec<_>>()
        .join("\n");
    for function in [
        "PinU64Box::create",
        "PinU64Box::borrow",
        "PinU64Box::borrow-mut",
        "PinU64Box::destroy",
    ] {
        assert!(
            generated.contains(&format!("#fn {function}")),
            "{function}"
        );
    }
    assert!(generated.contains("(#pin-own-borrow"));
    assert!(generated.contains("(#pin-ref #u64)"));
    assert!(generated.contains("(#pin-ref-mut #u64)"));
    assert!(generated.contains("(#pin-release pointer)"));

    let (status, _, stderr) =
        support::run(&mut Command::new(binary), Duration::from_secs(5), 1024).unwrap();
    assert_eq!(
        status.code(),
        Some(42),
        "{}",
        String::from_utf8_lossy(&stderr)
    );
}

#[test]
fn derived_pin_prevents_destroying_its_box() {
    let scratch = support::Scratch::new("pin-box-borrow");
    let input = scratch.path().join("main.lim");
    let original = example_source();
    let destroy = "(#call PinU64Box::destroy ((owner moved-owner)))";
    let read = "(#let value #u64";
    assert_eq!(original.matches(destroy).count(), 1);
    assert_eq!(original.matches(read).count(), 1);
    let source = original
        .replace(destroy, "")
        .replace(read, &format!("{destroy}\n  {read}"));
    fs::write(&input, source).unwrap();
    let (status, _, stderr) = support::run(
        Command::new(env!("CARGO_BIN_EXE_lim"))
            .arg("--emit-asm")
            .arg(&input)
            .arg(scratch.path().join("program.s")),
        Duration::from_secs(20),
        1024 * 1024,
    )
    .unwrap();
    assert!(!status.success());
    let diagnostic = String::from_utf8_lossy(&stderr);
    assert!(
        diagnostic.contains("borrow") || diagnostic.contains("pinned"),
        "{diagnostic}"
    );
}

#[test]
fn a_pointee_view_retains_the_allocator_after_leaking_the_movable_owner() {
    let scratch = support::Scratch::new("pin-box-allocator");
    let input = scratch.path().join("main.lim");
    let source = include_str!("fixtures/pin_box_arena.lim")
        .replace("../../library/", &format!("{}/library/", env!("CARGO_MANIFEST_DIR")))
        .replace("(#let arena Arena", "(#let-mut arena Arena")
        .replace("          (#call PinU64Box::destroy ((owner moved-owner)))", "")
        .replace("          (#let value #u64 (#unsafe (#pin-read value-reference)))", "          (#forget moved-owner)\n          (#set-field arena identity 2u64)\n          (#let value #u64 (#unsafe (#pin-read value-reference)))");
    fs::write(&input, source).unwrap();
    let (status, _, stderr) = support::run(
        Command::new(env!("CARGO_BIN_EXE_lim"))
            .arg("--emit-asm")
            .arg(&input)
            .arg(scratch.path().join("program.s")),
        Duration::from_secs(20),
        1024 * 1024,
    )
    .unwrap();
    assert!(!status.success());
    let diagnostic = String::from_utf8_lossy(&stderr);
    assert!(
        diagnostic.contains("borrow") && diagnostic.contains("arena"),
        "{diagnostic}"
    );
}

#[test]
fn mutable_native_heap_pin_reference_reads_in_place() {
    let scratch = support::Scratch::new("pin-box-mutable-api");
    let input = scratch.path().join("main.lim");
    let binary = scratch.path().join("program");
    let source = example_source()
        .replace(
            "(#let moved-owner PinU64Box",
            "(#let-mut moved-owner PinU64Box",
        )
        .replace(
            "(#drop value-reference)",
            "(#drop value-reference)
          (#let-mut pin (#pin-ref-mut #u64) (#call PinU64Box::borrow-mut ((owner (#borrow-mut moved-owner)))))
          (#let changed #u64 (#unsafe (#pin-read pin)))
          (#assert (#u64::eq changed 42u64)) (#forget pin)",
        );
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
    assert_eq!(Command::new(binary).status().unwrap().code(), Some(42));
}
