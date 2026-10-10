mod support;

use std::{fs, process::Command, time::Duration};

fn example_source() -> String {
    include_str!("../examples/pin_box.lim")
        .replace(
            "../library/linux_x86_64.lim",
            &format!("{}/library/linux_x86_64.lim", env!("CARGO_MANIFEST_DIR")),
        )
        .replace(
            "../library/pin_box.lim",
            &format!("{}/library/pin_box.lim", env!("CARGO_MANIFEST_DIR")),
        )
        .replace(
            "../library/pin.lim",
            &format!("{}/library/pin.lim", env!("CARGO_MANIFEST_DIR")),
        )
}

#[test]
fn allocator_owned_pin_box_runs_and_generated_code_is_inspectable() {
    let scratch = support::Scratch::new("pin-box");
    let input = scratch.path().join("main.lim");
    let binary = scratch.path().join("program");
    fs::write(&input, example_source()).unwrap();
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
        "pin-u64-create",
        "pin-u64-borrow",
        "pin-u64-borrow-mut",
        "pin-u64-destroy",
    ] {
        assert!(
            generated.contains(&format!("(#fn {function}")),
            "{function}"
        );
    }
    assert!(generated.contains("(#pin-own-borrow"));
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
    let source = example_source()
        .replace("          (#call pin-u64-destroy (: owner moved-owner))", "")
        .replace("          (#let value #u64 (#call PinnedU64-shared-read (: pin (#borrow value-reference))))", "          (#call pin-u64-destroy (: owner moved-owner))\n          (#let value #u64 (#call PinnedU64-shared-read (: pin (#borrow value-reference))))");
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
    let source = example_source()
        .replace("(#let arena Arena", "(#let-mut arena Arena")
        .replace("          (#call pin-u64-destroy (: owner moved-owner))", "")
        .replace("          (#let value #u64 (#call PinnedU64-shared-read (: pin (#borrow value-reference))))", "          (#forget moved-owner)\n          (#set-field arena identity 2u64)\n          (#let value #u64 (#call PinnedU64-shared-read (: pin (#borrow value-reference))))");
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
fn mutable_opaque_heap_pin_accessors_read_and_write_in_place() {
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
          (#let-mut pin PinnedU64 (#call pin-u64-borrow-mut (: owner (#borrow-mut moved-owner))))
          (#call PinnedU64-write (: pin (#borrow-mut pin) : value 43u64))
          (#let changed #u64 (#call PinnedU64-read (: pin (#borrow pin))))
          (#assert (#u64.== changed 43u64)) (#forget pin)",
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
