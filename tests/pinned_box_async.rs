use std::{fs, process::Command, time::Duration};

mod support;

fn example_source() -> String {
    include_str!("../examples/pinned_box_async.lim").replace(
        "../library/",
        &format!("{}/library/", env!("CARGO_MANIFEST_DIR")),
    )
}

fn compile_error(source: &str, label: &str) -> String {
    let scratch = support::Scratch::new(label);
    let input = scratch.path().join("main.lim");
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
    String::from_utf8_lossy(&stderr).into_owned()
}

#[test]
fn pinned_box_frame_survives_pending_polls_and_owner_moves() {
    let scratch = support::Scratch::new("pinned-box-async");
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
fn mutable_box_borrow_cannot_be_extracted_as_an_ordinary_reference() {
    let source = example_source().replace(
        "(#fn main () #u64",
        "(#fn invalid-extract ((owner (#ref-mut PinnedFrameBox))) (#ref-mut Work::Frame)\n  (#return (#deref (#call PinnedFrameBox::borrow-mut ((owner owner))))))\n(#fn main () #u64",
    );
    let diagnostic = compile_error(&source, "pinned-box-async-extract");
    assert!(
        diagnostic.contains("has type Named(")
            && diagnostic.contains("::Work::Frame")
            && diagnostic.contains("expected Reference { mutable: true"),
        "{diagnostic}"
    );
}

#[test]
fn box_cannot_be_destroyed_while_its_pinned_borrow_is_live() {
    let source = example_source().replace(
        "(#fn main () #u64",
        "(#fn invalid-destroy ((owner PinnedFrameBox)) ()\n  (#let-mut local PinnedFrameBox owner)\n  (#let pin (#pin-ref-mut Work::Frame) (#call PinnedFrameBox::borrow-mut ((owner (#borrow-mut local)))))\n  (#call PinnedFrameBox::destroy ((owner local)))\n  (#forget pin) (#return ()))\n(#fn main () #u64",
    );
    let diagnostic = compile_error(&source, "pinned-box-async-destroy");
    assert!(
        diagnostic.contains("cannot release pinned allocation")
            && diagnostic.contains("conflicting borrow"),
        "{diagnostic}"
    );
}
