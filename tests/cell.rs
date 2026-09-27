mod support;

use std::{fs, process::Command, time::Duration};

#[test]
fn generated_cell_is_inspectable_and_preserves_its_value() {
    let scratch = support::Scratch::new("cell");
    let source = include_str!("../examples/cell.lim").replace(
        "../library/cell.lim",
        &format!("{}/library/cell.lim", env!("CARGO_MANIFEST_DIR")),
    );
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

    let generated = fs::read_dir(scratch.path().join(".lim/cache"))
        .unwrap()
        .filter_map(Result::ok)
        .filter(|entry| entry.path().extension().is_some_and(|ext| ext == "lim"))
        .map(|entry| fs::read_to_string(entry.path()).unwrap())
        .collect::<Vec<_>>()
        .join("\n");
    assert!(generated.contains("#struct CellU32"), "{generated}");
    assert!(generated.contains("#fn CellU32-get"), "{generated}");
    assert!(generated.contains("#fn CellU32-set"), "{generated}");

    let (status, _, stderr) =
        support::run(&mut Command::new(binary), Duration::from_secs(5), 1024).unwrap();
    assert_eq!(
        status.code(),
        Some(42),
        "{}",
        String::from_utf8_lossy(&stderr)
    );
}
