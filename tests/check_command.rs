use std::{
    fs,
    process::Command,
    sync::atomic::{AtomicU64, Ordering},
};

fn scratch() -> std::path::PathBuf {
    static NEXT: AtomicU64 = AtomicU64::new(0);
    let path = std::env::temp_dir().join(format!(
        "lim-check-command-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir(&path).unwrap();
    path
}

#[test]
fn checks_project_imports_and_cfg_without_creating_native_output() {
    let directory = scratch();
    let src = directory.join("src");
    let modules = directory.join("modules");
    fs::create_dir_all(&src).unwrap();
    fs::create_dir_all(&modules).unwrap();
    fs::write(
        directory.join("lim.project"),
        "schema-version = 1\nname = \"check-case\"\nsource-root = \"src\"\nmodule-path = \"modules\"\ntarget = \"x86_64-sysv\"\n",
    )
    .unwrap();
    fs::write(
        modules.join("selected.lim"),
        "(#cfg-if (#cfg-is #feature enabled) (#type Selected #u64))",
    )
    .unwrap();
    fs::write(src.join("root-type.lim"), "(#type RootType #u64)").unwrap();
    let app = src.join("app");
    fs::create_dir_all(&app).unwrap();
    let input = app.join("main.lim");
    let source = "(#import \"root-type.lim\")\n(#import \"selected.lim\")\n(#fn main () Selected (#return 0u64))\n";
    fs::write(&input, source).unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg("--check")
        .arg(&input)
        .args(["--cfg", "feature=enabled"])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(output.stdout.is_empty());
    assert_eq!(fs::read_to_string(&input).unwrap(), source);
    assert!(!app.join("main").exists(), "check wrote a binary");
    assert!(!app.join("main.s").exists(), "check wrote assembly");
    fs::remove_dir_all(directory).unwrap();
}

#[test]
fn reports_borrow_diagnostic_as_json_with_primary_byte_span() {
    let directory = scratch();
    let input = directory.join("borrow.lim");
    let source = "(#fn main () #u64\n  (#let-mut owner #u64 1u64)\n  (#let view (#ref #u64) (#borrow owner))\n  (#set owner 2u64)\n  (#drop view)\n  (#return 0u64))\n";
    fs::write(&input, source).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg("--check")
        .arg(&input)
        .arg("--diagnostic-format=json")
        .output()
        .unwrap();
    assert!(!output.status.success());
    assert!(output.stdout.is_empty());
    let json = String::from_utf8(output.stderr).unwrap();
    assert!(json.contains("\"category\":\"borrow\""), "{json}");
    assert!(json.contains("\"primary\":true"), "{json}");
    assert!(
        json.contains(&format!("\"path\":\"{}\"", input.display())),
        "{json}"
    );
    let conflict = source.find("#set").unwrap();
    assert!(
        json.contains(&format!("\"byte_start\":{conflict}")),
        "{json}"
    );
    assert!(
        json.contains(&format!("\"byte_end\":{}", conflict + "#set".len())),
        "{json}"
    );
    assert_eq!(fs::read_to_string(&input).unwrap(), source);
    assert!(!directory.join("borrow").exists(), "check wrote a binary");
    fs::remove_dir_all(directory).unwrap();
}
