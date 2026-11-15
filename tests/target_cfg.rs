mod support;

use std::{fs, process::Command};

fn check(extra: &[&str], expected_arch: &str, project: bool) {
    let scratch = support::Scratch::new("target-cfg");
    let source = scratch.path().join("main.lim");
    fs::write(
        &source,
        format!(
            "#cfg-if (#cfg-and (#cfg-is #arch {expected_arch})
            (#cfg-is #target aarch64-unknown-linux-gnu) (#cfg-is #platform linux))
            (#fn main () #u64 (#return 42u64))
            (#cfg-else (#fn main () #u64 (#return wrong-target)))\n"
        ),
    )
    .unwrap();
    if project {
        fs::write(scratch.path().join("lim.project"),
            "schema-version = 1\nname = \"cross-test\"\nsource-root = \".\"\ntarget = \"aarch64-linux\"\n").unwrap();
    }
    let output = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg("--check")
        .arg(&source)
        .args(extra)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn check_uses_selected_target_instead_of_host_defaults() {
    check(&["--target", "aarch64-linux"], "aarch64", false);
}

#[test]
fn check_uses_project_target_defaults() {
    check(&[], "aarch64", true);
}

#[test]
fn explicit_cfg_overrides_survive_target_selection_in_either_order() {
    check(
        &["--cfg", "arch=x86_64", "--target", "aarch64-linux"],
        "x86_64",
        false,
    );
    check(
        &["--target", "aarch64-linux", "--cfg", "arch=x86_64"],
        "x86_64",
        false,
    );
}

#[test]
fn lsp_context_round_trip_preserves_selected_target_and_cfg() {
    let scratch = support::Scratch::new("target-lsp-context");
    let entry = scratch.path().join("main.lim");
    let path = scratch.path().join("lim.lsp");
    fs::write(&entry, "#fn main () #u64 (#return 42u64)\n").unwrap();
    let mut config = lim::CompileConfig::default();
    config.set("feature", "enabled");
    let context = lim::lsp_context::LspContext {
        entry,
        target: lim::TargetDescription::AARCH64_LINUX,
        config,
    };
    context.write(&path).unwrap();
    let text = fs::read_to_string(&path).unwrap();
    assert!(text.contains("target = \"aarch64-linux\""));
    assert!(text.contains("arch=aarch64"));
    assert!(text.contains("target=aarch64-unknown-linux-gnu"));
    let loaded = lim::lsp_context::LspContext::read(&path).unwrap();
    assert_eq!(loaded.target, context.target);
    assert_eq!(loaded.config, context.config.with_target(context.target));
    let modified = fs::metadata(&path).unwrap().modified().unwrap();
    loaded.write(&path).unwrap();
    assert_eq!(fs::metadata(&path).unwrap().modified().unwrap(), modified);
    fs::write(
        &path,
        "schema-version = 1\nentry = \"main.lim\"\ntarget = \"aarch64-linux\"\n",
    )
    .unwrap();
    let loaded = lim::lsp_context::LspContext::read(&path).unwrap();
    loaded.write(&path).unwrap();
    assert!(fs::read_to_string(&path).unwrap().contains("arch=aarch64"));
}
