use lim::{lsp_context::LspContext, CompileConfig, TargetDescription};
use std::{fs, path::PathBuf, process::Command};

fn directory(name: &str) -> PathBuf {
    let path = std::env::temp_dir().join(format!("lim-lsp-context-{name}-{}", std::process::id()));
    fs::create_dir_all(&path).unwrap();
    path
}

#[test]
fn cli_records_effective_cfg_project_paths_and_target_without_rewrites() {
    let base = directory("cli");
    fs::create_dir_all(base.join("src")).unwrap();
    fs::create_dir_all(base.join("modules")).unwrap();
    fs::write(base.join("lim.project"), "schema-version = 1\nname = \"demo\"\nsource-root = \"src\"\nmodule-path = \"modules\"\ntarget = \"x86_64-sysv\"\n").unwrap();
    fs::write(base.join("src/main.lim"), "(#cfg-if (#cfg-is #feature test) (#fn main () #u64 (#return 42u64)) (#cfg-else (#fn main () #u64 (#return missing))))").unwrap();
    let run = || {
        Command::new(env!("CARGO_BIN_EXE_lim"))
            .current_dir(&base)
            .args([
                "--check",
                "src/main.lim",
                "--cfg",
                "feature=test",
                "--write-lsp-config",
                "lim.lsp",
            ])
            .output()
            .unwrap()
    };
    let output = run();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let context = LspContext::read(&base.join("lim.lsp")).unwrap();
    assert_eq!(context.entry, base.join("src/main.lim"));
    assert_eq!(context.target, TargetDescription::X86_64_SYSTEM_V);
    let text = fs::read_to_string(base.join("lim.lsp")).unwrap();
    assert!(text.contains("feature=test"));
    assert!(text.contains("platform=linux"));
    assert!(text.contains(base.join("modules").to_str().unwrap()));
    let modified = fs::metadata(base.join("lim.lsp"))
        .unwrap()
        .modified()
        .unwrap();
    assert!(run().status.success());
    assert_eq!(
        modified,
        fs::metadata(base.join("lim.lsp"))
            .unwrap()
            .modified()
            .unwrap()
    );
    fs::write(
        base.join("src/main.lim"),
        "(#fn main () #u64 (#return missing))",
    )
    .unwrap();
    assert!(!run().status.success());
    assert_eq!(text, fs::read_to_string(base.join("lim.lsp")).unwrap());
}

#[test]
fn relative_paths_quoted_values_and_invalid_settings() {
    let base = directory("parser");
    let path = base.join("lim.lsp");
    let valid = "schema-version = 1\nentry = \"src/main.lim\"\ntarget = \"x86_64-sysv\"\ncfg = \"feature=a=b#c\"\nmodule-path = \"some modules\"\n";
    fs::write(&path, valid).unwrap();
    assert_eq!(
        LspContext::read(&path).unwrap().entry,
        base.join("src/main.lim")
    );
    for suffix in [
        "entry = \"other.lim\"",
        "cfg = \"feature=duplicate\"",
        "cfg = \"=x\"",
        "command = \"shell\"",
        "module-path = 42",
    ] {
        fs::write(&path, format!("{valid}{suffix}\n")).unwrap();
        assert!(LspContext::read(&path).is_err(), "{suffix}");
    }
    for invalid in [
        valid.replace("schema-version = 1", "schema-version = 2"),
        valid.replace("x86_64-sysv", "unsupported"),
        valid.replace("entry = \"src/main.lim\"\n", ""),
    ] {
        fs::write(&path, invalid).unwrap();
        assert!(LspContext::read(&path).is_err());
    }
}

#[test]
fn context_editor_checks_entry_not_isolated_module_and_reloads_flags() {
    let base = directory("editor");
    let entry = base.join("main.lim");
    let imported = base.join("child.lim");
    let text = "(#fn child () Number (#return 42u64))";
    fs::write(&entry, "(#cfg-if (#cfg-is #feature enabled) (#type Number #u64) (#cfg-else (#type Number #bool))) (#import \"child.lim\") (#fn main () #u64 (#return (#call child ())))").unwrap();
    let overlays = std::collections::HashMap::from([(imported.clone(), text.to_owned())]);
    let mut config = CompileConfig::default();
    config.set("feature", "enabled");
    let mut context = LspContext {
        entry,
        config,
        target: TargetDescription::X86_64_SYSTEM_V,
    };
    context.write(&base.join("lim.lsp")).unwrap();
    lim::check_source_for_editor(text, &imported, &CompileConfig::default(), &overlays).unwrap();
    context.config.set("feature", "disabled");
    // Rewriting the config doesn't require the unsaved import to exist on disk.
    fs::write(
        base.join("lim.lsp"),
        fs::read_to_string(base.join("lim.lsp"))
            .unwrap()
            .replace("feature=enabled", "feature=disabled"),
    )
    .unwrap();
    assert!(
        lim::check_source_for_editor(text, &imported, &CompileConfig::default(), &overlays)
            .is_err()
    );
    let unrelated = base.join("unrelated.lim");
    let error = lim::check_source_for_editor(
        "(#fn lone () () (#return ()))",
        &unrelated,
        &CompileConfig::default(),
        &overlays,
    )
    .unwrap_err();
    assert!(error.message.contains("not included"));
    fs::write(base.join("lim.lsp"), "schema-version = 2").unwrap();
    let error = lim::check_source_for_editor(text, &imported, &CompileConfig::default(), &overlays)
        .unwrap_err();
    assert!(error.message.contains("schema-version"));
    assert!(!base.join(".lim").exists());
}

#[test]
fn cli_build_and_assembly_generation_and_rejected_context_paths() {
    let base = directory("outputs");
    fs::write(base.join("main.lim"), "(#fn main () #u64 (#return 42u64))").unwrap();
    for args in [
        vec!["main.lim", "-o", "binary", "--write-lsp-config", "lim.lsp"],
        vec![
            "--emit-asm",
            "main.lim",
            "out.s",
            "--write-lsp-config",
            "lim.lsp",
        ],
    ] {
        let output = Command::new(env!("CARGO_BIN_EXE_lim"))
            .current_dir(&base)
            .args(args)
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
    let original = fs::read(base.join("main.lim")).unwrap();
    for args in [
        vec!["--check", "main.lim", "--write-lsp-config", "main.lim"],
        vec!["lsp", "--write-lsp-config", "lim.lsp"],
        vec!["--check", "main.lim", "--write-lsp-config"],
        vec![
            "main.lim",
            "-o",
            "same.lsp",
            "--write-lsp-config",
            "same.lsp",
        ],
    ] {
        let output = Command::new(env!("CARGO_BIN_EXE_lim"))
            .current_dir(&base)
            .args(args)
            .output()
            .unwrap();
        assert!(!output.status.success());
    }
    assert_eq!(original, fs::read(base.join("main.lim")).unwrap());
}
