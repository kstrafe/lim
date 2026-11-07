use lim::{lsp_context::LspContext, CompileConfig, TargetDescription};
use std::{fs, path::PathBuf, process::Command};

fn directory(name: &str) -> PathBuf {
    let path = std::env::temp_dir().join(format!("lim-lsp-context-{name}-{}", std::process::id()));
    fs::create_dir_all(&path).unwrap();
    path
}

fn assert_cfg(config: &CompileConfig, key: &str, value: &str) {
    let source = format!(
        "(#cfg-if (#cfg-is #{key} {value}) \
         (#fn main () #u64 (#return 0u64)) \
         (#cfg-else (#fn main () #u64 (#return missing))))"
    );
    let program = lim::parse_program_with_config(&source, config).unwrap();
    lim::check_types(&program).unwrap();
}

#[test]
fn multiple_context_blocks_keep_settings_independent_and_reject_invalid_documents() {
    let base = directory("multiple-parser");
    let path = base.join("lim.lsp");
    let valid = "schema-version = 2\n[[context]]\nentry = \"app.lim\"\ntarget = \"x86_64-sysv\"\ncfg = \"mode=app\"\nmodule-path = \"app-modules\"\n[[context]]\nentry = \"test.lim\"\ntarget = \"aarch64-linux\"\ncfg = \"mode=test\"\nmodule-path = \"test-modules\"\n";
    fs::write(&path, valid).unwrap();
    let contexts = LspContext::read_all(&path).unwrap();
    assert_eq!(contexts.len(), 2);
    assert_eq!(contexts[0].entry, base.join("app.lim"));
    assert_eq!(contexts[1].entry, base.join("test.lim"));
    assert_eq!(contexts[1].target, TargetDescription::AARCH64_LINUX);
    assert!(
        LspContext::read(&path).is_err(),
        "single-context API must not silently pick one"
    );
    for invalid in [
        valid.replace("schema-version = 2", "schema-version = 3"),
        valid.replace("target = \"aarch64-linux\"", "target = \"unsupported\""),
        valid.replace("[[context]]\nentry = \"app.lim\"", "entry = \"app.lim\""),
        valid.replace(
            "cfg = \"mode=test\"",
            "cfg = \"mode=test\"\ncfg = \"mode=again\"",
        ),
        format!("{valid}[[context]]\n"),
        format!(
            "schema-version = 2\n{}",
            "[[context]]\nentry = \"app.lim\"\ntarget = \"x86_64-sysv\"\n".repeat(2)
        ),
        format!(
            "schema-version = 2\n{}",
            (0..129)
                .map(|i| format!(
                    "[[context]]\nentry = \"entry-{i}.lim\"\ntarget = \"x86_64-sysv\"\n"
                ))
                .collect::<String>()
        ),
    ] {
        fs::write(&path, &invalid).unwrap();
        assert!(LspContext::read_all(&path).is_err(), "{invalid}");
    }
    fs::remove_dir_all(base).unwrap();
}

#[test]
fn cli_accumulates_distinct_entries_and_cfg_variants_without_duplicate_writes() {
    let base = directory("multiple-cli");
    for entry in ["app.lim", "test.lim"] {
        fs::write(base.join(entry), "(#fn main () #u64 (#return 0u64))").unwrap();
    }
    let run = |entry: &str, mode: &str| {
        Command::new(env!("CARGO_BIN_EXE_lim"))
            .current_dir(&base)
            .args([
                "--check",
                entry,
                "--cfg",
                &format!("mode={mode}"),
                "--write-lsp-config",
                "lim.lsp",
            ])
            .output()
            .unwrap()
    };
    for (entry, mode) in [
        ("app.lim", "app"),
        ("test.lim", "test"),
        ("app.lim", "alternate"),
    ] {
        let result = run(entry, mode);
        assert!(
            result.status.success(),
            "{}",
            String::from_utf8_lossy(&result.stderr)
        );
    }
    let path = base.join("lim.lsp");
    let contexts = LspContext::read_all(&path).unwrap();
    assert_eq!(contexts.len(), 3);
    assert_eq!(contexts[0].entry, base.join("app.lim"));
    assert_eq!(contexts[1].entry, base.join("test.lim"));
    assert_eq!(contexts[2].entry, base.join("app.lim"));
    let original = fs::read(&path).unwrap();
    let time = std::time::SystemTime::UNIX_EPOCH + std::time::Duration::from_secs(1_000_000);
    fs::OpenOptions::new()
        .write(true)
        .open(&path)
        .unwrap()
        .set_times(fs::FileTimes::new().set_modified(time))
        .unwrap();
    assert!(run("app.lim", "app").status.success());
    assert_eq!(fs::metadata(&path).unwrap().modified().unwrap(), time);
    assert_eq!(fs::read(&path).unwrap(), original);
    fs::write(base.join("app.lim"), ")").unwrap();
    assert!(
        run("test.lim", "new-test").status.success(),
        "a broken old entry must not block recording a healthy build"
    );
    assert_eq!(LspContext::read_all(&path).unwrap().len(), 4);
    let original = fs::read(&path).unwrap();
    fs::write(base.join("test.lim"), ")").unwrap();
    assert!(!run("test.lim", "broken").status.success());
    assert_eq!(fs::read(&path).unwrap(), original);
    fs::remove_dir_all(base).unwrap();
}

#[test]
fn parallel_cli_recording_preserves_every_entry() {
    let base = directory("multiple-parallel");
    let mut children = Vec::new();
    for index in 0..8 {
        let entry = format!("entry-{index}.lim");
        fs::write(base.join(&entry), "(#fn main () #u64 (#return 0u64))").unwrap();
        children.push(
            Command::new(env!("CARGO_BIN_EXE_lim"))
                .current_dir(&base)
                .args(["--check", &entry, "--write-lsp-config", "lim.lsp"])
                .stdout(std::process::Stdio::piped())
                .stderr(std::process::Stdio::piped())
                .spawn()
                .unwrap(),
        );
    }
    for child in children {
        let result = child.wait_with_output().unwrap();
        assert!(
            result.status.success(),
            "{}",
            String::from_utf8_lossy(&result.stderr)
        );
    }
    let contexts = LspContext::read_all(&base.join("lim.lsp")).unwrap();
    assert_eq!(contexts.len(), 8);
    let entries = contexts
        .into_iter()
        .map(|context| context.entry)
        .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(
        entries,
        (0..8)
            .map(|index| base.join(format!("entry-{index}.lim")))
            .collect()
    );
    fs::remove_dir_all(base).unwrap();
}

#[test]
fn editor_checks_all_contexts_including_the_shared_file() {
    let base = directory("multiple-editor");
    let library = base.join("library.lim");
    let source = "(#fn read-value () #u64 (#return false))";
    fs::write(&library, source).unwrap();
    let mut contexts = Vec::new();
    for (name, ty, value) in [("app", "#u64", "42u64"), ("test", "#bool", "false")] {
        let entry = base.join(format!("{name}.lim"));
        fs::write(
            &entry,
            format!("(#alias read-value = ./library.lim::read-value) (#fn provide () {ty} (#return {value}))"),
        )
        .unwrap();
        contexts.push(LspContext {
            entry,
            target: TargetDescription::X86_64_SYSTEM_V,
            config: CompileConfig::default(),
        });
    }
    LspContext::write_all(&contexts, &base.join("lim.lsp")).unwrap();
    let error = lim::check_source_for_editor(
        source,
        &library,
        &CompileConfig::default(),
        &std::collections::HashMap::new(),
    )
    .unwrap_err();
    assert_eq!(error.code, lim::DiagnosticCode::Type);
    assert_eq!(error.source_name.as_deref(), library.to_str());
    assert!(!base.join(".lim").exists());
    fs::remove_dir_all(base).unwrap();
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
fn omitted_target_and_cfg_use_host_defaults_in_both_schemas() {
    let base = directory("host-defaults");
    let path = base.join("lim.lsp");
    let target = TargetDescription::host().unwrap();
    for header in ["schema-version = 1\n", "schema-version = 2\n[[context]]\n"] {
        fs::write(&path, format!("{header}entry = \"app.lim\"\n")).unwrap();
        let context = LspContext::read(&path).unwrap();
        assert_eq!(context.target, target);
        assert_cfg(&context.config, "arch", std::env::consts::ARCH);
        assert_cfg(&context.config, "os", std::env::consts::OS);
        assert_cfg(&context.config, "platform", std::env::consts::OS);
    }
    fs::remove_dir_all(base).unwrap();
}

#[test]
fn omitted_cfg_uses_each_selected_target_and_preserves_explicit_overrides() {
    let base = directory("target-defaults");
    let path = base.join("lim.lsp");
    fs::write(
        &path,
        "schema-version = 2\n\
         [[context]]\nentry = \"app.lim\"\ntarget = \"x86_64-sysv\"\n\
         [[context]]\nentry = \"test.lim\"\ntarget = \"aarch64-linux\"\n\
         [[context]]\nentry = \"override.lim\"\ntarget = \"aarch64-linux\"\n\
         cfg = \"arch=custom\"\ncfg = \"feature=enabled\"\n",
    )
    .unwrap();
    let contexts = LspContext::read_all(&path).unwrap();
    for (context, (target, arch, triple)) in contexts[..2].iter().zip([
        (
            TargetDescription::X86_64_SYSTEM_V,
            "x86_64",
            "x86_64-unknown-linux-gnu",
        ),
        (
            TargetDescription::AARCH64_LINUX,
            "aarch64",
            "aarch64-unknown-linux-gnu",
        ),
    ]) {
        assert_eq!(context.target, target);
        assert_cfg(&context.config, "arch", arch);
        assert_cfg(&context.config, "target", triple);
        assert_cfg(&context.config, "platform", "linux");
    }
    let config = &contexts[2].config;
    assert_cfg(config, "arch", "custom");
    assert_cfg(config, "feature", "enabled");
    assert_cfg(config, "target", "aarch64-unknown-linux-gnu");
    assert_cfg(config, "os", "linux");
    fs::remove_dir_all(base).unwrap();
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
        "proof-work = \"100\"",
        "proof-phase-bytes = \"4096\"",
        "proof-total-bytes = \"8192\"",
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
    let text = "(#fn child () #u64 (#return 42u64))";
    fs::write(&entry, "(#cfg-if (#cfg-is #feature enabled) (#type Number #u64) (#cfg-else (#type Number #bool))) (#alias child = ./child.lim::child) (#fn main () Number (#return (#call child ())))").unwrap();
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
