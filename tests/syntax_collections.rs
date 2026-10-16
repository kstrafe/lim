mod support;
use std::{fs, process::Command, time::Duration};

#[test]
fn distributed_error_enum_is_concrete_cached_and_allocation_free() {
    let scratch = support::Scratch::new("collections");
    let root = scratch.path();
    fs::write(
        root.join("declaration.lim"),
        "(#syntax-collection Errors) (#gn errors (entries name) `((#enum ,name () ,entries)))",
    )
    .unwrap();
    fs::write(
        root.join("a.lim"),
        "(#import \"declaration.lim\") (#syntax-contribute Errors a (First #u64))",
    )
    .unwrap();
    fs::write(
        root.join("b.lim"),
        "(#import \"declaration.lim\") (#syntax-contribute Errors b (Second #u32))",
    )
    .unwrap();
    let source = "(#import \"b.lim\") (#import \"a.lim\") (@errors (#syntax-distribute Errors) Error)
      (#fn main () #u64 (#let error Error (First 42u64)) (#return (#match error (#case (First n) n) (#case (Second n) (#as n #u64)))))";
    fs::write(root.join("main.lim"), source).unwrap();
    for _ in 0..2 {
        let output = support::run(
            Command::new(env!("CARGO_BIN_EXE_lim"))
                .arg(root.join("main.lim"))
                .arg("-o")
                .arg(root.join("program")),
            Duration::from_secs(20),
            1024 * 1024,
        )
        .unwrap();
        assert!(output.0.success(), "{}", String::from_utf8_lossy(&output.2));
        assert_eq!(
            support::run(
                &mut Command::new(root.join("program")),
                Duration::from_secs(2),
                1024
            )
            .unwrap()
            .0
            .code(),
            Some(42)
        );
    }
    let asm = lim::compile_source_to_assembly(
        source,
        &root.join("main.lim"),
        &lim::CompileConfig::default(),
        &root.join(".lim"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    assert!(!asm.contains("call malloc"));
    assert!(!asm.contains("call calloc"));
}

#[test]
fn collection_errors_have_source_spans_and_generation_cannot_mutate_snapshots() {
    for (source, message) in [
        ("(#syntax-contribute Missing entry 1)", "unknown syntax collection"),
        ("(#syntax-collection Errors) (#syntax-collection Errors)", "duplicate syntax collection"),
        ("(#syntax-collection Errors) (#syntax-contribute Errors x 1) (#syntax-contribute Errors x 2)", "conflicting contribution"),
        ("(#gn bad () `((#syntax-collection Late))) (@bad)", "frozen before generation"),
        ("(#gn use (entries) `()) (@use (#syntax-distribute Missing))", "unknown syntax collection"),
        ("(#syntax-collection Entries) (#gn use (entries) `()) (@use (#syntax-distribute))", "#syntax-distribute requires exactly one syntax collection name"),
        ("(#syntax-collection Entries) (#gn use (entries) `()) (@use (#syntax-distribute Entries Extra))", "#syntax-distribute requires exactly one syntax collection name"),
        ("(#gn use ((entries #syntax-collection)) `()) (@use Entries)", "invalid generator capability"),
    ] {
        let error = lim::compile_source_to_assembly(source, std::path::Path::new("collections.lim"), &lim::CompileConfig::default(), &support::Scratch::new("collection-errors").path().join("cache"), lim::TargetDescription::X86_64_SYSTEM_V).unwrap_err();
        assert!(error.message.contains(message), "{}", error.message);
        assert!(error.span.is_some(), "{source}");
        assert!(lim::render_diagnostic(&error, source, "collections.lim").contains('^'));
    }
}

#[test]
fn cfg_selection_and_external_prefixes_apply_before_freezing() {
    let scratch = support::Scratch::new("collection-cfg");
    let root = scratch.path();
    fs::write(
        root.join("module.lim"),
        "(#syntax-collection Entries)
      (#syntax-contribute Entries stable (Stable #u64))
      (#cfg-if (#cfg-is #extra yes) (#syntax-contribute Entries extra (Extra #u32)))
      (#gn errors (entries name) `((#enum ,name () ,entries)))
      (@errors (#syntax-distribute Entries) Errors)
      (#fn value () #u64 (#return (#match (Stable 42u64) (#case (Stable n) n) (#case _ 0u64))))",
    )
    .unwrap();
    let source =
        "(#import-external \"module.lim\" ext-) (#fn main () #u64 (#return (#call ext-value (:))))";
    let mut config = lim::CompileConfig::default();
    config.set("extra", "no");
    let first = lim::compile_source_to_assembly(
        source,
        &root.join("main.lim"),
        &config,
        &root.join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    assert!(first.contains("ext"));
    config.set("extra", "yes");
    lim::compile_source_to_assembly(
        source,
        &root.join("main.lim"),
        &config,
        &root.join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
}
