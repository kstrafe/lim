mod support;

use std::process::Command;

#[test]
fn ready_bits_coalesce_and_stale_tokens_cannot_wake_reused_slots() {
    compile_and_run("wake_ready4.lim");
}

#[test]
fn polling_wake_is_visible_after_pending_and_retires_cleanly() {
    compile_and_run("async_registered_wake.lim");
}

fn compile_and_run(name: &str) {
    let scratch = support::Scratch::new("wake-ready4");
    let source_path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("examples")
        .join(name);
    let source = std::fs::read_to_string(&source_path).unwrap();
    let assembly = lim::compile_source_to_assembly(
        &source,
        &source_path,
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    let binary = scratch.path().join("program");
    lim::link_native_binary(
        &assembly,
        &binary,
        &[],
        &[],
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    assert_eq!(Command::new(binary).status().unwrap().code(), Some(42));
}
