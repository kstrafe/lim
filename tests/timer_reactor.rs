mod support;

use std::process::Command;

fn compile_and_run(source: &str, path: &std::path::Path) -> i32 {
    let scratch = support::Scratch::new("timer-reactor");
    let assembly = lim::compile_source_to_assembly(
        source,
        path,
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
    Command::new(binary).status().unwrap().code().unwrap()
}

#[test]
fn one_shot_timer_waits_without_spinning_and_can_be_cancelled() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/timer_reactor1.lim");
    let source = std::fs::read_to_string(&path).unwrap();
    assert_eq!(compile_and_run(&source, &path), 42);
}

#[test]
fn expression_statement_does_not_become_a_large_return_value() {
    let source = "(#struct Large ((a u64) (b u64) (c u64) (d u64) (e u64)))
      (#fn make () Large
        (#assert true)
        (#return (#struct-literal Large
          ((a 42u64) (b 0u64) (c 0u64) (d 0u64) (e 0u64)))))
      (#fn main () u64
        (#let value Large (#call make (:)))
        (#return (#get value a)))";
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/aggregate_let.lim");
    assert_eq!(compile_and_run(source, &path), 42);
}
