mod support;

use std::{fs, process::Command, time::Duration};

#[test]
fn bounded_ready_queue_runs_natively_and_reports_full_and_empty() {
    let scratch = support::Scratch::new("ready-queue");
    let root = env!("CARGO_MANIFEST_DIR");
    let source = format!(
        "(#import \"{root}/library/ready_queue.lim\")\n{}",
        fs::read_to_string(format!("{root}/examples/ready_queue.lim"))
            .unwrap()
            .replace("(#import \"../library/ready_queue.lim\")", "")
    );
    fs::write(scratch.path().join("main.lim"), source).unwrap();
    let build = support::run(
        Command::new(env!("CARGO_BIN_EXE_lim"))
            .arg(scratch.path().join("main.lim"))
            .arg("-o")
            .arg(scratch.path().join("program")),
        Duration::from_secs(20),
        1024 * 1024,
    )
    .unwrap();
    assert!(build.0.success(), "{}", String::from_utf8_lossy(&build.2));
    let result = support::run(
        &mut Command::new(scratch.path().join("program")),
        Duration::from_secs(3),
        1024,
    )
    .unwrap();
    assert_eq!(result.0.code(), Some(99), "status: {:?}", result.0);
}

#[test]
fn ready_queue_rejects_zero_capacity() {
    let source = format!(
        "(#import \"{}/library/ready_queue.lim\")\n(@ready-queue EmptyQueue EmptyEnqueue EmptyDequeue empty-create empty-enqueue empty-dequeue EmptyEnqueued EmptyFull EmptyItem EmptyEmpty ())\n(#fn main () u64 (#return 0u64))",
        env!("CARGO_MANIFEST_DIR")
    );
    let scratch = support::Scratch::new("ready-queue-zero");
    let error = lim::compile_source_to_assembly(
        &source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err();
    assert!(
        error.message.contains("at least one slot ID"),
        "{}",
        error.message
    );
}

#[test]
fn distinct_ready_queue_instantiations_have_disjoint_generated_names() {
    let source = format!(
        "(#import \"{}/library/ready_queue.lim\")
         (@ready-queue First FirstEnqueue FirstDequeue first-create first-enqueue first-dequeue FirstEnqueued FirstFull FirstItem FirstEmpty (a))
         (@ready-queue Second SecondEnqueue SecondDequeue second-create second-enqueue second-dequeue SecondEnqueued SecondFull SecondItem SecondEmpty (b c))
         (#fn main () u64
           (#let first First (#call first-create (#fn-args)))
           (#let second Second (#call second-create (#fn-args)))
           (#forget first) (#forget second) (#return 42u64))",
        env!("CARGO_MANIFEST_DIR")
    );
    let scratch = support::Scratch::new("ready-queue-pair");
    lim::compile_source_to_assembly(
        &source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
}

#[test]
fn ready_queue_state_cannot_be_implicitly_copied() {
    let source = format!(
        "(#import \"{}/library/ready_queue.lim\")
         (@ready-queue Queue QueueEnqueue QueueDequeue queue-create queue-enqueue queue-dequeue Enqueued Full Item Empty (a))
         (#fn main () u64
           (#let queue Queue (#call queue-create (#fn-args)))
           (#let moved Queue queue)
           (#forget queue) (#forget moved) (#return 0u64))",
        env!("CARGO_MANIFEST_DIR")
    );
    let scratch = support::Scratch::new("ready-queue-linear");
    let error = lim::compile_source_to_assembly(
        &source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_err();
    assert!(
        error.message.contains("queue")
            && (error.message.contains("moved") || error.message.contains("consumed")),
        "{}",
        error.message
    );
}
