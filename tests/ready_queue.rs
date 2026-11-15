mod support;

use std::{fs, process::Command, time::Duration};

#[test]
fn bounded_ready_queue_runs_natively_and_reports_full_and_empty() {
    let scratch = support::Scratch::new("ready-queue");
    let root = env!("CARGO_MANIFEST_DIR");
    let source = format!(
        "#alias lim-gen-ready-queue = \"{root}/library/ready_queue.lim::#ready-queue\"\n{0}",
        fs::read_to_string(format!("{root}/examples/ready_queue.lim"))
            .unwrap()
            .replace(
                "#alias lim-gen-ready-queue = ../library/ready_queue.lim::#ready-queue",
                ""
            )
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
        "#alias lim-gen-ready-queue = \"{0}/library/ready_queue.lim::#ready-queue\"\n#generate lim-gen-ready-queue EmptyQueue EmptyEnqueue EmptyDequeue empty-create empty-enqueue empty-dequeue EmptyEnqueue.EmptyEnqueued EmptyEnqueue.EmptyFull EmptyDequeue.EmptyItem EmptyDequeue.EmptyEmpty ()\n#fn main () #u64 (#return 0u64)\n",
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
        "#alias lim-gen-ready-queue = \"{0}/library/ready_queue.lim::#ready-queue\"\n#generate lim-gen-ready-queue First FirstEnqueue FirstDequeue first-create first-enqueue first-dequeue FirstEnqueue.FirstEnqueued FirstEnqueue.FirstFull FirstDequeue.FirstItem FirstDequeue.FirstEmpty (a)\n#generate lim-gen-ready-queue Second SecondEnqueue SecondDequeue second-create second-enqueue second-dequeue SecondEnqueue.SecondEnqueued SecondEnqueue.SecondFull SecondDequeue.SecondItem SecondDequeue.SecondEmpty (b c)\n#fn main () #u64\n             (#let first First (#call first-create ()))\n             (#let second Second (#call second-create ()))\n             (#forget first) (#forget second) (#return 42u64)\n",
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
        "#alias lim-gen-ready-queue = \"{0}/library/ready_queue.lim::#ready-queue\"\n#generate lim-gen-ready-queue Queue QueueEnqueue QueueDequeue queue-create queue-enqueue queue-dequeue QueueEnqueue.Enqueued QueueEnqueue.Full QueueDequeue.Item QueueDequeue.Empty (a)\n#fn main () #u64\n             (#let queue Queue (#call queue-create ()))\n             (#let moved Queue queue)\n             (#forget queue) (#forget moved) (#return 0u64)\n",
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

#[test]
fn queue_field_can_be_used_through_a_mutable_owner_reference() {
    let source = format!(
        "#alias lim-gen-ready-queue = \"{0}/library/ready_queue.lim::#ready-queue\"\n#generate lim-gen-ready-queue Queue QueueEnqueue QueueDequeue queue-create queue-enqueue queue-dequeue QueueEnqueue.Enqueued QueueEnqueue.Full QueueDequeue.Item QueueDequeue.Empty (a b)\n#struct Holder (#linear) ((ready Queue))\n\n#fn push ((holder (#ref-mut Holder))) ()\n             (#let result QueueEnqueue\n               (#call queue-enqueue ((queue (#borrow-mut (#get holder ready))) (task-id 42u64))))\n             (#forget result) (#return ())\n#fn pop ((holder (#ref-mut Holder))) #u64\n             (#let result QueueDequeue\n               (#call queue-dequeue ((queue (#borrow-mut (#get holder ready))))))\n             (#return (#match result\n               (#case (QueueDequeue.Item value) value) (#case QueueDequeue.Empty 0u64)))\n#fn main () #u64\n             (#let-mut holder Holder (#struct-literal Holder\n               ((ready (#call queue-create ())))))\n             (#call push ((holder (#borrow-mut holder))))\n             (#let value #u64 (#call pop ((holder (#borrow-mut holder)))))\n             (#forget holder) (#return value)\n",
        env!("CARGO_MANIFEST_DIR")
    );
    let scratch = support::Scratch::new("ready-queue-field");
    let assembly = lim::compile_source_to_assembly(
        &source,
        &scratch.path().join("main.lim"),
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
