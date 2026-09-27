mod support;

use std::{fs, process::Command, time::Duration};

#[test]
fn wake_aware_pipeline_is_generated_and_runs() {
    let scratch = support::Scratch::new("async-wake");
    let source = include_str!("../examples/async_wake_pipeline.lim")
        .replace(
            "../library/tasks.lim",
            &format!("{}/library/tasks.lim", env!("CARGO_MANIFEST_DIR")),
        )
        .replace(
            "../library/local_waker.lim",
            &format!("{}/library/local_waker.lim", env!("CARGO_MANIFEST_DIR")),
        );
    let input = scratch.path().join("main.lim");
    let program = scratch.path().join("program");
    fs::write(&input, source).unwrap();
    let (status, _, stderr) = support::run(
        Command::new(env!("CARGO_BIN_EXE_lim"))
            .arg(&input)
            .arg("-o")
            .arg(&program),
        Duration::from_secs(20),
        1024 * 1024,
    )
    .unwrap();
    assert!(status.success(), "{}", String::from_utf8_lossy(&stderr));
    let generated = fs::read_dir(scratch.path().join(".lim/cache"))
        .unwrap()
        .filter_map(Result::ok)
        .filter(|entry| {
            entry
                .path()
                .extension()
                .is_some_and(|extension| extension == "lim")
        })
        .map(|entry| fs::read_to_string(entry.path()).unwrap())
        .collect::<Vec<_>>()
        .join("\n");
    assert!(generated.contains("(#fn pipeline-poll"));
    assert!(generated.contains("(waker (#ref LocalWaker))"));
    assert!(generated.contains("(waker waker)"));
    let (status, _, stderr) =
        support::run(&mut Command::new(program), Duration::from_secs(5), 1024).unwrap();
    assert_eq!(
        status.code(),
        Some(42),
        "{}",
        String::from_utf8_lossy(&stderr)
    );
}

#[test]
fn pending_task_cannot_export_a_borrowed_waker() {
    let source = "(#struct Executor ((count u64)))
        (#struct Waker ((executor (#ref Executor))))
        (#enum State ((Waiting (#ref Waker))))
        (#fn escape () State
          (#let executor Executor (#struct-literal Executor ((count 0u64))))
          (#let waker Waker (#struct-literal Waker ((executor (#borrow executor)))))
          (#return (Waiting (#borrow waker))))";
    let program = lim::parse_program(source).unwrap();
    let error = lim::check_types(&program).unwrap_err();
    assert!(
        error.contains("local") || error.contains("outlive"),
        "{error}"
    );
}
