mod support;
use std::{fs, path::Path, process::Command, time::Duration};

fn source(body: &str) -> String {
    format!(
        "(#import \"{}/library/tasks.lim\")\n{body}",
        env!("CARGO_MANIFEST_DIR")
    )
}

#[test]
fn explicit_cancellation_consumes_a_task_and_runs_its_handler() {
    let scratch = support::Scratch::new("task-cancel");
    let source = include_str!("../examples/task_cancellation.lim")
        .replace(
            "../library/tasks.lim",
            &format!("{}/library/tasks.lim", env!("CARGO_MANIFEST_DIR")),
        )
        .replace(
            "../library/cell.lim",
            &format!("{}/library/cell.lim", env!("CARGO_MANIFEST_DIR")),
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
    assert_eq!(
        support::run(
            &mut Command::new(scratch.path().join("program")),
            Duration::from_secs(3),
            1024
        )
        .unwrap()
        .0
        .code(),
        Some(42)
    );
}

#[test]
fn generated_tasks_preserve_borrow_linearity_exhaustiveness_and_send_checks() {
    let scratch = support::Scratch::new("task-errors");
    let cases = [
        (
            "(@task (Held Poll Pending Ready) u64 ((Holding (#ref u64))))
          (#fn bad () Held (#let value u64 42u64) (#return (Holding (#borrow value))))",
            "local",
        ),
        (
            "(@task (Held Poll Pending Ready) u64 ((Holding (#ref u64))))
          (#fn poll ((task Held)) Poll (#forget task) (#return (Ready 1u64)))
          (#fn main () u64 (#let-mut value u64 1u64) (#let task Held (Holding (#borrow value)))
            (#set value 2u64) (#forget task) (#return value))",
            "borrow",
        ),
        (
            "(@task (Held Poll Pending Ready) u64 ((Holding u64)))
          (#fn poll ((task Held)) Poll (#forget task) (#return (Ready 1u64)))
          (#fn main () u64 (#let task Held (Holding 1u64))
            (#let first Poll (#call poll (: task task)))
            (#let second Poll (#call poll (: task task)))
            (#forget first) (#forget second) (#return 0u64))",
            "more than once",
        ),
        (
            "(@task (Held Poll Pending Ready) u64 ((First u64) (Second u64)))
          (#fn release ((task u64)) () (#forget task) (#return ()))
          (@task-cancel cancel Held ((First release)))",
            "exhaustive",
        ),
        (
            "(@task (Held Poll Pending Ready) u64 ((Holding (#ref (#ptr u8)))))
          (#fn poll ((task Held)) Poll (#forget task) (#return (Ready 1u64)))
          (@threaded-executor run Results ((held Held Poll Pending Ready poll u64 held-input)) Worker)",
            "Send",
        ),
    ];
    for (index, (body, expected)) in cases.iter().enumerate() {
        let source = source(body);
        let error = lim::compile_source_to_assembly(
            &source,
            &scratch.path().join(format!("bad-{index}.lim")),
            &lim::CompileConfig::default(),
            &scratch.path().join("cache"),
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap_err();
        assert!(
            error.message.contains(expected),
            "case {index}: {}",
            error.message
        );
        assert!(error.span.is_some(), "case {index}");
        assert!(lim::render_diagnostic(&error, &source, "task.lim").contains('^'));
    }
}

#[test]
fn cooperative_and_composed_tasks_use_inline_storage() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let scratch = support::Scratch::new("task-storage");
    for example in ["cooperative_tasks.lim", "async_pipeline.lim"] {
        let input = root.join("examples").join(example);
        let source = fs::read_to_string(&input).unwrap();
        let assembly = lim::compile_source_to_assembly(
            &source,
            &input,
            &lim::CompileConfig::default(),
            &scratch.path().join("cache"),
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap();
        assert!(!assembly.contains("call malloc"));
        assert!(!assembly.contains("call calloc"));
        assert!(!assembly.contains("call realloc"));
    }
}
