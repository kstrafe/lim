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
fn wake_executor_rejects_unsupported_capacity_and_slots() {
    let scratch = support::Scratch::new("wake-executor-shapes");
    let cases = [
        (
            "(@wake-executor run Results Task Poll Pending Ready u64 poll Waker wait
              (context u64)
              ((s0 t0 w0 r0 0u32) (s1 t1 w1 r1 1u32)
               (s2 t2 w2 r2 2u32) (s3 t3 w3 r3 3u32) (s4 t4 w4 r4 0u32)))",
            "supports at most four task jobs",
        ),
        (
            "(@wake-executor run Results Task Poll Pending Ready u64 poll Waker wait
              (context u64) ((state task waker result 4u32)))",
            "task slot must be 0u32 through 3u32",
        ),
        (
            "(@wake-executor run Results Task Poll Pending Ready u64 poll Waker wait
              (context u64)
              ((first-state first-task first-waker first-result 0u32)
               (second-state second-task second-waker second-result 0u32)))",
            "slots must be consecutive from 0u32",
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
        assert!(error.message.contains(expected), "{}", error.message);
        assert!(error.span.is_some());
    }
}

#[test]
fn wake_executor_runs_every_supported_fixed_capacity() {
    let scratch = support::Scratch::new("wake-executor-capacity");
    for capacity in 1..=4 {
        let jobs = (0..capacity)
            .map(|slot| format!("(state{slot} input{slot} wake{slot} result{slot} {slot}u32)"))
            .collect::<Vec<_>>()
            .join(" ");
        let mut call_args = (0..capacity)
            .map(|slot| format!(": input{slot} Waiting"))
            .collect::<Vec<_>>();
        call_args.extend((0..capacity).map(|slot| format!(": wake{slot} waker-ref")));
        call_args.push(": context 0u32".to_owned());
        let mut total = "(#get results result0)".to_owned();
        for slot in 1..capacity {
            total = format!("(#u64.+.wrap {total} (#get results result{slot}))");
        }
        let body = format!(
            "(@task (Task Poll Pending Ready) u64 ((Waiting)))
             (#struct Waker ((marker u64)))
             (#fn poll ((task Task) (waker (#ref Waker))) Poll
               (#forget waker) (#forget task) (#return (Ready 1u64)))
             (#fn wait ((context u32)) u32 (#return context))
             (@wake-executor run Results Task Poll Pending Ready u64 poll Waker
               wait (context u32) ({jobs}))
             (#fn main () u64
               (#let waker Waker (#struct-literal Waker ((marker 0u64))))
               (#let waker-ref (#ref Waker) (#borrow waker))
               (#let results Results
                 (#call run ({named_args})))
               (#forget waker)
               (#return {total}))",
            named_args = call_args.join(" "),
        );
        let program = source(&body);
        let assembly = lim::compile_source_to_assembly(
            &program,
            &scratch.path().join(format!("capacity-{capacity}.lim")),
            &lim::CompileConfig::default(),
            &scratch.path().join("cache"),
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap_or_else(|error| panic!("capacity {capacity}: {}", error.message));
        let binary = scratch.path().join(format!("capacity-{capacity}"));
        lim::link_native_binary(
            &assembly,
            &binary,
            &[],
            &[],
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap();
        assert_eq!(
            Command::new(binary).status().unwrap().code(),
            Some(capacity as i32),
            "capacity {capacity}"
        );
    }
}

#[test]
fn cooperative_and_composed_tasks_use_inline_storage() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let scratch = support::Scratch::new("task-storage");
    for example in [
        "cooperative_tasks.lim",
        "async_pipeline.lim",
        "wake_executor.lim",
    ] {
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

#[test]
fn wake_executor_generated_code_is_inspectable() {
    let scratch = support::Scratch::new("wake-executor-generated");
    let root = env!("CARGO_MANIFEST_DIR");
    let source = include_str!("../examples/wake_executor.lim")
        .replace("../library/tasks.lim", &format!("{root}/library/tasks.lim"))
        .replace(
            "../library/local_waker.lim",
            &format!("{root}/library/local_waker.lim"),
        )
        .replace(
            "../library/wake_ready4.lim",
            &format!("{root}/library/wake_ready4.lim"),
        )
        .replace(
            "../library/async_poll4.lim",
            &format!("{root}/library/async_poll4.lim"),
        )
        .replace(
            "../library/timer_reactor1.lim",
            &format!("{root}/library/timer_reactor1.lim"),
        );
    let input = scratch.path().join("main.lim");
    fs::write(&input, source).unwrap();
    let build = support::run(
        Command::new(env!("CARGO_BIN_EXE_lim"))
            .arg(&input)
            .arg("-o")
            .arg(scratch.path().join("program")),
        Duration::from_secs(20),
        1024 * 1024,
    )
    .unwrap();
    assert!(build.0.success(), "{}", String::from_utf8_lossy(&build.2));
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
    assert!(generated.contains("(#fn run-jobs"), "{generated}");
    assert!(generated.contains("(#call job-poll"), "{generated}");
    assert!(generated.contains("(#call wait-ready"), "{generated}");
}
