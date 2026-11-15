mod support;
use std::{fs, path::Path, process::Command, time::Duration};

fn source(body: &str) -> String {
    format!(
        "#alias lim-gen-async = \"{0}/library/tasks.lim::#async\"\n#alias lim-gen-async-wake = \"{0}/library/tasks.lim::#async-wake\"\n#alias lim-gen-executor = \"{0}/library/tasks.lim::#executor\"\n#alias lim-gen-task = \"{0}/library/tasks.lim::#task\"\n#alias lim-gen-task-cancel = \"{0}/library/tasks.lim::#task-cancel\"\n#alias lim-gen-threaded-executor = \"{0}/library/tasks.lim::#threaded-executor\"\n#alias lim-gen-wake-executor = \"{0}/library/tasks.lim::#wake-executor\"\n#alias async-complete = \"{0}/library/tasks.lim::async-complete\"\n#alias async-poll-case = \"{0}/library/tasks.lim::async-poll-case\"\n#alias async-state = \"{0}/library/tasks.lim::async-state\"\n#alias async-wake-poll-case = \"{0}/library/tasks.lim::async-wake-poll-case\"\n#alias executor-field = \"{0}/library/tasks.lim::executor-field\"\n#alias executor-initialize = \"{0}/library/tasks.lim::executor-initialize\"\n#alias executor-name = \"{0}/library/tasks.lim::executor-name\"\n#alias executor-parameter = \"{0}/library/tasks.lim::executor-parameter\"\n#alias executor-poll = \"{0}/library/tasks.lim::executor-poll\"\n#alias executor-result = \"{0}/library/tasks.lim::executor-result\"\n#alias task-cancel-case = \"{0}/library/tasks.lim::task-cancel-case\"\n#alias task-eighth = \"{0}/library/tasks.lim::task-eighth\"\n#alias task-fifth = \"{0}/library/tasks.lim::task-fifth\"\n#alias task-fourth = \"{0}/library/tasks.lim::task-fourth\"\n#alias task-second = \"{0}/library/tasks.lim::task-second\"\n#alias task-seventh = \"{0}/library/tasks.lim::task-seventh\"\n#alias task-sixth = \"{0}/library/tasks.lim::task-sixth\"\n#alias task-third = \"{0}/library/tasks.lim::task-third\"\n#alias wake-executor-cancel-call = \"{0}/library/tasks.lim::wake-executor-cancel-call\"\n#alias wake-executor-field = \"{0}/library/tasks.lim::wake-executor-field\"\n#alias wake-executor-generate = \"{0}/library/tasks.lim::wake-executor-generate\"\n#alias wake-executor-initialize = \"{0}/library/tasks.lim::wake-executor-initialize\"\n#alias wake-executor-poll = \"{0}/library/tasks.lim::wake-executor-poll\"\n#alias wake-executor-result = \"{0}/library/tasks.lim::wake-executor-result\"\n#alias wake-executor-result-field = \"{0}/library/tasks.lim::wake-executor-result-field\"\n#alias wake-executor-slot = \"{0}/library/tasks.lim::wake-executor-slot\"\n#alias wake-executor-slots-valid = \"{0}/library/tasks.lim::wake-executor-slots-valid\"\n#alias wake-executor-state-name = \"{0}/library/tasks.lim::wake-executor-state-name\"\n#alias wake-executor-task-parameter = \"{0}/library/tasks.lim::wake-executor-task-parameter\"\n#alias wake-executor-task-parameter-form = \"{0}/library/tasks.lim::wake-executor-task-parameter-form\"\n#alias wake-executor-wait-result = \"{0}/library/tasks.lim::wake-executor-wait-result\"\n#alias wake-executor-waker-parameter = \"{0}/library/tasks.lim::wake-executor-waker-parameter\"\n#alias wake-executor-waker-parameter-form = \"{0}/library/tasks.lim::wake-executor-waker-parameter-form\"\n{body}",
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
            "#generate lim-gen-task (Held Poll Poll.Pending Poll.Ready) #u64 ((Held.Holding (#ref #u64)))
#fn bad {
  #params = ();
  #returns = Held;
  #body = ( (#let value #u64 42u64) (#return (Held.Holding (#borrow value)))\n  );\n}\n",
            "local",
        ),
        (
            "#generate lim-gen-task (Held Poll Poll.Pending Poll.Ready) #u64 ((Held.Holding (#ref #u64)))
#fn poll {
  #params = ((task Held));
  #returns = Poll;
  #body = ( (#forget task) (#return (Poll.Ready 1u64))
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = ( (#let-mut value #u64 1u64) (#let task Held (Held.Holding (#borrow value)))
              (#set value 2u64) (#forget task) (#return value)\n  );\n}\n",
            "borrow",
        ),
        (
            "#generate lim-gen-task (Held Poll Poll.Pending Poll.Ready) #u64 ((Held.Holding #u64))
#fn poll {
  #params = ((task Held));
  #returns = Poll;
  #body = ( (#forget task) (#return (Poll.Ready 1u64))
  );
}
#fn main {
  #params = ();
  #returns = #u64;
  #body = ( (#let task Held (Held.Holding 1u64))
              (#let first Poll (#call poll ((task task))))
              (#let second Poll (#call poll ((task task))))
              (#forget first) (#forget second) (#return 0u64)\n  );\n}\n",
            "more than once",
        ),
        (
            "#generate lim-gen-task (Held Poll Poll.Pending Poll.Ready) #u64 ((Held.First #u64) (Held.Second #u64))
#fn release {
  #params = ((task #u64));
  #returns = ();
  #body = ( (#forget task) (#return ())
  );
}
#generate lim-gen-task-cancel cancel Held ((Held.First release))\n",
            "exhaustive",
        ),
        (
            "#generate lim-gen-task (Held Poll Poll.Pending Poll.Ready) #u64 ((Held.Holding (#ref (#ptr #u8))))
#fn poll {
  #params = ((task Held));
  #returns = Poll;
  #body = ( (#forget task) (#return (Poll.Ready 1u64))
  );
}
#generate lim-gen-threaded-executor run Results ((held Held Poll Poll.Pending Poll.Ready poll #u64 held-input)) Worker\n",
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
            "#generate lim-gen-wake-executor run (Results Outcome Lifecycle Lifecycle.Running Outcome.Complete Lifecycle.Cancelling Outcome.Stopped)
                (Task Poll Poll.Pending Poll.Ready #u64 poll Waker)
                (WaitResult Poll.Ready Outcome.Stopped #i64 wait (context #u64)) cancel
                ((s0 t0 w0 r0 0u32) (s1 t1 w1 r1 1u32)
                 (s2 t2 w2 r2 2u32) (s3 t3 w3 r3 3u32) (s4 t4 w4 r4 0u32))\n",
            "supports at most four task jobs",
        ),
        (
            "#generate lim-gen-wake-executor run (Results Outcome Lifecycle Lifecycle.Running Outcome.Complete Lifecycle.Cancelling Outcome.Stopped)
                (Task Poll Poll.Pending Poll.Ready #u64 poll Waker)
                (WaitResult Poll.Ready Outcome.Stopped #i64 wait (context #u64)) cancel
                ((state task waker result 4u32))\n",
            "task slot must be 0u32 through 3u32",
        ),
        (
            "#generate lim-gen-wake-executor run (Results Outcome Lifecycle Lifecycle.Running Outcome.Complete Lifecycle.Cancelling Outcome.Stopped)
                (Task Poll Poll.Pending Poll.Ready #u64 poll Waker)
                (WaitResult Poll.Ready Outcome.Stopped #i64 wait (context #u64)) cancel
                ((first-state first-task first-waker first-result 0u32)
                 (second-state second-task second-waker second-result 0u32))\n",
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
            .map(|slot| format!("(input{slot} Task.Waiting)"))
            .collect::<Vec<_>>();
        call_args.extend((0..capacity).map(|slot| format!("(wake{slot} waker-ref)")));
        call_args.push("(context 0u32)".to_owned());
        let mut total = "(#get results result0)".to_owned();
        for slot in 1..capacity {
            total = format!("(#u64::add-wrap {total} (#get results result{slot}))");
        }
        let body = format!(
            "#generate lim-gen-task (Task Poll Poll.Pending Poll.Ready) #u64 ((Task.Waiting))
#struct Waker () ((marker #u64))
#fn poll {{
  #params = ((task Task) (waker (#ref Waker)));
  #returns = Poll;
  #body = (
                 (#forget waker) (#forget task) (#return (Poll.Ready 1u64))
  );
}}
#fn wait {{
  #params = ((context #u32));
  #returns = WaitResult;
  #body = ( (#return (WaitResult.WaitReady context))
  );
}}
#fn cancel-poll {{
  #params = ((state Poll));
  #returns = ();
  #body = ( (#forget state) (#return ())
  );
}}
#generate lim-gen-wake-executor run (Results Outcome Lifecycle Lifecycle.Running Outcome.Complete Lifecycle.Cancelling Outcome.Stopped)
                 (Task Poll Poll.Pending Poll.Ready #u64 poll Waker)
                 (WaitResult WaitResult.WaitReady WaitResult.WaitStopped #i64 wait (context #u32))
                 cancel-poll ({jobs})
#fn main {{
  #params = ();
  #returns = #u64;
  #body = (
                 (#let waker Waker (#struct-literal Waker ((marker 0u64))))
                 (#let waker-ref (#ref Waker) (#borrow waker))
                 (#let outcome Outcome
                   (#call run ({named_args})))
                 (#forget waker)
                 (#return (#match outcome
                   (#case (Outcome.Complete results) {total})
                   (#case (Outcome.Stopped error) (#block (#forget error) (#unreachable)))))\n  );\n}}\n",
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
fn wake_executor_polls_only_selected_slots_across_ready_masks() {
    let scratch = support::Scratch::new("wake-executor-fairness");
    let body = "
#generate lim-gen-task (Task Poll Poll.Pending Poll.Ready) #u64 ((Task.Run (#tuple #u64 #u64)))
#struct Waker () ((marker #u64))
#struct WaitContext () ((waits #u32))
#fn poll {
  #params = ((task Task) (waker (#ref Waker)));
  #returns = Poll;
  #body = (
          (#forget waker)
          (#return (#match task
            (#case (Task.Run (#tuple target attempts))
              (#block
                (#let next #u64 (#u64::add-wrap attempts 1u64))
                (#if (#u64::ge next target)
                  (Poll.Ready next)
                  (Poll.Pending (Task.Run (#tuple target next))))))))
  );
}
#fn wait {
  #params = ((context (#ref-mut WaitContext)));
  #returns = WaitResult;
  #body = (
          (#let waits (#ref-mut #u32) (#borrow-mut (#get context waits)))
          (#deref-set waits (#u32::add-wrap (#deref waits) 1u32))
          (#drop waits)
          (#return (#if (#u32::eq (#get context waits) 1u32)
            (WaitResult.WaitReady 6u32)
            (WaitResult.WaitReady 1u32)))
  );
}
#fn cancel-poll {
  #params = ((state Poll));
  #returns = ();
  #body = (
          (#match state
            (#case (Poll.Pending task)
              (#match task (#case (Task.Run (#tuple target attempts))
                (#block (#forget target) (#forget attempts)))))
            (#case (Poll.Ready value) (#forget value)))
          (#return ())
  );
}
#generate lim-gen-wake-executor run
          (Results Outcome Lifecycle Lifecycle.Running Outcome.Complete Lifecycle.Cancelling Outcome.Stopped)
          (Task Poll Poll.Pending Poll.Ready #u64 poll Waker)
          (WaitResult WaitResult.WaitReady WaitResult.WaitStopped #i64 wait (context (#ref-mut WaitContext)))
          cancel-poll
          ((first-state first-task first-waker first 0u32)
           (second-state second-task second-waker second 1u32)
           (third-state third-task third-waker third 2u32))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let waker Waker (#struct-literal Waker ((marker 0u64))))
          (#let waker-ref (#ref Waker) (#borrow waker))
          (#let-mut wait-context WaitContext
            (#struct-literal WaitContext ((waits 0u32))))
          (#let wait-context-ref (#ref-mut WaitContext) (#borrow-mut wait-context))
          (#let outcome Outcome (#call run
            ((first-task (Task.Run (#tuple 2u64 0u64)))
             (second-task (Task.Run (#tuple 2u64 0u64)))
             (third-task (Task.Run (#tuple 2u64 0u64)))
             (first-waker waker-ref)
             (second-waker waker-ref)
             (third-waker waker-ref)
             (context wait-context-ref))))
          (#drop wait-context-ref)
          (#assert (#u32::eq (#get wait-context waits) 2u32))
          (#forget wait-context)
          (#forget waker)
          (#return (#match outcome
            (#case (Outcome.Complete results)
              (#block
                (#assert (#u64::eq (#get results first) 2u64))
                (#assert (#u64::eq (#get results second) 2u64))
                (#assert (#u64::eq (#get results third) 2u64))
                (#forget results)
                0u64))
            (#case (Outcome.Stopped reason) (#block (#forget reason) 1u64))))\n  );\n}\n";
    let program = source(body);
    let assembly = lim::compile_source_to_assembly(
        &program,
        &scratch.path().join("fairness.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_or_else(|error| panic!("{error:?}"));
    let binary = scratch.path().join("fairness");
    lim::link_native_binary(
        &assembly,
        &binary,
        &[],
        &[],
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    assert_eq!(Command::new(binary).status().unwrap().code(), Some(0));
}

#[test]
fn wake_executor_shutdown_cancels_pending_and_completed_states() {
    let scratch = support::Scratch::new("wake-executor-shutdown");
    let body = format!(
        "#alias AsyncPoll4Result = \"{0}/library/async_poll4.lim::AsyncPoll4Result\"\n#alias AsyncPollSource4 = \"{0}/library/async_poll4.lim::AsyncPollSource4\"\n#alias LinuxTimespec = \"{0}/library/linux_x86_64.lim::LinuxTimespec\"\n#alias TimerCreate1 = \"{0}/library/timer_reactor1.lim::TimerCreate1\"\n#alias TimerManyWait = \"{0}/library/timer_reactor1.lim::TimerManyWait\"\n#alias TimerPairReady1 = \"{0}/library/timer_reactor1.lim::TimerPairReady1\"\n#alias TimerPoll1 = \"{0}/library/timer_reactor1.lim::TimerPoll1\"\n#alias TimerReactor1 = \"{0}/library/timer_reactor1.lim::TimerReactor1\"\n#alias TimerWait1 = \"{0}/library/timer_reactor1.lim::TimerWait1\"\n#alias TimerWait2 = \"{0}/library/timer_reactor1.lim::TimerWait2\"\n#alias WakeReady4 = \"{0}/library/wake_ready4.lim::WakeReady4\"\n#alias WakeRegister4 = \"{0}/library/wake_tokens.lim::WakeRegister4\"\n#alias WakeRetire4 = \"{0}/library/wake_tokens.lim::WakeRetire4\"\n#alias WakeTable4 = \"{0}/library/wake_tokens.lim::WakeTable4\"\n#alias WakeToken4 = \"{0}/library/wake_tokens.lim::WakeToken4\"\n#alias async-poll4-disable-source = \"{0}/library/async_poll4.lim::async-poll4-disable-source\"\n#alias async-poll4-source = \"{0}/library/async_poll4.lim::async-poll4-source\"\n#alias async-poll4-wait = \"{0}/library/async_poll4.lim::async-poll4-wait\"\n#alias lINUX-SYS-ACCEPT = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-ACCEPT\"\n#alias lINUX-SYS-ACCEPT4 = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-ACCEPT4\"\n#alias lINUX-SYS-ACCESS = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-ACCESS\"\n#alias lINUX-SYS-ACCT = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-ACCT\"\n#alias lINUX-SYS-ADD-KEY = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-ADD-KEY\"\n#alias lINUX-SYS-ADJTIMEX = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-ADJTIMEX\"\n#alias lINUX-SYS-AFS-SYSCALL = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-AFS-SYSCALL\"\n#alias lINUX-SYS-ALARM = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-ALARM\"\n#alias lINUX-SYS-ARCH-PRCTL = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-ARCH-PRCTL\"\n#alias lINUX-SYS-BIND = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-BIND\"\n#alias lINUX-SYS-BPF = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-BPF\"\n#alias lINUX-SYS-BRK = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-BRK\"\n#alias lINUX-SYS-CACHESTAT = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-CACHESTAT\"\n#alias lINUX-SYS-CAPGET = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-CAPGET\"\n#alias lINUX-SYS-CAPSET = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-CAPSET\"\n#alias lINUX-SYS-CHDIR = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-CHDIR\"\n#alias lINUX-SYS-CHMOD = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-CHMOD\"\n#alias lINUX-SYS-CHOWN = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-CHOWN\"\n#alias lINUX-SYS-CHROOT = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-CHROOT\"\n#alias lINUX-SYS-CLOCK-ADJTIME = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-CLOCK-ADJTIME\"\n#alias lINUX-SYS-CLOCK-GETRES = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-CLOCK-GETRES\"\n#alias lINUX-SYS-CLOCK-GETTIME = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-CLOCK-GETTIME\"\n#alias lINUX-SYS-CLOCK-NANOSLEEP = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-CLOCK-NANOSLEEP\"\n#alias lINUX-SYS-CLOCK-SETTIME = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-CLOCK-SETTIME\"\n#alias lINUX-SYS-CLONE = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-CLONE\"\n#alias lINUX-SYS-CLONE3 = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-CLONE3\"\n#alias lINUX-SYS-CLOSE = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-CLOSE\"\n#alias lINUX-SYS-CLOSE-RANGE = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-CLOSE-RANGE\"\n#alias lINUX-SYS-CONNECT = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-CONNECT\"\n#alias lINUX-SYS-COPY-FILE-RANGE = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-COPY-FILE-RANGE\"\n#alias lINUX-SYS-CREAT = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-CREAT\"\n#alias lINUX-SYS-CREATE-MODULE = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-CREATE-MODULE\"\n#alias lINUX-SYS-DELETE-MODULE = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-DELETE-MODULE\"\n#alias lINUX-SYS-DUP = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-DUP\"\n#alias lINUX-SYS-DUP2 = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-DUP2\"\n#alias lINUX-SYS-DUP3 = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-DUP3\"\n#alias lINUX-SYS-EPOLL-CREATE = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-EPOLL-CREATE\"\n#alias lINUX-SYS-EPOLL-CREATE1 = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-EPOLL-CREATE1\"\n#alias lINUX-SYS-EPOLL-CTL = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-EPOLL-CTL\"\n#alias lINUX-SYS-EPOLL-CTL-OLD = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-EPOLL-CTL-OLD\"\n#alias lINUX-SYS-EPOLL-PWAIT = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-EPOLL-PWAIT\"\n#alias lINUX-SYS-EPOLL-PWAIT2 = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-EPOLL-PWAIT2\"\n#alias lINUX-SYS-EPOLL-WAIT = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-EPOLL-WAIT\"\n#alias lINUX-SYS-EPOLL-WAIT-OLD = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-EPOLL-WAIT-OLD\"\n#alias lINUX-SYS-EVENTFD = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-EVENTFD\"\n#alias lINUX-SYS-EVENTFD2 = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-EVENTFD2\"\n#alias lINUX-SYS-EXECVE = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-EXECVE\"\n#alias lINUX-SYS-EXECVEAT = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-EXECVEAT\"\n#alias lINUX-SYS-EXIT = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-EXIT\"\n#alias lINUX-SYS-EXIT-GROUP = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-EXIT-GROUP\"\n#alias lINUX-SYS-FACCESSAT = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-FACCESSAT\"\n#alias lINUX-SYS-FACCESSAT2 = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-FACCESSAT2\"\n#alias lINUX-SYS-FADVISE64 = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-FADVISE64\"\n#alias lINUX-SYS-FALLOCATE = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-FALLOCATE\"\n#alias lINUX-SYS-FANOTIFY-INIT = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-FANOTIFY-INIT\"\n#alias lINUX-SYS-FANOTIFY-MARK = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-FANOTIFY-MARK\"\n#alias lINUX-SYS-FCHDIR = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-FCHDIR\"\n#alias lINUX-SYS-FCHMOD = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-FCHMOD\"\n#alias lINUX-SYS-FCHMODAT = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-FCHMODAT\"\n#alias lINUX-SYS-FCHMODAT2 = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-FCHMODAT2\"\n#alias lINUX-SYS-FCHOWN = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-FCHOWN\"\n#alias lINUX-SYS-FCHOWNAT = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-FCHOWNAT\"\n#alias lINUX-SYS-FCHROOT = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-FCHROOT\"\n#alias lINUX-SYS-FCNTL = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-FCNTL\"\n#alias lINUX-SYS-FDATASYNC = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-FDATASYNC\"\n#alias lINUX-SYS-FGETXATTR = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-FGETXATTR\"\n#alias lINUX-SYS-FILE-GETATTR = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-FILE-GETATTR\"\n#alias lINUX-SYS-FILE-SETATTR = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-FILE-SETATTR\"\n#alias lINUX-SYS-FINIT-MODULE = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-FINIT-MODULE\"\n#alias lINUX-SYS-FLISTXATTR = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-FLISTXATTR\"\n#alias lINUX-SYS-FLOCK = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-FLOCK\"\n#alias lINUX-SYS-FORK = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-FORK\"\n#alias lINUX-SYS-FREMOVEXATTR = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-FREMOVEXATTR\"\n#alias lINUX-SYS-FSCONFIG = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-FSCONFIG\"\n#alias lINUX-SYS-FSETXATTR = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-FSETXATTR\"\n#alias lINUX-SYS-FSMOUNT = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-FSMOUNT\"\n#alias lINUX-SYS-FSOPEN = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-FSOPEN\"\n#alias lINUX-SYS-FSPICK = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-FSPICK\"\n#alias lINUX-SYS-FSTAT = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-FSTAT\"\n#alias lINUX-SYS-FSTATFS = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-FSTATFS\"\n#alias lINUX-SYS-FSYNC = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-FSYNC\"\n#alias lINUX-SYS-FTRUNCATE = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-FTRUNCATE\"\n#alias lINUX-SYS-FUTEX = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-FUTEX\"\n#alias lINUX-SYS-FUTEX-REQUEUE = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-FUTEX-REQUEUE\"\n#alias lINUX-SYS-FUTEX-WAIT = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-FUTEX-WAIT\"\n#alias lINUX-SYS-FUTEX-WAITV = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-FUTEX-WAITV\"\n#alias lINUX-SYS-FUTEX-WAKE = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-FUTEX-WAKE\"\n#alias lINUX-SYS-FUTIMESAT = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-FUTIMESAT\"\n#alias lINUX-SYS-GET-KERNEL-SYMS = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-GET-KERNEL-SYMS\"\n#alias lINUX-SYS-GET-MEMPOLICY = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-GET-MEMPOLICY\"\n#alias lINUX-SYS-GET-ROBUST-LIST = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-GET-ROBUST-LIST\"\n#alias lINUX-SYS-GET-THREAD-AREA = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-GET-THREAD-AREA\"\n#alias lINUX-SYS-GETCPU = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-GETCPU\"\n#alias lINUX-SYS-GETCWD = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-GETCWD\"\n#alias lINUX-SYS-GETDENTS = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-GETDENTS\"\n#alias lINUX-SYS-GETDENTS64 = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-GETDENTS64\"\n#alias lINUX-SYS-GETEGID = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-GETEGID\"\n#alias lINUX-SYS-GETEUID = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-GETEUID\"\n#alias lINUX-SYS-GETGID = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-GETGID\"\n#alias lINUX-SYS-GETGROUPS = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-GETGROUPS\"\n#alias lINUX-SYS-GETITIMER = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-GETITIMER\"\n#alias lINUX-SYS-GETPEERNAME = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-GETPEERNAME\"\n#alias lINUX-SYS-GETPGID = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-GETPGID\"\n#alias lINUX-SYS-GETPGRP = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-GETPGRP\"\n#alias lINUX-SYS-GETPID = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-GETPID\"\n#alias lINUX-SYS-GETPMSG = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-GETPMSG\"\n#alias lINUX-SYS-GETPPID = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-GETPPID\"\n#alias lINUX-SYS-GETPRIORITY = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-GETPRIORITY\"\n#alias lINUX-SYS-GETRANDOM = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-GETRANDOM\"\n#alias lINUX-SYS-GETRESGID = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-GETRESGID\"\n#alias lINUX-SYS-GETRESUID = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-GETRESUID\"\n#alias lINUX-SYS-GETRLIMIT = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-GETRLIMIT\"\n#alias lINUX-SYS-GETRUSAGE = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-GETRUSAGE\"\n#alias lINUX-SYS-GETSID = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-GETSID\"\n#alias lINUX-SYS-GETSOCKNAME = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-GETSOCKNAME\"\n#alias lINUX-SYS-GETSOCKOPT = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-GETSOCKOPT\"\n#alias lINUX-SYS-GETTID = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-GETTID\"\n#alias lINUX-SYS-GETTIMEOFDAY = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-GETTIMEOFDAY\"\n#alias lINUX-SYS-GETUID = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-GETUID\"\n#alias lINUX-SYS-GETXATTR = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-GETXATTR\"\n#alias lINUX-SYS-GETXATTRAT = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-GETXATTRAT\"\n#alias lINUX-SYS-INIT-MODULE = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-INIT-MODULE\"\n#alias lINUX-SYS-INOTIFY-ADD-WATCH = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-INOTIFY-ADD-WATCH\"\n#alias lINUX-SYS-INOTIFY-INIT = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-INOTIFY-INIT\"\n#alias lINUX-SYS-INOTIFY-INIT1 = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-INOTIFY-INIT1\"\n#alias lINUX-SYS-INOTIFY-RM-WATCH = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-INOTIFY-RM-WATCH\"\n#alias lINUX-SYS-IO-CANCEL = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-IO-CANCEL\"\n#alias lINUX-SYS-IO-DESTROY = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-IO-DESTROY\"\n#alias lINUX-SYS-IO-GETEVENTS = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-IO-GETEVENTS\"\n#alias lINUX-SYS-IO-PGETEVENTS = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-IO-PGETEVENTS\"\n#alias lINUX-SYS-IO-SETUP = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-IO-SETUP\"\n#alias lINUX-SYS-IO-SUBMIT = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-IO-SUBMIT\"\n#alias lINUX-SYS-IO-URING-ENTER = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-IO-URING-ENTER\"\n#alias lINUX-SYS-IO-URING-REGISTER = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-IO-URING-REGISTER\"\n#alias lINUX-SYS-IO-URING-SETUP = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-IO-URING-SETUP\"\n#alias lINUX-SYS-IOCTL = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-IOCTL\"\n#alias lINUX-SYS-IOPERM = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-IOPERM\"\n#alias lINUX-SYS-IOPL = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-IOPL\"\n#alias lINUX-SYS-IOPRIO-GET = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-IOPRIO-GET\"\n#alias lINUX-SYS-IOPRIO-SET = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-IOPRIO-SET\"\n#alias lINUX-SYS-KCMP = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-KCMP\"\n#alias lINUX-SYS-KEXEC-FILE-LOAD = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-KEXEC-FILE-LOAD\"\n#alias lINUX-SYS-KEXEC-LOAD = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-KEXEC-LOAD\"\n#alias lINUX-SYS-KEYCTL = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-KEYCTL\"\n#alias lINUX-SYS-KILL = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-KILL\"\n#alias lINUX-SYS-LANDLOCK-ADD-RULE = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-LANDLOCK-ADD-RULE\"\n#alias lINUX-SYS-LANDLOCK-CREATE-RULESET = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-LANDLOCK-CREATE-RULESET\"\n#alias lINUX-SYS-LANDLOCK-RESTRICT-SELF = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-LANDLOCK-RESTRICT-SELF\"\n#alias lINUX-SYS-LCHOWN = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-LCHOWN\"\n#alias lINUX-SYS-LGETXATTR = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-LGETXATTR\"\n#alias lINUX-SYS-LINK = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-LINK\"\n#alias lINUX-SYS-LINKAT = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-LINKAT\"\n#alias lINUX-SYS-LISTEN = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-LISTEN\"\n#alias lINUX-SYS-LISTMOUNT = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-LISTMOUNT\"\n#alias lINUX-SYS-LISTNS = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-LISTNS\"\n#alias lINUX-SYS-LISTXATTR = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-LISTXATTR\"\n#alias lINUX-SYS-LISTXATTRAT = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-LISTXATTRAT\"\n#alias lINUX-SYS-LLISTXATTR = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-LLISTXATTR\"\n#alias lINUX-SYS-LOOKUP-DCOOKIE = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-LOOKUP-DCOOKIE\"\n#alias lINUX-SYS-LREMOVEXATTR = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-LREMOVEXATTR\"\n#alias lINUX-SYS-LSEEK = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-LSEEK\"\n#alias lINUX-SYS-LSETXATTR = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-LSETXATTR\"\n#alias lINUX-SYS-LSM-GET-SELF-ATTR = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-LSM-GET-SELF-ATTR\"\n#alias lINUX-SYS-LSM-LIST-MODULES = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-LSM-LIST-MODULES\"\n#alias lINUX-SYS-LSM-SET-SELF-ATTR = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-LSM-SET-SELF-ATTR\"\n#alias lINUX-SYS-LSTAT = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-LSTAT\"\n#alias lINUX-SYS-MADVISE = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-MADVISE\"\n#alias lINUX-SYS-MAP-SHADOW-STACK = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-MAP-SHADOW-STACK\"\n#alias lINUX-SYS-MBIND = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-MBIND\"\n#alias lINUX-SYS-MEMBARRIER = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-MEMBARRIER\"\n#alias lINUX-SYS-MEMFD-CREATE = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-MEMFD-CREATE\"\n#alias lINUX-SYS-MEMFD-SECRET = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-MEMFD-SECRET\"\n#alias lINUX-SYS-MIGRATE-PAGES = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-MIGRATE-PAGES\"\n#alias lINUX-SYS-MINCORE = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-MINCORE\"\n#alias lINUX-SYS-MKDIR = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-MKDIR\"\n#alias lINUX-SYS-MKDIRAT = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-MKDIRAT\"\n#alias lINUX-SYS-MKNOD = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-MKNOD\"\n#alias lINUX-SYS-MKNODAT = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-MKNODAT\"\n#alias lINUX-SYS-MLOCK = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-MLOCK\"\n#alias lINUX-SYS-MLOCK2 = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-MLOCK2\"\n#alias lINUX-SYS-MLOCKALL = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-MLOCKALL\"\n#alias lINUX-SYS-MMAP = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-MMAP\"\n#alias lINUX-SYS-MODIFY-LDT = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-MODIFY-LDT\"\n#alias lINUX-SYS-MOUNT = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-MOUNT\"\n#alias lINUX-SYS-MOUNT-SETATTR = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-MOUNT-SETATTR\"\n#alias lINUX-SYS-MOVE-MOUNT = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-MOVE-MOUNT\"\n#alias lINUX-SYS-MOVE-PAGES = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-MOVE-PAGES\"\n#alias lINUX-SYS-MPROTECT = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-MPROTECT\"\n#alias lINUX-SYS-MQ-GETSETATTR = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-MQ-GETSETATTR\"\n#alias lINUX-SYS-MQ-NOTIFY = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-MQ-NOTIFY\"\n#alias lINUX-SYS-MQ-OPEN = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-MQ-OPEN\"\n#alias lINUX-SYS-MQ-TIMEDRECEIVE = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-MQ-TIMEDRECEIVE\"\n#alias lINUX-SYS-MQ-TIMEDSEND = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-MQ-TIMEDSEND\"\n#alias lINUX-SYS-MQ-UNLINK = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-MQ-UNLINK\"\n#alias lINUX-SYS-MREMAP = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-MREMAP\"\n#alias lINUX-SYS-MSEAL = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-MSEAL\"\n#alias lINUX-SYS-MSGCTL = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-MSGCTL\"\n#alias lINUX-SYS-MSGGET = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-MSGGET\"\n#alias lINUX-SYS-MSGRCV = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-MSGRCV\"\n#alias lINUX-SYS-MSGSND = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-MSGSND\"\n#alias lINUX-SYS-MSYNC = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-MSYNC\"\n#alias lINUX-SYS-MUNLOCK = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-MUNLOCK\"\n#alias lINUX-SYS-MUNLOCKALL = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-MUNLOCKALL\"\n#alias lINUX-SYS-MUNMAP = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-MUNMAP\"\n#alias lINUX-SYS-NAME-TO-HANDLE-AT = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-NAME-TO-HANDLE-AT\"\n#alias lINUX-SYS-NANOSLEEP = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-NANOSLEEP\"\n#alias lINUX-SYS-NEWFSTATAT = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-NEWFSTATAT\"\n#alias lINUX-SYS-NFSSERVCTL = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-NFSSERVCTL\"\n#alias lINUX-SYS-OPEN = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-OPEN\"\n#alias lINUX-SYS-OPEN-BY-HANDLE-AT = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-OPEN-BY-HANDLE-AT\"\n#alias lINUX-SYS-OPEN-TREE = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-OPEN-TREE\"\n#alias lINUX-SYS-OPEN-TREE-ATTR = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-OPEN-TREE-ATTR\"\n#alias lINUX-SYS-OPENAT = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-OPENAT\"\n#alias lINUX-SYS-OPENAT2 = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-OPENAT2\"\n#alias lINUX-SYS-PAUSE = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-PAUSE\"\n#alias lINUX-SYS-PERF-EVENT-OPEN = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-PERF-EVENT-OPEN\"\n#alias lINUX-SYS-PERSONALITY = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-PERSONALITY\"\n#alias lINUX-SYS-PIDFD-GETFD = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-PIDFD-GETFD\"\n#alias lINUX-SYS-PIDFD-OPEN = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-PIDFD-OPEN\"\n#alias lINUX-SYS-PIDFD-SEND-SIGNAL = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-PIDFD-SEND-SIGNAL\"\n#alias lINUX-SYS-PIPE = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-PIPE\"\n#alias lINUX-SYS-PIPE2 = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-PIPE2\"\n#alias lINUX-SYS-PIVOT-ROOT = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-PIVOT-ROOT\"\n#alias lINUX-SYS-PKEY-ALLOC = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-PKEY-ALLOC\"\n#alias lINUX-SYS-PKEY-FREE = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-PKEY-FREE\"\n#alias lINUX-SYS-PKEY-MPROTECT = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-PKEY-MPROTECT\"\n#alias lINUX-SYS-POLL = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-POLL\"\n#alias lINUX-SYS-PPOLL = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-PPOLL\"\n#alias lINUX-SYS-PRCTL = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-PRCTL\"\n#alias lINUX-SYS-PREAD64 = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-PREAD64\"\n#alias lINUX-SYS-PREADV = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-PREADV\"\n#alias lINUX-SYS-PREADV2 = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-PREADV2\"\n#alias lINUX-SYS-PRLIMIT64 = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-PRLIMIT64\"\n#alias lINUX-SYS-PROCESS-MADVISE = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-PROCESS-MADVISE\"\n#alias lINUX-SYS-PROCESS-MRELEASE = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-PROCESS-MRELEASE\"\n#alias lINUX-SYS-PROCESS-VM-READV = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-PROCESS-VM-READV\"\n#alias lINUX-SYS-PROCESS-VM-WRITEV = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-PROCESS-VM-WRITEV\"\n#alias lINUX-SYS-PSELECT6 = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-PSELECT6\"\n#alias lINUX-SYS-PTRACE = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-PTRACE\"\n#alias lINUX-SYS-PUTPMSG = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-PUTPMSG\"\n#alias lINUX-SYS-PWRITE64 = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-PWRITE64\"\n#alias lINUX-SYS-PWRITEV = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-PWRITEV\"\n#alias lINUX-SYS-PWRITEV2 = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-PWRITEV2\"\n#alias lINUX-SYS-QUERY-MODULE = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-QUERY-MODULE\"\n#alias lINUX-SYS-QUOTACTL = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-QUOTACTL\"\n#alias lINUX-SYS-QUOTACTL-FD = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-QUOTACTL-FD\"\n#alias lINUX-SYS-READ = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-READ\"\n#alias lINUX-SYS-READAHEAD = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-READAHEAD\"\n#alias lINUX-SYS-READLINK = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-READLINK\"\n#alias lINUX-SYS-READLINKAT = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-READLINKAT\"\n#alias lINUX-SYS-READV = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-READV\"\n#alias lINUX-SYS-REBOOT = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-REBOOT\"\n#alias lINUX-SYS-RECVFROM = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-RECVFROM\"\n#alias lINUX-SYS-RECVMMSG = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-RECVMMSG\"\n#alias lINUX-SYS-RECVMSG = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-RECVMSG\"\n#alias lINUX-SYS-REMAP-FILE-PAGES = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-REMAP-FILE-PAGES\"\n#alias lINUX-SYS-REMOVEXATTR = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-REMOVEXATTR\"\n#alias lINUX-SYS-REMOVEXATTRAT = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-REMOVEXATTRAT\"\n#alias lINUX-SYS-RENAME = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-RENAME\"\n#alias lINUX-SYS-RENAMEAT = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-RENAMEAT\"\n#alias lINUX-SYS-RENAMEAT2 = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-RENAMEAT2\"\n#alias lINUX-SYS-REQUEST-KEY = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-REQUEST-KEY\"\n#alias lINUX-SYS-RESTART-SYSCALL = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-RESTART-SYSCALL\"\n#alias lINUX-SYS-RMDIR = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-RMDIR\"\n#alias lINUX-SYS-RSEQ = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-RSEQ\"\n#alias lINUX-SYS-RSEQ-SLICE-YIELD = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-RSEQ-SLICE-YIELD\"\n#alias lINUX-SYS-RT-SIGACTION = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-RT-SIGACTION\"\n#alias lINUX-SYS-RT-SIGPENDING = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-RT-SIGPENDING\"\n#alias lINUX-SYS-RT-SIGPROCMASK = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-RT-SIGPROCMASK\"\n#alias lINUX-SYS-RT-SIGQUEUEINFO = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-RT-SIGQUEUEINFO\"\n#alias lINUX-SYS-RT-SIGRETURN = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-RT-SIGRETURN\"\n#alias lINUX-SYS-RT-SIGSUSPEND = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-RT-SIGSUSPEND\"\n#alias lINUX-SYS-RT-SIGTIMEDWAIT = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-RT-SIGTIMEDWAIT\"\n#alias lINUX-SYS-RT-TGSIGQUEUEINFO = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-RT-TGSIGQUEUEINFO\"\n#alias lINUX-SYS-SCHED-GET-PRIORITY-MAX = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SCHED-GET-PRIORITY-MAX\"\n#alias lINUX-SYS-SCHED-GET-PRIORITY-MIN = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SCHED-GET-PRIORITY-MIN\"\n#alias lINUX-SYS-SCHED-GETAFFINITY = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SCHED-GETAFFINITY\"\n#alias lINUX-SYS-SCHED-GETATTR = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SCHED-GETATTR\"\n#alias lINUX-SYS-SCHED-GETPARAM = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SCHED-GETPARAM\"\n#alias lINUX-SYS-SCHED-GETSCHEDULER = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SCHED-GETSCHEDULER\"\n#alias lINUX-SYS-SCHED-RR-GET-INTERVAL = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SCHED-RR-GET-INTERVAL\"\n#alias lINUX-SYS-SCHED-SETAFFINITY = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SCHED-SETAFFINITY\"\n#alias lINUX-SYS-SCHED-SETATTR = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SCHED-SETATTR\"\n#alias lINUX-SYS-SCHED-SETPARAM = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SCHED-SETPARAM\"\n#alias lINUX-SYS-SCHED-SETSCHEDULER = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SCHED-SETSCHEDULER\"\n#alias lINUX-SYS-SCHED-YIELD = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SCHED-YIELD\"\n#alias lINUX-SYS-SECCOMP = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SECCOMP\"\n#alias lINUX-SYS-SECURITY = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SECURITY\"\n#alias lINUX-SYS-SELECT = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SELECT\"\n#alias lINUX-SYS-SEMCTL = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SEMCTL\"\n#alias lINUX-SYS-SEMGET = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SEMGET\"\n#alias lINUX-SYS-SEMOP = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SEMOP\"\n#alias lINUX-SYS-SEMTIMEDOP = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SEMTIMEDOP\"\n#alias lINUX-SYS-SENDFILE = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SENDFILE\"\n#alias lINUX-SYS-SENDMMSG = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SENDMMSG\"\n#alias lINUX-SYS-SENDMSG = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SENDMSG\"\n#alias lINUX-SYS-SENDTO = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SENDTO\"\n#alias lINUX-SYS-SET-MEMPOLICY = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SET-MEMPOLICY\"\n#alias lINUX-SYS-SET-MEMPOLICY-HOME-NODE = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SET-MEMPOLICY-HOME-NODE\"\n#alias lINUX-SYS-SET-ROBUST-LIST = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SET-ROBUST-LIST\"\n#alias lINUX-SYS-SET-THREAD-AREA = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SET-THREAD-AREA\"\n#alias lINUX-SYS-SET-TID-ADDRESS = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SET-TID-ADDRESS\"\n#alias lINUX-SYS-SETDOMAINNAME = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SETDOMAINNAME\"\n#alias lINUX-SYS-SETFSGID = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SETFSGID\"\n#alias lINUX-SYS-SETFSUID = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SETFSUID\"\n#alias lINUX-SYS-SETGID = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SETGID\"\n#alias lINUX-SYS-SETGROUPS = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SETGROUPS\"\n#alias lINUX-SYS-SETHOSTNAME = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SETHOSTNAME\"\n#alias lINUX-SYS-SETITIMER = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SETITIMER\"\n#alias lINUX-SYS-SETNS = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SETNS\"\n#alias lINUX-SYS-SETPGID = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SETPGID\"\n#alias lINUX-SYS-SETPRIORITY = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SETPRIORITY\"\n#alias lINUX-SYS-SETREGID = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SETREGID\"\n#alias lINUX-SYS-SETRESGID = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SETRESGID\"\n#alias lINUX-SYS-SETRESUID = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SETRESUID\"\n#alias lINUX-SYS-SETREUID = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SETREUID\"\n#alias lINUX-SYS-SETRLIMIT = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SETRLIMIT\"\n#alias lINUX-SYS-SETSID = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SETSID\"\n#alias lINUX-SYS-SETSOCKOPT = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SETSOCKOPT\"\n#alias lINUX-SYS-SETTIMEOFDAY = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SETTIMEOFDAY\"\n#alias lINUX-SYS-SETUID = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SETUID\"\n#alias lINUX-SYS-SETXATTR = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SETXATTR\"\n#alias lINUX-SYS-SETXATTRAT = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SETXATTRAT\"\n#alias lINUX-SYS-SHMAT = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SHMAT\"\n#alias lINUX-SYS-SHMCTL = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SHMCTL\"\n#alias lINUX-SYS-SHMDT = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SHMDT\"\n#alias lINUX-SYS-SHMGET = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SHMGET\"\n#alias lINUX-SYS-SHUTDOWN = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SHUTDOWN\"\n#alias lINUX-SYS-SIGALTSTACK = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SIGALTSTACK\"\n#alias lINUX-SYS-SIGNALFD = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SIGNALFD\"\n#alias lINUX-SYS-SIGNALFD4 = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SIGNALFD4\"\n#alias lINUX-SYS-SOCKET = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SOCKET\"\n#alias lINUX-SYS-SOCKETPAIR = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SOCKETPAIR\"\n#alias lINUX-SYS-SPLICE = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SPLICE\"\n#alias lINUX-SYS-STAT = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-STAT\"\n#alias lINUX-SYS-STATFS = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-STATFS\"\n#alias lINUX-SYS-STATMOUNT = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-STATMOUNT\"\n#alias lINUX-SYS-STATX = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-STATX\"\n#alias lINUX-SYS-SWAPOFF = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SWAPOFF\"\n#alias lINUX-SYS-SWAPON = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SWAPON\"\n#alias lINUX-SYS-SYMLINK = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SYMLINK\"\n#alias lINUX-SYS-SYMLINKAT = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SYMLINKAT\"\n#alias lINUX-SYS-SYNC = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SYNC\"\n#alias lINUX-SYS-SYNC-FILE-RANGE = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SYNC-FILE-RANGE\"\n#alias lINUX-SYS-SYNCFS = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SYNCFS\"\n#alias lINUX-SYS-SYSCTL = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SYSCTL\"\n#alias lINUX-SYS-SYSFS = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SYSFS\"\n#alias lINUX-SYS-SYSINFO = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SYSINFO\"\n#alias lINUX-SYS-SYSLOG = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-SYSLOG\"\n#alias lINUX-SYS-TEE = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-TEE\"\n#alias lINUX-SYS-TGKILL = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-TGKILL\"\n#alias lINUX-SYS-TIME = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-TIME\"\n#alias lINUX-SYS-TIMER-CREATE = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-TIMER-CREATE\"\n#alias lINUX-SYS-TIMER-DELETE = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-TIMER-DELETE\"\n#alias lINUX-SYS-TIMER-GETOVERRUN = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-TIMER-GETOVERRUN\"\n#alias lINUX-SYS-TIMER-GETTIME = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-TIMER-GETTIME\"\n#alias lINUX-SYS-TIMER-SETTIME = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-TIMER-SETTIME\"\n#alias lINUX-SYS-TIMERFD-CREATE = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-TIMERFD-CREATE\"\n#alias lINUX-SYS-TIMERFD-GETTIME = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-TIMERFD-GETTIME\"\n#alias lINUX-SYS-TIMERFD-SETTIME = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-TIMERFD-SETTIME\"\n#alias lINUX-SYS-TIMES = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-TIMES\"\n#alias lINUX-SYS-TKILL = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-TKILL\"\n#alias lINUX-SYS-TRUNCATE = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-TRUNCATE\"\n#alias lINUX-SYS-TUXCALL = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-TUXCALL\"\n#alias lINUX-SYS-UMASK = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-UMASK\"\n#alias lINUX-SYS-UMOUNT2 = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-UMOUNT2\"\n#alias lINUX-SYS-UNAME = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-UNAME\"\n#alias lINUX-SYS-UNLINK = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-UNLINK\"\n#alias lINUX-SYS-UNLINKAT = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-UNLINKAT\"\n#alias lINUX-SYS-UNSHARE = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-UNSHARE\"\n#alias lINUX-SYS-UPROBE = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-UPROBE\"\n#alias lINUX-SYS-URETPROBE = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-URETPROBE\"\n#alias lINUX-SYS-USELIB = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-USELIB\"\n#alias lINUX-SYS-USERFAULTFD = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-USERFAULTFD\"\n#alias lINUX-SYS-USTAT = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-USTAT\"\n#alias lINUX-SYS-UTIME = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-UTIME\"\n#alias lINUX-SYS-UTIMENSAT = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-UTIMENSAT\"\n#alias lINUX-SYS-UTIMES = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-UTIMES\"\n#alias lINUX-SYS-VFORK = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-VFORK\"\n#alias lINUX-SYS-VHANGUP = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-VHANGUP\"\n#alias lINUX-SYS-VMSPLICE = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-VMSPLICE\"\n#alias lINUX-SYS-VSERVER = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-VSERVER\"\n#alias lINUX-SYS-WAIT4 = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-WAIT4\"\n#alias lINUX-SYS-WAITID = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-WAITID\"\n#alias lINUX-SYS-WRITE = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-WRITE\"\n#alias lINUX-SYS-WRITEV = \"{0}/library/linux_x86_64_syscall_numbers.lim::lINUX-SYS-WRITEV\"\n#alias linux-accept = \"{0}/library/linux_x86_64.lim::linux-accept\"\n#alias linux-accept4 = \"{0}/library/linux_x86_64.lim::linux-accept4\"\n#alias linux-access = \"{0}/library/linux_x86_64.lim::linux-access\"\n#alias linux-alarm = \"{0}/library/linux_x86_64.lim::linux-alarm\"\n#alias linux-arch-prctl = \"{0}/library/linux_x86_64.lim::linux-arch-prctl\"\n#alias linux-bind = \"{0}/library/linux_x86_64.lim::linux-bind\"\n#alias linux-brk = \"{0}/library/linux_x86_64.lim::linux-brk\"\n#alias linux-capget = \"{0}/library/linux_x86_64.lim::linux-capget\"\n#alias linux-capset = \"{0}/library/linux_x86_64.lim::linux-capset\"\n#alias linux-chdir = \"{0}/library/linux_x86_64.lim::linux-chdir\"\n#alias linux-chmod = \"{0}/library/linux_x86_64.lim::linux-chmod\"\n#alias linux-chown = \"{0}/library/linux_x86_64.lim::linux-chown\"\n#alias linux-clock-getres = \"{0}/library/linux_x86_64.lim::linux-clock-getres\"\n#alias linux-clock-gettime = \"{0}/library/linux_x86_64.lim::linux-clock-gettime\"\n#alias linux-clock-nanosleep = \"{0}/library/linux_x86_64.lim::linux-clock-nanosleep\"\n#alias linux-close = \"{0}/library/linux_x86_64.lim::linux-close\"\n#alias linux-close-range = \"{0}/library/linux_x86_64.lim::linux-close-range\"\n#alias linux-connect = \"{0}/library/linux_x86_64.lim::linux-connect\"\n#alias linux-copy-file-range = \"{0}/library/linux_x86_64.lim::linux-copy-file-range\"\n#alias linux-creat = \"{0}/library/linux_x86_64.lim::linux-creat\"\n#alias linux-dup = \"{0}/library/linux_x86_64.lim::linux-dup\"\n#alias linux-dup2 = \"{0}/library/linux_x86_64.lim::linux-dup2\"\n#alias linux-dup3 = \"{0}/library/linux_x86_64.lim::linux-dup3\"\n#alias linux-epoll-create = \"{0}/library/linux_x86_64.lim::linux-epoll-create\"\n#alias linux-epoll-create1 = \"{0}/library/linux_x86_64.lim::linux-epoll-create1\"\n#alias linux-epoll-ctl = \"{0}/library/linux_x86_64.lim::linux-epoll-ctl\"\n#alias linux-epoll-pwait = \"{0}/library/linux_x86_64.lim::linux-epoll-pwait\"\n#alias linux-epoll-pwait2 = \"{0}/library/linux_x86_64.lim::linux-epoll-pwait2\"\n#alias linux-epoll-wait = \"{0}/library/linux_x86_64.lim::linux-epoll-wait\"\n#alias linux-eventfd = \"{0}/library/linux_x86_64.lim::linux-eventfd\"\n#alias linux-eventfd2 = \"{0}/library/linux_x86_64.lim::linux-eventfd2\"\n#alias linux-execve = \"{0}/library/linux_x86_64.lim::linux-execve\"\n#alias linux-execveat = \"{0}/library/linux_x86_64.lim::linux-execveat\"\n#alias linux-exit = \"{0}/library/linux_x86_64.lim::linux-exit\"\n#alias linux-exit-group = \"{0}/library/linux_x86_64.lim::linux-exit-group\"\n#alias linux-faccessat = \"{0}/library/linux_x86_64.lim::linux-faccessat\"\n#alias linux-faccessat2 = \"{0}/library/linux_x86_64.lim::linux-faccessat2\"\n#alias linux-fadvise64 = \"{0}/library/linux_x86_64.lim::linux-fadvise64\"\n#alias linux-fallocate = \"{0}/library/linux_x86_64.lim::linux-fallocate\"\n#alias linux-fchdir = \"{0}/library/linux_x86_64.lim::linux-fchdir\"\n#alias linux-fchmod = \"{0}/library/linux_x86_64.lim::linux-fchmod\"\n#alias linux-fchmodat = \"{0}/library/linux_x86_64.lim::linux-fchmodat\"\n#alias linux-fchmodat2 = \"{0}/library/linux_x86_64.lim::linux-fchmodat2\"\n#alias linux-fchown = \"{0}/library/linux_x86_64.lim::linux-fchown\"\n#alias linux-fchownat = \"{0}/library/linux_x86_64.lim::linux-fchownat\"\n#alias linux-fcntl = \"{0}/library/linux_x86_64.lim::linux-fcntl\"\n#alias linux-fdatasync = \"{0}/library/linux_x86_64.lim::linux-fdatasync\"\n#alias linux-fgetxattr = \"{0}/library/linux_x86_64.lim::linux-fgetxattr\"\n#alias linux-flistxattr = \"{0}/library/linux_x86_64.lim::linux-flistxattr\"\n#alias linux-flock = \"{0}/library/linux_x86_64.lim::linux-flock\"\n#alias linux-fork = \"{0}/library/linux_x86_64.lim::linux-fork\"\n#alias linux-fremovexattr = \"{0}/library/linux_x86_64.lim::linux-fremovexattr\"\n#alias linux-fsetxattr = \"{0}/library/linux_x86_64.lim::linux-fsetxattr\"\n#alias linux-fstat = \"{0}/library/linux_x86_64.lim::linux-fstat\"\n#alias linux-fstatfs = \"{0}/library/linux_x86_64.lim::linux-fstatfs\"\n#alias linux-fsync = \"{0}/library/linux_x86_64.lim::linux-fsync\"\n#alias linux-ftruncate = \"{0}/library/linux_x86_64.lim::linux-ftruncate\"\n#alias linux-futex = \"{0}/library/linux_x86_64.lim::linux-futex\"\n#alias linux-futex-cmp-requeue = \"{0}/library/linux_x86_64.lim::linux-futex-cmp-requeue\"\n#alias linux-futex-requeue = \"{0}/library/linux_x86_64.lim::linux-futex-requeue\"\n#alias linux-futex-wait = \"{0}/library/linux_x86_64.lim::linux-futex-wait\"\n#alias linux-futex-waitv = \"{0}/library/linux_x86_64.lim::linux-futex-waitv\"\n#alias linux-futex-wake = \"{0}/library/linux_x86_64.lim::linux-futex-wake\"\n#alias linux-futimesat = \"{0}/library/linux_x86_64.lim::linux-futimesat\"\n#alias linux-get-robust-list = \"{0}/library/linux_x86_64.lim::linux-get-robust-list\"\n#alias linux-getcpu = \"{0}/library/linux_x86_64.lim::linux-getcpu\"\n#alias linux-getcwd = \"{0}/library/linux_x86_64.lim::linux-getcwd\"\n#alias linux-getdents = \"{0}/library/linux_x86_64.lim::linux-getdents\"\n#alias linux-getdents64 = \"{0}/library/linux_x86_64.lim::linux-getdents64\"\n#alias linux-getegid = \"{0}/library/linux_x86_64.lim::linux-getegid\"\n#alias linux-geteuid = \"{0}/library/linux_x86_64.lim::linux-geteuid\"\n#alias linux-getgid = \"{0}/library/linux_x86_64.lim::linux-getgid\"\n#alias linux-getgroups = \"{0}/library/linux_x86_64.lim::linux-getgroups\"\n#alias linux-getitimer = \"{0}/library/linux_x86_64.lim::linux-getitimer\"\n#alias linux-getpeername = \"{0}/library/linux_x86_64.lim::linux-getpeername\"\n#alias linux-getpgid = \"{0}/library/linux_x86_64.lim::linux-getpgid\"\n#alias linux-getpgrp = \"{0}/library/linux_x86_64.lim::linux-getpgrp\"\n#alias linux-getpid = \"{0}/library/linux_x86_64.lim::linux-getpid\"\n#alias linux-getppid = \"{0}/library/linux_x86_64.lim::linux-getppid\"\n#alias linux-getpriority = \"{0}/library/linux_x86_64.lim::linux-getpriority\"\n#alias linux-getrandom = \"{0}/library/linux_x86_64.lim::linux-getrandom\"\n#alias linux-getrandom-byte = \"{0}/library/linux_x86_64.lim::linux-getrandom-byte\"\n#alias linux-getresgid = \"{0}/library/linux_x86_64.lim::linux-getresgid\"\n#alias linux-getresuid = \"{0}/library/linux_x86_64.lim::linux-getresuid\"\n#alias linux-getrlimit = \"{0}/library/linux_x86_64.lim::linux-getrlimit\"\n#alias linux-getrusage = \"{0}/library/linux_x86_64.lim::linux-getrusage\"\n#alias linux-getsid = \"{0}/library/linux_x86_64.lim::linux-getsid\"\n#alias linux-getsockname = \"{0}/library/linux_x86_64.lim::linux-getsockname\"\n#alias linux-getsockopt = \"{0}/library/linux_x86_64.lim::linux-getsockopt\"\n#alias linux-gettid = \"{0}/library/linux_x86_64.lim::linux-gettid\"\n#alias linux-gettimeofday = \"{0}/library/linux_x86_64.lim::linux-gettimeofday\"\n#alias linux-getuid = \"{0}/library/linux_x86_64.lim::linux-getuid\"\n#alias linux-getxattr = \"{0}/library/linux_x86_64.lim::linux-getxattr\"\n#alias linux-inotify-add-watch = \"{0}/library/linux_x86_64.lim::linux-inotify-add-watch\"\n#alias linux-inotify-init = \"{0}/library/linux_x86_64.lim::linux-inotify-init\"\n#alias linux-inotify-init1 = \"{0}/library/linux_x86_64.lim::linux-inotify-init1\"\n#alias linux-inotify-rm-watch = \"{0}/library/linux_x86_64.lim::linux-inotify-rm-watch\"\n#alias linux-io-cancel = \"{0}/library/linux_x86_64.lim::linux-io-cancel\"\n#alias linux-io-destroy = \"{0}/library/linux_x86_64.lim::linux-io-destroy\"\n#alias linux-io-getevents = \"{0}/library/linux_x86_64.lim::linux-io-getevents\"\n#alias linux-io-pgetevents = \"{0}/library/linux_x86_64.lim::linux-io-pgetevents\"\n#alias linux-io-setup = \"{0}/library/linux_x86_64.lim::linux-io-setup\"\n#alias linux-io-submit = \"{0}/library/linux_x86_64.lim::linux-io-submit\"\n#alias linux-io-uring-enter = \"{0}/library/linux_x86_64.lim::linux-io-uring-enter\"\n#alias linux-io-uring-register = \"{0}/library/linux_x86_64.lim::linux-io-uring-register\"\n#alias linux-io-uring-setup = \"{0}/library/linux_x86_64.lim::linux-io-uring-setup\"\n#alias linux-ioctl = \"{0}/library/linux_x86_64.lim::linux-ioctl\"\n#alias linux-ioprio-get = \"{0}/library/linux_x86_64.lim::linux-ioprio-get\"\n#alias linux-ioprio-set = \"{0}/library/linux_x86_64.lim::linux-ioprio-set\"\n#alias linux-kill = \"{0}/library/linux_x86_64.lim::linux-kill\"\n#alias linux-lchown = \"{0}/library/linux_x86_64.lim::linux-lchown\"\n#alias linux-lgetxattr = \"{0}/library/linux_x86_64.lim::linux-lgetxattr\"\n#alias linux-link = \"{0}/library/linux_x86_64.lim::linux-link\"\n#alias linux-linkat = \"{0}/library/linux_x86_64.lim::linux-linkat\"\n#alias linux-listen = \"{0}/library/linux_x86_64.lim::linux-listen\"\n#alias linux-listxattr = \"{0}/library/linux_x86_64.lim::linux-listxattr\"\n#alias linux-llistxattr = \"{0}/library/linux_x86_64.lim::linux-llistxattr\"\n#alias linux-lremovexattr = \"{0}/library/linux_x86_64.lim::linux-lremovexattr\"\n#alias linux-lseek = \"{0}/library/linux_x86_64.lim::linux-lseek\"\n#alias linux-lsetxattr = \"{0}/library/linux_x86_64.lim::linux-lsetxattr\"\n#alias linux-lstat = \"{0}/library/linux_x86_64.lim::linux-lstat\"\n#alias linux-madvise = \"{0}/library/linux_x86_64.lim::linux-madvise\"\n#alias linux-membarrier = \"{0}/library/linux_x86_64.lim::linux-membarrier\"\n#alias linux-memfd-create = \"{0}/library/linux_x86_64.lim::linux-memfd-create\"\n#alias linux-memfd-secret = \"{0}/library/linux_x86_64.lim::linux-memfd-secret\"\n#alias linux-mincore = \"{0}/library/linux_x86_64.lim::linux-mincore\"\n#alias linux-mkdir = \"{0}/library/linux_x86_64.lim::linux-mkdir\"\n#alias linux-mkdirat = \"{0}/library/linux_x86_64.lim::linux-mkdirat\"\n#alias linux-mknod = \"{0}/library/linux_x86_64.lim::linux-mknod\"\n#alias linux-mknodat = \"{0}/library/linux_x86_64.lim::linux-mknodat\"\n#alias linux-mlock = \"{0}/library/linux_x86_64.lim::linux-mlock\"\n#alias linux-mlock2 = \"{0}/library/linux_x86_64.lim::linux-mlock2\"\n#alias linux-mlockall = \"{0}/library/linux_x86_64.lim::linux-mlockall\"\n#alias linux-mmap = \"{0}/library/linux_x86_64.lim::linux-mmap\"\n#alias linux-mprotect = \"{0}/library/linux_x86_64.lim::linux-mprotect\"\n#alias linux-mq-getsetattr = \"{0}/library/linux_x86_64.lim::linux-mq-getsetattr\"\n#alias linux-mq-notify = \"{0}/library/linux_x86_64.lim::linux-mq-notify\"\n#alias linux-mq-open = \"{0}/library/linux_x86_64.lim::linux-mq-open\"\n#alias linux-mq-timedreceive = \"{0}/library/linux_x86_64.lim::linux-mq-timedreceive\"\n#alias linux-mq-timedsend = \"{0}/library/linux_x86_64.lim::linux-mq-timedsend\"\n#alias linux-mq-unlink = \"{0}/library/linux_x86_64.lim::linux-mq-unlink\"\n#alias linux-mremap = \"{0}/library/linux_x86_64.lim::linux-mremap\"\n#alias linux-mseal = \"{0}/library/linux_x86_64.lim::linux-mseal\"\n#alias linux-msgctl = \"{0}/library/linux_x86_64.lim::linux-msgctl\"\n#alias linux-msgget = \"{0}/library/linux_x86_64.lim::linux-msgget\"\n#alias linux-msgrcv = \"{0}/library/linux_x86_64.lim::linux-msgrcv\"\n#alias linux-msgsnd = \"{0}/library/linux_x86_64.lim::linux-msgsnd\"\n#alias linux-msync = \"{0}/library/linux_x86_64.lim::linux-msync\"\n#alias linux-munlock = \"{0}/library/linux_x86_64.lim::linux-munlock\"\n#alias linux-munlockall = \"{0}/library/linux_x86_64.lim::linux-munlockall\"\n#alias linux-munmap = \"{0}/library/linux_x86_64.lim::linux-munmap\"\n#alias linux-nanosleep = \"{0}/library/linux_x86_64.lim::linux-nanosleep\"\n#alias linux-newfstatat = \"{0}/library/linux_x86_64.lim::linux-newfstatat\"\n#alias linux-open = \"{0}/library/linux_x86_64.lim::linux-open\"\n#alias linux-openat = \"{0}/library/linux_x86_64.lim::linux-openat\"\n#alias linux-openat2 = \"{0}/library/linux_x86_64.lim::linux-openat2\"\n#alias linux-personality = \"{0}/library/linux_x86_64.lim::linux-personality\"\n#alias linux-pidfd-getfd = \"{0}/library/linux_x86_64.lim::linux-pidfd-getfd\"\n#alias linux-pidfd-open = \"{0}/library/linux_x86_64.lim::linux-pidfd-open\"\n#alias linux-pidfd-send-signal = \"{0}/library/linux_x86_64.lim::linux-pidfd-send-signal\"\n#alias linux-pipe = \"{0}/library/linux_x86_64.lim::linux-pipe\"\n#alias linux-pipe2 = \"{0}/library/linux_x86_64.lim::linux-pipe2\"\n#alias linux-pkey-alloc = \"{0}/library/linux_x86_64.lim::linux-pkey-alloc\"\n#alias linux-pkey-free = \"{0}/library/linux_x86_64.lim::linux-pkey-free\"\n#alias linux-pkey-mprotect = \"{0}/library/linux_x86_64.lim::linux-pkey-mprotect\"\n#alias linux-poll = \"{0}/library/linux_x86_64.lim::linux-poll\"\n#alias linux-ppoll = \"{0}/library/linux_x86_64.lim::linux-ppoll\"\n#alias linux-prctl = \"{0}/library/linux_x86_64.lim::linux-prctl\"\n#alias linux-pread64 = \"{0}/library/linux_x86_64.lim::linux-pread64\"\n#alias linux-preadv = \"{0}/library/linux_x86_64.lim::linux-preadv\"\n#alias linux-preadv2 = \"{0}/library/linux_x86_64.lim::linux-preadv2\"\n#alias linux-prlimit64 = \"{0}/library/linux_x86_64.lim::linux-prlimit64\"\n#alias linux-process-vm-readv = \"{0}/library/linux_x86_64.lim::linux-process-vm-readv\"\n#alias linux-process-vm-writev = \"{0}/library/linux_x86_64.lim::linux-process-vm-writev\"\n#alias linux-pselect6 = \"{0}/library/linux_x86_64.lim::linux-pselect6\"\n#alias linux-pwrite64 = \"{0}/library/linux_x86_64.lim::linux-pwrite64\"\n#alias linux-pwritev = \"{0}/library/linux_x86_64.lim::linux-pwritev\"\n#alias linux-pwritev2 = \"{0}/library/linux_x86_64.lim::linux-pwritev2\"\n#alias linux-read = \"{0}/library/linux_x86_64.lim::linux-read\"\n#alias linux-read-byte = \"{0}/library/linux_x86_64.lim::linux-read-byte\"\n#alias linux-read-byte-from = \"{0}/library/linux_x86_64.lim::linux-read-byte-from\"\n#alias linux-readahead = \"{0}/library/linux_x86_64.lim::linux-readahead\"\n#alias linux-readlink = \"{0}/library/linux_x86_64.lim::linux-readlink\"\n#alias linux-readlinkat = \"{0}/library/linux_x86_64.lim::linux-readlinkat\"\n#alias linux-readv = \"{0}/library/linux_x86_64.lim::linux-readv\"\n#alias linux-recvfrom = \"{0}/library/linux_x86_64.lim::linux-recvfrom\"\n#alias linux-recvmmsg = \"{0}/library/linux_x86_64.lim::linux-recvmmsg\"\n#alias linux-recvmsg = \"{0}/library/linux_x86_64.lim::linux-recvmsg\"\n#alias linux-removexattr = \"{0}/library/linux_x86_64.lim::linux-removexattr\"\n#alias linux-rename = \"{0}/library/linux_x86_64.lim::linux-rename\"\n#alias linux-renameat = \"{0}/library/linux_x86_64.lim::linux-renameat\"\n#alias linux-renameat2 = \"{0}/library/linux_x86_64.lim::linux-renameat2\"\n#alias linux-rmdir = \"{0}/library/linux_x86_64.lim::linux-rmdir\"\n#alias linux-rt-sigaction = \"{0}/library/linux_x86_64.lim::linux-rt-sigaction\"\n#alias linux-rt-sigpending = \"{0}/library/linux_x86_64.lim::linux-rt-sigpending\"\n#alias linux-rt-sigprocmask = \"{0}/library/linux_x86_64.lim::linux-rt-sigprocmask\"\n#alias linux-rt-sigqueueinfo = \"{0}/library/linux_x86_64.lim::linux-rt-sigqueueinfo\"\n#alias linux-rt-sigsuspend = \"{0}/library/linux_x86_64.lim::linux-rt-sigsuspend\"\n#alias linux-rt-sigtimedwait = \"{0}/library/linux_x86_64.lim::linux-rt-sigtimedwait\"\n#alias linux-rt-tgsigqueueinfo = \"{0}/library/linux_x86_64.lim::linux-rt-tgsigqueueinfo\"\n#alias linux-sched-get-priority-max = \"{0}/library/linux_x86_64.lim::linux-sched-get-priority-max\"\n#alias linux-sched-get-priority-min = \"{0}/library/linux_x86_64.lim::linux-sched-get-priority-min\"\n#alias linux-sched-getaffinity = \"{0}/library/linux_x86_64.lim::linux-sched-getaffinity\"\n#alias linux-sched-getattr = \"{0}/library/linux_x86_64.lim::linux-sched-getattr\"\n#alias linux-sched-getparam = \"{0}/library/linux_x86_64.lim::linux-sched-getparam\"\n#alias linux-sched-getscheduler = \"{0}/library/linux_x86_64.lim::linux-sched-getscheduler\"\n#alias linux-sched-rr-get-interval = \"{0}/library/linux_x86_64.lim::linux-sched-rr-get-interval\"\n#alias linux-sched-setaffinity = \"{0}/library/linux_x86_64.lim::linux-sched-setaffinity\"\n#alias linux-sched-setattr = \"{0}/library/linux_x86_64.lim::linux-sched-setattr\"\n#alias linux-sched-setparam = \"{0}/library/linux_x86_64.lim::linux-sched-setparam\"\n#alias linux-sched-setscheduler = \"{0}/library/linux_x86_64.lim::linux-sched-setscheduler\"\n#alias linux-sched-yield = \"{0}/library/linux_x86_64.lim::linux-sched-yield\"\n#alias linux-select = \"{0}/library/linux_x86_64.lim::linux-select\"\n#alias linux-semctl = \"{0}/library/linux_x86_64.lim::linux-semctl\"\n#alias linux-semget = \"{0}/library/linux_x86_64.lim::linux-semget\"\n#alias linux-semop = \"{0}/library/linux_x86_64.lim::linux-semop\"\n#alias linux-semtimedop = \"{0}/library/linux_x86_64.lim::linux-semtimedop\"\n#alias linux-sendfile = \"{0}/library/linux_x86_64.lim::linux-sendfile\"\n#alias linux-sendmmsg = \"{0}/library/linux_x86_64.lim::linux-sendmmsg\"\n#alias linux-sendmsg = \"{0}/library/linux_x86_64.lim::linux-sendmsg\"\n#alias linux-sendto = \"{0}/library/linux_x86_64.lim::linux-sendto\"\n#alias linux-set-robust-list = \"{0}/library/linux_x86_64.lim::linux-set-robust-list\"\n#alias linux-setfsgid = \"{0}/library/linux_x86_64.lim::linux-setfsgid\"\n#alias linux-setfsuid = \"{0}/library/linux_x86_64.lim::linux-setfsuid\"\n#alias linux-setgid = \"{0}/library/linux_x86_64.lim::linux-setgid\"\n#alias linux-setitimer = \"{0}/library/linux_x86_64.lim::linux-setitimer\"\n#alias linux-setpgid = \"{0}/library/linux_x86_64.lim::linux-setpgid\"\n#alias linux-setpriority = \"{0}/library/linux_x86_64.lim::linux-setpriority\"\n#alias linux-setregid = \"{0}/library/linux_x86_64.lim::linux-setregid\"\n#alias linux-setresgid = \"{0}/library/linux_x86_64.lim::linux-setresgid\"\n#alias linux-setresuid = \"{0}/library/linux_x86_64.lim::linux-setresuid\"\n#alias linux-setreuid = \"{0}/library/linux_x86_64.lim::linux-setreuid\"\n#alias linux-setrlimit = \"{0}/library/linux_x86_64.lim::linux-setrlimit\"\n#alias linux-setsid = \"{0}/library/linux_x86_64.lim::linux-setsid\"\n#alias linux-setsockopt = \"{0}/library/linux_x86_64.lim::linux-setsockopt\"\n#alias linux-setuid = \"{0}/library/linux_x86_64.lim::linux-setuid\"\n#alias linux-setxattr = \"{0}/library/linux_x86_64.lim::linux-setxattr\"\n#alias linux-shmat = \"{0}/library/linux_x86_64.lim::linux-shmat\"\n#alias linux-shmctl = \"{0}/library/linux_x86_64.lim::linux-shmctl\"\n#alias linux-shmdt = \"{0}/library/linux_x86_64.lim::linux-shmdt\"\n#alias linux-shmget = \"{0}/library/linux_x86_64.lim::linux-shmget\"\n#alias linux-shutdown = \"{0}/library/linux_x86_64.lim::linux-shutdown\"\n#alias linux-sigaltstack = \"{0}/library/linux_x86_64.lim::linux-sigaltstack\"\n#alias linux-signalfd = \"{0}/library/linux_x86_64.lim::linux-signalfd\"\n#alias linux-signalfd4 = \"{0}/library/linux_x86_64.lim::linux-signalfd4\"\n#alias linux-socket = \"{0}/library/linux_x86_64.lim::linux-socket\"\n#alias linux-socketpair = \"{0}/library/linux_x86_64.lim::linux-socketpair\"\n#alias linux-splice = \"{0}/library/linux_x86_64.lim::linux-splice\"\n#alias linux-stat = \"{0}/library/linux_x86_64.lim::linux-stat\"\n#alias linux-statfs = \"{0}/library/linux_x86_64.lim::linux-statfs\"\n#alias linux-statx = \"{0}/library/linux_x86_64.lim::linux-statx\"\n#alias linux-symlink = \"{0}/library/linux_x86_64.lim::linux-symlink\"\n#alias linux-symlinkat = \"{0}/library/linux_x86_64.lim::linux-symlinkat\"\n#alias linux-sync-file-range = \"{0}/library/linux_x86_64.lim::linux-sync-file-range\"\n#alias linux-syncfs = \"{0}/library/linux_x86_64.lim::linux-syncfs\"\n#alias linux-sysinfo = \"{0}/library/linux_x86_64.lim::linux-sysinfo\"\n#alias linux-tee = \"{0}/library/linux_x86_64.lim::linux-tee\"\n#alias linux-tgkill = \"{0}/library/linux_x86_64.lim::linux-tgkill\"\n#alias linux-time = \"{0}/library/linux_x86_64.lim::linux-time\"\n#alias linux-timer-create = \"{0}/library/linux_x86_64.lim::linux-timer-create\"\n#alias linux-timer-delete = \"{0}/library/linux_x86_64.lim::linux-timer-delete\"\n#alias linux-timer-getoverrun = \"{0}/library/linux_x86_64.lim::linux-timer-getoverrun\"\n#alias linux-timer-gettime = \"{0}/library/linux_x86_64.lim::linux-timer-gettime\"\n#alias linux-timer-settime = \"{0}/library/linux_x86_64.lim::linux-timer-settime\"\n#alias linux-timerfd-create = \"{0}/library/linux_x86_64.lim::linux-timerfd-create\"\n#alias linux-timerfd-gettime = \"{0}/library/linux_x86_64.lim::linux-timerfd-gettime\"\n#alias linux-timerfd-settime = \"{0}/library/linux_x86_64.lim::linux-timerfd-settime\"\n#alias linux-times = \"{0}/library/linux_x86_64.lim::linux-times\"\n#alias linux-tkill = \"{0}/library/linux_x86_64.lim::linux-tkill\"\n#alias linux-truncate = \"{0}/library/linux_x86_64.lim::linux-truncate\"\n#alias linux-umask = \"{0}/library/linux_x86_64.lim::linux-umask\"\n#alias linux-uname = \"{0}/library/linux_x86_64.lim::linux-uname\"\n#alias linux-unlink = \"{0}/library/linux_x86_64.lim::linux-unlink\"\n#alias linux-unlinkat = \"{0}/library/linux_x86_64.lim::linux-unlinkat\"\n#alias linux-utime = \"{0}/library/linux_x86_64.lim::linux-utime\"\n#alias linux-utimensat = \"{0}/library/linux_x86_64.lim::linux-utimensat\"\n#alias linux-utimes = \"{0}/library/linux_x86_64.lim::linux-utimes\"\n#alias linux-vmsplice = \"{0}/library/linux_x86_64.lim::linux-vmsplice\"\n#alias linux-wait4 = \"{0}/library/linux_x86_64.lim::linux-wait4\"\n#alias linux-waitid = \"{0}/library/linux_x86_64.lim::linux-waitid\"\n#alias linux-write = \"{0}/library/linux_x86_64.lim::linux-write\"\n#alias linux-write-byte = \"{0}/library/linux_x86_64.lim::linux-write-byte\"\n#alias linux-writev = \"{0}/library/linux_x86_64.lim::linux-writev\"\n#alias timer-reactor-many-wait = \"{0}/library/timer_reactor1.lim::timer-reactor-many-wait\"\n#alias timer-reactor1-cancel = \"{0}/library/timer_reactor1.lim::timer-reactor1-cancel\"\n#alias timer-reactor1-create = \"{0}/library/timer_reactor1.lim::timer-reactor1-create\"\n#alias timer-reactor1-poll = \"{0}/library/timer_reactor1.lim::timer-reactor1-poll\"\n#alias timer-reactor1-source = \"{0}/library/timer_reactor1.lim::timer-reactor1-source\"\n#alias timer-reactor1-wait = \"{0}/library/timer_reactor1.lim::timer-reactor1-wait\"\n#alias timer-reactor2-wait = \"{0}/library/timer_reactor1.lim::timer-reactor2-wait\"\n#alias wake-ready4-create = \"{0}/library/wake_ready4.lim::wake-ready4-create\"\n#alias wake-ready4-notify = \"{0}/library/wake_ready4.lim::wake-ready4-notify\"\n#alias wake-ready4-register = \"{0}/library/wake_ready4.lim::wake-ready4-register\"\n#alias wake-ready4-retire = \"{0}/library/wake_ready4.lim::wake-ready4-retire\"\n#alias wake-ready4-take = \"{0}/library/wake_ready4.lim::wake-ready4-take\"\n#alias wake-table4-create = \"{0}/library/wake_tokens.lim::wake-table4-create\"\n#alias wake-table4-create-exhausted = \"{0}/library/wake_tokens.lim::wake-table4-create-exhausted\"\n#alias wake-table4-register = \"{0}/library/wake_tokens.lim::wake-table4-register\"\n#alias wake-table4-retire = \"{0}/library/wake_tokens.lim::wake-table4-retire\"\n#alias wake-table4-valid = \"{0}/library/wake_tokens.lim::wake-table4-valid\"\n#alias wake-token4-generation = \"{0}/library/wake_tokens.lim::wake-token4-generation\"\n#alias wake-token4-slot = \"{0}/library/wake_tokens.lim::wake-token4-slot\"\n",
        env!("CARGO_MANIFEST_DIR")
    ) + "
#generate lim-gen-task (StopTask StopPoll StopPoll.StopPending StopPoll.StopReady) #u64
          (StopTask.ReadyNow (StopTask.Waiting (#tuple #u64 Waker TimerReactor1)))
#struct Waker () ((marker #u64))
#fn destroy-waker {
  #params = ((waker Waker));
  #returns = ();
  #body = (
          (#forget waker) (#return ())
  );
}
#fn stop-poll {
  #params = ((task StopTask) (waker (#ref Waker)));
  #returns = StopPoll;
  #body = (
          (#forget waker)
          (#return (#match task
            (#case StopTask.ReadyNow (StopPoll.StopReady 31u64))
            (#case (StopTask.Waiting (#tuple amount held-waker timer))
              (StopPoll.StopPending (StopTask.Waiting (#tuple amount held-waker timer))))))
  );
}
#fn stop-wait {
  #params = ((context #u32));
  #returns = WaitResult;
  #body = (
          (#return (WaitResult.WaitStopped (#as context #i64)))
  );
}
#fn cancel-state {
  #params = ((state StopPoll));
  #returns = ();
  #body = (
          (#match state
            (#case (StopPoll.StopPending task)
              (#match task
                (#case StopTask.ReadyNow ())
                (#case (StopTask.Waiting (#tuple amount held-waker timer))
                  (#block
                    (#forget amount)
                    (#let closed #i64 (#call timer-reactor1-cancel ((timer timer))))
                    (#assert (#i64::eq closed 0i64))
                    (#forget closed)
                    (#call destroy-waker ((waker held-waker)))
                    ()))
                ))
            (#case (StopPoll.StopReady value)
              (#block
                (#forget value))))
          (#return ())
  );
}
#generate lim-gen-wake-executor run-stop
          (StopResults StopOutcome StopLifecycle StopLifecycle.StopRunning
            StopOutcome.StopComplete StopLifecycle.StopCancelling StopOutcome.StopStopped)
          (StopTask StopPoll StopPoll.StopPending StopPoll.StopReady #u64 stop-poll Waker)
          (WaitResult WaitResult.WaitReady WaitResult.WaitStopped #i64 stop-wait (context #u32))
          cancel-state
          ((ready-state ready-task ready-waker ready 0u32)
           (pending-state pending-task pending-waker pending 1u32)
           (pending-state-two pending-task-two pending-waker-two pending-two 2u32))
#fn main {
  #params = ();
  #returns = #u64;
  #body = (
          (#let timer-created TimerCreate1
            (#call timer-reactor1-create ((nanoseconds 900000000u64))))
          (#let-else (TimerCreate1.TimerCreated1 timer) TimerCreate1 timer-created (#unreachable))
          (#let timer-created-two TimerCreate1
            (#call timer-reactor1-create ((nanoseconds 800000000u64))))
          (#let-else (TimerCreate1.TimerCreated1 timer-two) TimerCreate1 timer-created-two (#unreachable))
          (#let waker Waker (#struct-literal Waker ((marker 0u64))))
          (#let held-waker Waker (#struct-literal Waker ((marker 1u64))))
          (#let held-waker-two Waker (#struct-literal Waker ((marker 2u64))))
          (#let waker-ref (#ref Waker) (#borrow waker))
          (#let outcome StopOutcome
            (#call run-stop
              ((ready-task StopTask.ReadyNow)
               (pending-task (StopTask.Waiting (#tuple 9u64 held-waker timer)))
               (pending-task-two (StopTask.Waiting (#tuple 10u64 held-waker-two timer-two)))
               (ready-waker waker-ref) (pending-waker waker-ref)
               (pending-waker-two waker-ref)
               (context 42u32))))
          (#forget waker)
          (#return (#match outcome
            (#case (StopOutcome.StopStopped reason)
              (#if (#i64::eq reason 42i64)
                (#block (#forget reason) 42u64)
                (#block (#forget reason) 1u64)))
            (#case (StopOutcome.StopComplete results)
              (#block (#forget results) 2u64))))\n  );\n}\n";
    let program = source(&body);
    let assembly = lim::compile_source_to_assembly(
        &program,
        &scratch.path().join("shutdown.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_or_else(|error| panic!("{error:?}"));
    let binary = scratch.path().join("shutdown");
    lim::link_native_binary(
        &assembly,
        &binary,
        &[],
        &[],
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    let status = Command::new(binary).status().unwrap();
    assert_eq!(status.code(), Some(42), "shutdown status: {status:?}");
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
        )
        .replace(
            "../library/wake_tokens.lim",
            &format!("{root}/library/wake_tokens.lim"),
        )
        .replace(
            "../library/linux_x86_64.lim",
            &format!("{root}/library/linux_x86_64.lim"),
        )
        .replace(
            "../library/linux_x86_64_syscall_numbers.lim",
            &format!("{root}/library/linux_x86_64_syscall_numbers.lim"),
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
    let generated = fs::read_dir(scratch.path().join(".lim/generated"))
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
    assert!(generated.contains("#fn run-jobs"), "{generated}");
    assert!(generated.contains("(#call job-poll"), "{generated}");
    assert!(generated.contains("(#call wait-ready"), "{generated}");
}
