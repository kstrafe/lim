mod support;

use std::{
    collections::HashSet,
    io::Write,
    process::{Command, Stdio},
};

#[test]
fn native_x86_64_syscall_catalog_is_complete_and_ordered() {
    let source = include_str!("../library/linux_x86_64_syscall_numbers.lim");
    let mut names = HashSet::new();
    let mut entries = Vec::new();
    for line in source.lines() {
        let Some(rest) = line.strip_prefix("(#const LINUX-SYS-") else {
            continue;
        };
        let (name, rest) = rest.split_once(' ').expect("syscall name and type");
        let value = rest
            .strip_prefix("usize ")
            .and_then(|value| value.strip_suffix("usize)"))
            .expect("usize syscall number")
            .parse::<u16>()
            .expect("numeric syscall number");
        assert!(names.insert(name), "duplicate syscall name {name}");
        entries.push((name, value));
    }

    assert_eq!(entries.len(), 386);
    assert_eq!(entries.first(), Some(&("READ", 0)));
    assert_eq!(entries.last(), Some(&("FCHROOT", 472)));
    assert!(entries.windows(2).all(|pair| pair[0].1 < pair[1].1));
    for (name, number) in [
        ("PIPE2", 293),
        ("OPENAT2", 437),
        ("GETRANDOM", 318),
        ("MSEAL", 462),
    ] {
        assert!(entries.contains(&(name, number)), "missing {name}={number}");
    }
}

#[test]
fn echo_example_prints_the_bytes_read_from_standard_input() {
    let scratch = support::Scratch::new("io-example");
    let executable = scratch.path().join("echo-input");
    let example = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/echo_input.lim");
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(example)
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("run Lim compiler");
    assert!(
        compilation.status.success(),
        "compiler failed:\n{}",
        String::from_utf8_lossy(&compilation.stderr)
    );

    let assembly = scratch.path().join("echo-input.s");
    let emission = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg("--emit-asm")
        .arg(std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/echo_input.lim"))
        .arg(&assembly)
        .output()
        .expect("emit echo assembly");
    assert!(
        emission.status.success(),
        "assembly emission failed:\n{}",
        String::from_utf8_lossy(&emission.stderr)
    );
    let assembly = std::fs::read_to_string(assembly).expect("read emitted assembly");
    assert!(assembly.contains("syscall"));
    assert!(!assembly.contains(".extern read"));
    assert!(!assembly.contains(".extern write"));

    let input = b"hello from Lim\n";
    let mut child = Command::new(executable)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("run compiled echo example");
    child
        .stdin
        .take()
        .expect("piped stdin")
        .write_all(input)
        .expect("write test input");
    let output = child.wait_with_output().expect("wait for echo example");
    assert!(
        output.status.success(),
        "echo example failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(output.stdout, input);
}

#[test]
fn linux_memory_mapping_syscalls_match_kernel_results() {
    let scratch = support::Scratch::new("linux-memory");
    let executable = scratch.path().join("memory-checks");
    let example =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/linux_memory.lim");
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(example)
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("run Lim compiler");
    assert!(
        compilation.status.success(),
        "compiler failed:\n{}",
        String::from_utf8_lossy(&compilation.stderr)
    );
    let output = Command::new(executable)
        .output()
        .expect("run compiled memory syscall test");
    assert_eq!(output.status.code(), Some(42));
}

#[test]
fn linux_socket_listener_accepts_connections_and_checks_descriptor_flags() {
    let scratch = support::Scratch::new("linux-socket-listener");
    let executable = scratch.path().join("listener-checks");
    let example =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/linux_socket_listener.lim");
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(example)
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("compile Lim socket listener example");
    assert!(
        compilation.status.success(),
        "compiler failed:\n{}",
        String::from_utf8_lossy(&compilation.stderr)
    );
    let (status, stdout, stderr) = support::run(
        &mut Command::new(executable),
        std::time::Duration::from_secs(5),
        1024,
    )
    .expect("run socket listener example within five seconds");
    assert_eq!(status.code(), Some(42));
    assert_eq!(stdout, include_bytes!("fixtures/socket_listener.stdout"));
    assert!(stderr.is_empty());
}

#[test]
fn linux_socket_messages_preserve_datagrams_and_report_batch_lengths() {
    let scratch = support::Scratch::new("linux-socket-messages");
    let executable = scratch.path().join("message-checks");
    let example =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/linux_socket_messages.lim");
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(example)
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("compile Lim socket message example");
    assert!(
        compilation.status.success(),
        "compiler failed:\n{}",
        String::from_utf8_lossy(&compilation.stderr)
    );
    let (status, stdout, stderr) = support::run(
        &mut Command::new(executable),
        std::time::Duration::from_secs(5),
        1024,
    )
    .expect("run socket message example within five seconds");
    assert_eq!(status.code(), Some(42));
    assert_eq!(stdout, include_bytes!("fixtures/socket_messages.stdout"));
    assert!(stderr.is_empty());
}

#[test]
fn linux_memory_lock_syscalls_check_results_and_print_output() {
    let scratch = support::Scratch::new("linux-memory-lock");
    let executable = scratch.path().join("memory-lock-checks");
    let example =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/linux_memory_lock.lim");
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(example)
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("compile Lim memory-lock example");
    assert!(
        compilation.status.success(),
        "compiler failed:\n{}",
        String::from_utf8_lossy(&compilation.stderr)
    );

    let output = Command::new(executable)
        .output()
        .expect("run compiled memory-lock example");
    assert_eq!(output.status.code(), Some(42));
    assert_eq!(output.stdout, include_bytes!("fixtures/memory_lock.stdout"));
    assert!(output.stderr.is_empty());
}

#[test]
fn linux_select_reports_readiness_and_checks_raw_signal_mask_size() {
    let scratch = support::Scratch::new("linux-select");
    let executable = scratch.path().join("select-checks");
    let example =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/linux_select.lim");
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(example)
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("compile Lim select example");
    assert!(
        compilation.status.success(),
        "compiler failed:\n{}",
        String::from_utf8_lossy(&compilation.stderr)
    );
    let (status, stdout, stderr) = support::run(
        &mut Command::new(executable),
        std::time::Duration::from_secs(5),
        1024,
    )
    .expect("run select example within five seconds");
    assert_eq!(status.code(), Some(42));
    assert_eq!(stdout, include_bytes!("fixtures/select.stdout"));
    assert!(stderr.is_empty());
}

#[test]
fn linux_signal_receivers_consume_self_signals_and_restore_mask() {
    let scratch = support::Scratch::new("linux-signal-receive");
    let executable = scratch.path().join("signal-receive-checks");
    let example =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/linux_signal_receive.lim");
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(example)
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("compile Lim signal receive example");
    assert!(
        compilation.status.success(),
        "compiler failed:\n{}",
        String::from_utf8_lossy(&compilation.stderr)
    );
    let (status, stdout, stderr) = support::run(
        &mut Command::new(executable),
        std::time::Duration::from_secs(5),
        1024,
    )
    .expect("run signal receive example within five seconds");
    assert_eq!(status.code(), Some(42));
    assert_eq!(stdout, include_bytes!("fixtures/signal_receive.stdout"));
    assert!(stderr.is_empty());
}

#[test]
fn linux_shared_memory_attachments_share_bytes_and_release_the_segment() {
    let scratch = support::Scratch::new("linux-shared-memory");
    let executable = scratch.path().join("shared-memory-checks");
    let example =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/linux_shared_memory.lim");
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(example)
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("compile Lim shared-memory example");
    assert!(
        compilation.status.success(),
        "compiler failed:\n{}",
        String::from_utf8_lossy(&compilation.stderr)
    );
    let (status, stdout, stderr) = support::run(
        &mut Command::new(executable),
        std::time::Duration::from_secs(5),
        1024,
    )
    .expect("run shared-memory example within five seconds");
    assert_eq!(status.code(), Some(42));
    assert_eq!(stdout, include_bytes!("fixtures/shared_memory.stdout"));
    assert!(stderr.is_empty());
}

#[test]
fn linux_message_queue_selects_types_and_preserves_oversized_messages() {
    let scratch = support::Scratch::new("linux-message-queue");
    let executable = scratch.path().join("message-queue-checks");
    let example =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/linux_message_queue.lim");
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(example)
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("compile Lim message queue example");
    assert!(
        compilation.status.success(),
        "compiler failed:\n{}",
        String::from_utf8_lossy(&compilation.stderr)
    );
    let (status, stdout, stderr) = support::run(
        &mut Command::new(executable),
        std::time::Duration::from_secs(5),
        1024,
    )
    .expect("run message queue example within five seconds");
    assert_eq!(status.code(), Some(42));
    assert_eq!(stdout, include_bytes!("fixtures/message_queue.stdout"));
    assert!(stderr.is_empty());
}

#[test]
fn linux_semaphore_batches_are_atomic_and_timed_waits_expire() {
    let scratch = support::Scratch::new("linux-semaphores");
    let executable = scratch.path().join("semaphore-checks");
    let example =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/linux_semaphores.lim");
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(example)
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("compile Lim semaphore example");
    assert!(
        compilation.status.success(),
        "compiler failed:\n{}",
        String::from_utf8_lossy(&compilation.stderr)
    );
    let (status, stdout, stderr) = support::run(
        &mut Command::new(executable),
        std::time::Duration::from_secs(5),
        1024,
    )
    .expect("run semaphore example within five seconds");
    assert_eq!(status.code(), Some(42));
    assert_eq!(stdout, include_bytes!("fixtures/semaphores.stdout"));
    assert!(stderr.is_empty());
}

#[test]
fn linux_scheduler_setters_preserve_current_policy_and_priorities() {
    let scratch = support::Scratch::new("linux-scheduler-updates");
    let executable = scratch.path().join("scheduler-update-checks");
    let example = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("examples/linux_scheduler_updates.lim");
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(example)
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("compile Lim scheduler update example");
    assert!(
        compilation.status.success(),
        "compiler failed:\n{}",
        String::from_utf8_lossy(&compilation.stderr)
    );
    let (status, stdout, stderr) = support::run(
        &mut Command::new(executable),
        std::time::Duration::from_secs(5),
        1024,
    )
    .expect("run scheduler update example within five seconds");
    assert_eq!(status.code(), Some(42));
    assert_eq!(stdout, include_bytes!("fixtures/scheduler_updates.stdout"));
    assert!(stderr.is_empty());
}

#[test]
fn linux_process_vectors_and_vmsplice_transfer_exact_payloads() {
    let scratch = support::Scratch::new("linux-process-vectors");
    let executable = scratch.path().join("process-vector-checks");
    let example =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/linux_process_vectors.lim");
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(example)
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("compile Lim process vector example");
    assert!(
        compilation.status.success(),
        "compiler failed:\n{}",
        String::from_utf8_lossy(&compilation.stderr)
    );
    let (status, stdout, stderr) = support::run(
        &mut Command::new(executable),
        std::time::Duration::from_secs(5),
        1024,
    )
    .expect("run process vector example within five seconds");
    assert_eq!(status.code(), Some(42));
    assert_eq!(stdout, include_bytes!("fixtures/process_vectors.stdout"));
    assert!(stderr.is_empty());
}

#[test]
fn linux_process_controls_restore_name_and_preserve_capabilities() {
    let scratch = support::Scratch::new("linux-process-control");
    let executable = scratch.path().join("process-control-checks");
    let example =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/linux_process_control.lim");
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(example)
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("compile Lim process control example");
    assert!(
        compilation.status.success(),
        "compiler failed:\n{}",
        String::from_utf8_lossy(&compilation.stderr)
    );
    let (status, stdout, stderr) = support::run(
        &mut Command::new(executable),
        std::time::Duration::from_secs(5),
        1024,
    )
    .expect("run process control example within five seconds");
    assert_eq!(status.code(), Some(42));
    assert_eq!(stdout, include_bytes!("fixtures/process_control.stdout"));
    assert!(stderr.is_empty());
}

#[test]
fn linux_fifo_creation_permissions_and_payloads_match_kernel_results() {
    let scratch = support::Scratch::new("linux-fifo");
    let executable = scratch.path().join("fifo-checks");
    let example = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/linux_fifo.lim");
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(example)
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("compile Lim FIFO example");
    assert!(
        compilation.status.success(),
        "compiler failed:\n{}",
        String::from_utf8_lossy(&compilation.stderr)
    );
    let (status, stdout, stderr) = support::run(
        Command::new(executable).current_dir(scratch.path()),
        std::time::Duration::from_secs(5),
        1024,
    )
    .expect("run FIFO example within five seconds");
    assert_eq!(status.code(), Some(42));
    assert_eq!(stdout, include_bytes!("fixtures/fifo.stdout"));
    assert!(stderr.is_empty());
    assert!(!scratch.path().join("a").exists());
    assert!(!scratch.path().join("b").exists());
}

#[test]
fn linux_program_break_grows_shrinks_and_preserves_personality() {
    let scratch = support::Scratch::new("linux-program-break");
    let executable = scratch.path().join("break-checks");
    let example =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/linux_program_break.lim");
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(example)
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("compile program break example");
    assert!(
        compilation.status.success(),
        "{}",
        String::from_utf8_lossy(&compilation.stderr)
    );
    let (status, stdout, stderr) = support::run(
        &mut Command::new(executable),
        std::time::Duration::from_secs(5),
        1024,
    )
    .expect("run program break example within five seconds");
    assert_eq!(status.code(), Some(42));
    assert_eq!(stdout, include_bytes!("fixtures/program_break.stdout"));
    assert!(stderr.is_empty());
}

#[test]
fn linux_protection_keys_enforce_write_restrictions_and_release_cleanly() {
    let scratch = support::Scratch::new("linux-pkeys");
    let executable = scratch.path().join("pkey-checks");
    let example = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/linux_pkeys.lim");
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(example)
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("compile protection key example");
    assert!(
        compilation.status.success(),
        "{}",
        String::from_utf8_lossy(&compilation.stderr)
    );
    let (status, stdout, stderr) = support::run(
        &mut Command::new(executable),
        std::time::Duration::from_secs(5),
        1024,
    )
    .expect("run protection key example within five seconds");
    assert_eq!(status.code(), Some(42), "requires Linux PKU support");
    assert_eq!(stdout, include_bytes!("fixtures/pkeys.stdout"));
    assert!(stderr.is_empty());
}

#[test]
fn linux_sealed_and_secret_memory_enforce_protection_and_preserve_payloads() {
    for (example, expected) in [
        (
            "linux_mseal.lim",
            include_bytes!("fixtures/mseal.stdout").as_slice(),
        ),
        (
            "linux_secret_memory.lim",
            include_bytes!("fixtures/secret_memory.stdout").as_slice(),
        ),
    ] {
        let scratch = support::Scratch::new("linux-protected-memory");
        let executable = scratch.path().join("check");
        let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
            .arg(
                std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                    .join("examples")
                    .join(example),
            )
            .arg("-o")
            .arg(&executable)
            .output()
            .expect("compile protected-memory example");
        assert!(
            compilation.status.success(),
            "{}",
            String::from_utf8_lossy(&compilation.stderr)
        );
        let (status, stdout, stderr) = support::run(
            &mut Command::new(executable),
            std::time::Duration::from_secs(5),
            1024,
        )
        .expect("run protected-memory example within five seconds");
        assert_eq!(
            status.code(),
            Some(42),
            "{example}: requires kernel support and sufficient memlock limit"
        );
        assert_eq!(stdout, expected, "{example}");
        assert!(stderr.is_empty(), "{example}");
    }
}

#[test]
fn linux_posix_message_queues_preserve_priorities_and_check_attributes() {
    let scratch = support::Scratch::new("linux-posix-mq");
    let executable = scratch.path().join("mq-checks");
    let example =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/linux_posix_mq.lim");
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(example)
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("compile POSIX message queue example");
    assert!(
        compilation.status.success(),
        "{}",
        String::from_utf8_lossy(&compilation.stderr)
    );
    let (status, stdout, stderr) = support::run(
        &mut Command::new(executable),
        std::time::Duration::from_secs(5),
        1024,
    )
    .expect("run message queue example within five seconds");
    assert_eq!(status.code(), Some(42));
    assert_eq!(stdout, include_bytes!("fixtures/posix_mq.stdout"));
    assert!(stderr.is_empty());
}

#[test]
fn linux_native_aio_transfers_bytes_and_checks_completion_records() {
    let scratch = support::Scratch::new("linux-aio");
    let executable = scratch.path().join("aio-checks");
    let example = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/linux_aio.lim");
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(example)
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("compile native AIO example");
    assert!(
        compilation.status.success(),
        "{}",
        String::from_utf8_lossy(&compilation.stderr)
    );
    let (status, stdout, stderr) = support::run(
        &mut Command::new(executable),
        std::time::Duration::from_secs(5),
        1024,
    )
    .expect("run AIO example within five seconds");
    assert_eq!(status.code(), Some(42));
    assert_eq!(stdout, include_bytes!("fixtures/aio.stdout"));
    assert!(stderr.is_empty());
}

#[test]
fn linux_io_uring_reuses_rings_and_transfers_registered_file_payloads() {
    let scratch = support::Scratch::new("linux-io-uring");
    let binary = scratch.path().join("check");
    let example =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/linux_io_uring.lim");
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(example)
        .arg("-o")
        .arg(&binary)
        .output()
        .unwrap();
    assert!(
        compilation.status.success(),
        "{}",
        String::from_utf8_lossy(&compilation.stderr)
    );
    let (status, stdout, stderr) = support::run(
        &mut Command::new(binary),
        std::time::Duration::from_secs(5),
        1024,
    )
    .unwrap();
    assert_eq!(
        status.code(),
        Some(42),
        "requires io_uring support: {stderr:?}"
    );
    assert_eq!(stdout, include_bytes!("fixtures/io_uring.stdout"));
    assert!(stderr.is_empty());
}

#[test]
fn linux_robust_futex_restores_registration_and_wakes_direct_and_requeued_waiters() {
    let scratch = support::Scratch::new("linux-robust-futex");
    let executable = scratch.path().join("robust-checks");
    let example =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/linux_robust_futex.lim");
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(example)
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("compile robust futex example");
    assert!(
        compilation.status.success(),
        "{}",
        String::from_utf8_lossy(&compilation.stderr)
    );
    // Exercise different scheduling interleavings without recompiling. Each
    // run must prove a queued waiter was woken, not accept EAGAIN as success.
    for iteration in 0..8 {
        let (status, stdout, stderr) = support::run(
            &mut Command::new(&executable),
            std::time::Duration::from_secs(5),
            1024,
        )
        .expect("run robust futex example within five seconds");
        assert_eq!(status.code(), Some(42), "iteration {iteration}");
        assert_eq!(stdout, include_bytes!("fixtures/robust_futex.stdout"));
        assert!(stderr.is_empty());
    }
}

#[test]
fn linux_signal_stack_restores_state_and_checks_alarm_and_tkill() {
    let scratch = support::Scratch::new("linux-signal-stack");
    let executable = scratch.path().join("signal-stack-checks");
    let example =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/linux_signal_stack.lim");
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(example)
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("compile signal stack example");
    assert!(
        compilation.status.success(),
        "{}",
        String::from_utf8_lossy(&compilation.stderr)
    );
    let (status, stdout, stderr) = support::run(
        &mut Command::new(executable),
        std::time::Duration::from_secs(5),
        1024,
    )
    .expect("run signal stack example within five seconds");
    assert_eq!(status.code(), Some(42));
    assert_eq!(stdout, include_bytes!("fixtures/signal_stack.stdout"));
    assert!(stderr.is_empty());
}

#[test]
fn linux_signal_handler_uses_altstack_and_restores_mask_after_sigsuspend() {
    let scratch = support::Scratch::new("linux-signal-handler");
    let executable = scratch.path().join("signal-handler-checks");
    let example =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/linux_signal_handler.lim");
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(example)
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("compile signal handler example");
    assert!(
        compilation.status.success(),
        "{}",
        String::from_utf8_lossy(&compilation.stderr)
    );
    for attempt in 0..8 {
        let (status, stdout, stderr) = support::run(
            Command::new(&executable).current_dir(scratch.path()),
            std::time::Duration::from_secs(5),
            1024,
        )
        .expect("run signal handler example within five seconds");
        assert_eq!(
            status.code(),
            Some(42),
            "attempt {attempt}: {status}; stdout={stdout:?}; stderr={stderr:?}"
        );
        assert_eq!(stdout, include_bytes!("fixtures/signal_handler.stdout"));
        assert!(stderr.is_empty());
    }
}

#[test]
fn signal_handler_checks_reject_broken_delivery_stack_and_return() {
    use std::os::unix::process::ExitStatusExt;
    let scratch = support::Scratch::new("linux-signal-handler-negative");
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let original = include_str!("../examples/linux_signal_handler.lim");
    for (name, from, to) in [
        ("wrong-stack", "0x0c000004", "0x04000004"),
        (
            "missing-return",
            "2:\\nmov eax, 15\\nsyscall\\nud2",
            "2:\\nud2",
        ),
        (
            "missing-delivery",
            "(#unsafe (#call linux-rt-sigsuspend (: signal-set unblocked-mask : sigset-size 8usize)))",
            "-4i64",
        ),
    ] {
        assert_eq!(original.matches(from).count(), 1, "mutation must be unique");
        let source = original.replace(from, to);
        let assembly = lim::compile_source_to_assembly(
            &source,
            &root.join("examples/linux_signal_handler.lim"),
            &lim::CompileConfig::default(),
            &scratch.path().join("cache"),
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap_or_else(|error| panic!("{name}: {}", error.message));
        let executable = scratch.path().join(name);
        lim::link_native_binary(
            &assembly,
            &executable,
            &[],
            &[],
            lim::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap();
        let (status, stdout, stderr) = support::run(
            Command::new(&executable).current_dir(scratch.path()),
            std::time::Duration::from_secs(5),
            1024,
        )
        .unwrap();
        assert_eq!(status.signal(), Some(4), "{name}: {status}");
        assert_eq!(stdout, b"H\n", "{name}: only the first handler may print");
        assert!(stderr.is_empty());
    }
}

#[test]
fn linux_exec_replaces_children_by_path_and_descriptor() {
    let scratch = support::Scratch::new("linux-exec");
    for (fixture, binary) in [("exec_target.lim", "target"), ("exec_driver.lim", "driver")] {
        let source = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures")
            .join(fixture);
        let output = Command::new(env!("CARGO_BIN_EXE_lim"))
            .arg(source)
            .arg("-o")
            .arg(scratch.path().join(binary))
            .output()
            .expect("compile exec fixture");
        assert!(
            output.status.success(),
            "{fixture}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
    let (status, stdout, stderr) = support::run(
        Command::new(scratch.path().join("driver")).current_dir(scratch.path()),
        std::time::Duration::from_secs(5),
        1024,
    )
    .expect("run exec driver within five seconds");
    assert_eq!(status.code(), Some(42));
    assert_eq!(stdout, include_bytes!("fixtures/exec.stdout"));
    assert!(stderr.is_empty());
}

#[test]
fn linux_ioctl_checks_pipe_counts_nonblocking_mode_and_errors() {
    let scratch = support::Scratch::new("linux-ioctl");
    let executable = scratch.path().join("ioctl-checks");
    let example = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/linux_ioctl.lim");
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(example)
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("compile Lim ioctl example");
    assert!(
        compilation.status.success(),
        "compiler failed:\n{}",
        String::from_utf8_lossy(&compilation.stderr)
    );
    let (status, stdout, stderr) = support::run(
        &mut Command::new(executable),
        std::time::Duration::from_secs(5),
        1024,
    )
    .expect("run ioctl example within five seconds");
    assert_eq!(status.code(), Some(42));
    assert_eq!(stdout, include_bytes!("fixtures/ioctl.stdout"));
    assert!(stderr.is_empty());
}

#[test]
fn linux_identity_setters_preserve_credentials_and_report_invalid_ids() {
    let scratch = support::Scratch::new("linux-identity");
    let executable = scratch.path().join("identity-checks");
    let example =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/linux_identity.lim");
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(example)
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("compile Lim identity example");
    assert!(
        compilation.status.success(),
        "compiler failed:\n{}",
        String::from_utf8_lossy(&compilation.stderr)
    );
    let (status, stdout, stderr) = support::run(
        &mut Command::new(executable),
        std::time::Duration::from_secs(5),
        1024,
    )
    .expect("run identity example within five seconds");
    assert_eq!(status.code(), Some(42));
    assert_eq!(stdout, include_bytes!("fixtures/identity.stdout"));
    assert!(stderr.is_empty());
}

#[test]
fn linux_waitid_observes_and_reaps_children_with_explicit_exit_statuses() {
    let scratch = support::Scratch::new("linux-waitid");
    let executable = scratch.path().join("waitid-checks");
    let example =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/linux_waitid.lim");
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(example)
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("compile Lim waitid example");
    assert!(
        compilation.status.success(),
        "compiler failed:\n{}",
        String::from_utf8_lossy(&compilation.stderr)
    );
    let (status, stdout, stderr) = support::run(
        &mut Command::new(executable),
        std::time::Duration::from_secs(5),
        1024,
    )
    .expect("run waitid example within five seconds");
    assert_eq!(status.code(), Some(42));
    assert_eq!(stdout, include_bytes!("fixtures/waitid.stdout"));
    assert!(stderr.is_empty());
}

#[test]
fn linux_syscall_wrappers_report_kernel_results() {
    let scratch = support::Scratch::new("linux-syscalls");
    let executable = scratch.path().join("syscall-checks");
    let example =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/linux_syscalls.lim");
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(example)
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("run Lim compiler");
    assert!(
        compilation.status.success(),
        "compiler failed:\n{}",
        String::from_utf8_lossy(&compilation.stderr)
    );

    let output = Command::new(executable)
        .output()
        .expect("run compiled syscall checks");
    assert_eq!(output.status.code(), Some(42));
    assert!(output.stdout.is_empty());
    assert!(output.stderr.is_empty());
}

#[test]
fn linux_process_queries_match_kernel_results() {
    let scratch = support::Scratch::new("linux-process-queries");
    let executable = scratch.path().join("process-queries");
    let example =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/linux_process_queries.lim");
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(example)
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("compile Lim process query example");
    assert!(
        compilation.status.success(),
        "compiler failed:\n{}",
        String::from_utf8_lossy(&compilation.stderr)
    );

    let output = Command::new(executable)
        .output()
        .expect("run compiled process query example");
    assert_eq!(output.status.code(), Some(42));
    assert!(output.stdout.is_empty());
    assert!(output.stderr.is_empty());
}

#[test]
fn linux_pidfd_syscalls_check_self_and_print_expected_output() {
    let scratch = support::Scratch::new("linux-pidfd");
    let executable = scratch.path().join("pidfd-checks");
    let example = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/linux_pidfd.lim");
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(example)
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("compile Lim pidfd example");
    assert!(
        compilation.status.success(),
        "compiler failed:\n{}",
        String::from_utf8_lossy(&compilation.stderr)
    );

    let output = Command::new(executable)
        .output()
        .expect("run compiled pidfd example");
    assert_eq!(output.status.code(), Some(42));
    assert_eq!(output.stdout, include_bytes!("fixtures/pidfd.stdout"));
    assert!(output.stderr.is_empty());
}

#[test]
fn linux_memfd_file_operations_match_kernel_results() {
    let scratch = support::Scratch::new("linux-memfd");
    let executable = scratch.path().join("memfd-checks");
    let example = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/linux_memfd.lim");
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(example)
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("compile Lim memfd example");
    assert!(
        compilation.status.success(),
        "compiler failed:\n{}",
        String::from_utf8_lossy(&compilation.stderr)
    );

    let output = Command::new(executable)
        .output()
        .expect("run compiled memfd example");
    assert_eq!(output.status.code(), Some(42));
    assert!(output.stdout.is_empty());
    assert!(output.stderr.is_empty());
}

#[test]
fn linux_local_socket_syscalls_match_kernel_results() {
    let scratch = support::Scratch::new("linux-sockets");
    let executable = scratch.path().join("socket-checks");
    let example =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/linux_sockets.lim");
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(example)
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("compile Lim local socket example");
    assert!(
        compilation.status.success(),
        "compiler failed:\n{}",
        String::from_utf8_lossy(&compilation.stderr)
    );

    let output = Command::new(executable)
        .output()
        .expect("run compiled local socket example");
    assert_eq!(output.status.code(), Some(42));
    assert_eq!(output.stdout, b"Lim\n");
    assert!(output.stderr.is_empty());
}

#[test]
fn linux_epoll_eventfd_syscalls_match_kernel_results() {
    let scratch = support::Scratch::new("linux-epoll");
    let executable = scratch.path().join("epoll-checks");
    let example = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/linux_epoll.lim");
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(example)
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("compile Lim epoll example");
    assert!(
        compilation.status.success(),
        "compiler failed:\n{}",
        String::from_utf8_lossy(&compilation.stderr)
    );

    let output = Command::new(executable)
        .output()
        .expect("run compiled epoll example");
    assert_eq!(output.status.code(), Some(42));
    assert!(output.stdout.is_empty());
    assert!(output.stderr.is_empty());
}

#[test]
fn linux_time_syscalls_match_kernel_results() {
    let scratch = support::Scratch::new("linux-time");
    let executable = scratch.path().join("time-checks");
    let example = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/linux_time.lim");
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(example)
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("compile Lim time example");
    assert!(
        compilation.status.success(),
        "compiler failed:\n{}",
        String::from_utf8_lossy(&compilation.stderr)
    );

    let output = Command::new(executable)
        .output()
        .expect("run compiled time example");
    assert_eq!(output.status.code(), Some(42));
    assert!(output.stdout.is_empty());
    assert!(output.stderr.is_empty());
}

#[test]
fn linux_zero_copy_transfers_match_kernel_results() {
    let scratch = support::Scratch::new("linux-zero-copy");
    let executable = scratch.path().join("zero-copy-checks");
    let example =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/linux_zero_copy.lim");
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(example)
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("compile Lim zero-copy example");
    assert!(
        compilation.status.success(),
        "compiler failed:\n{}",
        String::from_utf8_lossy(&compilation.stderr)
    );

    let output = Command::new(executable)
        .output()
        .expect("run compiled zero-copy example");
    assert_eq!(output.status.code(), Some(42));
    assert!(output.stdout.is_empty());
    assert!(output.stderr.is_empty());
}

#[test]
fn linux_futex_results_match_kernel_behavior() {
    let scratch = support::Scratch::new("linux-futex");
    let executable = scratch.path().join("futex-checks");
    let example = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/linux_futex.lim");
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(example)
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("compile Lim futex example");
    assert!(
        compilation.status.success(),
        "compiler failed:\n{}",
        String::from_utf8_lossy(&compilation.stderr)
    );

    let output = Command::new(executable)
        .output()
        .expect("run compiled futex example");
    assert_eq!(output.status.code(), Some(42));
    assert!(output.stdout.is_empty());
    assert!(output.stderr.is_empty());
}

#[test]
fn linux_futex2_waits_wakes_and_requeues_between_shared_words() {
    let scratch = support::Scratch::new("linux-futex2");
    let executable = scratch.path().join("futex2-checks");
    let example =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/linux_futex2.lim");
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(example)
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("compile futex2 example");
    assert!(
        compilation.status.success(),
        "{}",
        String::from_utf8_lossy(&compilation.stderr)
    );
    for attempt in 0..8 {
        let (status, stdout, stderr) = support::run(
            Command::new(&executable).current_dir(scratch.path()),
            std::time::Duration::from_secs(5),
            1024,
        )
        .expect("run futex2 example within five seconds");
        assert_eq!(status.code(), Some(42), "attempt {attempt}: {status}");
        assert_eq!(stdout, include_bytes!("fixtures/futex2.stdout"));
        assert!(stderr.is_empty());
    }
}

#[test]
fn futex2_requeue_checks_reject_waking_instead_of_moving_the_waiter() {
    use std::os::unix::process::ExitStatusExt;
    let scratch = support::Scratch::new("linux-futex2-false-requeue");
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let original = include_str!("../examples/linux_futex2.lim");
    let from = "(#unsafe (#call linux-futex-requeue (: waiters memory : flags 0u32 : wake-count 0i32 : requeue-count 1i32)))\n      (#unsafe (#call linux-futex-wake";
    let to = "(#unsafe (#call linux-futex-requeue (: waiters memory : flags 0u32 : wake-count 1i32 : requeue-count 0i32)))\n      (#unsafe (#call linux-futex-wake";
    assert_eq!(
        original.matches(from).count(),
        1,
        "mutate only the live requeue"
    );
    let source = original.replace(from, to);
    let assembly = lim::compile_source_to_assembly(
        &source,
        &root.join("examples/linux_futex2.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_or_else(|error| panic!("{}", error.message));
    let executable = scratch.path().join("wrong-requeue");
    lim::link_native_binary(
        &assembly,
        &executable,
        &[],
        &[],
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    let (status, stdout, stderr) = support::run(
        Command::new(&executable).current_dir(scratch.path()),
        std::time::Duration::from_secs(5),
        1024,
    )
    .unwrap();
    assert_eq!(
        status.signal(),
        Some(4),
        "the destination must have a live waiter: {status}"
    );
    // The incorrectly woken fourth child can print D before the parent's
    // assertion traps. Do not assume which side of that race runs first.
    assert!(stdout.starts_with(b"A\nB\nC\n"));
    assert!(stderr.is_empty());
}

#[test]
fn linux_directory_syscalls_match_kernel_results() {
    let scratch = support::Scratch::new("linux-directory");
    let executable = scratch.path().join("directory-checks");
    let example =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/linux_directory.lim");
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(example)
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("compile Lim directory example");
    assert!(
        compilation.status.success(),
        "compiler failed:\n{}",
        String::from_utf8_lossy(&compilation.stderr)
    );

    let (status, stdout, stderr) = support::run(
        Command::new(executable).current_dir(scratch.path()),
        std::time::Duration::from_secs(5),
        1024,
    )
    .expect("run directory example within five seconds");
    assert_eq!(status.code(), Some(42));
    assert_eq!(stdout, include_bytes!("fixtures/directory.stdout"));
    assert!(stderr.is_empty());
    assert!(!scratch.path().join("file").exists());
    assert!(!scratch.path().join("link").exists());
}

#[test]
fn linux_resource_syscalls_match_kernel_results() {
    let scratch = support::Scratch::new("linux-resources");
    let executable = scratch.path().join("resource-checks");
    let example =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/linux_resources.lim");
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(example)
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("compile Lim resources example");
    assert!(
        compilation.status.success(),
        "compiler failed:\n{}",
        String::from_utf8_lossy(&compilation.stderr)
    );

    let output = Command::new(executable)
        .output()
        .expect("run compiled resources example");
    assert_eq!(output.status.code(), Some(42));
    assert!(output.stdout.is_empty());
    assert!(output.stderr.is_empty());
}

#[test]
fn linux_signal_syscalls_restore_process_state() {
    let scratch = support::Scratch::new("linux-signals");
    let executable = scratch.path().join("signal-checks");
    let example =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/linux_signals.lim");
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(example)
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("compile Lim signals example");
    assert!(
        compilation.status.success(),
        "compiler failed:\n{}",
        String::from_utf8_lossy(&compilation.stderr)
    );

    let output = Command::new(executable)
        .output()
        .expect("run compiled signals example");
    assert_eq!(output.status.code(), Some(42));
    assert!(output.stdout.is_empty());
    assert!(output.stderr.is_empty());
}

#[test]
fn linux_posix_and_timerfd_syscalls_match_kernel_state() {
    let scratch = support::Scratch::new("linux-timers");
    let executable = scratch.path().join("timer-checks");
    let example =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/linux_timers.lim");
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(example)
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("compile Lim timers example");
    assert!(
        compilation.status.success(),
        "compiler failed:\n{}",
        String::from_utf8_lossy(&compilation.stderr)
    );

    let output = Command::new(executable)
        .output()
        .expect("run compiled timers example");
    assert_eq!(output.status.code(), Some(42));
    assert!(output.stdout.is_empty());
    assert!(output.stderr.is_empty());
}

#[test]
fn linux_extended_attribute_syscalls_match_kernel_results() {
    let scratch = support::Scratch::new("linux-xattrs");
    let executable = scratch.path().join("xattr-checks");
    let example =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/linux_xattrs.lim");
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(example)
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("compile Lim xattrs example");
    assert!(
        compilation.status.success(),
        "compiler failed:\n{}",
        String::from_utf8_lossy(&compilation.stderr)
    );

    let output = Command::new(executable)
        .current_dir(scratch.path())
        .output()
        .expect("run compiled xattrs example");
    assert_eq!(output.status.code(), Some(42));
    assert!(output.stdout.is_empty());
    assert!(output.stderr.is_empty());
    assert!(!scratch.path().join("xattr-file").exists());
}

#[test]
fn linux_file_attribute_syscalls_change_scratch_file_and_print_output() {
    let scratch = support::Scratch::new("linux-file-attributes");
    let executable = scratch.path().join("file-attributes");
    let example =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/linux_file_attributes.lim");
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(example)
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("compile Lim file-attributes example");
    assert!(
        compilation.status.success(),
        "compiler failed:\n{}",
        String::from_utf8_lossy(&compilation.stderr)
    );

    let output = Command::new(executable)
        .current_dir(scratch.path())
        .output()
        .expect("run compiled file-attributes example");
    assert_eq!(output.status.code(), Some(42));
    assert_eq!(
        output.stdout,
        include_bytes!("fixtures/file_attributes.stdout")
    );
    assert!(output.stderr.is_empty());
    assert!(!scratch.path().join("attrs").exists());
}

#[test]
fn linux_vectored_io_syscalls_preserve_position_and_print_output() {
    let scratch = support::Scratch::new("linux-vectored-io");
    let executable = scratch.path().join("vectored-io");
    let example =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/linux_vectored_io.lim");
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(example)
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("compile Lim vectored-IO example");
    assert!(
        compilation.status.success(),
        "compiler failed:\n{}",
        String::from_utf8_lossy(&compilation.stderr)
    );

    let output = Command::new(executable)
        .output()
        .expect("run compiled vectored-IO example");
    assert_eq!(output.status.code(), Some(42));
    assert_eq!(output.stdout, include_bytes!("fixtures/vectored_io.stdout"));
    assert!(output.stderr.is_empty());
}

#[test]
fn linux_interval_timer_syscalls_restore_prior_state() {
    let scratch = support::Scratch::new("linux-interval-timers");
    let executable = scratch.path().join("interval-timer-checks");
    let example =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/linux_interval_timers.lim");
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(example)
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("compile Lim interval timers example");
    assert!(
        compilation.status.success(),
        "compiler failed:\n{}",
        String::from_utf8_lossy(&compilation.stderr)
    );

    let output = Command::new(executable)
        .output()
        .expect("run compiled interval timers example");
    assert_eq!(output.status.code(), Some(42));
    assert!(output.stdout.is_empty());
    assert!(output.stderr.is_empty());
}

#[test]
fn linux_inotify_reports_create_and_delete_events() {
    let scratch = support::Scratch::new("linux-inotify");
    let executable = scratch.path().join("inotify-checks");
    let example =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/linux_inotify.lim");
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(example)
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("compile Lim inotify example");
    assert!(
        compilation.status.success(),
        "compiler failed:\n{}",
        String::from_utf8_lossy(&compilation.stderr)
    );

    let output = Command::new(executable)
        .current_dir(scratch.path())
        .output()
        .expect("run compiled inotify example");
    assert_eq!(output.status.code(), Some(42));
    assert!(output.stdout.is_empty());
    assert!(output.stderr.is_empty());
    assert!(!scratch.path().join("watch-dir").exists());
}

#[test]
fn linux_fork_and_wait4_report_child_exit_status() {
    let scratch = support::Scratch::new("linux-wait4");
    let executable = scratch.path().join("wait4-checks");
    let example = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/linux_wait4.lim");
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(example)
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("compile Lim wait4 example");
    assert!(
        compilation.status.success(),
        "compiler failed:\n{}",
        String::from_utf8_lossy(&compilation.stderr)
    );

    let output = Command::new(executable)
        .output()
        .expect("run compiled wait4 example");
    assert_eq!(output.status.code(), Some(42));
    assert!(output.stdout.is_empty());
    assert!(output.stderr.is_empty());
}

#[test]
fn linux_scheduler_affinity_round_trips_allowed_mask() {
    let scratch = support::Scratch::new("linux-affinity");
    let executable = scratch.path().join("affinity-checks");
    let example =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/linux_affinity.lim");
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(example)
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("compile Lim affinity example");
    assert!(
        compilation.status.success(),
        "compiler failed:\n{}",
        String::from_utf8_lossy(&compilation.stderr)
    );

    let output = Command::new(executable)
        .output()
        .expect("run compiled affinity example");
    assert_eq!(output.status.code(), Some(42));
    assert!(output.stdout.is_empty());
    assert!(output.stderr.is_empty());
}

#[test]
fn linux_copy_file_range_copies_data_and_advances_offsets() {
    let scratch = support::Scratch::new("linux-copy-file-range");
    let executable = scratch.path().join("copy-file-range-checks");
    let example =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/linux_copy_file_range.lim");
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(example)
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("compile Lim copy_file_range example");
    assert!(
        compilation.status.success(),
        "compiler failed:\n{}",
        String::from_utf8_lossy(&compilation.stderr)
    );

    let output = Command::new(executable)
        .output()
        .expect("run compiled copy_file_range example");
    assert_eq!(output.status.code(), Some(42));
    assert!(output.stdout.is_empty());
    assert!(output.stderr.is_empty());
}

#[test]
fn linux_scheduler_query_syscalls_match_kernel_policy() {
    let scratch = support::Scratch::new("linux-scheduler-queries");
    let executable = scratch.path().join("scheduler-query-checks");
    let example = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("examples/linux_scheduler_queries.lim");
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(example)
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("compile Lim scheduler query example");
    assert!(
        compilation.status.success(),
        "compiler failed:\n{}",
        String::from_utf8_lossy(&compilation.stderr)
    );

    let output = Command::new(executable)
        .output()
        .expect("run compiled scheduler query example");
    assert_eq!(output.status.code(), Some(42));
    assert!(output.stdout.is_empty());
    assert!(output.stderr.is_empty());
}

#[test]
fn linux_rename_and_legacy_path_syscalls_match_kernel_results() {
    let scratch = support::Scratch::new("linux-renameat2");
    let executable = scratch.path().join("renameat2-checks");
    let working_directory = scratch.path().join("cwd");
    std::fs::create_dir(&working_directory).unwrap();
    let example =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/linux_renameat2.lim");
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(example)
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("compile Lim renameat2 example");
    assert!(
        compilation.status.success(),
        "compiler failed:\n{}",
        String::from_utf8_lossy(&compilation.stderr)
    );

    let output = Command::new(executable)
        .current_dir(&working_directory)
        .output()
        .expect("run compiled renameat2 example");
    assert_eq!(output.status.code(), Some(42));
    assert!(output.stdout.is_empty());
    assert!(output.stderr.is_empty());
    assert_eq!(std::fs::read_dir(working_directory).unwrap().count(), 0);
}

#[test]
fn linux_file_metadata_syscalls_match_kernel_results() {
    let scratch = support::Scratch::new("linux-statx");
    let executable = scratch.path().join("statx-checks");
    let example = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/linux_statx.lim");
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(example)
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("compile Lim statx example");
    assert!(
        compilation.status.success(),
        "compiler failed:\n{}",
        String::from_utf8_lossy(&compilation.stderr)
    );

    let output = Command::new(executable)
        .output()
        .expect("run compiled statx example");
    assert_eq!(output.status.code(), Some(42));
    assert!(output.stdout.is_empty());
    assert!(output.stderr.is_empty());
}

#[test]
fn linux_openat2_resolves_paths_and_rejects_unknown_flags() {
    let scratch = support::Scratch::new("linux-openat2");
    let executable = scratch.path().join("openat2-checks");
    let working_directory = scratch.path().join("cwd");
    std::fs::create_dir(&working_directory).unwrap();
    let example =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/linux_openat2.lim");
    let compilation = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg(example)
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("compile Lim openat2 example");
    assert!(
        compilation.status.success(),
        "compiler failed:\n{}",
        String::from_utf8_lossy(&compilation.stderr)
    );

    let output = Command::new(executable)
        .current_dir(&working_directory)
        .output()
        .expect("run compiled openat2 example");
    assert_eq!(output.status.code(), Some(42));
    assert!(output.stdout.is_empty());
    assert!(output.stderr.is_empty());
    assert_eq!(std::fs::read_dir(working_directory).unwrap().count(), 0);
}
