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
    assert!(output.stdout.is_empty());
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

    let output = Command::new(executable)
        .output()
        .expect("run compiled directory example");
    assert_eq!(output.status.code(), Some(42));
    assert!(output.stdout.is_empty());
    assert!(output.stderr.is_empty());
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
fn linux_posix_timer_syscalls_match_kernel_state() {
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
        .output()
        .expect("run compiled xattrs example");
    assert_eq!(output.status.code(), Some(42));
    assert!(output.stdout.is_empty());
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
fn linux_renameat2_checks_noreplace_and_success() {
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
fn linux_statx_reports_memfd_size() {
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
