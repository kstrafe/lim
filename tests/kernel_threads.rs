//! Generated workers must not acquire a C runtime through compiler lowering.
use std::{
    fs,
    path::{Path, PathBuf},
    process::Command,
    time::Duration,
};
mod support;

fn assembly(source: &str, input: &Path, directory: &Path) -> Result<String, lim::Diagnostic> {
    lim::compile_source_to_assembly(
        source,
        input,
        &lim::CompileConfig::default(),
        &directory.join("cache"),
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
}

fn build(source: &str, input: &Path, directory: &Path) -> (PathBuf, String) {
    let asm = assembly(source, input, directory).unwrap();
    for symbol in [
        "pthread_create",
        "pthread_join",
        ".extern malloc",
        ".extern free",
    ] {
        assert!(
            !asm.contains(symbol),
            "unexpected runtime dependency: {symbol}"
        );
    }
    let binary = directory.join("program");
    lim::link_native_binary(
        &asm,
        &binary,
        &[],
        &[],
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap();
    let elf = Command::new("readelf")
        .args(["-lW", "-dW"])
        .arg(&binary)
        .env("LC_ALL", "C")
        .output()
        .unwrap();
    assert!(elf.status.success());
    let elf = String::from_utf8(elf.stdout).unwrap();
    assert!(!elf.contains("INTERP"));
    assert!(elf.contains("There is no dynamic section"));
    (binary, asm)
}

fn runs(binary: &Path, stdout: &[u8]) {
    let (status, actual, stderr) =
        support::run(&mut Command::new(binary), Duration::from_secs(10), 4096).unwrap();
    assert_eq!(status.code(), Some(42), "{status}: {stderr:?}");
    assert_eq!(actual, stdout);
    assert!(stderr.is_empty(), "{stderr:?}");
}

fn joined(task: &str, arguments: &str) -> String {
    format!(
        "(#match (#call {task}-spawn ( {arguments}))
      (#case ({task}-spawn-ok handle)
        (#match (#call {task}-join (: task handle))
          (#case ({task}-join-ok result) result)
          (#case ({task}-join-error (#tuple retry error)) (#panic))))
      (#case ({task}-spawn-error error) (#panic)))"
    )
}

#[test]
fn existing_thread_and_library_executor_examples_are_static() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    for example in [
        "thread_spawn.lim",
        "threaded_tasks.lim",
        "atomic_claim.lim",
        "kernel_threads.lim",
    ] {
        let scratch = support::Scratch::new("kernel-thread-example");
        let input = root.join("examples").join(example);
        let (binary, _) = build(&fs::read_to_string(&input).unwrap(), &input, scratch.path());
        for _ in 0..16 {
            runs(
                &binary,
                if example == "kernel_threads.lim" {
                    b"T\n"
                } else {
                    b""
                },
            );
        }
    }
}

#[test]
fn thread_argument_result_layouts_and_nested_workers_run() {
    let scratch = support::Scratch::new("kernel-thread-layout");
    let declarations = include_str!("../examples/thread_spawn.lim")
        .split("(#fn main")
        .next()
        .unwrap();
    // Construct a nested worker through the same public spawn/join API.
    let declarations = format!(
        "{declarations}
      (#fn middle () #u64 (#drop {}) (#return 42u64))
      (@#thread-spawn (: task MiddleTask : worker middle))
      (#fn wide ((value #u128)) #u128 (#return (#u128.+.wrap value 3u128)))
      (@#thread-spawn (: task WideTask : worker wide))
      (#fn narrow-float ((value #f32)) #f32 (#return (#f32.* value 2.0f32)))
      (@#thread-spawn (: task NarrowFloatTask : worker narrow-float))
      (#fn many-floats ((a #f64) (b #f64) (c #f64) (d #f64) (e #f64) (f #f64) (g #f64) (h #f64) (i #f64)) #f64
        (#return (#f64.+ a i)))
      (@#thread-spawn (: task ManyFloatsTask : worker many-floats))
      (#fn units ((before ()) (value #u64) (after ())) #u64 (#return value))
      (@#thread-spawn (: task UnitsTask : worker units))",
        joined("NoopTask", "")
    );
    let cases = [
      ("wide", format!("(#assert (#u128.== {} 1267650600228229401496703205379u128)) (#return 42u64)", joined("WideTask", "(value 1267650600228229401496703205376u128)"))),
      ("narrow-float", format!("(#assert (#f32.== {} 42.0f32)) (#return 42u64)", joined("NarrowFloatTask", "(value 21.0f32)"))),
      ("float-stack", format!("(#assert (#f64.== {} 42.0f64)) (#return 42u64)", joined("ManyFloatsTask", "(a 1.0f64) (b 2.0f64) (c 3.0f64) (d 4.0f64) (e 5.0f64) (f 6.0f64) (g 7.0f64) (h 8.0f64) (i 41.0f64)"))),
      ("unit-arguments", format!("(#return {})", joined("UnitsTask", "(before ()) (value 42u64) (after ())"))),
      ("float", format!("(#assert (#f64.== {} 42.0f64)) (#return 42u64)", joined("ScaleTask", "(value 21.0f64)"))),
      ("stack-arguments", format!("(#assert (#u64.== {} 28u64)) (#return 42u64)", joined("SumSevenTask", "(a 1u64) (b 2u64) (c 3u64) (d 4u64) (e 5u64) (f 6u64) (g 7u64)"))),
      ("pair", format!("(#let pair Pair {})
        (#assert (#u64.== (#get pair left) 21u64))
        (#assert (#u64.== (#get pair right) 22u64))
        (#forget pair) (#return 42u64)", joined("PairTask", "(pair (#struct-literal Pair ((left 20u64) (right 21u64))))"))),
      ("large", format!("(#return {})",
        joined("LargeTask", "(value (#struct-literal Large ((a 1u64) (b 2u64) (c 3u64) (d 4u64) (e 5u64) (f 6u64) (g 7u64))))")
            .replace("(LargeTask-join-ok result) result", "(LargeTask-join-ok result) (#block (#assert (#u64.== (#get result a) 1u64)) (#assert (#u64.== (#get result g) 7u64)) (#forget result) 42u64)"))),
      ("nested", format!("(#return {})", joined("MiddleTask", ""))),
    ];
    for (name, body) in cases {
        eprintln!("testing ABI case {name}");
        let source = format!("{declarations} (#fn main () #u64 {body})");
        let (binary, _) = build(
            &source,
            &scratch.path().join(format!("{name}.lim")),
            scratch.path(),
        );
        for _ in 0..16 {
            runs(&binary, b"");
        }
    }
}

#[test]
fn foreign_worker_calls_are_rejected_transitively() {
    let scratch = support::Scratch::new("kernel-thread-ffi");
    let source = "(#extern-fn #abi-c abs ((value #i32)) #i32)
      (#fn helper () #i32 (#return (#unsafe (#unsafe-call abs (: value -42i32)))))
      (#fn work () #i32 (#return (#call helper (:))))
      (@#thread-spawn (: task Work : worker work))";
    let error = assembly(source, &scratch.path().join("input.lim"), scratch.path()).unwrap_err();
    assert!(
        error.message.contains("external/indirect callee 'abs'"),
        "{error:?}"
    );
    assert!(error.span.is_some(), "{error:?}");
}

#[test]
fn large_worker_frames_size_the_mapping_from_the_call_graph() {
    let scratch = support::Scratch::new("kernel-thread-stack");
    let source = format!(
        "(#fn large-frame ((value #u64)) #u64
      (#let values (#array #u64 16384) (#array-repeat value))
      (#let result #u64 (#index values 16383usize)) (#forget values) (#return result))
      (#fn work ((value #u64)) #u64 (#return (#call large-frame (: value value))))
      (@#thread-spawn (: task Work : worker work))
      (#fn main () #u64 (#return {}))",
        joined("Work", "(value 42u64)")
    );
    let (binary, asm) = build(&source, &scratch.path().join("input.lim"), scratch.path());
    let stack = asm
        .lines()
        .find_map(|line| line.strip_prefix(".set .Llim_thread_stack_Work, "))
        .unwrap()
        .parse::<usize>()
        .unwrap();
    assert!(stack > 16384 * 8, "{stack}");
    assert_eq!(stack % 4096, 0);
    runs(&binary, b"");
}

#[test]
fn argument_and_result_packets_can_span_multiple_pages() {
    let scratch = support::Scratch::new("kernel-thread-packet");
    let result = joined("ArrayTask", "(value values)").replace(
        "(ArrayTask-join-ok result) result",
        "(ArrayTask-join-ok result) (#block
          (#assert (#u64.== (#index result 0usize) 42u64))
          (#assert (#u64.== (#index result 511usize) 37u64))
          (#assert (#u64.== (#index result 1023usize) 42u64))
          (#forget result) 42u64)",
    );
    let source = format!(
        "(#fn identity ((value (#array #u64 1024))) (#array #u64 1024) (#return value))
      (@#thread-spawn (: task ArrayTask : worker identity))
      (#fn main () #u64
        (#let-mut values (#array #u64 1024) (#array-repeat 42u64))
        (#set-index values 511usize 37u64)
        (#return {result}))"
    );
    let (binary, _) = build(&source, &scratch.path().join("input.lim"), scratch.path());
    runs(&binary, b"");
}

fn trace(binary: &Path, path: &Path, injections: &[&str], stdout: &[u8]) -> String {
    let mut command = Command::new("strace");
    command
        .args(["-qq", "-f", "-o"])
        .arg(path)
        .args(["-e", "trace=mmap,mprotect,clone,futex,munmap,exit"]);
    for injection in injections {
        command.args(["-e", injection]);
    }
    command.arg("--").arg(binary);
    let (status, actual, stderr) =
        support::run(&mut command, Duration::from_secs(15), 4096).unwrap();
    assert_eq!(status.code(), Some(42), "{status}: {stderr:?}");
    assert_eq!(actual, stdout);
    assert!(stderr.is_empty(), "{stderr:?}");
    fs::read_to_string(path).unwrap()
}

#[test]
#[ignore = "Linux ptrace audit: requires strace and permission to trace target programs"]
fn trace_kernel_thread_lifecycle_and_inject_spawn_failures() {
    let scratch = support::Scratch::new("kernel-thread-trace");
    let input = Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/kernel_threads.lim");
    let (binary, _) = build(&fs::read_to_string(&input).unwrap(), &input, scratch.path());
    let log = trace(
        &binary,
        &scratch.path().join("lifecycle.trace"),
        &[],
        b"T\n",
    );
    for syscall in ["mmap(", "mprotect(", "clone(", "munmap(", "exit("] {
        assert_eq!(
            log.lines().filter(|line| line.contains(syscall)).count(),
            32,
            "{syscall}: {log}"
        );
    }
    assert!(log.contains("PROT_NONE"), "{log}");
    assert!(log.contains("CLONE_PARENT_SETTID"), "{log}");
    assert!(log.contains("CLONE_CHILD_CLEARTID"), "{log}");
    assert!(log.contains("CLONE_SETTLS"), "{log}");
    assert!(log.contains("tls=NULL"), "{log}");
    assert!(!log.contains("FUTEX_WAIT_PRIVATE"), "{log}");
    for (syscall, expected, unmapped) in [
        ("mmap", "allocation", 0),
        ("mprotect", "allocation", 1),
        ("clone", "creation", 1),
    ] {
        let source = format!(
            "(#fn work () #u64 (#return 42u64)) (@#thread-spawn (: task Work : worker work))
          (#fn main () #u64
            (#return (#match (#call Work-spawn (:))
              (#case (Work-spawn-ok task) (#panic))
              (#case (Work-spawn-error error)
                (#match error (#case Work-spawn-{expected}-error 42u64) (#case _ (#panic)))))))"
        );
        let (binary, _) = build(&source, &scratch.path().join("failure.lim"), scratch.path());
        let log = trace(
            &binary,
            &scratch.path().join(format!("{syscall}.trace")),
            &[&format!("inject={syscall}:error=ENOMEM:when=1")],
            b"",
        );
        assert!(log.contains("(INJECTED)"), "{log}");
        assert_eq!(
            log.lines().filter(|line| line.contains("munmap(")).count(),
            unmapped,
            "{log}"
        );
        if unmapped != 0 {
            let base = log
                .lines()
                .find(|line| line.contains("mmap("))
                .unwrap()
                .split("= ")
                .last()
                .unwrap()
                .trim();
            assert!(base.starts_with("0x"), "{log}");
            assert!(
                log.contains(&format!("munmap({base}, ")),
                "mapping was not released: {log}"
            );
        }
    }
}

#[test]
#[ignore = "Linux ptrace audit: injects futex errors and delays child exit"]
fn join_retries_transient_errors_and_retains_the_handle_on_other_errors() {
    let scratch = support::Scratch::new("kernel-thread-join-errors");
    let source = "(#fn work () #u64 (#return 42u64)) (@#thread-spawn (: task Work : worker work))
      (#fn main () #u64
        (#return (#match (#call Work-spawn (:))
          (#case (Work-spawn-ok task)
            (#match (#call Work-join (: task task))
              (#case (Work-join-ok value) value)
              (#case (Work-join-error (#tuple retry error))
                (#block
                  (#assert (#i32.== error 5i32))
                  (#let letter #u8 82u8)
                  (#assert (#i64.== (#unsafe (#asm #i64
                    ((rax 1usize) (rdi 1usize) (rsi (#addr-of letter)) (rdx 1usize)) \"syscall\")) 1i64))
                  (#match (#call Work-join (: task retry))
                    (#case (Work-join-ok value) value)
                    (#case (Work-join-error (#tuple still-owned code)) (#panic)))))))
          (#case (Work-spawn-error error) (#panic)))))";
    let (binary, _) = build(source, &scratch.path().join("input.lim"), scratch.path());
    for errno in ["EINTR", "EAGAIN", "EIO"] {
        // Hold the child at exit entry so the parent has a blocked join to
        // exercise. Require actual injected-call evidence, not a presumed race.
        let log = trace(
            &binary,
            &scratch.path().join(format!("{errno}.trace")),
            &[
                "inject=exit:delay_enter=1s:when=1",
                &format!("inject=futex:error={errno}:when=1"),
            ],
            if errno == "EIO" { b"R" } else { b"" },
        );
        assert!(
            log.contains(&format!("= -1 {errno}")) && log.contains("(INJECTED)"),
            "{log}"
        );
        assert!(log.contains("FUTEX_WAIT"), "{log}");
        assert!(!log.contains("FUTEX_WAIT_PRIVATE"), "{log}");
        assert_eq!(
            log.lines().filter(|line| line.contains("munmap(")).count(),
            1,
            "{log}"
        );
    }
}

#[test]
fn writing_the_stack_guard_traps() {
    use std::os::unix::process::ExitStatusExt;
    let scratch = support::Scratch::new("kernel-thread-guard");
    let source = format!("(#fn work () #u64
      (#drop (#unsafe (#asm #u64 () \"mov rax, rsp\\nand rax, -4096\\nsub rax, 65536\\nmov BYTE PTR [rax], 1\")))
      (#return 42u64)) (@#thread-spawn (: task Work : worker work))
      (#fn main () #u64 (#return {}))", joined("Work", ""));
    let (binary, asm) = build(&source, &scratch.path().join("input.lim"), scratch.path());
    assert!(asm.contains(".set .Llim_thread_stack_Work, 65536\n"));
    let (status, stdout, stderr) =
        support::run(&mut Command::new(binary), Duration::from_secs(10), 4096).unwrap();
    assert_eq!(status.signal(), Some(11), "{status}");
    assert!(stdout.is_empty() && stderr.is_empty());
}
