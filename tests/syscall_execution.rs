//! Opt-in runtime evidence: requires Linux x86-64, ptrace permission, and the
//! kernel features used by the syscall corpus. Never silently skip failures.
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
    process::{Command, Stdio},
    time::Duration,
};

mod support;

fn syscall_entry(line: &str) -> Option<(u32, &str)> {
    // strace -f -n -o FILE: "PID [ NUM] syscall(args) = result".
    // Signal/exit notices also have a numeric tag, but aren't syscall entries.
    let (pid, rest) = line.split_once('[')?;
    if !pid.trim().chars().all(|c| c.is_ascii_digit()) {
        return None;
    }
    let (number, body) = rest.split_once(']')?;
    let number = number.trim().parse().ok()?;
    let body = body.trim_start();
    let (name, _) = body.split_once('(')?;
    if name.is_empty() || !name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_') {
        return None;
    }
    Some((number, name))
}

fn observed_calls(trace: &str) -> Result<BTreeSet<u32>, String> {
    if trace.contains("runs in 32 bit mode") || trace.contains("runs in x32 mode") {
        return Err("trace changed syscall ABI".into());
    }
    let mut launched = false;
    let mut observed = BTreeSet::new();
    for line in trace.lines() {
        let Some((number, name)) = syscall_entry(line) else {
            continue;
        };
        if !launched {
            // strace's launch execve is not a call issued by the Lim program.
            // Later execve/execveat calls (including children) do count.
            if number != 59 || name != "execve" || !line.ends_with("= 0") {
                return Err(format!("expected successful initial execve, got {line}"));
            }
            launched = true;
            continue;
        }
        observed.insert(number);
    }
    if !launched {
        return Err("trace contains no successful program launch".into());
    }
    Ok(observed)
}

#[test]
fn trace_parser_excludes_launcher_metadata_and_resumed_lines() {
    let trace = "123 [ 59] execve(\"program\", [], 0x0) = 0\n\
        123 [ 59] --- SIGCHLD {si_code=CLD_EXITED} ---\n\
        123 [ 59] +++ exited with 0 +++\n\
        123 [ 61] <... wait4 resumed>NULL, 0, NULL) = 124\n\
        123 [ 1] write(1, \"[ 55] getsockopt(\", 20) = 20\n\
        124 [ 59] execve(\"target\", [], NULL <unfinished ...>\n\
        124 [ 322] execveat(3, \"\", [], [], AT_EMPTY_PATH) = 0\n";
    assert_eq!(observed_calls(trace).unwrap(), BTreeSet::from([1, 59, 322]));
    let launch_only =
        "123 [ 59] execve(\"program\", [], NULL) = 0\n123 [ 59] +++ exited with 0 +++\n";
    assert!(observed_calls(launch_only).unwrap().is_empty());
    assert!(observed_calls("123 [ 59] execve(\"missing\", [], NULL) = -1 ENOENT\n").is_err());
    assert!(observed_calls("strace: ptrace: Operation not permitted\n").is_err());
    assert!(observed_calls("123 [ 9] mmap(NULL, 4096, 3, 34, -1, 0) = 0x1000\n").is_err());
}

fn walk(expression: &lim::Expr, visit: &mut impl FnMut(&lim::Expr)) {
    visit(expression);
    if let lim::Expr::List(items) = expression {
        for item in items {
            walk(item, visit);
        }
    }
}

fn implemented() -> BTreeMap<u32, String> {
    let catalog: BTreeMap<_, _> = include_str!("../library/linux_x86_64_syscall_numbers.lim")
        .lines()
        .filter_map(|line| {
            let rest = line.strip_prefix("(#const ")?;
            let (name, value) = rest.split_once(" #usize ").unwrap();
            let value = value
                .strip_suffix("usize)")
                .unwrap()
                .parse::<u32>()
                .unwrap();
            Some((name.to_owned(), value))
        })
        .collect();
    let mut result = BTreeMap::new();
    for form in lim::parse(include_str!("../library/linux_x86_64.lim")).unwrap() {
        walk(&form.expr, &mut |expr| {
            let lim::Expr::List(items) = expr else { return };
            if !matches!(items.first(), Some(lim::Expr::Symbol(head)) if head == "#fn" || head == "#unsafe-fn")
            {
                return;
            }
            walk(expr, &mut |nested| {
                if let lim::Expr::Symbol(name) = nested {
                    if name.starts_with("LINUX-SYS-") {
                        result.insert(
                            *catalog.get(name).expect("known syscall number"),
                            name.clone(),
                        );
                    }
                }
            });
        });
    }
    assert!(result.len() >= 278);
    result
}

fn compile(source: &Path, binary: &Path, cwd: &Path) {
    let (status, _, stderr) = support::run(
        Command::new(env!("CARGO_BIN_EXE_lim"))
            .arg(source)
            .arg("-o")
            .arg(binary)
            .current_dir(cwd),
        Duration::from_secs(30),
        1024 * 1024,
    )
    .unwrap();
    assert!(
        status.success(),
        "{}: {}",
        source.display(),
        String::from_utf8_lossy(&stderr)
    );
    // No dynamic-loader startup may contaminate the coverage evidence.
    let output = Command::new("readelf")
        .args(["-lW", "-dW"])
        .arg(binary)
        .env("LC_ALL", "C")
        .output()
        .expect("readelf must be installed");
    assert!(output.status.success());
    let metadata = String::from_utf8(output.stdout).unwrap();
    assert!(
        !metadata.contains("INTERP"),
        "{} uses an interpreter",
        binary.display()
    );
    assert!(
        metadata.contains("There is no dynamic section"),
        "{} is not static",
        binary.display()
    );
}

struct Case {
    source: String,
    status: i32,
    stdout: Vec<u8>,
    stderr: Vec<u8>,
    stdin: Vec<u8>,
    exec_target: bool,
}

#[test]
#[ignore = "Linux ptrace audit: requires strace syscall error injection"]
fn byte_io_retries_interruption_without_changing_the_syscall_number() {
    let scratch = support::Scratch::new("byte-io-interruption");
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let binary = scratch.path().join("echo");
    compile(
        &root.join("examples/echo_input.lim"),
        &binary,
        scratch.path(),
    );
    let input = scratch.path().join("stdin");
    let payload = b"interrupted Lim IO\n\0\xff";
    fs::write(&input, payload).unwrap();
    for syscall in ["read", "write"] {
        for errno in ["EINTR", "EBADF"] {
            let log = scratch.path().join(format!("{syscall}-{errno}.trace"));
            let (status, stdout, stderr) = support::run(
                Command::new("strace")
                    .args(["-qq", "-o"])
                    .arg(&log)
                    .args([
                        "-e",
                        "trace=read,write",
                        "-e",
                        &format!("inject={syscall}:error={errno}:when=1"),
                    ])
                    .arg("--")
                    .arg(&binary)
                    .stdin(Stdio::from(fs::File::open(&input).unwrap())),
                Duration::from_secs(10),
                4096,
            )
            .unwrap();
            let log = fs::read_to_string(log).unwrap();
            assert!(
                log.contains(&format!("= -1 {errno}")) && log.contains("(INJECTED)"),
                "{log}"
            );
            assert!(stderr.is_empty(), "{stderr:?}");
            assert_eq!(
                status.code(),
                Some(if errno == "EINTR" { 0 } else { 1 }),
                "{syscall} {errno}: {log}"
            );
            assert_eq!(
                stdout,
                if errno == "EINTR" {
                    payload.as_slice()
                } else {
                    b""
                },
                "{syscall} {errno}: {log}"
            );
        }
    }
}

fn fixture(root: &Path, name: &str) -> Vec<u8> {
    if name == "-" {
        Vec::new()
    } else {
        fs::read(root.join(name)).unwrap()
    }
}

fn cases(root: &Path) -> Vec<Case> {
    let mut result = Vec::new();
    for line in include_str!("../examples/outcomes.txt").lines() {
        let fields: Vec<_> = line.split_whitespace().collect();
        if fields.len() != 5 || !fields[2].starts_with("linux_") {
            continue;
        }
        assert_eq!(
            fields[0], "exit",
            "Linux corpus expectation needs explicit handling: {line}"
        );
        result.push(Case {
            source: format!("examples/{}", fields[2]),
            status: fields[1].parse().unwrap(),
            stdout: fixture(root, fields[3]),
            stderr: fixture(root, fields[4]),
            stdin: Vec::new(),
            exec_target: false,
        });
    }
    result.push(Case {
        source: "tests/fixtures/exec_driver.lim".into(),
        status: 42,
        stdout: include_bytes!("fixtures/exec.stdout").to_vec(),
        stderr: Vec::new(),
        stdin: Vec::new(),
        exec_target: true,
    });
    result.push(Case {
        source: "examples/echo_input.lim".into(),
        status: 0,
        stdout: b"traced Lim input\n".to_vec(),
        stderr: Vec::new(),
        stdin: b"traced Lim input\n".to_vec(),
        exec_target: false,
    });
    assert!(result.len() >= 54);
    result
}

#[test]
#[ignore = "Linux x86-64 syscall audit: requires strace/ptrace and the corpus kernel features"]
fn every_implemented_syscall_is_observed_in_passing_programs() {
    assert!(
        cfg!(all(target_os = "linux", target_arch = "x86_64")),
        "native Linux x86-64 required"
    );
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let scratch = support::Scratch::new("syscall-execution");
    let required = implemented();
    let mut evidence: BTreeMap<u32, BTreeSet<String>> = BTreeMap::new();
    for (index, case) in cases(&root).into_iter().enumerate() {
        let cwd = scratch.path().join(index.to_string());
        fs::create_dir(&cwd).unwrap();
        let binary = cwd.join("program");
        compile(&root.join(&case.source), &binary, &cwd);
        if case.exec_target {
            compile(
                &root.join("tests/fixtures/exec_target.lim"),
                &cwd.join("target"),
                &cwd,
            );
        }
        let input = cwd.join("stdin");
        fs::write(&input, &case.stdin).unwrap();
        let trace = cwd.join("syscalls.trace");
        let (status, stdout, stderr) = support::run(
            Command::new("strace")
                .args(["-qq", "-f", "-n", "-s", "32", "-o"])
                .arg(&trace)
                .arg("--")
                .arg(&binary)
                .current_dir(&cwd)
                .stdin(Stdio::from(fs::File::open(&input).unwrap())),
            Duration::from_secs(15),
            1024 * 1024,
        )
        .unwrap_or_else(|error| panic!("{}: trace failed: {error}", case.source));
        assert_eq!(
            status.code(),
            Some(case.status),
            "{}: {status}; {}",
            case.source,
            String::from_utf8_lossy(&stderr)
        );
        assert_eq!(stdout, case.stdout, "{}: stdout", case.source);
        assert_eq!(
            stderr, case.stderr,
            "{}: stderr or tracer error",
            case.source
        );
        assert!(
            fs::metadata(&trace).unwrap().len() <= 64 * 1024 * 1024,
            "trace exceeds bound"
        );
        let observed = observed_calls(&fs::read_to_string(&trace).unwrap())
            .unwrap_or_else(|error| panic!("{}: {error}", case.source));
        println!(
            "PASS {}: {} syscall numbers observed",
            case.source,
            observed.len()
        );
        for number in observed {
            evidence
                .entry(number)
                .or_default()
                .insert(case.source.clone());
        }
    }
    let mut missing = Vec::new();
    for (number, name) in &required {
        match evidence.get(number) {
            Some(sources) => println!(
                "OBSERVED {number} {name}: {}",
                sources.iter().cloned().collect::<Vec<_>>().join(", ")
            ),
            None => missing.push(format!("{number} {name}")),
        }
    }
    println!(
        "{}/{} implemented syscall numbers observed in passing programs",
        required.len() - missing.len(),
        required.len()
    );
    assert!(
        missing.is_empty(),
        "unobserved implemented syscalls:\n{}",
        missing.join("\n")
    );
}
