mod support;
use std::os::unix::process::ExitStatusExt;
use std::{
    collections::BTreeSet,
    fs,
    path::{Path, PathBuf},
    process::{Command, ExitStatus},
    sync::atomic::{AtomicUsize, Ordering},
    time::Duration,
};

static NEXT_DIRECTORY: AtomicUsize = AtomicUsize::new(0);
struct Scratch(PathBuf);
impl Scratch {
    fn new() -> Self {
        loop {
            let path = std::env::temp_dir().join(format!(
                "lim-native-examples-{}-{}",
                std::process::id(),
                NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed)
            ));
            match fs::create_dir(&path) {
                Ok(()) => return Self(path),
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("create scratch directory: {error}"),
            }
        }
    }
}
impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn run(
    command: &mut Command,
    directory: &Path,
    budget: Duration,
) -> Result<(ExitStatus, Vec<u8>, Vec<u8>), String> {
    let command = command.current_dir(directory);
    support::run(command, budget, 1024 * 1024)
}

fn outcome_matches(kind: &str, expected: &str, status: ExitStatus) -> bool {
    match kind {
        "exit" => expected
            .parse::<i32>()
            .ok()
            .is_some_and(|code| status.code() == Some(code)),
        "signal" => expected
            .parse::<i32>()
            .ok()
            .is_some_and(|signal| status.signal() == Some(signal)),
        _ => false,
    }
}

fn collect_sources(directory: &Path, root: &Path, paths: &mut BTreeSet<String>) {
    for entry in fs::read_dir(directory).unwrap() {
        let entry = entry.unwrap();
        if entry.file_name().to_string_lossy().starts_with('.') {
            continue;
        }
        let path = entry.path();
        if entry.file_type().unwrap().is_dir() {
            collect_sources(&path, root, paths);
        } else if path.extension().is_some_and(|extension| extension == "lim") {
            paths.insert(
                path.strip_prefix(root)
                    .unwrap()
                    .to_str()
                    .unwrap()
                    .to_owned(),
            );
        }
    }
}

fn expected_output(root: &Path, name: &str) -> Vec<u8> {
    if name == "-" {
        Vec::new()
    } else {
        fs::read(root.join(name)).unwrap()
    }
}

#[test]
fn every_native_example_has_its_declared_outcome() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let examples = root.join("examples");
    let mut sources = BTreeSet::new();
    collect_sources(&examples, &examples, &mut sources);
    let manifest = include_str!("../examples/outcomes.txt");
    let mut declared = BTreeSet::new();
    let cases = manifest
        .lines()
        .filter(|line| !line.trim().is_empty() && !line.starts_with('#'))
        .map(|line| {
            let fields = line.split_whitespace().collect::<Vec<_>>();
            assert_eq!(fields.len(), 5, "invalid expectation: {line}");
            assert!(
                matches!(fields[0], "exit" | "signal" | "module" | "error"),
                "invalid expectation: {line}"
            );
            assert!(
                declared.insert(fields[2].to_owned()),
                "duplicate expectation: {line}"
            );
            fields
        })
        .collect::<Vec<_>>();
    assert_eq!(
        sources, declared,
        "every example needs exactly one expectation"
    );
    let scratch = Scratch::new();
    for (index, fields) in cases.into_iter().enumerate() {
        let [kind, expected, source, stdout, stderr] = fields.as_slice() else {
            unreachable!()
        };
        let output = scratch.0.join(format!("program-{index}"));
        let mut compiler = Command::new(env!("CARGO_BIN_EXE_lim"));
        if matches!(*kind, "module" | "error") {
            compiler
                .arg("--emit-asm")
                .arg(examples.join(source))
                .arg(&output);
        } else {
            compiler.arg(examples.join(source)).arg("-o").arg(&output);
        }
        let (status, _, compiler_errors) = run(&mut compiler, &scratch.0, Duration::from_secs(20))
            .unwrap_or_else(|error| panic!("{source}: compile {error}"));
        if *kind == "error" {
            assert_eq!(
                status.code(),
                Some(1),
                "{source}: expected compiler error, got {status}"
            );
            assert!(
                String::from_utf8_lossy(&compiler_errors).contains(&format!("error[{expected}]")),
                "{source}: {}",
                String::from_utf8_lossy(&compiler_errors)
            );
            assert!(
                !output.exists(),
                "{source}: failed compilation published output"
            );
            continue;
        }
        assert!(
            status.success(),
            "{source}: compiler/linker failed: {status}\n{}",
            String::from_utf8_lossy(&compiler_errors)
        );
        if *kind == "module" {
            continue;
        }
        let (status, actual_stdout, actual_stderr) = run(
            &mut Command::new(&output),
            &scratch.0,
            Duration::from_secs(2),
        )
        .unwrap_or_else(|error| panic!("{source}: runtime {error}"));
        assert!(
            outcome_matches(kind, expected, status),
            "{source}: expected {kind} {expected}, got {status}"
        );
        assert_eq!(
            actual_stdout,
            expected_output(root, stdout),
            "{source}: stdout differs"
        );
        assert_eq!(
            actual_stderr,
            expected_output(root, stderr),
            "{source}: stderr differs"
        );
    }
}

#[test]
fn wrong_results_and_unexpected_signals_are_failures() {
    assert!(outcome_matches(
        "exit",
        "255",
        ExitStatus::from_raw(255 << 8)
    ));
    assert!(!outcome_matches(
        "exit",
        "42",
        ExitStatus::from_raw(41 << 8)
    ));
    assert!(!outcome_matches("exit", "139", ExitStatus::from_raw(11)));
    assert!(!outcome_matches("signal", "4", ExitStatus::from_raw(11)));
    assert!(outcome_matches("signal", "4", ExitStatus::from_raw(4)));
}

#[test]
fn compiler_rejection_is_not_a_runtime_outcome() {
    let scratch = Scratch::new();
    let source = scratch.0.join("invalid.lim");
    let output = scratch.0.join("program");
    fs::write(
        &source,
        "(#fn main () u64 (#let value u64 false) (#return value))",
    )
    .unwrap();
    let (status, _, errors) = run(
        Command::new(env!("CARGO_BIN_EXE_lim"))
            .arg(&source)
            .arg("-o")
            .arg(&output),
        &scratch.0,
        Duration::from_secs(20),
    )
    .unwrap();
    assert_eq!(status.code(), Some(1));
    assert!(String::from_utf8_lossy(&errors).contains("error[E4000]"));
    assert!(!output.exists());
}

#[test]
fn a_timed_out_example_fails() {
    let scratch = Scratch::new();
    assert!(run(
        Command::new("sh").args(["-c", "exec sleep 10"]),
        &scratch.0,
        Duration::from_millis(30)
    )
    .unwrap_err()
    .contains("timeout"));
}
