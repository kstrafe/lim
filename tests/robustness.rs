use std::{
    fs,
    path::Path,
    process::{Command, Stdio},
    thread,
    time::{Duration, Instant},
};

const PROCESS_TIMEOUT: Duration = Duration::from_secs(3);

fn run_bounded(input: &Path, output: &Path) -> (i32, String, String) {
    let mut child = Command::new(env!("CARGO_BIN_EXE_lim"))
        .arg("--emit-asm")
        .arg(input)
        .arg(output)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn compiler subprocess");
    let started = Instant::now();
    loop {
        if let Some(status) = child.try_wait().expect("poll compiler subprocess") {
            let result = child.wait_with_output().expect("collect compiler output");
            return (
                status.code().unwrap_or(-1),
                String::from_utf8_lossy(&result.stdout).into_owned(),
                String::from_utf8_lossy(&result.stderr).into_owned(),
            );
        }
        if started.elapsed() >= PROCESS_TIMEOUT {
            child.kill().expect("kill timed-out compiler");
            let _ = child.wait();
            panic!(
                "compiler exceeded {PROCESS_TIMEOUT:?} on {}",
                input.display()
            );
        }
        thread::sleep(Duration::from_millis(5));
    }
}

#[test]
fn seeded_malformed_and_truncated_sources_fail_deterministically_in_bounded_processes() {
    let directory = std::env::temp_dir().join(format!(
        "lim-robustness-{}-{}",
        std::process::id(),
        std::thread::current().name().unwrap_or("worker")
    ));
    let _ = fs::remove_dir_all(&directory);
    fs::create_dir_all(&directory).unwrap();
    let input = directory.join("case.lim");
    let output = directory.join("case.s");
    let mut seed = 0x5eed_u64;

    let mut cases = vec![
        "(#fn main () u64".to_owned(),
        "(#fn main () u64 (#return \"unfinished))".to_owned(),
        "(#fn main () u64 (#return (#u64.+.wrap 1u64 2u64))".to_owned(),
        "(@unknown-generator u64)".to_owned(),
        "(#generator abort (message) (#gn-error message)) (@abort \"deterministic expansion failure\")".to_owned(),
    ];
    let alphabet = b"()#@;`,'\" abcdef0123456789_+-";
    for length in 1..=48 {
        let mut source = String::with_capacity(length);
        for _ in 0..length {
            seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
            source.push(alphabet[(seed as usize) % alphabet.len()] as char);
        }
        cases.push(source);
    }

    for (index, source) in cases.iter().enumerate() {
        fs::write(&input, source).unwrap();
        let first = run_bounded(&input, &output);
        assert_ne!(
            first.0, 0,
            "malformed seed {index} unexpectedly compiled: {source:?}"
        );
        assert!(
            !output.exists(),
            "failed compilation left an assembly artifact for seed {index}"
        );
        let second = run_bounded(&input, &output);
        assert_eq!(
            first, second,
            "seed {index} produced nondeterministic diagnostics: {source:?}"
        );
        assert!(
            !output.exists(),
            "retry left an assembly artifact for seed {index}"
        );
    }
    fs::remove_dir_all(directory).unwrap();
}
