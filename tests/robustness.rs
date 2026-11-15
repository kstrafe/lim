mod support;
use std::{fs, path::Path, process::Command, time::Duration};

const PROCESS_TIMEOUT: Duration = Duration::from_secs(3);

fn run_bounded(input: &Path, output: &Path) -> (i32, String, String) {
    let (status, stdout, stderr) = support::run(
        Command::new(env!("CARGO_BIN_EXE_lim"))
            .arg("--emit-asm")
            .arg(input)
            .arg(output),
        PROCESS_TIMEOUT,
        1024 * 1024,
    )
    .expect("bounded compiler");
    (
        status.code().unwrap_or(-1),
        String::from_utf8_lossy(&stdout).into_owned(),
        String::from_utf8_lossy(&stderr).into_owned(),
    )
}

#[test]
fn seeded_malformed_and_truncated_sources_fail_deterministically_in_bounded_processes() {
    let scratch = support::Scratch::new("robustness");
    let directory = scratch.path();
    let input = directory.join("case.lim");
    let output = directory.join("case.s");
    let mut seed = 0x5eed_u64;

    let mut cases = vec![
        "#fn main {\n  #params = (".to_owned(),
        "#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return \"unfinished)\n".to_owned(),
        "#fn main {\n  #params = ();\n  #returns = #u64;\n  #body = ( (#return (#u64::add-wrap 1u64 2u64)".to_owned(),
        "#generate unknown-generator #u64\n".to_owned(),
        "#gn abort { message; } (#gn-error message)\n#generate abort { message = \"deterministic expansion failure\"; }\n"
            .to_owned(),
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
}
