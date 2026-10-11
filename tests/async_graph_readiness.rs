mod support;

use std::fs;

/// Deliberately broad: imports can introduce async into programs whose names
/// do not contain "async". Report every gate before asserting readiness.
#[test]
#[ignore = "manual graph-default audit of the full valid example manifest"]
fn graph_route_compiles_every_valid_example_including_transitive_imports() {
    // Match the broad staged-contract audit's stack rather than the small
    // default test thread. Individual CLI compilation remains separately tested.
    std::thread::Builder::new().stack_size(32 * 1024 * 1024)
        .spawn(audit).unwrap().join().unwrap();
}

fn audit() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let scratch = support::Scratch::new("graph-default-readiness");
    let mut config = lim::CompileConfig::default();
    config.set("async-lowering", "graph");
    let mut failures = Vec::new();
    let mut checked = 0;
    for line in include_str!("../examples/outcomes.txt").lines() {
        let fields = line.split_whitespace().collect::<Vec<_>>();
        if fields.len() != 5 || !matches!(fields[0], "exit" | "graph-exit" | "signal" | "module") {
            continue;
        }
        let path = root.join("examples").join(fields[2]);
        let source = fs::read_to_string(&path).unwrap();
        checked += 1;
        if let Err(error) = lim::compile_source_to_assembly(
            &source,
            &path,
            &config,
            &scratch.path().join("cache"),
            lim::TargetDescription::X86_64_SYSTEM_V,
        ) {
            let location = error
                .span
                .map(|span| format!(":{}:{}", span.line, span.column))
                .unwrap_or_default();
            let name = error.source_name.as_deref().unwrap_or(fields[2]);
            failures.push(format!(
                "{name}{location}: {:?}: {}",
                error.code, error.message
            ));
        }
    }
    eprintln!(
        "graph default audit: {} / {checked} compile",
        checked - failures.len()
    );
    for failure in &failures {
        eprintln!("{failure}");
    }
    assert!(
        failures.is_empty(),
        "graph-default migration still has {} gates",
        failures.len()
    );
}
