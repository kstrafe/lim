//! Reproducible CLI timing sampler for async source shapes.
//!
//! Run with `nix develop --command cargo test --release --test async_compile_timing
//! -- --ignored --nocapture`. The ignored test intentionally prints measurements
//! instead of asserting machine dependent thresholds.

use std::{
    collections::BTreeMap,
    fs,
    path::{Path, PathBuf},
    process::Command,
    time::{Duration, Instant, SystemTime, UNIX_EPOCH},
};

const SAMPLES: usize = 5;

struct Scratch(PathBuf);

impl Scratch {
    fn new() -> Self {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let path =
            std::env::temp_dir().join(format!("lim-async-timing-{}-{nonce}", std::process::id()));
        fs::create_dir_all(&path).unwrap();
        Self(path)
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn fixture(scratch: &Path, name: &str, source: &str) -> PathBuf {
    let path = scratch.join(format!("{name}.lim"));
    fs::write(&path, source).unwrap();
    path
}

fn sample(binary: &Path, source: &Path) -> (Duration, BTreeMap<String, f64>) {
    let started = Instant::now();
    let output = Command::new(binary)
        .arg("--check")
        .arg(source)
        .arg("--timings")
        .output()
        .unwrap();
    let wall = started.elapsed();
    assert!(
        output.status.success(),
        "{}\n{}",
        source.display(),
        String::from_utf8_lossy(&output.stderr)
    );
    let stderr = String::from_utf8(output.stderr).unwrap();
    let mut stages = BTreeMap::new();
    for line in stderr.lines() {
        let Some(rest) = line.strip_prefix("timing ") else {
            continue;
        };
        let Some((name, value)) = rest.trim().split_once(' ') else {
            continue;
        };
        if let Some(milliseconds) = value.strip_suffix("ms") {
            if let Ok(milliseconds) = milliseconds.trim().parse() {
                stages.insert(name.to_owned(), milliseconds);
            }
        }
    }
    (wall, stages)
}

fn median(values: &mut [f64]) -> f64 {
    values.sort_by(f64::total_cmp);
    values[values.len() / 2]
}

#[test]
#[ignore = "manual release timing sampler; run with --ignored --nocapture"]
fn async_compile_shapes_and_warm_cache() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let scratch = Scratch::new();
    let straight = fixture(
        &scratch.0,
        "straight-async",
        r#"(#enum Child () ((Child.Start #u64) (Child.Resume #u64)))
(#enum ChildPoll () ((ChildPoll.Pending Child) (ChildPoll.Ready #u64)))
(#fn child-poll ((task Child) (waker (#ref #u64))) ChildPoll
  (#return (#match task
    (#case (Child.Start value) (ChildPoll.Pending (Child.Resume value)))
    (#case (Child.Resume value) (ChildPoll.Ready value)))))
(#generate #async-fn ( : protocol Await : waker #u64 : function
  (#fn work ((value #u64)) #u64
    (#let result #u64 (#await #u64 Child ChildPoll.Pending ChildPoll.Ready child-poll (Child.Start value)))
    (#return result))))
(#fn main () #u64 (#return 0u64))
"#,
    );
    let nested = fixture(
        &scratch.0,
        "nested-child-parent",
        include_str!("../examples/async_composition.lim"),
    );
    let pinned = fixture(
        &scratch.0,
        "pinned-local-borrower",
        include_str!("../examples/async_fn_local_self_reference.lim"),
    );
    let warm = fixture(
        &scratch.0,
        "warm-cache-async",
        include_str!("../examples/async_nested_await.lim"),
    );
    let binary = PathBuf::from(env!("CARGO_BIN_EXE_lim"));

    println!(
        "async compile timing: release CLI, {SAMPLES} measured samples after one warmup; wall includes process startup, --timings stages are compiler reported"
    );
    for (label, source) in [
        ("straight_async", straight),
        ("nested_child_parent", nested),
        ("pinned_local_borrower", pinned),
    ] {
        let _ = sample(&binary, &source);
        let mut walls = Vec::new();
        let mut stages: BTreeMap<String, Vec<f64>> = BTreeMap::new();
        for _ in 0..SAMPLES {
            let (wall, report) = sample(&binary, &source);
            walls.push(wall.as_secs_f64() * 1000.0);
            for (name, value) in report {
                stages.entry(name).or_default().push(value);
            }
        }
        let wall = median(&mut walls);
        let report = stages
            .into_iter()
            .map(|(name, mut values)| format!("{name}={:.3}ms", median(&mut values)))
            .collect::<Vec<_>>()
            .join(" ");
        println!("{label}: median_wall={wall:.3}ms {report}");
    }

    // Repeated invocations share the source's generated and semantic cache
    // directory. The first measured sample is warm because of the warmup above.
    let _ = sample(&binary, &warm);
    let mut walls = Vec::new();
    let mut stages: BTreeMap<String, Vec<f64>> = BTreeMap::new();
    for _ in 0..SAMPLES {
        let (wall, report) = sample(&binary, &warm);
        walls.push(wall.as_secs_f64() * 1000.0);
        for (name, value) in report {
            stages.entry(name).or_default().push(value);
        }
    }
    let wall = median(&mut walls);
    let report = stages
        .into_iter()
        .map(|(name, mut values)| format!("{name}={:.3}ms", median(&mut values)))
        .collect::<Vec<_>>()
        .join(" ");
    println!("cached_warm_async: median_wall={wall:.3}ms {report}");
    println!("fixtures: async_fn_composition, async_fn_local_self_reference, async_nested_await");
    println!("repository: {}", root.display());
}
