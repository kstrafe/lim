#!/usr/bin/env python3
"""Compare native dependency-schedule construction and full drain cost.

Example (run the benchmark itself under scripts/limited-run.sh):
  scripts/limited-run.sh python3 scripts/benchmark-proof-schedule-metadata.py \
    --before-schedule /path/to/before/schedule.rs \
    --after-schedule /path/to/after/schedule.rs --nodes 512 2048 --output schedule.json

Use the same process memory/CPU limits as other compiler benchmarks.
The benchmark compiles tiny standalone drivers with rustc (no Cargo or crates),
then uses wait4 for each child's peak RSS and elapsed wall time. It does not
run proof kernels. Keep node counts within the limited-run memory guard.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import time


def rust_string(value):
    return json.dumps(str(value), ensure_ascii=False)


def file_sha256(path):
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def driver_source(schedule_path, variant):
    path = rust_string(str(schedule_path))
    if variant == "before":
        constructor = r'''
    let metadata = names.iter().enumerate().map(|(i, name)| metadata_for(i, name, &names, scenario)).collect();
    scheduler::Schedule::with_limit(metadata, |_| Ok(false), count).map_err(|e| e.1)
'''
    else:
        constructor = r'''
    scheduler::Schedule::from_source(count,
        |i| names[i].as_str(),
        |i| Ok(metadata_for(i, &names[i], &names, scenario)),
        |_| Ok(false), count).map_err(|e| e.1)
'''
    return f'''#![allow(dead_code)]
#[path = {path}]
mod scheduler;
use scheduler::Metadata;
use std::collections::BTreeSet;

fn metadata_for(i: usize, name: &str, names: &[String], scenario: &str) -> Metadata {{
    let mut dependencies = BTreeSet::new();
    match scenario {{
        "independent" => {{}},
        "chain" => {{ if i > 0 {{ dependencies.insert(names[i - 1].clone()); }} }},
        "fanout" => {{
            // Each node depends on up to the previous eight; deliberate duplicate
            // insertions model repeated source references without changing groups.
            for back in 1..=8 {{
                if i >= back {{ dependencies.insert(names[i - back].clone()); }}
                if back <= 2 && i >= back {{ dependencies.insert(names[i - back].clone()); }}
            }}
        }},
        _ => unreachable!(),
    }}
    Metadata {{ name: name.to_owned(), dependencies, members: None }}
}}

fn main() {{
    let args: Vec<String> = std::env::args().collect();
    let count: usize = args[1].parse().unwrap();
    let scenario = &args[2];
    // Common source-directory representation is present in both variants.
    let names: Vec<String> = (0..count).map(|i| format!("decl_{{i:08}}" )).collect();
    let mut schedule = match build(count, &names, scenario) {{
        Ok(schedule) => schedule,
        Err(error) => {{ eprintln!("schedule construction failed: {{error}}"); std::process::exit(2); }}
    }};
    let mut drained = 0usize;
    loop {{
        match schedule.next() {{
            Ok(Some(group)) => {{
                // Inputs form only singleton groups. Ascending source priority
                // is the exact expected order for all three DAG shapes.
                if group.as_slice() != [drained] {{
                    eprintln!("unexpected group/order at {{drained}}: {{group:?}}");
                    std::process::exit(3);
                }}
                drained += 1;
            }},
            Ok(None) => break,
            Err((index, error)) => {{ eprintln!("drain failed at {{index}}: {{error}}"); std::process::exit(4); }}
        }}
    }}
    if drained != count {{ eprintln!("drained {{drained}}, expected {{count}}"); std::process::exit(5); }}
    println!("OK {{drained}}");
}}

fn build(count: usize, names: &[String], scenario: &str) -> Result<scheduler::Schedule, String> {{
{constructor}
}}
'''


def run_wait4(argv):
    start = time.monotonic()
    process = subprocess.Popen(argv, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    _, status, usage = os.wait4(process.pid, 0)
    elapsed = time.monotonic() - start
    # wait4 reaps the child; collect its already-buffered small output.
    stdout = process.stdout.read()
    stderr = process.stderr.read()
    code = os.waitstatus_to_exitcode(status)
    process.returncode = code
    if code:
        raise RuntimeError(f"child exited {code}: {stderr.strip()}")
    return elapsed, usage.ru_maxrss, stdout.strip()


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--before-schedule", required=True, type=Path)
    parser.add_argument("--after-schedule", required=True, type=Path)
    parser.add_argument("--iterations", type=int, default=5)
    parser.add_argument("--nodes", type=int, nargs="+", default=[512, 2048])
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args(argv)
    if not 1 <= args.iterations <= 5:
        parser.error("--iterations must be between 1 and 5")
    if any(n < 1 or n > 1_100_000 for n in args.nodes):
        parser.error("each --nodes count must be between 1 and 1100000")
    schedules = {"before": args.before_schedule.resolve(strict=True),
                 "after": args.after_schedule.resolve(strict=True)}
    for label, path in schedules.items():
        if not path.is_file():
            parser.error(f"--{label}-schedule must name a file")
    rustc = shutil.which("rustc")
    if not rustc:
        parser.error("rustc must be available (for example through nix develop)")
    results = []
    with tempfile.TemporaryDirectory(prefix="lim-proof-schedule-") as temporary:
        temp = Path(temporary)
        binaries = {}
        hashes = {}
        compiler_path = Path(rustc).resolve(strict=True)
        compiler_hash = file_sha256(compiler_path)
        compiler_version = subprocess.check_output([rustc, "--version"], text=True).strip()
        for label, path in schedules.items():
            source = driver_source(path, label)
            source_path = temp / f"{label}.rs"
            binary_path = temp / label
            source_path.write_text(source)
            compile_result = subprocess.run([rustc, "--edition=2021", "-C", "opt-level=0",
                                             "-D", "warnings", str(source_path), "-o", str(binary_path)],
                                            capture_output=True, text=True)
            if compile_result.returncode:
                raise RuntimeError(f"rustc {label} failed:\n{compile_result.stderr}")
            binaries[label] = binary_path
            hashes[label] = {"schedule_sha256": file_sha256(path),
                             "driver_sha256": hashlib.sha256(source.encode()).hexdigest(),
                             "rustc_path": str(compiler_path), "rustc_version": compiler_version,
                             "rustc_sha256": compiler_hash}
        for count in args.nodes:
            for scenario in ("independent", "chain", "fanout"):
                order = [("before", "after") if i % 2 == 0 else ("after", "before")
                         for i in range(args.iterations)]
                for i, pair in enumerate(order, 1):
                    for label in pair:
                        elapsed, peak_rss, output = run_wait4([str(binaries[label]), str(count), scenario])
                        if output != f"OK {count}":
                            raise RuntimeError(f"bad {label} output for {scenario}/{count}: {output!r}")
                        results.append({"variant": label, "scenario": scenario, "nodes": count,
                                        "iteration": i, "seconds": elapsed,
                                        "peak_rss_kib": peak_rss, "verified_drain": output})
    document = {"schema": 1, "iterations": args.iterations, "nodes": args.nodes,
                "compiler_and_sources": hashes, "samples": results}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(document, indent=2) + "\n")
    print(json.dumps({"output": str(args.output), "samples": len(results), "status": "ok"}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
