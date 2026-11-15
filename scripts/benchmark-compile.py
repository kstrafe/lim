#!/usr/bin/env python3
"""Measure end-to-end compilation including native linking (warm by default).

Example:
  python3 scripts/benchmark-compile.py examples/async_fn.lim --baseline /tmp/lim-before
  python3 scripts/benchmark-compile.py --async-heavy --cfg async-lowering=graph \\
      --baseline /tmp/lim-before
  python3 scripts/benchmark-compile.py --async-pinned-heavy --cold-generators \\
      --cfg async-lowering=graph --baseline /tmp/lim-before

Each compiler gets separate warmups because compiler fingerprints invalidate
generator caches. Outputs go in a temporary directory, never over user binaries.
"""

import argparse
from pathlib import Path
import statistics
import subprocess
import tempfile
import time


def measure(compiler, source, output, repetitions, compare_runtime=False, cfgs=(), cold=False):
    compiler = str(compiler.resolve())
    source_text = source.read_text() if cold else None

    def invoke(input_path):
        command = [compiler, str(input_path), "-o", str(output)]
        for cfg in cfgs:
            command.extend(["--cfg", cfg])
        started = time.perf_counter_ns()
        subprocess.run(command, check=True, stdout=subprocess.DEVNULL)
        return (time.perf_counter_ns() - started) / 1_000_000

    def sample():
        if not cold:
            return invoke(source)
        # Synthetic workloads have no imports. A fresh source directory also
        # means a fresh .lim cache, without deleting anyone's existing cache.
        # Snapshot setup/teardown is deliberately outside the timed compiler.
        with tempfile.TemporaryDirectory(prefix="lim-cold-generators-") as directory:
            input_path = Path(directory) / source.name
            input_path.write_text(source_text)
            return invoke(input_path)

    for _ in range(2):
        sample()
    samples = [sample() for _ in range(repetitions)]
    print(f"{compiler}: median={statistics.median(samples):.2f} ms "
          f"min={min(samples):.2f} ms max={max(samples):.2f} ms n={repetitions}")
    artifact = output.read_bytes()
    print(f"binary_bytes={len(artifact)}")
    runtime = None
    if compare_runtime:
        result = subprocess.run([str(output)], stdin=subprocess.DEVNULL,
                                capture_output=True, timeout=5)
        runtime = (result.returncode, result.stdout, result.stderr)
    return statistics.median(samples), artifact, runtime


def reference_heavy_source():
    """Exercise shared provenance facts without relying on generated code."""
    lines = ["#fn identity ((input (#ref #u64))) (#ref #u64) (#return input)"]
    for function in range(64):
        lines.append(f"#fn worker-{function} ((input (#ref #u64))) (#ref #u64)")
        for binding in range(24):
            previous = "input" if binding == 0 else f"value-{binding - 1}"
            lines.append(f"  (#let value-{binding} (#ref #u64) {previous})")
        lines.append("  (#return (#call identity ((input value-23))))")
    lines.append("#fn main () #u64 (#let owner #u64 42u64) "
                 "(#return (#deref (#call worker-0 ((input (#borrow owner))))))")
    return "\n".join(lines) + "\n"


def snapshot_heavy_source():
    """Exercise nested branch-result snapshot lookup and lexical cleanup."""
    lines = []
    for function in range(64):
        lines.append(f"#fn worker-{function} ((input (#ref #u64)) (choose #bool)) (#ref #u64)")
        for binding in range(24):
            previous = "input" if binding == 0 else f"value-{binding - 1}"
            lines.append(f"  (#let value-{binding} (#ref #u64) (#if choose "
                         f"(#block (#let left-{binding} (#ref #u64) {previous}) left-{binding}) "
                         f"(#block (#let right-{binding} (#ref #u64) {previous}) right-{binding})))")
        lines.append("  (#return value-23)")
    lines.append("#fn main () #u64 (#let owner #u64 42u64) "
                 "(#return (#deref (#call worker-0 ((input (#borrow owner)) (choose true)))))")
    return "\n".join(lines) + "\n"


def scoped_heavy_source():
    """Exercise nested scoped-loan fixed points across 64 checked functions."""
    lines = []
    for function in range(64):
        expression = "42u64"
        for _ in range(24):
            expression = f"(#borrow owner {expression})"
        lines.append(f"#fn worker-{function} () #u64 (#let owner #u64 42u64) "
                     f"(#return {expression})")
    lines.append("#fn main () #u64 (#return (#call worker-0 ()))")
    return "\n".join(lines) + "\n"


def thread_heavy_source():
    """Exercise task/worker lookup with forward-declared worker signatures."""
    lines = []
    for task in range(256):
        lines.append(f"(@#thread-spawn ((task Task-{task}) (worker worker-{task})))")
    for task in range(256):
        lines.append(f"#fn worker-{task} ((value #u64)) #u64 (#return value)")
    lines.append("#fn main () #u64 (#return 42u64)")
    return "\n".join(lines) + "\n"


def async_heavy_source():
    """Exercise shared declaration identities across 64 graph invocations."""
    lines = [
        "#enum Step ((StepStart #u64))",
        "#enum StepPoll ((StepPending Step) (StepReady #u64))",
        "#syntax StepAwait (#u64 Step StepPending StepReady step-poll)",
        "#fn step-poll ((task Step) (waker (#ref #u64))) StepPoll "
        "(#return (#match task (#case (StepStart value) (StepReady value))))",
    ]
    for function in range(64):
        lines.append(
            f"(@#async-fn ((protocol JobAwait-{function}) (waker #u64) (function "
            f"(#fn job-{function} ((seed #u64)) #u64 "
            f"(#let value #u64 (#await StepAwait (StepStart {function}u64))) "
            "(#return (#u64.+.wrap value seed))))))")
    lines.append(
        "#fn main () #u64 (#let waker #u64 0u64) "
        "(#let result Job-0-poll-result "
        "(#call job-0-poll ((task (#call job-0 ((seed 42u64)))) "
        "(waker (#borrow waker))))) "
        "(#forget waker) (#return (#match result "
        "(#case (job-0-ready value) value) "
        "(#case (job-0-pending task) (#block (#forget task) (#unreachable)))))")
    return "\n".join(lines) + "\n"


def async_pinned_heavy_source():
    """Exercise owner-inclusive cancellation across eight pinned dispatchers."""
    lines = [
        "#enum Step ((StepStart #u64))\n#linear Step",
        "#enum StepPoll ((StepPending Step) (StepReady #u64))",
        "#syntax StepAwait (#u64 Step StepPending StepReady step-poll)",
        "#fn step-poll ((task Step) (waker (#ref #u64))) StepPoll "
        "(#return (#match task (#case (StepStart value) (StepReady value))))",
    ]
    for function in range(8):
        lines.append(f"(@#async-fn-pinned ((protocol JobAwait-{function}) (waker #u64) "
                     f"(function (#fn job-{function} ((seed #u64)) #u64")
        for owner in range(8):
            lines.append(f"(#let owner-{owner} Step (StepStart seed))")
            lines.append(f"(#let value-{owner} #u64 (#await StepAwait (StepStart 0u64)))")
        for owner in range(8):
            lines.append(f"(#forget owner-{owner})")
        lines.append("(#return seed)))))")
    lines.append("#fn main () #u64 (#let waker #u64 0u64) "
                 "(#let-mut frame Job-0-frame (#call job-0 ((seed 42u64)))) "
                 "(#let result Job-0-poll-result (#call job-0-poll "
                 "((task (#pin-borrow-mut frame)) (waker (#borrow waker))))) "
                 "(#let answer #u64 (#match result (#case (job-0-ready value) value) "
                 "(#case (job-0-pending unexpected) (#block (#forget unexpected) (#unreachable))))) "
                 "(#forget frame) (#forget waker) (#return answer)")
    return "\n".join(lines) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path, nargs="?")
    parser.add_argument("--reference-heavy", action="store_true",
                        help="benchmark 64 functions with 24 reference aliases each")
    parser.add_argument("--scoped-heavy", action="store_true",
                        help="benchmark 64 functions with 24 nested scoped borrows each")
    parser.add_argument("--snapshot-heavy", action="store_true",
                        help="benchmark 64 functions with 24 lexical branch-result aliases each")
    parser.add_argument("--thread-heavy", action="store_true",
                        help="benchmark 256 tasks with forward-declared worker signatures")
    parser.add_argument("--async-heavy", action="store_true",
                        help="benchmark 64 async functions sharing a declaration environment")
    parser.add_argument("--async-pinned-heavy", action="store_true",
                        help="benchmark eight pinned functions with eight suspended owners each")
    parser.add_argument("--cold-generators", action="store_true",
                        help="force generation in a fresh directory for every synthetic-workload sample")
    parser.add_argument("--cfg", action="append", default=[],
                        help="pass a compile configuration to both compilers (repeatable)")
    parser.add_argument("--compiler", type=Path, default=Path("target/release/lim"))
    parser.add_argument("--baseline", type=Path)
    parser.add_argument("--repetitions", type=int, default=20)
    parser.add_argument("--compare-runtime", action="store_true",
                        help="compare exit status/stdout/stderr instead of identical binary bytes (no stdin)")
    args = parser.parse_args()
    if sum((args.source is not None, args.reference_heavy, args.scoped_heavy,
            args.snapshot_heavy, args.thread_heavy, args.async_heavy, args.async_pinned_heavy)) != 1:
        parser.error("provide a source file or exactly one heavy-workload flag")
    if args.cold_generators and args.source is not None:
        parser.error("--cold-generators requires a synthetic workload without imports")
    if args.repetitions < 1:
        parser.error("--repetitions must be positive")
    with tempfile.TemporaryDirectory(prefix="lim-compile-benchmark-") as directory:
        output = Path(directory) / "program"
        if args.reference_heavy:
            args.source = Path(directory) / "reference-heavy.lim"
            args.source.write_text(reference_heavy_source())
        if args.scoped_heavy:
            args.source = Path(directory) / "scoped-heavy.lim"
            args.source.write_text(scoped_heavy_source())
        if args.snapshot_heavy:
            args.source = Path(directory) / "snapshot-heavy.lim"
            args.source.write_text(snapshot_heavy_source())
        if args.thread_heavy:
            args.source = Path(directory) / "thread-heavy.lim"
            args.source.write_text(thread_heavy_source())
        if args.async_heavy:
            args.source = Path(directory) / "async-heavy.lim"
            args.source.write_text(async_heavy_source())
        if args.async_pinned_heavy:
            args.source = Path(directory) / "async-pinned-heavy.lim"
            args.source.write_text(async_pinned_heavy_source())
        baseline = None
        if args.baseline:
            baseline = measure(args.baseline, args.source, output, args.repetitions, args.compare_runtime, args.cfg, args.cold_generators)
            if args.reference_heavy or args.scoped_heavy or args.snapshot_heavy or args.thread_heavy or args.async_heavy or args.async_pinned_heavy:
                # Each synthetic workload needs an equally sized warm cache.
                # Compiler fingerprints otherwise leave both artifact sets in
                # one directory and bias whichever compiler runs second.
                isolated = Path(directory) / "current"
                isolated.mkdir()
                isolated_source = isolated / args.source.name
                isolated_source.write_text(args.source.read_text())
                args.source = isolated_source
        current = measure(args.compiler, args.source, output, args.repetitions, args.compare_runtime, args.cfg, args.cold_generators)
        if baseline:
            if args.compare_runtime and baseline[2] != current[2]:
                raise SystemExit("baseline and current runtime outcomes differ")
            if not args.compare_runtime and baseline[1] != current[1]:
                raise SystemExit("baseline and current executable bytes differ")
            print(f"speedup={baseline[0] / current[0]:.2f}x "
                  f"reduction={100 * (1 - current[0] / baseline[0]):.1f}% "
                  + ("runtime outcomes identical" if args.compare_runtime else "executable bytes identical"))


if __name__ == "__main__":
    main()
