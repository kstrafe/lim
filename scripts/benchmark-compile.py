#!/usr/bin/env python3
"""Measure warm, end-to-end compilation including native linking.

Example:
  python3 scripts/benchmark-compile.py examples/async_fn.lim --baseline /tmp/lim-before

Each compiler gets separate warmups because compiler fingerprints invalidate
generator caches. Outputs go in a temporary directory, never over user binaries.
"""

import argparse
from pathlib import Path
import statistics
import subprocess
import tempfile
import time


def measure(compiler, source, output, repetitions, compare_runtime=False):
    command = [str(compiler.resolve()), str(source), "-o", str(output)]
    for _ in range(2):
        subprocess.run(command, check=True, stdout=subprocess.DEVNULL)
    samples = []
    for _ in range(repetitions):
        started = time.perf_counter_ns()
        subprocess.run(command, check=True, stdout=subprocess.DEVNULL)
        samples.append((time.perf_counter_ns() - started) / 1_000_000)
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
    lines = ["(#fn identity ((input (#ref u64))) (#ref u64) (#return input))"]
    for function in range(64):
        lines.append(f"(#fn worker-{function} ((input (#ref u64))) (#ref u64)")
        for binding in range(24):
            previous = "input" if binding == 0 else f"value-{binding - 1}"
            lines.append(f"  (#let value-{binding} (#ref u64) {previous})")
        lines.append("  (#return (#call identity (: input value-23))))")
    lines.append("(#fn main () u64 (#let owner u64 42u64) "
                 "(#return (#deref (#call worker-0 (: input (#borrow owner))))))")
    return "\n".join(lines) + "\n"


def snapshot_heavy_source():
    """Exercise nested branch-result snapshot lookup and lexical cleanup."""
    lines = []
    for function in range(64):
        lines.append(f"(#fn worker-{function} ((input (#ref u64)) (choose bool)) (#ref u64)")
        for binding in range(24):
            previous = "input" if binding == 0 else f"value-{binding - 1}"
            lines.append(f"  (#let value-{binding} (#ref u64) (#if choose "
                         f"(#block (#let left-{binding} (#ref u64) {previous}) left-{binding}) "
                         f"(#block (#let right-{binding} (#ref u64) {previous}) right-{binding})))")
        lines.append("  (#return value-23))")
    lines.append("(#fn main () u64 (#let owner u64 42u64) "
                 "(#return (#deref (#call worker-0 (: input (#borrow owner) : choose true)))))")
    return "\n".join(lines) + "\n"


def scoped_heavy_source():
    """Exercise nested scoped-loan fixed points across 64 checked functions."""
    lines = []
    for function in range(64):
        expression = "42u64"
        for _ in range(24):
            expression = f"(#borrow owner {expression})"
        lines.append(f"(#fn worker-{function} () u64 (#let owner u64 42u64) "
                     f"(#return {expression}))")
    lines.append("(#fn main () u64 (#return (#call worker-0 ())))")
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
    parser.add_argument("--compiler", type=Path, default=Path("target/release/lim"))
    parser.add_argument("--baseline", type=Path)
    parser.add_argument("--repetitions", type=int, default=20)
    parser.add_argument("--compare-runtime", action="store_true",
                        help="compare exit status/stdout/stderr instead of identical binary bytes (no stdin)")
    args = parser.parse_args()
    if sum((args.source is not None, args.reference_heavy, args.scoped_heavy,
            args.snapshot_heavy)) != 1:
        parser.error("provide a source file, --reference-heavy, --scoped-heavy, or --snapshot-heavy")
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
        baseline = None
        if args.baseline:
            baseline = measure(args.baseline, args.source, output, args.repetitions, args.compare_runtime)
        current = measure(args.compiler, args.source, output, args.repetitions, args.compare_runtime)
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
