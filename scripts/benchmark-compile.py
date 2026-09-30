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


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("--compiler", type=Path, default=Path("target/release/lim"))
    parser.add_argument("--baseline", type=Path)
    parser.add_argument("--repetitions", type=int, default=20)
    parser.add_argument("--compare-runtime", action="store_true",
                        help="compare exit status/stdout/stderr instead of identical binary bytes (no stdin)")
    args = parser.parse_args()
    if args.repetitions < 1:
        parser.error("--repetitions must be positive")
    with tempfile.TemporaryDirectory(prefix="lim-compile-benchmark-") as directory:
        output = Path(directory) / "program"
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
