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


def measure(compiler, source, output, repetitions):
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
    return statistics.median(samples), output.read_bytes()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("--compiler", type=Path, default=Path("target/release/lim"))
    parser.add_argument("--baseline", type=Path)
    parser.add_argument("--repetitions", type=int, default=20)
    args = parser.parse_args()
    if args.repetitions < 1:
        parser.error("--repetitions must be positive")
    with tempfile.TemporaryDirectory(prefix="lim-compile-benchmark-") as directory:
        output = Path(directory) / "program"
        baseline = None
        if args.baseline:
            baseline = measure(args.baseline, args.source, output, args.repetitions)
        current = measure(args.compiler, args.source, output, args.repetitions)
        if baseline:
            if baseline[1] != current[1]:
                raise SystemExit("baseline and current executable bytes differ")
            print(f"speedup={baseline[0] / current[0]:.2f}x "
                  f"reduction={100 * (1 - current[0] / baseline[0]):.1f}% "
                  "executable bytes identical")


if __name__ == "__main__":
    main()
