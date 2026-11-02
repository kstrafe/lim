#!/usr/bin/env python3
"""Compare checked type-signature reuse under scripts/limited-run.sh.

Use compilers built with the same profile. Generates 200 reflexivity proofs
over a function with 20 explicit parameters; this is a focused workload, not
a representative whole-program benchmark. No Lean toolchain is required.
"""
import argparse
import json
from pathlib import Path
import resource
import statistics
import subprocess
import tempfile
import time


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--before", type=Path, required=True)
    parser.add_argument("--after", type=Path, required=True)
    parser.add_argument("--iterations", type=int, default=25)
    args = parser.parse_args()
    if not 1 <= args.iterations <= 1000:
        parser.error("iterations must be between 1 and 1000")
    executables = [str(path.resolve(strict=True)) for path in [args.before, args.after]]
    parameters = " ".join(f"(x{i} #pt-nat)" for i in range(20))
    ty = f"(#pt-pi ({parameters}) #pt-nat)"
    source = f"(#math-definition choose-first () {ty} (#pt-lambda ({parameters}) x0))\n"
    for index in range(200):
        source += f"""(#theorem signature-{index}
  (#universes) (#parameters)
  (#statement (#pt-eq {ty} (#pt-use choose-first ()) (#pt-use choose-first ())))
  (#proof (#pt-refl {ty} (#pt-use choose-first ()))))
"""
    wall_samples = [[], []]
    cpu_samples = [[], []]
    with tempfile.TemporaryDirectory(prefix="lim-signature-benchmark-") as directory:
        path = Path(directory) / "proofs.lim"
        path.write_text(source)
        for iteration in range(args.iterations + 1):
            for index in [0, 1] if iteration % 2 == 0 else [1, 0]:
                before = resource.getrusage(resource.RUSAGE_CHILDREN)
                start = time.perf_counter_ns()
                result = subprocess.run(
                    [executables[index], "--check-theorem", str(path), "signature-199"],
                    capture_output=True, timeout=30, check=False,
                )
                wall_ms = (time.perf_counter_ns() - start) / 1e6
                after = resource.getrusage(resource.RUSAGE_CHILDREN)
                if result.returncode:
                    raise RuntimeError(result.stderr.decode(errors="replace"))
                if result.stdout.decode().strip() != "checked theorem signature-199":
                    raise RuntimeError("benchmark target has an unexpected foundation audit")
                if iteration:
                    wall_samples[index].append(wall_ms)
                    cpu_samples[index].append(1000 * (
                        after.ru_utime + after.ru_stime - before.ru_utime - before.ru_stime
                    ))
    medians = list(map(statistics.median, wall_samples))
    means = list(map(statistics.mean, cpu_samples))
    print(json.dumps({
        "source_bytes": len(source.encode()), "theorems": 200, "parameters": 20,
        "samples_per_compiler": args.iterations,
        "wall_median_ms": {"before": medians[0], "after": medians[1]},
        "cpu_mean_ms": {"before": means[0], "after": means[1]},
        "wall_reduction_percent": 100 * (1 - medians[1] / medians[0]),
        "cpu_reduction_percent": 100 * (1 - means[1] / means[0]),
    }, indent=2))


if __name__ == "__main__":
    main()
