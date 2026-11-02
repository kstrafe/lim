#!/usr/bin/env python3
"""Compare theorem checking with independent synthetic proof declarations.

The workload measures bounded identity proofs with nested typed lets. It is
checker scheduling stress, not an FLT proof or a Lean producer benchmark.
Run under scripts/limited-run.sh; each sample uses a fresh worker process.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parent.parent
MEMORY_BENCHMARK = ROOT / "scripts/benchmark-proof-memory.py"
CASE = "synthetic_proof_schedule"
TIMEOUT_SECONDS = 70
MAX_SOURCE_BYTES = 8 * 1024 * 1024
CORE_DEPTH = 96
PROOF_TOTAL_BYTES = 1024 * 1024 * 1024
BUDGET = {"work_per_phase": 200_000,
          "transformation_bytes_per_phase": 64 * 1024 * 1024,
          "transformation_bytes_total": PROOF_TOTAL_BYTES}


def validate_parameters(declarations, lets, iterations):
    for option, value, low, high in (("declarations", declarations, 1, 3000),
                                     ("lets", lets, 1, 32),
                                     ("iterations", iterations, 1, 5)):
        if not low <= value <= high:
            raise ValueError(f"--{option} must be between {low} and {high}")
    if lets + 1 > CORE_DEPTH:
        raise ValueError("generated proof exceeds Core depth 96")


def proof_body(lets):
    body = "(#pt-refl #pt-nat #pt-zero)"
    for index in reversed(range(lets)):
        body = (f"(#pt-let (#parameter scratch-{index} #pt-nat) "
                f"#pt-zero {body})")
    return body


def generate_source(path, declarations=3000, lets=16):
    validate_parameters(declarations, lets, 1)
    path = Path(path)
    digest = hashlib.sha256()
    size = 0
    try:
        with path.open("wb") as stream:
            for index in range(declarations):
                row = (f"(#theorem theorem-{index} (#universes) (#parameters) "
                       "(#statement (#pt-eq #pt-nat #pt-zero #pt-zero)) "
                       f"(#proof {proof_body(lets)}))\n").encode("utf-8")
                if size + len(row) > MAX_SOURCE_BYTES:
                    raise ValueError("generated source exceeds the 8 MiB limit")
                stream.write(row)
                digest.update(row)
                size += len(row)
    except BaseException:
        path.unlink(missing_ok=True)
        raise
    return size, digest.hexdigest()


def run_bounded(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE):
    with subprocess.Popen(command, cwd=ROOT, stdout=stdout, stderr=stderr,
                          start_new_session=True) as proc:
        try:
            output, error = proc.communicate(timeout=TIMEOUT_SECONDS)
        except subprocess.TimeoutExpired:
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            proc.communicate()
            raise
        return subprocess.CompletedProcess(command, proc.returncode, output, error)


def compiler_args(source, target):
    return ["--check-theorem", str(source), target,
            "--proof-work", str(BUDGET["work_per_phase"]),
            "--proof-phase-bytes", str(BUDGET["transformation_bytes_per_phase"]),
            "--proof-total-bytes", str(PROOF_TOTAL_BYTES)]


def verify_preflight(compilers, source, declarations):
    target = f"theorem-{declarations - 1}"
    expected_stdout = (
        f"checked theorem {target}\n"
        f"proof budget: work={BUDGET['work_per_phase']} "
        f"phase-bytes={BUDGET['transformation_bytes_per_phase']} "
        f"total-bytes={BUDGET['transformation_bytes_total']}\n"
    ).encode("utf-8")
    for label in ("before", "after"):
        result = run_bounded([str(compilers[label]), *compiler_args(source, target)])
        if result.returncode != 0:
            raise RuntimeError(f"{label} compiler failed theorem-check preflight")
        if result.stdout != expected_stdout or result.stderr:
            raise RuntimeError(f"{label} compiler returned unexpected theorem-check output")
    return target


def run_sample(label, compiler, sample_index, source, target, source_info,
               parameters):
    command = [sys.executable, str(MEMORY_BENCHMARK), "--worker", "--lim",
               str(compiler), "--case-name", CASE,
               "--argv-json", json.dumps(compiler_args(source, target), separators=(",", ":")),
               "--input-bytes", str(source_info[0]),
               "--budget-json", json.dumps(BUDGET, separators=(",", ":"))]
    try:
        result = run_bounded(command)
        data = json.loads(result.stdout)
        if (result.returncode != 0 or not isinstance(data, dict) or
                data.get("case") != CASE or data.get("status") != "ok"):
            raise ValueError("worker status or exit code indicates failure")
        data.update({"label": label, "sample": sample_index,
                     "exitcode": result.returncode,
                     "parameters": parameters, "source_bytes": source_info[0],
                     "source_sha256": source_info[1], "budget": dict(BUDGET)})
        print(json.dumps(data, separators=(",", ":")), flush=True)
        return True
    except (OSError, ValueError, TypeError, json.JSONDecodeError,
            subprocess.TimeoutExpired):
        print(json.dumps({"case": CASE, "label": label, "sample": sample_index,
                          "status": "worker_error", "exitcode": None, "wall_ms": None,
                          "cpu_ms": None, "peak_rss_kib": None,
                          "parameters": parameters, "source_bytes": source_info[0],
                          "source_sha256": source_info[1], "budget": dict(BUDGET)},
                         separators=(",", ":")), flush=True)
        return False


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--before", required=True)
    parser.add_argument("--after", required=True)
    parser.add_argument("--declarations", type=int, default=3000)
    parser.add_argument("--lets", type=int, default=16)
    parser.add_argument("--iterations", type=int, default=3)
    args = parser.parse_args(argv)
    try:
        validate_parameters(args.declarations, args.lets, args.iterations)
    except ValueError as exc:
        parser.error(str(exc))
    compilers = {}
    for label in ("before", "after"):
        try:
            executable = Path(getattr(args, label)).resolve(strict=True)
        except (OSError, RuntimeError) as exc:
            parser.error(f"--{label}: {exc}")
        if not executable.is_file() or not os.access(executable, os.X_OK):
            parser.error(f"--{label} must name an executable file")
        compilers[label] = executable
    params = {"declarations": args.declarations, "lets": args.lets}
    failures = 0
    with tempfile.TemporaryDirectory(prefix="lim-proof-schedule-") as directory:
        source = Path(directory) / "synthetic.lim"
        try:
            source_info = generate_source(source, args.declarations, args.lets)
            target = verify_preflight(compilers, source, args.declarations)
        except (OSError, ValueError, RuntimeError, subprocess.TimeoutExpired) as exc:
            print(f"benchmark-proof-schedule: {exc}", file=sys.stderr)
            return 1
        for sample in range(1, args.iterations + 1):
            order = ("before", "after") if sample % 2 else ("after", "before")
            for label in order:
                if not run_sample(label, compilers[label], sample, source, target,
                                  source_info, params):
                    failures += 1
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
