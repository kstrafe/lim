#!/usr/bin/env python3
"""Compare native proof emission and checking under synthetic retention stress.

Run under ``scripts/limited-run.sh``. The generated export is synthetic protocol
stress data, not a genuine FLT proof or Lean producer benchmark.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import runpy
import signal
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parent.parent
RETENTION = ROOT / "scripts/benchmark-proof-retention.py"
MEMORY_BENCHMARK = ROOT / "scripts/benchmark-proof-memory.py"
REPORT_HELPERS = ROOT / "scripts/benchmark-proof-report.py"
CASE = "synthetic_native_retention"
TIMEOUT_SECONDS = 70
MAX_SOURCE_BYTES = 64 * 1024 * 1024
PROOF_TOTAL_BYTES = 1_073_741_824
BUDGET = {"work_per_phase": 200_000,
          "transformation_bytes_per_phase": 67_108_864,
          "transformation_bytes_total": PROOF_TOTAL_BYTES}


def validate_parameters(declarations, lets, unused, iterations):
    for option, value, low, high in (("declarations", declarations, 1, 500),
                                     ("lets", lets, 1, 16),
                                     ("unused-expressions", unused, 0, 190000),
                                     ("iterations", iterations, 1, 5)):
        if not low <= value <= high:
            raise ValueError(f"--{option} must be between {low} and {high}")
    if 21 + declarations * lets + unused > 200000:
        raise ValueError("generated source would exceed the expression table limit")


def generate_source(path, declarations=100, lets=4, unused=190000):
    validate_parameters(declarations, lets, unused, 1)
    generator = runpy.run_path(str(RETENTION))["generate_export"]
    generator(path, declarations, lets, unused)
    size = path.stat().st_size
    if size > MAX_SOURCE_BYTES:
        path.unlink(missing_ok=True)
        raise ValueError("generated source exceeds the 64 MiB limit")
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return size, digest.hexdigest()


def receipt_digest(path):
    helper = runpy.run_path(str(REPORT_HELPERS))["receipt_digest"]
    return helper(path)


def file_fingerprint(path):
    size = 0
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            size += len(block)
            digest.update(block)
    return size, digest.hexdigest()


def run_bounded(command, stdout=subprocess.PIPE):
    with subprocess.Popen(command, cwd=ROOT, stdout=stdout,
                          stderr=subprocess.DEVNULL, start_new_session=True) as proc:
        try:
            output, _ = proc.communicate(timeout=TIMEOUT_SECONDS)
        except subprocess.TimeoutExpired:
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            proc.communicate()
            raise
        return subprocess.CompletedProcess(command, proc.returncode, output)


def compiler_args(source, target, report, proof):
    return ["--check-lean-export", str(source), target,
            "--proof-work", str(BUDGET["work_per_phase"]),
            "--proof-phase-bytes", str(BUDGET["transformation_bytes_per_phase"]),
            "--proof-total-bytes", str(PROOF_TOTAL_BYTES),
            "--report", str(report), "--emit-proof", str(proof)]


def run_compiler(compilers, label, source, target, report, proof):
    return run_bounded([str(compilers[label]), *compiler_args(source, target, report, proof)])


def verify_preflight(compilers, source, target, directory):
    fingerprints = {}
    for label in ("before", "after"):
        report = Path(directory) / f"preflight-{label}.json"
        proof = Path(directory) / f"preflight-{label}.proof"
        result = run_compiler(compilers, label, source, target, report, proof)
        if result.returncode != 0:
            raise RuntimeError(f"{label} compiler failed emission preflight")
        fingerprints[label] = (receipt_digest(report), file_fingerprint(proof))
        if not all(item[0] for item in fingerprints[label]):
            raise RuntimeError(f"{label} compiler produced an empty report or proof")
    if fingerprints["before"] != fingerprints["after"]:
        raise RuntimeError("before/after report or emitted proof fingerprint differs")
    return fingerprints["before"]


def run_sample(label, compiler, sample_index, source, target, source_info,
               parameters, directory, expected):
    report = Path(directory) / f"sample-{sample_index}-{label}.json"
    proof = Path(directory) / f"sample-{sample_index}-{label}.proof"
    command = [sys.executable, str(MEMORY_BENCHMARK), "--worker", "--lim",
               str(compiler), "--case-name", CASE,
               "--argv-json", json.dumps(compiler_args(source, target, report, proof), separators=(",", ":")),
               "--input-bytes", str(source_info[0]),
               "--budget-json", json.dumps(BUDGET, separators=(",", ":"))]
    try:
        result = run_bounded(command)
        data = json.loads(result.stdout)
        if (not isinstance(data, dict) or result.returncode != 0 or
                data.get("case") != CASE or data.get("status") != "ok"):
            raise ValueError("worker status or exit code indicates failure")
        report_fp, proof_fp = receipt_digest(report), file_fingerprint(proof)
        if not report_fp[0] or not proof_fp[0] or (report_fp, proof_fp) != expected:
            raise ValueError("sample report or emitted proof fingerprint differs")
        data.update({"label": label, "sample": sample_index, "budget": dict(BUDGET),
                     "parameters": parameters, "source_bytes": source_info[0],
                     "source_sha256": source_info[1], "report_bytes": report_fp[0],
                     "report_sha256": report_fp[1], "proof_bytes": proof_fp[0],
                     "proof_sha256": proof_fp[1]})
        print(json.dumps(data, separators=(",", ":")), flush=True)
        return True
    except (OSError, ValueError, TypeError, json.JSONDecodeError,
            subprocess.TimeoutExpired):
        print(json.dumps({"case": CASE, "label": label, "sample": sample_index,
                          "status": "worker_error", "wall_ms": None,
                          "peak_rss_kib": None, "budget": dict(BUDGET),
                          "parameters": parameters, "source_bytes": source_info[0],
                          "source_sha256": source_info[1]}, separators=(",", ":")), flush=True)
        return False


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--before", required=True)
    parser.add_argument("--after", required=True)
    parser.add_argument("--declarations", type=int, default=100)
    parser.add_argument("--lets", type=int, default=4)
    parser.add_argument("--unused-expressions", type=int, default=190000)
    parser.add_argument("--iterations", type=int, default=3)
    args = parser.parse_args(argv)
    try:
        validate_parameters(args.declarations, args.lets, args.unused_expressions, args.iterations)
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

    params = {"declarations": args.declarations, "lets": args.lets,
              "unused_expressions": args.unused_expressions, "iterations": args.iterations}
    target = f"$lean:s5:Audits{len(str(args.declarations - 1)) + len('opaquePayload')}:{'opaquePayload' + str(args.declarations - 1)}"
    failures = 0
    with tempfile.TemporaryDirectory(prefix="lim-native-retention-") as directory:
        source = Path(directory) / "synthetic.ndjson"
        try:
            source_info = generate_source(source, args.declarations, args.lets, args.unused_expressions)
            expected = verify_preflight(compilers, source, target, directory)
        except (OSError, ValueError, RuntimeError, subprocess.TimeoutExpired) as exc:
            print(f"benchmark-proof-native-retention: {exc}", file=sys.stderr)
            return 1
        for sample in range(1, args.iterations + 1):
            order = ("before", "after") if sample % 2 else ("after", "before")
            for label in order:
                if not run_sample(label, compilers[label], sample, source, target,
                                  source_info, params, directory, expected):
                    failures += 1
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
