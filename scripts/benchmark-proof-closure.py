#!/usr/bin/env python3
"""Bounded before/after benchmark for checked-index proof closure.

Run under ``scripts/limited-run.sh``; this script does not install its own
resource guard. Synthetic declarations extend the hash-pinned identity export.
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
FIXTURE = ROOT / "tests/fixtures/lean_export/identity.ndjson"
FIXTURE_SHA256 = "ad05e4153b542ea6dcd88e4a92d0a8e42ad2d757bdbc19552e3229a979c974ec"
MEMORY_BENCHMARK = ROOT / "scripts/benchmark-proof-memory.py"
REPORT_HELPERS = ROOT / "scripts/benchmark-proof-report.py"
CASE = "synthetic_closure_frontier"
TIMEOUT_SECONDS = 70
MAX_SOURCE_BYTES = 64 * 1024 * 1024
MAX_NAME_PAYLOAD_BYTES = 16 * 1024 * 1024
FIXTURE_NAME_PAYLOAD_BYTES = 126
PROOF_TOTAL_BYTES = 4_294_967_296
BUDGET = {"work_per_phase": 200_000,
          "transformation_bytes_per_phase": 67_108_864,
          "transformation_bytes_total": PROOF_TOTAL_BYTES}


def validate_parameters(declarations, width, iterations):
    if not 1 <= declarations <= 2500:
        raise ValueError("--declarations must be between 1 and 2500")
    if not 1 <= width <= 32:
        raise ValueError("--width must be between 1 and 32")
    if not 1 <= iterations <= 5:
        raise ValueError("--iterations must be between 1 and 5")
    # A component has a 64-byte minimum; its full canonical key and display
    # spelling contribute 2*64 + 22 + digits(64) bytes per name.
    if FIXTURE_NAME_PAYLOAD_BYTES + declarations * (2 * 64 + 22 + len("64")) > MAX_NAME_PAYLOAD_BYTES:
        raise ValueError("declarations project more than 16 MiB of name payload")


def _line(stream, digest, count, obj):
    encoded = (json.dumps(obj, separators=(",", ":")) + "\n").encode("ascii")
    count += len(encoded)
    if count > MAX_SOURCE_BYTES:
        raise ValueError("generated source exceeds the 64 MiB limit")
    stream.write(encoded)
    digest.update(encoded)
    return count


def generate_export(path, declarations=1000, width=16):
    validate_parameters(declarations, width, 1)
    fixture_bytes = FIXTURE.read_bytes()
    if hashlib.sha256(fixture_bytes).hexdigest() != FIXTURE_SHA256:
        raise ValueError("pinned identity fixture SHA256 does not match")
    digest = hashlib.sha256()
    size = 0
    with path.open("wb") as stream:
        if len(fixture_bytes) > MAX_SOURCE_BYTES:
            raise ValueError("fixture exceeds the 64 MiB source limit")
        stream.write(fixture_bytes)
        digest.update(fixture_bytes)
        size = len(fixture_bytes)
        size = _line(stream, digest, size, {"const": {"name": 3, "us": []}, "ie": 20})
        next_name = 5
        next_expr = 21
        const_ids = []
        for index in range(declarations):
            component = f"Closure{index:04d}".ljust(64, "x")
            name_id = next_name
            next_name += 1
            size = _line(stream, digest, size,
                         {"str": {"pre": 1, "str": component}, "in": name_id})

            prior_consts = const_ids[max(0, index - width):index]
            values = prior_consts if prior_consts else [20]
            body = 19
            for value_expr in values:
                let_id = next_expr
                next_expr += 1
                size = _line(stream, digest, size,
                             {"letE": {"name": 0, "type": 12, "value": value_expr,
                                       "body": body, "nondep": True}, "ie": let_id})
                body = let_id
            theorem = {"thm": {"name": name_id, "levelParams": [], "type": 12,
                               "value": body, "all": [name_id]}}
            size = _line(stream, digest, size, theorem)
            const_id = next_expr
            next_expr += 1
            size = _line(stream, digest, size,
                         {"const": {"name": name_id, "us": []}, "ie": const_id})
            const_ids.append(const_id)
    return size, digest.hexdigest()


def receipt_digest(path):
    # Reuse the report benchmark's byte count plus full SHA-256 implementation.
    helper = runpy.run_path(str(REPORT_HELPERS))["receipt_digest"]
    return helper(path)


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


def compiler_args(source, target, report=None):
    args = ["--check-lean-export", str(source), target,
            "--proof-total-bytes", str(PROOF_TOTAL_BYTES)]
    if report is not None:
        args.extend(["--report", str(report)])
    return args


def verify_receipts(compilers, source, target, directory):
    fingerprints = {}
    for label in ("before", "after"):
        report = Path(directory) / f"preflight-{label}.json"
        result = run_bounded([str(compilers[label]), *compiler_args(source, target, report)])
        if result.returncode != 0:
            raise RuntimeError(f"{label} compiler failed receipt preflight")
        fingerprints[label] = receipt_digest(report)
        if not fingerprints[label][0]:
            raise RuntimeError(f"{label} compiler produced an empty receipt")
    if fingerprints["before"] != fingerprints["after"]:
        raise RuntimeError("before/after full receipt byte count or SHA-256 differs")
    return fingerprints["before"]


def run_sample(label, compiler, sample_index, source, target, source_bytes,
               source_sha256, declarations, width):
    parameters = {"declarations": declarations, "width": width}
    report = source.parent / f"report-{sample_index}-{label}.json"
    command = [sys.executable, str(MEMORY_BENCHMARK), "--worker", "--lim",
               str(compiler), "--case-name", CASE,
               "--argv-json", json.dumps(compiler_args(source, target, report), separators=(",", ":")),
               "--input-bytes", str(source_bytes),
               "--budget-json", json.dumps(BUDGET, separators=(",", ":"))]
    try:
        result = run_bounded(command)
        data = json.loads(result.stdout)
        if not isinstance(data, dict) or data.get("case") != CASE or data.get("status") != "ok" or result.returncode != 0:
            raise ValueError("worker status or exit code indicates failure")
        fingerprint = receipt_digest(report)
        if not fingerprint[0]:
            raise ValueError("compiler produced an empty report")
        data.update({"label": label, "sample_index": sample_index,
                     "parameters": parameters, "budget": dict(BUDGET),
                     "source_bytes": source_bytes, "source_sha256": source_sha256,
                     "report_bytes": fingerprint[0], "report_sha256": fingerprint[1]})
        print(json.dumps(data, separators=(",", ":")), flush=True)
        return True, fingerprint
    except (OSError, ValueError, TypeError, json.JSONDecodeError, subprocess.TimeoutExpired):
        data = {"case": CASE, "label": label, "sample_index": sample_index,
                "parameters": parameters, "budget": dict(BUDGET),
                "source_bytes": source_bytes, "source_sha256": source_sha256,
                "status": "worker_error", "wall_ms": None, "cpu_ms": None,
                "peak_rss_kib": None}
        print(json.dumps(data, separators=(",", ":")), flush=True)
        return False, None


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--before", required=True)
    parser.add_argument("--after", required=True)
    parser.add_argument("--declarations", type=int, default=1000)
    parser.add_argument("--width", type=int, default=16)
    parser.add_argument("--iterations", type=int, default=3)
    args = parser.parse_args(argv)
    try:
        validate_parameters(args.declarations, args.width, args.iterations)
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
    target_name = f"Closure{args.declarations - 1:04d}".ljust(64, "x")
    target = f"$lean:s5:Audits{len(target_name)}:{target_name}"
    failures = 0
    with tempfile.TemporaryDirectory(prefix="lim-proof-closure-") as directory:
        source = Path(directory) / "synthetic.ndjson"
        try:
            source_bytes, source_sha256 = generate_export(source, args.declarations, args.width)
            receipt_bytes, receipt_sha256 = verify_receipts(compilers, source, target, directory)
        except (OSError, ValueError, RuntimeError, subprocess.TimeoutExpired) as exc:
            print(f"benchmark-proof-closure: {exc}", file=sys.stderr)
            return 1
        print(json.dumps({"case": CASE, "stage": "receipt_preflight", "status": "ok",
                          "parameters": {"declarations": args.declarations, "width": args.width,
                                         "iterations": args.iterations},
                          "budget": dict(BUDGET), "source_bytes": source_bytes,
                          "source_sha256": source_sha256, "report_bytes": receipt_bytes,
                          "report_sha256": receipt_sha256}, separators=(",", ":")), flush=True)
        for sample_index in range(1, args.iterations + 1):
            order = ("before", "after") if sample_index % 2 else ("after", "before")
            for label in order:
                ok, fingerprint = run_sample(label, compilers[label], sample_index,
                                             source, target, source_bytes, source_sha256,
                                             args.declarations, args.width)
                if not ok:
                    failures += 1
                elif fingerprint != (receipt_bytes, receipt_sha256):
                    print("benchmark-proof-closure: sample receipt differs from preflight", file=sys.stderr)
                    failures += 1
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
