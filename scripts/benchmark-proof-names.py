#!/usr/bin/env python3
"""Compare raw proof name-table retention with synthetic unused names.

Run the main process under the existing 2 GiB/200% CPU resource guard::

    bash scripts/limited-run.sh python3 scripts/benchmark-proof-names.py \
        --before /path/to/before/lim --after /path/to/after/lim

This is synthetic protocol stress data, not a real new proof corpus. The
pinned identity proof is followed only by primitive name records. Checking
the existing theorem still reads through EOF. Complete report fingerprints
must match before timed samples start. Each sample uses a fresh
benchmark-proof-memory.py worker within the main process's external guard.
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
FIXTURE = ROOT / "tests/fixtures/lean_export/identity.ndjson"
FIXTURE_SHA256 = "ad05e4153b542ea6dcd88e4a92d0a8e42ad2d757bdbc19552e3229a979c974ec"
MEMORY_BENCHMARK = ROOT / "scripts/benchmark-proof-memory.py"
TARGET = "Audit.identity.theorem"
CASE = "synthetic_unused_names"
TIMEOUT_SECONDS = 60
HASH_CHUNK_BYTES = 64 * 1024
MAX_SOURCE_BYTES = 64 * 1024 * 1024
MAX_NAME_PAYLOAD_BYTES = 16 * 1024 * 1024
# The pinned fixture's four names contribute canonical key + display bytes.
FIXTURE_NAME_PAYLOAD_BYTES = 126
BUDGET = {
    "work_per_phase": 200_000,
    "transformation_bytes_per_phase": 64 * 1024 * 1024,
    "transformation_bytes_total": 256 * 1024 * 1024,
}


def projected_name_payload(names, name_bytes):
    # Audit has key "$lean:s5:Audit" (14 bytes) and display "Audit" (5 bytes).
    # Each child adds "s{length}:" to its key and "." to its display.
    per_name = 2 * name_bytes + 22 + len(str(name_bytes))
    return FIXTURE_NAME_PAYLOAD_BYTES + names * per_name


def validate_names(names, name_bytes):
    if not 1 <= names <= 50_000:
        raise ValueError("--names must be between 1 and 50000")
    if not 1 <= name_bytes <= 1024:
        raise ValueError("--name-bytes must be between 1 and 1024")
    if len(f"name{names - 1}") > name_bytes:
        raise ValueError("--name-bytes must fit the complete name{index} prefix")
    if projected_name_payload(names, name_bytes) > MAX_NAME_PAYLOAD_BYTES:
        raise ValueError("--names and --name-bytes project more than 16 MiB of name payload")


def parse_args(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--before", required=True, help="before-version lim executable")
    parser.add_argument("--after", required=True, help="after-version lim executable")
    parser.add_argument("--names", type=int, default=12_000,
                        help="unused names (1..50000; default: 12000)")
    parser.add_argument("--name-bytes", type=int, default=512,
                        help="fixed component byte length (1..1024; default: 512)")
    parser.add_argument("--iterations", type=int, default=5,
                        help="fresh samples per compiler (1..25; default: 5)")
    args = parser.parse_args(argv)
    if not 1 <= args.iterations <= 25:
        parser.error("--iterations must be between 1 and 25")
    try:
        validate_names(args.names, args.name_bytes)
    except ValueError as exc:
        parser.error(str(exc))
    return parser, args


def generate_export(path, names, name_bytes):
    validate_names(names, name_bytes)
    fixture_bytes = FIXTURE.read_bytes()
    if hashlib.sha256(fixture_bytes).hexdigest() != FIXTURE_SHA256:
        raise ValueError("pinned identity fixture SHA256 does not match")
    digest = hashlib.sha256()
    size = 0
    with path.open("wb") as stream:
        def write(data):
            nonlocal size
            if size + len(data) > MAX_SOURCE_BYTES:
                raise ValueError("generated source exceeds the 64 MiB limit")
            stream.write(data)
            digest.update(data)
            size += len(data)

        write(fixture_bytes)
        for index in range(names):
            prefix = f"name{index}"
            component = prefix + "x" * (name_bytes - len(prefix))
            row = {"in": 5 + index, "str": {"pre": 1, "str": component}}
            write((json.dumps(row, separators=(",", ":")) + "\n").encode("ascii"))
    return size, digest.hexdigest()


def file_digest(path):
    digest = hashlib.sha256()
    size = 0
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(HASH_CHUNK_BYTES), b""):
            digest.update(chunk)
            size += len(chunk)
    return size, digest.hexdigest()


def compiler_args(export_path, report_path=None):
    # These pin the unchanged default budgets for both binaries and preflight.
    args = ["--check-lean-export", str(export_path), TARGET,
            "--proof-work", str(BUDGET["work_per_phase"]),
            "--proof-phase-bytes", str(BUDGET["transformation_bytes_per_phase"]),
            "--proof-total-bytes", str(BUDGET["transformation_bytes_total"])]
    if report_path is not None:
        args.extend(["--report", str(report_path)])
    return args


def run_bounded(command, stdout=subprocess.DEVNULL):
    with subprocess.Popen(command, cwd=ROOT, stdout=stdout,
                          stderr=subprocess.DEVNULL,
                          start_new_session=True) as process:
        try:
            output, _ = process.communicate(timeout=TIMEOUT_SECONDS)
        except subprocess.TimeoutExpired:
            # A worker may still have a compiler child when its parent times out.
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            process.communicate()
            raise
        return subprocess.CompletedProcess(command, process.returncode, output)


def verify_receipts(compilers, export_path, directory):
    fingerprints = {}
    for label in ("before", "after"):
        report_path = Path(directory) / f"receipt-{label}.json"
        try:
            result = run_bounded([str(compilers[label]),
                                  *compiler_args(export_path, report_path)])
            if result.returncode != 0:
                raise RuntimeError(f"{label} compiler failed receipt preflight")
            fingerprints[label] = file_digest(report_path)
            if fingerprints[label][0] == 0:
                raise RuntimeError(f"{label} compiler produced an empty receipt")
        except (OSError, subprocess.TimeoutExpired) as exc:
            raise RuntimeError(f"{label} receipt preflight failed or exceeded 60s") from exc
    if fingerprints["before"] != fingerprints["after"]:
        raise RuntimeError("before/after receipt byte count or SHA-256 differs")
    return fingerprints["before"]


def run_sample(label, compiler, sample_index, export_path, source_bytes,
               source_sha256, parameters):
    command = [sys.executable, str(MEMORY_BENCHMARK), "--worker",
               "--lim", str(compiler), "--case-name", CASE,
               "--argv-json", json.dumps(compiler_args(export_path), separators=(",", ":")),
               "--input-bytes", str(source_bytes),
               "--budget-json", json.dumps(BUDGET, separators=(",", ":"))]
    try:
        result = run_bounded(command, stdout=subprocess.PIPE)
        data = json.loads(result.stdout)
        if not isinstance(data, dict):
            raise ValueError("worker output is not a JSON object")
        ok = result.returncode == 0 and data.get("status") == "ok"
    except (OSError, ValueError, subprocess.TimeoutExpired):
        ok = False
        data = {"case": CASE, "input_bytes": source_bytes, "budget": dict(BUDGET),
                "status": "worker_error", "wall_ms": None, "cpu_ms": None,
                "peak_rss_kib": None,
                "diagnostic": "worker failed, exceeded 60s, or returned invalid data"}
    data.update({"label": label, "sample_index": sample_index, "synthetic": True,
                 "source_bytes": source_bytes, "source_sha256": source_sha256,
                 "parameters": parameters})
    print(json.dumps(data, separators=(",", ":")), flush=True)
    return ok


def main(argv=None):
    parser, args = parse_args(argv)
    compilers = {}
    for label in ("before", "after"):
        try:
            executable = Path(getattr(args, label)).resolve(strict=True)
        except (OSError, RuntimeError) as exc:
            parser.error(f"--{label}: {exc}")
        if not executable.is_file() or not os.access(executable, os.X_OK):
            parser.error(f"--{label} must name an executable file")
        compilers[label] = executable

    parameters = {"names": args.names, "name_bytes": args.name_bytes,
                  "iterations": args.iterations,
                  "projected_name_payload_bytes": projected_name_payload(
                      args.names, args.name_bytes)}
    failures = 0
    with tempfile.TemporaryDirectory(prefix="lim-proof-names-") as directory:
        export_path = Path(directory) / "synthetic.ndjson"
        try:
            source_bytes, source_sha256 = generate_export(
                export_path, args.names, args.name_bytes)
            receipt_bytes, receipt_sha256 = verify_receipts(
                compilers, export_path, directory)
        except (OSError, ValueError, RuntimeError) as exc:
            print(f"benchmark-proof-names: {exc}", file=sys.stderr)
            return 1
        print(json.dumps({"case": CASE, "stage": "receipt_preflight", "status": "ok",
                          "synthetic": True, "source_bytes": source_bytes,
                          "source_sha256": source_sha256, "parameters": parameters,
                          "budget": dict(BUDGET), "receipt_bytes": receipt_bytes,
                          "receipt_sha256": receipt_sha256},
                         separators=(",", ":")), flush=True)
        for sample_index in range(1, args.iterations + 1):
            order = ("before", "after") if sample_index % 2 else ("after", "before")
            for label in order:
                if not run_sample(label, compilers[label], sample_index, export_path,
                                  source_bytes, source_sha256, parameters):
                    failures += 1
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
