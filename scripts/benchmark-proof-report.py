#!/usr/bin/env python3
"""Compare report serialization for a synthetic Lean export.

Run under ``scripts/limited-run.sh`` to keep the complete benchmark and its
workers within the resource guard. For example::

    scripts/limited-run.sh python3 scripts/benchmark-proof-report.py \
        --before /path/to/before/lim --after /path/to/after/lim

The generated input is synthetic protocol stress data, not a Lean producer or
an FLT proof. Each sample uses a fresh worker to measure compiler child RSS.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parent.parent
RETENTION_SCRIPT = ROOT / "scripts/benchmark-proof-retention.py"
MEMORY_BENCHMARK = ROOT / "scripts/benchmark-proof-memory.py"
PARENT_TIMEOUT_SECONDS = 70
MAX_SOURCE_BYTES = 64 * 1024 * 1024
PROOF_TOTAL_BYTES = 1_073_741_824
BUDGET = {
    "work_per_phase": 200_000,
    "transformation_bytes_per_phase": 67_108_864,
    "transformation_bytes_total": PROOF_TOTAL_BYTES,
}


def generate_source(path, declarations, name_bytes):
    generator = runpy.run_path(str(RETENTION_SCRIPT))["generate_export"]
    generator(path, declarations, lets=1)
    temporary = path.with_suffix(".rewritten")
    digest = hashlib.sha256()
    size = 0
    with path.open("rb") as source, temporary.open("wb") as output:
        for raw_line in source:
            line = raw_line
            if len(raw_line) > 64 * 1024:
                raise ValueError("generated protocol row exceeds bounded line size")
            try:
                row = json.loads(raw_line)
            except (UnicodeDecodeError, json.JSONDecodeError) as exc:
                raise ValueError("generated protocol contains an invalid row") from exc
            if (isinstance(row, dict) and set(row) == {"in", "str"}
                    and isinstance(row.get("in"), int)
                    and isinstance(row.get("str"), dict)
                    and set(row["str"]) == {"pre", "str"}
                    and isinstance(row["str"].get("str"), str)
                    and row["str"]["str"].startswith("opaquePayload")):
                index_text = row["str"]["str"][len("opaquePayload"):]
                if index_text.isdecimal():
                    index = int(index_text)
                    # Keep names deterministic and distinct while honoring the
                    # requested byte length (including the decimal suffix).
                    suffix = str(index).encode("ascii")
                    if len(suffix) > name_bytes:
                        raise ValueError("name byte length is too short for index")
                    row["str"]["str"] = (b"n" * (name_bytes - len(suffix)) + suffix).decode("ascii")
                    line = (json.dumps(row, separators=(",", ":")) + "\n").encode("ascii")
            size += len(line)
            if size > MAX_SOURCE_BYTES:
                raise ValueError("generated source exceeds 64 MiB limit")
            digest.update(line)
            output.write(line)
    temporary.replace(path)
    return size, digest.hexdigest()


def receipt_digest(path):
    digest = hashlib.sha256()
    size = 0
    with path.open("rb") as stream:
        while True:
            chunk = stream.read(64 * 1024)
            if not chunk:
                break
            size += len(chunk)
            digest.update(chunk)
    return size, digest.hexdigest()


def run_sample(label, compiler, sample_index, source, target, source_bytes,
               source_sha256, report_path, declarations, name_bytes):
    budget = dict(BUDGET)
    compiler_args = [
        "--check-lean-export", str(source), target,
        "--proof-total-bytes", str(PROOF_TOTAL_BYTES),
        "--report", str(report_path),
    ]
    command = [
        sys.executable, str(MEMORY_BENCHMARK), "--worker", "--case-name",
        "synthetic_report_serialization", "--lim", str(compiler),
        "--argv-json", json.dumps(compiler_args, separators=(",", ":")),
        "--input-bytes", str(source_bytes),
        "--budget-json", json.dumps(budget, separators=(",", ":")),
    ]
    worker_data = None
    try:
        result = subprocess.run(command, cwd=ROOT, stdout=subprocess.PIPE,
                                stderr=subprocess.DEVNULL,
                                timeout=PARENT_TIMEOUT_SECONDS, check=False,
                                text=True)
        decoded = json.loads(result.stdout)
        if isinstance(decoded, dict):
            worker_data = decoded
    except (subprocess.TimeoutExpired, json.JSONDecodeError, OSError):
        result = None
    ok = result is not None and result.returncode == 0 and worker_data is not None and worker_data.get("status") == "ok"
    if worker_data is None:
        worker_data = {
            "case": "synthetic_report_serialization", "input_bytes": source_bytes,
            "budget": budget, "status": "worker_error", "wall_ms": None,
            "cpu_ms": None, "peak_rss_kib": None,
            "diagnostic": "worker failed, timed out, or returned invalid data",
        }
    record = dict(worker_data)
    record.update({"label": label, "sample_index": sample_index,
                   "source_bytes": source_bytes, "source_sha256": source_sha256,
                   "parameters": {"declarations": declarations,
                                  "name_bytes": name_bytes}})
    if ok:
        try:
            report_bytes, report_sha256 = receipt_digest(report_path)
            record["report_bytes"] = report_bytes
            record["report_sha256"] = report_sha256
        except OSError:
            record["status"] = "report_error"
            record["diagnostic"] = "successful compiler run did not produce a readable report"
            ok = False
    print(json.dumps(record, separators=(",", ":")), flush=True)
    return ok, (record.get("report_bytes"), record.get("report_sha256")) if ok else None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--before", required=True, help="before-version lim executable")
    parser.add_argument("--after", required=True, help="after-version lim executable")
    parser.add_argument("--iterations", type=int, default=5, help="samples per compiler (1..25; default: 5)")
    parser.add_argument("--declarations", type=int, default=3000, help="synthetic declarations (1..3000; default: 3000)")
    parser.add_argument("--name-bytes", type=int, default=1024, help="bytes in each synthetic payload name (1..1024; default: 1024)")
    args = parser.parse_args()
    for option, value, low, high in (("--iterations", args.iterations, 1, 25),
                                     ("--declarations", args.declarations, 1, 3000),
                                     ("--name-bytes", args.name_bytes, 1, 1024)):
        if not low <= value <= high:
            parser.error(f"{option} must be between {low} and {high}")
    if len(str(args.declarations - 1)) > args.name_bytes:
        parser.error("--name-bytes is too small to include the final declaration index")
    compilers = {}
    for label in ("before", "after"):
        try:
            executable = Path(getattr(args, label)).resolve(strict=True)
        except OSError as exc:
            parser.error(f"--{label}: {exc}")
        if not executable.is_file() or not os.access(executable, os.X_OK):
            parser.error(f"--{label} must name an executable file")
        compilers[label] = executable

    failures = 0
    reference = None
    name = (b'n' * (args.name_bytes - len(str(args.declarations - 1))) +
            str(args.declarations - 1).encode('ascii')).decode('ascii')
    # Canonical identity also handles the valid one-byte numeric component,
    # whose display spelling is quoted rather than a plain dotted name.
    target = f"$lean:s5:Audits{len(name)}:{name}"
    with tempfile.TemporaryDirectory(prefix="lim-proof-report-") as directory:
        source = Path(directory) / "synthetic.ndjson"
        source_bytes, source_sha256 = generate_source(source, args.declarations, args.name_bytes)
        for sample_index in range(1, args.iterations + 1):
            order = ("before", "after") if sample_index % 2 else ("after", "before")
            for label in order:
                report = Path(directory) / f"report-{sample_index}-{label}.json"
                ok, fingerprint = run_sample(label, compilers[label], sample_index,
                                             source, target, source_bytes,
                                             source_sha256, report,
                                             args.declarations, args.name_bytes)
                if not ok:
                    failures += 1
                elif reference is None:
                    reference = fingerprint
                elif fingerprint != reference:
                    print("benchmark-proof-report: receipt byte count or SHA-256 differs", file=sys.stderr)
                    failures += 1
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
