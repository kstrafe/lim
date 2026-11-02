#!/usr/bin/env python3
"""Compare retained declaration type checking with synthetic raw proof data.

Run under ``scripts/limited-run.sh`` so the benchmark and its fresh workers
stay inside the resource guard. This is synthetic protocol stress data, not a
real mathematical proof. Each sample measures one compiler process through
``benchmark-proof-memory.py``.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parent.parent
FIXTURE = ROOT / "tests/fixtures/lean_export/identity.ndjson"
FIXTURE_SHA256 = "ad05e4153b542ea6dcd88e4a92d0a8e42ad2d757bdbc19552e3229a979c974ec"
MEMORY_BENCHMARK = ROOT / "scripts/benchmark-proof-memory.py"
PARENT_TIMEOUT_SECONDS = 70
MAX_SOURCE_BYTES = 64 * 1024 * 1024
MAX_EXPRESSIONS = 200_000
PROOF_TOTAL_BYTES = 4 * 1024 * 1024 * 1024
BUDGET = {
    "work_per_phase": 200_000,
    "transformation_bytes_per_phase": 64 * 1024 * 1024,
    "transformation_bytes_total": PROOF_TOTAL_BYTES,
}


def write_row(stream, row):
    stream.write(json.dumps(row, separators=(",", ":")) + "\n")


def generate_export(path, declarations, lets):
    fixture_bytes = FIXTURE.read_bytes()
    if hashlib.sha256(fixture_bytes).hexdigest() != FIXTURE_SHA256:
        raise ValueError("pinned identity fixture SHA256 does not match")
    expression = 21
    name_id = 5
    with path.open("wb") as stream:
        stream.write(fixture_bytes)
    with path.open("a", encoding="utf-8", newline="\n") as stream:
        # The existing fixture has Sort 0 at expression 8. Seed Sort 1 as 20.
        write_row(stream, {"il": 2, "succ": 0})
        write_row(stream, {"ie": 20, "sort": 2})
        for index in range(declarations):
            marker_name = name_id
            theorem_name = name_id + 1
            name_id += 2
            write_row(stream, {"in": marker_name,
                               "str": {"pre": 1, "str": f"Marker_{index}"}})
            write_row(stream, {"in": theorem_name,
                               "str": {"pre": 1, "str": f"declaration_{index}"}})
            write_row(stream, {
                "def": {"name": marker_name, "levelParams": [], "type": 20,
                        "value": 8, "hints": "abbrev", "safety": "safe",
                        "all": [marker_name]},
            })
            marker_value = expression
            expression += 1
            write_row(stream, {"ie": marker_value,
                               "const": {"name": marker_name, "us": []}})
            body = 12
            for _ in range(lets):
                write_row(stream, {
                    "ie": expression,
                    "letE": {"name": 0, "type": 20,
                             "value": marker_value, "body": body,
                             "nondep": True},
                })
                body = expression
                expression += 1
            write_row(stream, {
                "thm": {"name": theorem_name, "levelParams": [], "type": body,
                        "value": 19, "all": [theorem_name]},
            })
    return f"Audit.declaration_{declarations - 1}"


def run_sample(label, compiler, sample_index, export_path, target,
               source_bytes, source_sha256, declarations, lets, iterations):
    budget = dict(BUDGET)
    compiler_args = ["--check-lean-export", str(export_path), target,
                     "--proof-work", str(budget["work_per_phase"]),
                     "--proof-phase-bytes",
                     str(budget["transformation_bytes_per_phase"]),
                     "--proof-total-bytes", str(budget["transformation_bytes_total"])]
    command = [
        sys.executable, str(MEMORY_BENCHMARK), "--worker",
        "--lim", str(compiler), "--case-name", "synthetic_declaration_types",
        "--argv-json", json.dumps(compiler_args, separators=(",", ":")),
        "--input-bytes", str(source_bytes),
        "--budget-json", json.dumps(budget, separators=(",", ":")),
    ]
    try:
        result = subprocess.run(command, cwd=ROOT, stdout=subprocess.PIPE,
                                stderr=subprocess.DEVNULL,
                                timeout=PARENT_TIMEOUT_SECONDS, check=False,
                                text=True)
        data = json.loads(result.stdout)
        if not isinstance(data, dict):
            raise ValueError("worker output is not an object")
    except (subprocess.TimeoutExpired, json.JSONDecodeError, ValueError, OSError):
        result = None
        data = {
            "case": "synthetic_declaration_types", "input_bytes": source_bytes,
            "budget": budget, "status": "worker_error", "wall_ms": None,
            "cpu_ms": None, "peak_rss_kib": None,
            "diagnostic": "worker failed, timed out, or returned invalid data",
        }
    data.update({
        "label": label,
        "sample_index": sample_index,
        "source_bytes": source_bytes,
        "source_sha256": source_sha256,
        "parameters": {"declarations": declarations, "lets": lets,
                       "iterations": iterations},
    })
    print(json.dumps(data, separators=(",", ":")), flush=True)
    return result is not None and result.returncode == 0 and data.get("status") == "ok"


def receipt_digest(path):
    digest = hashlib.sha256()
    size = 0
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(64 * 1024), b""):
            size += len(chunk)
            digest.update(chunk)
    return size, digest.hexdigest()


def verify_receipts(compilers, export_path, target, directory):
    fingerprints = {}
    for label, compiler in compilers.items():
        report_path = Path(directory) / f"receipt-{label}.json"
        command = [str(compiler), "--check-lean-export", str(export_path), target,
                   "--proof-work", str(BUDGET["work_per_phase"]),
                   "--proof-phase-bytes",
                   str(BUDGET["transformation_bytes_per_phase"]),
                   "--proof-total-bytes", str(BUDGET["transformation_bytes_total"]),
                   "--report", str(report_path)]
        try:
            result = subprocess.run(command, cwd=ROOT, stdout=subprocess.DEVNULL,
                                    stderr=subprocess.DEVNULL, timeout=60,
                                    check=False)
            if result.returncode != 0:
                raise RuntimeError(f"{label} compiler failed receipt verification")
            fingerprints[label] = receipt_digest(report_path)
        except (OSError, subprocess.TimeoutExpired) as exc:
            raise RuntimeError(f"{label} receipt verification failed") from exc
    if fingerprints["before"] != fingerprints["after"]:
        raise RuntimeError("before/after receipt byte count or SHA-256 differs")
    return fingerprints["before"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--before", required=True, help="before-version lim executable")
    parser.add_argument("--after", required=True, help="after-version lim executable")
    parser.add_argument("--iterations", type=int, default=5,
                        help="samples per compiler (1..25; default: 5)")
    parser.add_argument("--declarations", type=int, default=1800,
                        help="synthetic marker and theorem pairs (1..1800; default: 1800)")
    parser.add_argument("--lets", type=int, default=48,
                        help="typed unused lets per theorem (1..64; default: 48)")
    args = parser.parse_args()

    for option, value, high in (("--iterations", args.iterations, 25),
                                ("--declarations", args.declarations, 1800),
                                ("--lets", args.lets, 64)):
        if not 1 <= value <= high:
            parser.error(f"{option} must be between 1 and {high}")
    expression_count = 21 + args.declarations * (1 + args.lets)
    if expression_count > MAX_EXPRESSIONS:
        parser.error("generated source would exceed the expression table limit")

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
    with tempfile.TemporaryDirectory(prefix="lim-proof-declarations-") as directory:
        export_path = Path(directory) / "synthetic.ndjson"
        target = generate_export(export_path, args.declarations, args.lets)
        source_bytes = export_path.stat().st_size
        if source_bytes > MAX_SOURCE_BYTES:
            parser.error("generated source exceeds the 64 MiB limit")
        digest = hashlib.sha256()
        with export_path.open("rb") as stream:
            for chunk in iter(lambda: stream.read(64 * 1024), b""):
                digest.update(chunk)
        source_sha256 = digest.hexdigest()
        try:
            receipt_bytes, receipt_sha256 = verify_receipts(
                compilers, export_path, target, directory)
        except RuntimeError as exc:
            print(f"benchmark-proof-declarations: {exc}", file=sys.stderr)
            return 1
        print(json.dumps({"case": "synthetic_declaration_types_receipt",
                          "receipt_bytes": receipt_bytes,
                          "receipt_sha256": receipt_sha256},
                         separators=(",", ":")), flush=True)
        for sample_index in range(1, args.iterations + 1):
            order = ("before", "after") if sample_index % 2 else ("after", "before")
            for label in order:
                if not run_sample(label, compilers[label], sample_index,
                                  export_path, target, source_bytes,
                                  source_sha256, args.declarations, args.lets,
                                  args.iterations):
                    failures += 1
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
