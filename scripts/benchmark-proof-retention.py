#!/usr/bin/env python3
"""Compare proof-expression retention with synthetic erased-let stress data.

Run under ``scripts/limited-run.sh`` so the complete benchmark and its workers
stay inside the resource guard. For example:

    scripts/limited-run.sh python3 scripts/benchmark-proof-retention.py \
        --before /path/to/before/lim --after /path/to/after/lim

This is synthetic protocol stress data, not a genuine Lean producer or FLT
proof. Each sample starts a fresh worker from benchmark-proof-memory.py, which
reports the compiler process RSS. No proof source or compiler receipts are
printed.
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
PROOF_TOTAL_BYTES = 1_073_741_824
BUDGET = {
    "work_per_phase": 200_000,
    "transformation_bytes_per_phase": 67_108_864,
    "transformation_bytes_total": PROOF_TOTAL_BYTES,
}


def write_row(stream, row):
    stream.write(json.dumps(row, separators=(",", ":")) + "\n")


def generate_export(path, declarations, lets, unused=0):
    fixture_bytes = FIXTURE.read_bytes()
    if hashlib.sha256(fixture_bytes).hexdigest() != FIXTURE_SHA256:
        raise ValueError("pinned identity fixture SHA256 does not match")
    with path.open("wb") as stream:
        stream.write(fixture_bytes)
    # Continue the fixture's NDJSON stream with the stress protocol rows.
    with path.open("a", encoding="utf-8", newline="\n") as stream:
        write_row(stream, {"il": 2, "succ": 0})
        write_row(stream, {"ie": 20, "sort": 2})
        expr = 21
        for index in range(declarations):
            name = 5 + 2 * index
            binder_name = name + 1
            write_row(stream, {"in": name, "str": {"pre": 1, "str": f"opaquePayload{index}"}})
            write_row(stream, {"in": binder_name,
                               "str": {"pre": 1, "str": f"erasedBinder{index}"}})
            body = 19
            for _ in range(lets):
                write_row(stream, {
                    "ie": expr,
                    "letE": {"name": binder_name, "type": 20, "value": 8,
                             "body": body, "nondep": True},
                })
                body = expr
                expr += 1
            write_row(stream, {
                "thm": {"name": name, "levelParams": [], "type": 12,
                        "value": body, "all": [name]},
            })
        for _ in range(unused):
            write_row(stream, {"ie": expr, "bvar": 0})
            expr += 1


def run_sample(label, compiler, sample_index, export_path, target, source_bytes,
               source_sha256, declarations, lets, iterations, unused, total_bytes):
    compiler_args = [
        "--check-lean-export", str(export_path), target,
        "--proof-total-bytes", str(total_bytes),
    ]
    budget = dict(BUDGET, transformation_bytes_total=total_bytes)
    command = [
        sys.executable, str(MEMORY_BENCHMARK), "--worker",
        "--lim", str(compiler), "--case-name", target,
        "--argv-json", json.dumps(compiler_args, separators=(",", ":")),
        "--input-bytes", str(source_bytes),
        "--budget-json", json.dumps(budget, separators=(",", ":")),
    ]
    try:
        result = subprocess.run(
            command, cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
            timeout=PARENT_TIMEOUT_SECONDS, check=False, text=True,
        )
        worker_data = json.loads(result.stdout)
        if not isinstance(worker_data, dict):
            raise ValueError("worker output is not a JSON object")
    except (subprocess.TimeoutExpired, json.JSONDecodeError, ValueError):
        worker_data = {
            "case": target, "input_bytes": source_bytes, "budget": budget,
            "status": "worker_error", "wall_ms": None, "cpu_ms": None,
            "peak_rss_kib": None,
            "diagnostic": "worker failed, exceeded its finite timeout, or returned invalid data",
        }
        result = None
    worker_data.update({
        "label": label,
        "sample_index": sample_index,
        "source_bytes": source_bytes,
        "source_sha256": source_sha256,
        "parameters": {"declarations": declarations, "lets": lets,
                       "iterations": iterations, "unused_expressions": unused},
    })
    print(json.dumps(worker_data, separators=(",", ":")), flush=True)
    return result is not None and result.returncode == 0 and worker_data.get("status") == "ok"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--before", required=True, help="before-version lim executable")
    parser.add_argument("--after", required=True, help="after-version lim executable")
    parser.add_argument("--iterations", type=int, default=5,
                        help="samples per compiler and generated export (1..25; default: 5)")
    parser.add_argument("--declarations", type=int, default=3000,
                        help="synthetic theorem declarations (1..3000; default: 3000)")
    parser.add_argument("--lets", type=int, default=32,
                        help="erased lets per theorem (1..64; default: 32)")
    parser.add_argument("--unused-expressions", type=int, default=0,
                        help="additional checked primitive records (0..190000)")
    parser.add_argument("--total-bytes", type=int, default=PROOF_TOTAL_BYTES,
                        help="explicit cumulative traffic budget (1..64 GiB; default: 1 GiB)")
    args = parser.parse_args()

    for option, value, low, high in (
        ("--iterations", args.iterations, 1, 25),
        ("--declarations", args.declarations, 1, 3000),
        ("--lets", args.lets, 1, 64),
        ("--unused-expressions", args.unused_expressions, 0, 190000),
        ("--total-bytes", args.total_bytes, 1, 64 << 30),
    ):
        if not low <= value <= high:
            parser.error(f"{option} must be between {low} and {high}")
    if 21 + args.declarations * args.lets + args.unused_expressions > 200000:
        parser.error("generated source would exceed the expression table limit")
    compilers = {}
    for label in ("before", "after"):
        candidate = getattr(args, label)
        try:
            executable = Path(candidate).resolve(strict=True)
        except OSError as exc:
            parser.error(f"--{label}: {exc}")
        if not executable.is_file() or not os.access(executable, os.X_OK):
            parser.error(f"--{label} must name an executable file")
        compilers[label] = executable

    failures = 0
    target = f"Audit.opaquePayload{args.declarations - 1}"
    with tempfile.TemporaryDirectory(prefix="lim-proof-retention-") as directory:
        export_path = Path(directory) / "synthetic.ndjson"
        generate_export(export_path, args.declarations, args.lets, args.unused_expressions)
        source_bytes = export_path.stat().st_size
        source_sha256 = hashlib.sha256(export_path.read_bytes()).hexdigest()
        for sample_index in range(1, args.iterations + 1):
            order = ("before", "after") if sample_index % 2 else ("after", "before")
            for label in order:
                if not run_sample(label, compilers[label], sample_index, export_path,
                                  target, source_bytes, source_sha256,
                                  args.declarations, args.lets, args.iterations,
                                  args.unused_expressions, args.total_bytes):
                    failures += 1
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
