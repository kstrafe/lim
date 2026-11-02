#!/usr/bin/env python3
"""Measure RSS and time for raw and native proof replay fixtures.

Run this utility under ``scripts/limited-run.sh`` so the complete benchmark,
including its Python workers, stays inside the resource guard. For example:

    scripts/limited-run.sh python3 scripts/benchmark-proof-memory.py --lim target/release/lim

Each sample starts a fresh Python worker, which runs exactly one ``lim``
process. The worker reports that child's peak RSS and CPU use. This is an
external measurement utility, not checker authority. It never prints proof
source or compiler diagnostics.
"""

import argparse
import json
import os
from pathlib import Path
import resource
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parent.parent
FIXTURES = {
    "gcd": "tests/fixtures/lean_export_gcd/provenance.json",
    "gcd_self": "tests/fixtures/lean_export_gcd_self/provenance.json",
    "gcd_calculation": "tests/fixtures/lean_export_gcd_calculation/provenance.json",
    "division_composition": "tests/fixtures/lean_export_division_composition/provenance.json",
    "remainder": "tests/fixtures/lean_export_remainder/provenance.json",
}
TIMEOUT_SECONDS = 60
DIAGNOSTIC_LIMIT = 400


def cases_from_manifests():
    cases = {}
    for fixture, manifest_name in FIXTURES.items():
        manifest = json.loads((ROOT / manifest_name).read_text(encoding="utf-8"))
        target = manifest["targets"][-1]
        export = manifest["export"]["file"]
        native_info = manifest.get("native")
        if not native_info or target not in native_info.get("targets", {}):
            raise ValueError(f"{fixture}: final target lacks an exact native mapping")
        native_target = native_info["targets"][target]
        budget = manifest.get("proof_budget")
        extra = []
        if budget is not None:
            required = ("work_per_phase", "transformation_bytes_per_phase",
                        "transformation_bytes_total")
            if any(key not in budget for key in required):
                raise ValueError(f"{fixture}: incomplete proof_budget")
            extra = ["--proof-work", str(budget["work_per_phase"]),
                     "--proof-phase-bytes", str(budget["transformation_bytes_per_phase"]),
                     "--proof-total-bytes", str(budget["transformation_bytes_total"])]
        raw_args = ["--check-lean-export", export, target]
        if fixture in ("gcd", "gcd_self", "gcd_calculation"):
            raw_args.append("--lean-foundations")
        cases[f"raw_{fixture}"] = {
            "input": export,
            "budget": budget,
            "argv": raw_args + extra,
        }
        cases[f"native_{fixture}"] = {
            "input": native_info["file"],
            "budget": budget,
            "argv": ["--check-theorem", native_info["file"], native_target] + extra,
        }
    return cases


def worker(args):
    argv = [args.lim, *json.loads(args.argv_json)]
    start = time.perf_counter_ns()
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    try:
        result = subprocess.run(argv, cwd=ROOT, stdout=subprocess.DEVNULL,
                                stderr=subprocess.PIPE, timeout=TIMEOUT_SECONDS,
                                check=False)
        status = "ok" if result.returncode == 0 else "compiler_error"
        detail = "" if result.returncode == 0 else f"lim exited {result.returncode}"
    except subprocess.TimeoutExpired:
        status, detail = "timeout", f"sample exceeded {TIMEOUT_SECONDS}s"
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    wall_ms = (time.perf_counter_ns() - start) / 1_000_000
    record = {
        "case": args.case_name,
        "input_bytes": args.input_bytes,
        "budget": json.loads(args.budget_json),
        "status": status,
        "wall_ms": round(wall_ms, 3),
        "cpu_ms": round(1000 * (after.ru_utime + after.ru_stime - before.ru_utime - before.ru_stime), 3),
        "peak_rss_kib": after.ru_maxrss // 1024 if sys.platform == "darwin" else after.ru_maxrss,
    }
    if detail:
        record["diagnostic"] = detail[:DIAGNOSTIC_LIMIT]
    print(json.dumps(record, separators=(",", ":")), flush=True)
    return 0 if status == "ok" else 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lim", required=True, help="path to the lim executable")
    parser.add_argument("--iterations", type=int, default=3,
                        help="fresh worker samples per case (1..100; default: 3)")
    parser.add_argument("--case", action="append", help="case name; repeat to filter")
    parser.add_argument("--worker", action="store_true", help=argparse.SUPPRESS)
    parser.add_argument("--case-name", help=argparse.SUPPRESS)
    parser.add_argument("--argv-json", help=argparse.SUPPRESS)
    parser.add_argument("--input-bytes", type=int, help=argparse.SUPPRESS)
    parser.add_argument("--budget-json", help=argparse.SUPPRESS)
    args = parser.parse_args()

    if args.worker:
        return worker(args)
    if not 1 <= args.iterations <= 100:
        parser.error("iterations must be between 1 and 100")
    try:
        lim = str(Path(args.lim).resolve(strict=True))
        if not Path(lim).is_file() or not os.access(lim, os.X_OK):
            parser.error("--lim must name an executable file")
        cases = cases_from_manifests()
    except (OSError, ValueError, KeyError, json.JSONDecodeError) as exc:
        parser.error(str(exc))
    if args.case:
        unknown = set(args.case) - cases.keys()
        if unknown:
            parser.error("unknown case(s): " + ", ".join(sorted(unknown)))
        selected = {name: spec for name, spec in cases.items() if name in args.case}
    else:
        selected = cases

    failures = 0
    script = str(Path(__file__).resolve())
    for name, spec in selected.items():
        input_bytes = (ROOT / spec["input"]).stat().st_size
        for _ in range(args.iterations):
            command = [sys.executable, script, "--worker", "--lim", lim,
                       "--case-name", name, "--argv-json", json.dumps(spec["argv"]),
                       "--input-bytes", str(input_bytes),
                       "--budget-json", json.dumps(spec["budget"])]
            try:
                result = subprocess.run(command, cwd=ROOT, stdout=subprocess.PIPE,
                                        stderr=subprocess.DEVNULL, timeout=TIMEOUT_SECONDS + 10,
                                        check=False, text=True)
                record = json.loads(result.stdout)
            except (subprocess.TimeoutExpired, json.JSONDecodeError):
                record = {"case": name, "input_bytes": input_bytes,
                          "budget": spec["budget"], "status": "worker_error",
                          "wall_ms": None, "cpu_ms": None, "peak_rss_kib": None,
                          "diagnostic": "worker failed or exceeded its finite timeout"}
            print(json.dumps(record, separators=(",", ":")), flush=True)
            failures += record["status"] != "ok"
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
