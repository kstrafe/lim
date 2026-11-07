#!/usr/bin/env python3
"""Measure retained initializer syntax, not proof replay or FLT verification.

Build the library test binary first, then pass its path. Each sample starts a
fresh worker and alternates Vec and paged storage modes. This storage-only
microbenchmark checks syntax records only: it checks no proofs, represents no
full FLT workload, and does not change default replay caps.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import resource
import statistics
import subprocess
import sys
import time


TEST = "proof::kernel::core::export::initializers::storage_tests::initializer_storage_benchmark"
PREFIX = "lim-initializer-benchmark "
ROWS = 3000


def worker(binary, mode):
    started = time.perf_counter_ns()
    env = dict(os.environ, LIM_INITIALIZER_BENCH_MODE=mode)
    result = subprocess.run(
        [binary, TEST, "--exact", "--ignored", "--nocapture"],
        env=env, capture_output=True, text=True, timeout=120, check=False,
    )
    if result.returncode or result.stderr:
        raise ValueError("initializer storage benchmark test failed: " + result.stderr[:1000])
    reports = [json.loads(line.split(PREFIX, 1)[1])
               for line in result.stdout.splitlines() if PREFIX in line]
    if len(reports) != 1 or reports[0].get("mode") != mode or reports[0].get("rows") != ROWS:
        raise ValueError("unexpected initializer storage benchmark output")
    report = reports[0]
    for field in ("wall_ns", "resident_bytes"):
        value = report.get(field)
        if type(value) is not int or value < 0:
            raise ValueError(f"initializer benchmark {field} must be a nonnegative integer")
    report.update({
        "syntax_records_only": True,
        "proofs_checked": 0,
        "full_FLT": False,
        "default_caps_changed": False,
    })
    report["process_wall_ms"] = (time.perf_counter_ns() - started) / 1_000_000
    rss = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
    report["peak_rss_kib"] = rss // 1024 if sys.platform == "darwin" else rss
    print(json.dumps(report, separators=(",", ":")))


def main():
    if len(sys.argv) == 4 and sys.argv[1] == "--worker":
        if sys.argv[3] not in ("vec", "paged"):
            raise ValueError("worker mode must be vec or paged")
        worker(sys.argv[2], sys.argv[3])
        return 0

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--test-binary", type=Path, required=True)
    parser.add_argument("--iterations", type=int, default=5)
    args = parser.parse_args()
    if not 1 <= args.iterations <= 5:
        parser.error("--iterations must be between 1 and 5")
    binary = args.test_binary.resolve(strict=True)
    if not binary.is_file() or not os.access(binary, os.X_OK):
        parser.error("--test-binary must name an executable library test binary")
    digest = hashlib.sha256()
    with binary.open("rb") as stream:
        for block in iter(lambda: stream.read(65536), b""):
            digest.update(block)
    fingerprint = digest.hexdigest()

    records = []
    for sample in range(1, args.iterations + 1):
        order = ("vec", "paged") if sample % 2 else ("paged", "vec")
        for mode in order:
            result = subprocess.run(
                [sys.executable, str(Path(__file__).resolve()), "--worker", str(binary), mode],
                capture_output=True, text=True, timeout=125, check=False,
            )
            if result.returncode:
                raise ValueError("fresh initializer benchmark worker failed: " + result.stderr[:1000])
            record = json.loads(result.stdout)
            for field in ("wall_ns", "resident_bytes"):
                value = record.get(field)
                if type(value) is not int or value < 0:
                    raise ValueError(f"initializer benchmark {field} must be a nonnegative integer")
            if record.get("mode") != mode or record.get("rows") != ROWS:
                raise ValueError("initializer benchmark report has unexpected mode or row count")
            record.update({
                "syntax_records_only": True,
                "proofs_checked": 0,
                "full_FLT": False,
                "default_caps_changed": False,
            })
            record["sample"] = sample
            records.append(record)

    medians = {}
    for mode in ("vec", "paged"):
        samples = [record for record in records if record["mode"] == mode]
        medians[mode] = {
            key: statistics.median(record[key] for record in samples)
            for key in ("wall_ns", "process_wall_ms", "peak_rss_kib", "resident_bytes")
        }
    print(json.dumps({
        "benchmark": "proof-initializer-storage-only",
        "rows": ROWS,
        "syntax_records_only": True,
        "proofs_checked": 0,
        "full_FLT": False,
        "default_caps_changed": False,
        "test_binary": str(binary),
        "test_binary_sha256": fingerprint,
        "iterations": args.iterations,
        "records": records,
        "medians": medians,
    }, indent=2))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError, KeyError, json.JSONDecodeError,
            subprocess.TimeoutExpired) as error:
        print(f"benchmark-proof-initializers: {error}", file=sys.stderr)
        raise SystemExit(1)
