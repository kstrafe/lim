#!/usr/bin/env python3
"""Measure scratch digest metadata, not proof replay or FLT verification.

Build the library test binary first, then pass its path under limited-run.sh.
Each sample is a fresh process; the old Vec model and paged storage alternate.
No replay caps or host resource limits are changed.
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

TEST = "proof::kernel::core::scratch::digest_tests::million_digest_metadata_benchmark"
PREFIX = "lim-digest-benchmark "
ROWS = 1_052_234


def worker(binary, mode):
    started = time.perf_counter_ns()
    env = dict(os.environ, LIM_DIGEST_BENCH_MODE=mode)
    result = subprocess.run(
        [binary, TEST, "--exact", "--ignored", "--nocapture"],
        env=env, capture_output=True, text=True, timeout=120, check=False,
    )
    if result.returncode or result.stderr:
        raise ValueError("metadata benchmark test failed: " + result.stderr[:1000])
    reports = [json.loads(line.split(PREFIX, 1)[1])
               for line in result.stdout.splitlines() if PREFIX in line]
    if len(reports) != 1 or reports[0]["mode"] != mode or reports[0]["rows"] != ROWS:
        raise ValueError("unexpected metadata benchmark output")
    report = reports[0]
    report["process_wall_ms"] = (time.perf_counter_ns() - started) / 1_000_000
    rss = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
    report["peak_rss_kib"] = rss // 1024 if sys.platform == "darwin" else rss
    print(json.dumps(report))


def main():
    if len(sys.argv) == 4 and sys.argv[1] == "--worker":
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
                raise ValueError("fresh metadata worker failed: " + result.stderr[:1000])
            record = json.loads(result.stdout)
            record["sample"] = sample
            records.append(record)
    medians = {}
    for mode in ("vec", "paged"):
        rows = [r for r in records if r["mode"] == mode]
        medians[mode] = {key: statistics.median(r[key] for r in rows)
                         for key in ("wall_ns", "process_wall_ms", "peak_rss_kib", "resident_bytes")}
    print(json.dumps(dict(benchmark="scratch-page-digest-metadata-only", rows=ROWS,
                         proofs_checked=0, default_caps_changed=False,
                         test_binary=str(binary), test_binary_sha256=fingerprint,
                         iterations=args.iterations, records=records, medians=medians), indent=2))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError, KeyError, subprocess.TimeoutExpired) as error:
        print(f"benchmark-proof-scratch-digests: {error}", file=sys.stderr)
        raise SystemExit(1)
