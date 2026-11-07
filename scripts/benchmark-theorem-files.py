#!/usr/bin/env python3
"""Compare theorem checking on pinned GCD proofs and a large native file.

Run under scripts/limited-run.sh after both compiler binaries exist. The
driver never builds a binary or changes the caller's resource limits.
The large case appends valid Lim comments to the checked gcd-closed native file,
so it measures large-file input handling while keeping the declared proof set
and kernel work identical.
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
import tempfile
import time

ROOT = Path(__file__).resolve().parent.parent
AFTER_DEFAULT = ROOT / "target/debug/lim"
CLOSED = ROOT / "theorems/lean_replay/gcd-closed.lim"
SELF = ROOT / "theorems/lean_replay/gcd-self.lim"
CLOSED_TARGET = "lean-250-GcdProbe-closed"
SELF_TARGET = "lean-334-GcdSelfSource-self"
MIB = 1024 * 1024
LARGE_BYTES = 9 * MIB
TIMEOUT = 180


def sha256(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def worker(executable, source, target, flags):
    start = time.perf_counter_ns()
    result = subprocess.run(
        [str(executable), "--check-theorem", str(source), target, *flags],
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=TIMEOUT,
        check=False,
    )
    wall = (time.perf_counter_ns() - start) / 1_000_000_000
    rss = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
    if sys.platform != "darwin":  # Linux reports KiB; macOS reports bytes.
        rss_kib = int(rss)
    else:
        rss_kib = int(rss // 1024)
    return {
        "status": result.returncode,
        "stdout": result.stdout.decode("utf-8", "replace"),
        "stderr": result.stderr.decode("utf-8", "replace"),
        "wall_seconds": wall,
        "peak_rss_kib": rss_kib,
    }


def main():
    if len(sys.argv) == 6 and sys.argv[1] == "--worker":
        record = worker(Path(sys.argv[2]), Path(sys.argv[3]), sys.argv[4],
                        json.loads(sys.argv[5]))
        print(json.dumps(record))
        return 0
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--before", type=Path, required=True)
    parser.add_argument("--after", type=Path, default=AFTER_DEFAULT)
    parser.add_argument("--repeats", type=int, default=3)
    args = parser.parse_args()
    if not 1 <= args.repeats <= 10:
        parser.error("--repeats must be between 1 and 10")

    executables = {"before": args.before, "after": args.after}
    for label, path in executables.items():
        if not path.is_file() or not os.access(path, os.X_OK):
            parser.error(f"--{label} must name an existing executable: {path}")
    if not CLOSED.is_file() or not SELF.is_file():
        parser.error("expected checked native GCD files are missing")

    # The self proof needs its documented explicit profile. Identical flags are
    # passed to both binaries, preserving kernel budgets across all comparisons.
    self_flags = ["--proof-work", "1000000", "--proof-phase-bytes", "134217728",
                  "--proof-total-bytes", "1073741824"]
    cases = [
        {"name": "native_gcd_closed", "source": CLOSED,
         "target": CLOSED_TARGET, "flags": []},
        {"name": "native_gcd_self", "source": SELF,
         "target": SELF_TARGET, "flags": self_flags},
    ]
    with tempfile.TemporaryDirectory(prefix="lim-proof-file-") as tmp:
        large = Path(tmp) / "gcd-closed-over-8MiB.lim"
        # Appended semicolon comments are valid Lim input and add no declarations.
        base = CLOSED.read_bytes()
        pad_size = LARGE_BYTES - len(base)
        if pad_size <= 0:
            parser.error("closed native proof unexpectedly exceeds large-file bound")
        with large.open("wb") as out:
            out.write(base)
            out.write(b"\n; benchmark padding; no declarations or proof terms\n")
            remaining = LARGE_BYTES - out.tell()
            # Keep each comment smaller than the reader's form bound, so this
            # really measures the file-backed route rather than its fallback.
            while remaining:
                count = min(remaining, 4096)
                out.write(b"\n" if count == 1 else b";" + b"x" * (count - 2) + b"\n")
                remaining -= count
        actual_size = large.stat().st_size
        if actual_size <= 8 * MIB:
            parser.error("large native case did not exceed 8 MiB")
        cases.append({"name": "native_gcd_closed_large_file", "source": large,
                      "target": CLOSED_TARGET, "flags": []})

        records = []
        failures = 0
        for repeat in range(1, args.repeats + 1):
            order = ("before", "after") if repeat % 2 else ("after", "before")
            for case in cases:
                paired = {}
                for label in order:
                    try:
                        child = subprocess.run(
                            [sys.executable, str(Path(__file__).resolve()), "--worker",
                             str(executables[label]), str(case["source"]),
                             case["target"], json.dumps(case["flags"])],
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                            timeout=TIMEOUT + 5, check=False,
                        )
                        paired[label] = json.loads(child.stdout)
                        if child.returncode != 0:
                            paired[label]["worker_error"] = child.stderr
                    except (OSError, subprocess.TimeoutExpired, ValueError) as error:
                        paired[label] = {"error": str(error), "status": None,
                                         "stdout": None, "stderr": None,
                                         "wall_seconds": None, "peak_rss_kib": None}
                accepted = all(paired[label].get("status") == 0 for label in executables)
                identical = accepted and all(
                    paired["before"][key] == paired["after"][key]
                    for key in ("status", "stdout", "stderr"))
                expected = f"checked theorem {case['target']}\n"
                if case["flags"]:
                    expected += "proof budget: work=1000000 phase-bytes=134217728 total-bytes=1073741824\n"
                    expected += "logical foundations: Quot.sound, propext\n"
                accepted = accepted and all(
                    paired[label].get("stdout") == expected and
                    paired[label].get("stderr") == "" for label in executables)
                if not accepted or not identical:
                    failures += 1
                records.append({
                    "repeat": repeat, "order": order, "case": case["name"],
                    "source_bytes": case["source"].stat().st_size,
                    "source_sha256": sha256(case["source"]),
                    "target": case["target"], "proof_budget_flags": case["flags"],
                    "samples": paired, "accepted_identically": accepted and identical,
                })

        summary = {
            "benchmark": "native-proof-file-check-theorem",
            "baseline": str(executables["before"]),
            "target": str(executables["after"]),
            "binary_sha256": {k: sha256(v) for k, v in executables.items()},
            "repeats": args.repeats,
            "proof_budgets": "unchanged between binaries; closed uses CLI defaults, self uses fixture-documented profile",
            "large_case": "gcd-closed native file plus valid comments; declared proofs unchanged",
            "records": records, "failures": failures,
        }
        summary["case_medians"] = {}
        for case in cases:
            summary["case_medians"][case["name"]] = {}
            for label in executables:
                samples = [r["samples"][label] for r in records
                           if r["case"] == case["name"] and r["accepted_identically"]]
                summary["case_medians"][case["name"]][label] = {
                    "wall_seconds": statistics.median(x["wall_seconds"] for x in samples) if samples else None,
                    "peak_rss_kib": statistics.median(x["peak_rss_kib"] for x in samples) if samples else None,
                    "successful_samples": len(samples),
                }
        print(json.dumps(summary, indent=2))
        return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
