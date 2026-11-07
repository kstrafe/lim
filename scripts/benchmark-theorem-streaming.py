#!/usr/bin/env python3
"""Measure standalone --check-theorem frontend streaming on a deterministic source.

Run inside scripts/limited-run.sh nix develop. This program runs each compiler
serially, alternating before/after order, and never changes the caller's limits.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import statistics
import subprocess
import sys
import tempfile
import time
import resource


MAX_SOURCE_BYTES = 8 * 1024 * 1024
TIMEOUT_SECONDS = 120


def generate(path, declarations):
    # These are synthetic generic reflexivity proofs, not imported Lean/FLT
    # evidence. Every declaration must be checked before selecting the target.
    rows = []
    for i in range(declarations):
        rows.append(f"""(#theorem proof-{i}
  (#universes u)
  (#parameters (#parameter a (#pt-type u)) (#parameter value a))
  (#statement (#pt-eq a value value))
  (#proof (#pt-refl a value)))""")
    data = ("\n".join(rows) + "\n").encode()
    if len(data) > MAX_SOURCE_BYTES:
        raise ValueError("generated source exceeds 8 MiB")
    path.write_bytes(data)
    return len(data), hashlib.sha256(data).hexdigest()


def worker(compiler, source, target):
    # One fresh worker per compiler sample makes RUSAGE_CHILDREN's peak belong
    # to that sample rather than to an earlier, larger compiler invocation.
    start = time.perf_counter_ns()
    result = subprocess.run(
        [compiler, "--check-theorem", source, target],
        stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        timeout=TIMEOUT_SECONDS, check=False,
    )
    wall = (time.perf_counter_ns() - start) / 1_000_000_000
    usage = resource.getrusage(resource.RUSAGE_CHILDREN)
    rss = usage.ru_maxrss // 1024 if sys.platform == "darwin" else usage.ru_maxrss
    expected = f"checked theorem {target}\n".encode()
    record = {
        "exit_code": result.returncode,
        "stdout": result.stdout.decode("utf-8", "replace"),
        "stderr": result.stderr.decode("utf-8", "replace"),
        "wall_seconds": wall,
        "peak_rss_kib": rss,
        "success": result.returncode == 0 and result.stdout == expected and not result.stderr,
    }
    print(json.dumps(record))
    return 0 if record["success"] else 1


def main():
    if len(sys.argv) == 5 and sys.argv[1] == "--worker":
        return worker(*sys.argv[2:])
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--before", required=True)
    parser.add_argument("--after", required=True)
    parser.add_argument("--repeats", type=int, default=5)
    parser.add_argument("--declarations", type=int, default=3000)
    parser.add_argument("--output", default="-")
    args = parser.parse_args()
    if not 1 <= args.repeats <= 25:
        parser.error("--repeats must be between 1 and 25")
    if not 1 <= args.declarations <= 3000:
        parser.error("--declarations must be between 1 and 3000")
    compilers = {}
    for label in ("before", "after"):
        try:
            exe = Path(getattr(args, label)).resolve(strict=True)
        except (OSError, RuntimeError) as exc:
            parser.error(f"--{label}: {exc}")
        if not exe.is_file() or not os.access(exe, os.X_OK):
            parser.error(f"--{label} must name an executable file")
        compilers[label] = exe

    records = []
    failures = 0
    with tempfile.TemporaryDirectory(prefix="lim-theorem-streaming-") as tmp:
        root = Path(tmp)
        source = root / "synthetic.lim"
        size, digest = generate(source, args.declarations)
        target = f"proof-{args.declarations - 1}"
        for repeat in range(1, args.repeats + 1):
            pair = {}
            order = ("before", "after") if repeat % 2 else ("after", "before")
            for label in order:
                try:
                    result = subprocess.run(
                        [sys.executable, str(Path(__file__).resolve()), "--worker",
                         str(compilers[label]), str(source), target],
                        stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                        timeout=TIMEOUT_SECONDS + 5, check=False,
                    )
                    pair[label] = json.loads(result.stdout)
                    pair[label]["success"] = result.returncode == 0 and pair[label]["success"]
                except (OSError, subprocess.TimeoutExpired, ValueError, IndexError) as exc:
                    pair[label] = {"success": False, "error": str(exc),
                                   "wall_seconds": None, "peak_rss_kib": None}
                if not pair[label]["success"]:
                    failures += 1
            if all(pair.get(k, {}).get("success") for k in ("before", "after")):
                if pair["before"]["stdout"] != pair["after"]["stdout"]:
                    failures += 1
                    pair["output_match"] = False
                else:
                    pair["output_match"] = True
            else:
                pair["output_match"] = False
            records.append({"repeat": repeat, "order": order, "samples": pair,
                            "source_bytes": size, "source_sha256": digest,
                            "target": target})

    summary = {"benchmark": "standalone-check-theorem-streaming", "source_bytes": size,
               "source_sha256": digest, "target": target, "declarations": args.declarations,
               "repeats": args.repeats, "records": records, "failures": failures,
               "compilers": {label: {"path": str(path),
                   "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}
                   for label, path in compilers.items()},
               "proof_budget": "unchanged compiler defaults",
               "workload": "synthetic mathematical-only source, not FLT"}
    for label in ("before", "after"):
        good = [r["samples"][label] for r in records
                if r["samples"].get(label, {}).get("success")]
        summary[label + "_median"] = {
            "wall_seconds": statistics.median(x["wall_seconds"] for x in good) if good else None,
            "peak_rss_kib": statistics.median(x["peak_rss_kib"] for x in good
                                                if x["peak_rss_kib"] is not None)
            if any(x["peak_rss_kib"] is not None for x in good) else None,
            "successful_samples": len(good),
        }
    rendered = json.dumps(summary, indent=2) + "\n"
    if args.output == "-":
        print(rendered, end="")
    else:
        Path(args.output).write_text(rendered, encoding="utf-8")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
