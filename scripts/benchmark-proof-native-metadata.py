#!/usr/bin/env python3
"""Measure checked native emission with paged long-name report metadata.

Run under scripts/limited-run.sh. This fixed synthetic case adds 90 closed
identity theorems with 12,000-byte names. It does not add genuine FLT coverage.
Every fresh worker must reproduce complete emitted-proof and receipt hashes.
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
FIXTURE = ROOT / "tests/fixtures/lean_export/identity.ndjson"
FIXTURE_SHA256 = "ad05e4153b542ea6dcd88e4a92d0a8e42ad2d757bdbc19552e3229a979c974ec"
TARGET = "Audit.identity.theorem"


def generate_source(path):
    fixture = FIXTURE.read_bytes()
    if hashlib.sha256(fixture).hexdigest() != FIXTURE_SHA256:
        raise ValueError("pinned identity fixture SHA256 does not match")
    rows = fixture.decode().splitlines()
    theorem = rows.pop()
    for index in range(90):
        rows.append(json.dumps({"in": 5 + index,
                               "str": {"pre": 0, "str": "N" * 12000 + str(index)}},
                              separators=(",", ":")))
    for index in range(90):
        rows.append(json.dumps({"thm": {"name": 5 + index, "levelParams": [],
                                       "type": 12, "value": 19, "all": [5 + index]}},
                              separators=(",", ":")))
    rows.append(theorem)
    source = ("\n".join(rows) + "\n").encode()
    if len(source) > 2 * 1024 * 1024:
        raise ValueError("synthetic metadata input exceeded its fixed byte bound")
    path.write_bytes(source)
    return len(source), hashlib.sha256(source).hexdigest()


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--before", required=True)
    parser.add_argument("--after", required=True)
    parser.add_argument("--iterations", type=int, default=5)
    args = parser.parse_args(argv)
    if not 1 <= args.iterations <= 5:
        parser.error("--iterations must be between 1 and 5")
    compilers = {}
    for label in ("before", "after"):
        try:
            path = Path(getattr(args, label)).resolve(strict=True)
        except (OSError, RuntimeError) as error:
            parser.error(f"--{label}: {error}")
        if not path.is_file() or not os.access(path, os.X_OK):
            parser.error(f"--{label} must name an executable file")
        compilers[label] = path
    helper = runpy.run_path(str(ROOT / "scripts/benchmark-proof-native-retention.py"))
    with tempfile.TemporaryDirectory(prefix="lim-native-metadata-bench-") as temporary:
        directory = Path(temporary)
        source = directory / "long-names.ndjson"
        try:
            info = generate_source(source)
            expected = helper["verify_preflight"](compilers, source, TARGET, directory)
        except (OSError, ValueError, RuntimeError, subprocess.TimeoutExpired) as error:
            print(f"benchmark-proof-native-metadata: {error}", file=sys.stderr)
            return 1
        print(json.dumps({"stage": "preflight", "scenario": "long_name_native_metadata",
                          "status": "ok", "source_bytes": info[0], "source_sha256": info[1],
                          "report_bytes": expected[0][0], "report_sha256": expected[0][1],
                          "proof_bytes": expected[1][0], "proof_sha256": expected[1][1]}),
              flush=True)
        parameters = {"scenario": "long_name_native_metadata", "extra_theorems": 90,
                      "name_bytes": 12000, "iterations": args.iterations}
        failures = 0
        for sample in range(1, args.iterations + 1):
            order = ("before", "after") if sample % 2 else ("after", "before")
            for label in order:
                if not helper["run_sample"](label, compilers[label], sample, source, TARGET,
                                             info, parameters, directory, expected):
                    failures += 1
        return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
