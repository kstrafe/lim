#!/usr/bin/env python3
"""Compare raw proof universe-table retention with synthetic unused levels.

Run the main process under the existing 2 GiB/200% CPU resource guard::

    bash scripts/limited-run.sh python3 scripts/benchmark-proof-levels.py \
        --before /path/to/before/lim --after /path/to/after/lim

This synthetic workload adds no mathematical coverage. The pinned identity
proof is followed by primitive names and unused parameter level records,
which are checked through EOF. Complete report fingerprints must match before
timed samples start. Each sample uses a fresh benchmark-proof-memory.py worker
inside the main process's external guard.
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
CASE = "synthetic_unused_levels"
TIMEOUT_SECONDS = 60
HASH_CHUNK_BYTES = 64 * 1024
MAX_SOURCE_BYTES = 64 * 1024 * 1024
MAX_PRIMITIVE_PAYLOAD_BYTES = 64 * 1024 * 1024
MAX_NAME_PAYLOAD_BYTES = 16 * 1024 * 1024
MAX_SOURCE_LEVELS = 20_000
MAX_PARAMETER_KEY_BYTES = 512
# il1 and ie0 each carry variable u: 96 + len("$lean:s1:u") = 106.
# Twenty expressions cost 128 each; ie13 adds its global name's 25-byte key.
FIXTURE_PRIMITIVE_PAYLOAD_BYTES = 2 * 106 + 20 * 128 + 25
FIXTURE_NAME_PAYLOAD_BYTES = 126
BUDGET = {
    "work_per_phase": 200_000,
    "transformation_bytes_per_phase": 64 * 1024 * 1024,
    "transformation_bytes_total": 256 * 1024 * 1024,
}


def parameter_component(parameter_bytes, index=None):
    # The one-byte component must differ from the fixture's root-level "u".
    prefix = "v" if index is None else f"v{index}"
    return prefix + "x" * (parameter_bytes - len(prefix))


def parameter_key_bytes(parameter_bytes):
    return len(f"$lean:s{parameter_bytes}:") + parameter_bytes


def projected_primitive_payload(levels, parameter_bytes):
    # Preserve the original single-variable memory_weight accounting even
    # when a measured compiler stores duplicate levels more compactly.
    weight = 96 + parameter_key_bytes(parameter_bytes)
    return FIXTURE_PRIMITIVE_PAYLOAD_BYTES + levels * weight


def validate_levels(levels, parameter_bytes, distinct=False):
    if not 1 <= levels <= MAX_SOURCE_LEVELS - 2:
        raise ValueError("--levels must be between 1 and 19998 (20000 source levels total)")
    if not 1 <= parameter_bytes <= 480:
        raise ValueError("--parameter-bytes must be between 1 and 480")
    key_bytes = parameter_key_bytes(parameter_bytes)
    if key_bytes > MAX_PARAMETER_KEY_BYTES:
        raise ValueError("--parameter-bytes produces a canonical key longer than 512 bytes")
    if distinct and len(f"v{levels - 1}") > parameter_bytes:
        raise ValueError("--parameter-bytes must fit distinct parameter suffixes")
    name_count = levels if distinct else 1
    if FIXTURE_NAME_PAYLOAD_BYTES + name_count * (key_bytes + parameter_bytes) > MAX_NAME_PAYLOAD_BYTES:
        raise ValueError("projected name payload exceeds 16 MiB")
    if projected_primitive_payload(levels, parameter_bytes) > MAX_PRIMITIVE_PAYLOAD_BYTES:
        raise ValueError("--levels and --parameter-bytes project more than 64 MiB of primitive payload")


def parse_args(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--before", required=True, help="before-version lim executable")
    parser.add_argument("--after", required=True, help="after-version lim executable")
    parser.add_argument("--levels", type=int, default=19_000,
                        help="unused parameter levels (1..19998; default: 19000)")
    parser.add_argument("--parameter-bytes", type=int, default=256,
                        help="parameter component byte length (1..480; default: 256)")
    parser.add_argument("--iterations", type=int, default=5,
                        help="fresh samples per compiler (1..25; default: 5)")
    parser.add_argument("--distinct", action="store_true",
                        help="give every level a distinct parameter name")
    args = parser.parse_args(argv)
    if not 1 <= args.iterations <= 25:
        parser.error("--iterations must be between 1 and 25")
    try:
        validate_levels(args.levels, args.parameter_bytes, args.distinct)
    except ValueError as exc:
        parser.error(str(exc))
    return parser, args


def generate_export(path, levels, parameter_bytes, distinct=False):
    validate_levels(levels, parameter_bytes, distinct)
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

        def write_row(row):
            write((json.dumps(row, separators=(",", ":")) + "\n").encode("ascii"))

        write(fixture_bytes)
        if not distinct:
            write_row({"in": 5, "str": {"pre": 0,
                                        "str": parameter_component(parameter_bytes)}})
        for index, level_id in enumerate(range(2, levels + 2)):
            name_id = 5 + index if distinct else 5
            if distinct:
                write_row({"in": name_id, "str": {"pre": 0,
                    "str": parameter_component(parameter_bytes, index)}})
            write_row({"il": level_id, "param": name_id})
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
    # Pin the unchanged defaults for both binaries and receipt preflight.
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
            # Stop the compiler child too if a worker exceeds its deadline.
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

    parameters = {"levels": args.levels, "source_levels": args.levels + 2, "distinct": args.distinct,
                  "parameter_bytes": args.parameter_bytes,
                  "parameter_key_bytes": parameter_key_bytes(args.parameter_bytes),
                  "iterations": args.iterations,
                  "projected_primitive_payload_bytes": projected_primitive_payload(
                      args.levels, args.parameter_bytes)}
    failures = 0
    with tempfile.TemporaryDirectory(prefix="lim-proof-levels-") as directory:
        export_path = Path(directory) / "synthetic.ndjson"
        try:
            source_bytes, source_sha256 = generate_export(
                export_path, args.levels, args.parameter_bytes, args.distinct)
            receipt_bytes, receipt_sha256 = verify_receipts(
                compilers, export_path, directory)
        except (OSError, ValueError, RuntimeError) as exc:
            print(f"benchmark-proof-levels: {exc}", file=sys.stderr)
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
