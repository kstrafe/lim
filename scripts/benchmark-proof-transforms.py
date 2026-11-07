#!/usr/bin/env python3
"""Compare kernel transforms on the pinned accepted raw/native proof corpus.

Run under scripts/limited-run.sh. Each compiler sample uses a fresh worker;
before/after order alternates and no resource limits are changed. These small
proofs are not the full FLT export. Every timed check must succeed, after
preflight verifies complete matching success output for the immutable input.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import runpy
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent.parent
WORKER = ROOT / "scripts/benchmark-proof-memory.py"
TIMEOUT_SECONDS = 70


def digest(path):
    result = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(64 * 1024), b""):
            result.update(block)
    return result.hexdigest()


def run(command):
    with subprocess.Popen(command, cwd=ROOT, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, start_new_session=True) as child:
        try:
            stdout, stderr = child.communicate(timeout=TIMEOUT_SECONDS)
        except subprocess.TimeoutExpired:
            os.killpg(child.pid, 9)
            child.communicate()
            raise
        return subprocess.CompletedProcess(command, child.returncode, stdout, stderr)


def preflight(compilers, arguments):
    expected = (f"checked theorem {arguments[2]}\n" if arguments[0] == "--check-theorem"
                else f"checked Lean export theorem {arguments[2]} (").encode()
    outputs = []
    for label, compiler in compilers.items():
        result = run([str(compiler), *arguments])
        if result.returncode or result.stderr or not result.stdout.startswith(expected):
            raise ValueError(f"{label} failed proof preflight or returned unexpected output")
        outputs.append(result.stdout)
    if outputs[0] != outputs[1]:
        raise ValueError("complete before/after proof-check output differs")
    return hashlib.sha256(outputs[0]).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--before", required=True)
    parser.add_argument("--after", required=True)
    parser.add_argument("--iterations", type=int, default=5)
    args = parser.parse_args()
    if not 1 <= args.iterations <= 5:
        parser.error("--iterations must be between 1 and 5")
    compilers = {}
    try:
        for label in ("before", "after"):
            path = Path(getattr(args, label)).resolve(strict=True)
            if not path.is_file() or not os.access(path, os.X_OK):
                raise ValueError(f"--{label} must name an executable file")
            compilers[label] = path
        compiler_hashes = {label: digest(path) for label, path in compilers.items()}
        cases = runpy.run_path(str(WORKER))["cases_from_manifests"]()
        with tempfile.TemporaryDirectory(prefix="lim-proof-transforms-") as scratch:
            for name, spec in cases.items():
                source = Path(scratch) / f"{name}.input"
                shutil.copyfile(ROOT / spec["input"], source)
                fingerprint = digest(source)
                arguments = list(spec["argv"])
                arguments[1] = str(source)
                output_hash = preflight(compilers, arguments)
                for sample in range(1, args.iterations + 1):
                    order = ("before", "after") if sample % 2 else ("after", "before")
                    for label in order:
                        result = run([
                            sys.executable, str(WORKER), "--worker", "--lim", str(compilers[label]),
                            "--case-name", name, "--argv-json", json.dumps(arguments),
                            "--input-bytes", str(source.stat().st_size),
                            "--budget-json", json.dumps(spec["budget"]),
                        ])
                        row = json.loads(result.stdout)
                        if result.returncode or row.get("status") != "ok" or row.get("case") != name:
                            raise ValueError(f"{label} {name}: timed proof check failed")
                        row.update(label=label, sample=sample, input=spec["input"],
                                   input_sha256=fingerprint, compiler_sha256=compiler_hashes[label],
                                   preflight_stdout_sha256=output_hash)
                        print(json.dumps(row, separators=(",", ":")), flush=True)
    except (OSError, ValueError, KeyError, TypeError, subprocess.TimeoutExpired) as error:
        print(f"benchmark-proof-transforms: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
