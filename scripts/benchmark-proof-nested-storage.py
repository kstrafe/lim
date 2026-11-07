#!/usr/bin/env python3
"""Measure native checking of synthetic nested-inductive signature stress.

The generated families are ordinary Lim source modeled on examples/proof_nested.lim.
This is synthetic parser/kernel storage stress, not a genuine FLT input or proof.
Run under scripts/limited-run.sh after the before/after binaries exist.
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

MIB = 1024 * 1024
MAX_GROUPS = 200
MAX_DECLARATIONS = 4096
MAX_FILE_BYTES = 128 * MIB
MAX_FORM_BYTES = 8 * MIB
TIMEOUT = 180


def sha256(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(64 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def generate(path, groups, constructors, name_bytes):
    if not 1 <= groups <= MAX_GROUPS:
        raise ValueError(f"groups must be between 1 and {MAX_GROUPS}")
    if not 2 <= constructors <= 64:
        raise ValueError("constructors must be between 2 and 64")
    if not 16 <= name_bytes <= 16384:
        raise ValueError("name-bytes must be between 16 and 16384")
    if groups * 2 + 1 > MAX_DECLARATIONS:
        raise ValueError("source exceeds the unchanged 4096 declaration limit")

    size = 0
    with path.open("wb") as out:
        def emit(form):
            nonlocal size
            raw = (form + "\n").encode("ascii")
            if len(raw) > MAX_FORM_BYTES:
                raise ValueError("one generated declaration exceeds the 8 MiB form limit")
            size += len(raw)
            if size > MAX_FILE_BYTES:
                raise ValueError("generated source exceeds the 128 MiB file limit")
            out.write(raw)

        for group in range(groups):
            suffix = f"{group:03d}"
            seq, tree = "seq" + suffix, "tree" + suffix
            # Binder names are erased. Constructor names survive in the
            # derived view's signature and therefore exercise retained storage.
            names = [f"case{i:03d}-" + "x" * (name_bytes - 8)
                     for i in range(constructors - 1)]
            entries = " ".join(f"({name} ((first Element) (rest #pt-self)))"
                               for name in names)
            emit(f"(#math-inductive {seq} () ((Element (#pt-type 0))) (#pt-type 0) "
                 f"((nil ()) {entries}))")
            emit(f"(#math-inductive {tree} () () (#pt-type 0) "
                 f"((leaf ()) (node ((children (#pt-app (#pt-use {seq} ()) "
                 f"(#pt-use {tree} ())))))))")

        emit("(#theorem nested-storage-final-reflexivity (#universes) (#parameters) "
             "(#statement (#pt-eq #pt-nat #pt-zero #pt-zero)) "
             "(#proof (#pt-refl #pt-nat #pt-zero)))")
    return size, sha256(path)


def worker(executable, source, target):
    start = time.perf_counter_ns()
    result = subprocess.run(
        [str(executable), "--check-theorem", str(source), target],
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=TIMEOUT, check=False,
    )
    wall = (time.perf_counter_ns() - start) / 1_000_000_000
    # The worker is fresh for this sample, so CHILDREN measures only its lim.
    rss = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
    rss_kib = int(rss if sys.platform != "darwin" else rss // 1024)
    return {"status": result.returncode,
            "stdout": result.stdout.decode("utf-8", "replace"),
            "stderr": result.stderr.decode("utf-8", "replace"),
            "wall_seconds": wall, "peak_rss_kib": rss_kib}


def main():
    if len(sys.argv) == 5 and sys.argv[1] == "--worker":
        print(json.dumps(worker(Path(sys.argv[2]), Path(sys.argv[3]), sys.argv[4])))
        return 0
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--before", type=Path, required=True)
    parser.add_argument("--after", type=Path, required=True)
    parser.add_argument("--repeats", type=int, default=3)
    parser.add_argument("--groups", type=int, default=128)
    parser.add_argument("--constructors", type=int, default=64)
    parser.add_argument("--name-bytes", type=int, default=1600)
    args = parser.parse_args()
    if not 1 <= args.repeats <= 10:
        parser.error("--repeats must be between 1 and 10")
    for label, path in (("before", args.before), ("after", args.after)):
        if not path.is_file() or not os.access(path, os.X_OK):
            parser.error(f"--{label} must name an existing executable: {path}")
    target = "nested-storage-final-reflexivity"
    compiler_hashes = {"before": sha256(args.before), "after": sha256(args.after)}
    with tempfile.TemporaryDirectory(prefix="lim-nested-storage-") as tmp:
        source = Path(tmp) / "synthetic-nested-storage.lim"
        try:
            source_bytes, source_hash = generate(source, args.groups, args.constructors,
                                                 args.name_bytes)
        except ValueError as error:
            parser.error(str(error))
        records, failures = [], 0
        for repeat in range(1, args.repeats + 1):
            order = ("before", "after") if repeat % 2 else ("after", "before")
            samples = {}
            for label in order:
                try:
                    child = subprocess.run(
                        [sys.executable, str(Path(__file__).resolve()), "--worker",
                         str(args.before if label == "before" else args.after),
                         str(source), target], stdout=subprocess.PIPE,
                        stderr=subprocess.PIPE, text=True, timeout=TIMEOUT + 5,
                        check=False)
                    samples[label] = json.loads(child.stdout)
                    if child.returncode:
                        samples[label]["worker_error"] = child.stderr
                except (OSError, subprocess.TimeoutExpired, ValueError) as error:
                    samples[label] = {"error": str(error), "status": None,
                                      "stdout": None, "stderr": None,
                                      "wall_seconds": None, "peak_rss_kib": None}
            expected = f"checked theorem {target}\n"
            accepted = all(samples[k].get("status") == 0 and
                           samples[k].get("stdout") == expected and
                           samples[k].get("stderr") == "" for k in ("before", "after"))
            identical = accepted and all(samples["before"][key] == samples["after"][key]
                                         for key in ("status", "stdout", "stderr"))
            failures += not (accepted and identical)
            records.append({"repeat": repeat, "order": order, "samples": samples,
                            "accepted_identically": accepted and identical})
        summary = {
            "benchmark": "synthetic-native-nested-inductive-storage",
            "synthetic_not_flt": True, "before": str(args.before), "after": str(args.after),
            "source_bytes": source_bytes, "source_sha256": source_hash,
            "groups": args.groups, "constructors_per_container": args.constructors,
            "constructor_name_bytes": args.name_bytes, "declarations": args.groups * 2 + 1,
            "proof_budgets": "unchanged CLI defaults for both binaries",
            "repeats": args.repeats, "records": records, "failures": failures,
            "compiler_sha256": compiler_hashes,
        }
        if compiler_hashes != {"before": sha256(args.before), "after": sha256(args.after)}:
            raise RuntimeError("compiler executable changed during the benchmark")
        summary["medians"] = {}
        for label in ("before", "after"):
            values = [r["samples"][label] for r in records if r["accepted_identically"]]
            summary["medians"][label] = {
                "wall_seconds": statistics.median(x["wall_seconds"] for x in values) if values else None,
                "peak_rss_kib": statistics.median(x["peak_rss_kib"] for x in values) if values else None,
                "successful_samples": len(values),
            }
        print(json.dumps(summary, indent=2))
        return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
