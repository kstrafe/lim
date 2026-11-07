#!/usr/bin/env python3
"""Reproduce the pinned, constructive closed Nat.gcd replay fixture."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import runpy
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent
PINS = runpy.run_path(str(ROOT / "scripts/regenerate-lean-replay.py"))
FIXTURES = ROOT / "tests/fixtures/lean_export_gcd_closed"
SOURCE = FIXTURES / "Source.lean"
ORIGIN = ROOT / "scripts/lean-export-private-origins.lean"
TARGET = "GcdProbe.closed"
TARGETS = [TARGET]
TARGET_AXIOMS = {TARGET: []}
OWNERS = {"Init.Core", "Init.Data.Nat.Basic", "Init.Data.Nat.Gcd",
          "Init.Prelude", "Init.SimpLemmas", "Init.WF", "Source"}
EXPECTED_DECLARATIONS = 251
EXPECTED_SOURCE_SHA256 = "3e81aa542e780a7bc92ed70de4eddb61ee231bc88719b3cc18688190ed7d3560"
EXPECTED_RAW_SHA256 = "76980f212b359452b3390ad0a75b8f10cd96998fc2d2839bb35348d792c19604"
PROOF_BUDGET = {"work_per_phase": 20_000_000,
                "transformation_bytes_per_phase": 1_073_741_824,
                "transformation_bytes_total": 2_147_483_648}
BUDGET_ARGS = ["--proof-work", str(PROOF_BUDGET["work_per_phase"]),
               "--proof-phase-bytes", str(PROOF_BUDGET["transformation_bytes_per_phase"]),
               "--proof-total-bytes", str(PROOF_BUDGET["transformation_bytes_total"])]


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-root", type=Path, required=True)
    parser.add_argument("--exporter-dir", type=Path, required=True)
    parser.add_argument("--loader", type=Path)
    parser.add_argument("--lim", type=Path, required=True)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    source_bytes = SOURCE.read_bytes()
    if digest(source_bytes) != EXPECTED_SOURCE_SHA256:
        raise ValueError("GCD closed source must match its pinned original SHA-256")
    lean, exporter, lim = (p.resolve(strict=True) for p in
                           (args.lean_root, args.exporter_dir, args.lim))
    for filename, sha in PINS["EXPORTER_FILES"].items():
        if digest((exporter / filename).read_bytes()) != sha:
            raise ValueError(f"pinned exporter source mismatch: {filename}")
    executable = [str(lean / "bin/lean")]
    if args.loader:
        executable.insert(0, str(args.loader.resolve(strict=True)))
    env = dict(os.environ, LEAN_SYSROOT=str(lean))
    version = subprocess.check_output([*executable, "--version"], env=env, timeout=30, text=True)
    if "version 4.33.1," not in version or PINS["LEAN_REVISION"] not in version:
        raise ValueError("expected pinned Lean 4.33.1")

    old = json.loads((ROOT / "tests/fixtures/lean_export_gcd/provenance.json").read_bytes())
    needed = {"Init.Core": "src/Init/Core.lean",
              "Init.Data.Nat.Basic": "src/Init/Data/Nat/Basic.lean",
              "Init.Data.Nat.Gcd": "src/Init/Data/Nat/Gcd.lean",
              "Init.Prelude": "src/Init/Prelude.lean",
              "Init.SimpLemmas": "src/Init/SimpLemmas.lean",
              "Init.WF": "src/Init/WF.lean"}
    source_records = {module: next(x for x in old["upstream_sources"] if x["source"] == src)
                      for module, src in needed.items()}
    for module, rec in source_records.items():
        source_path = lean / "src/lean" / rec["source"].removeprefix("src/")
        if digest(source_path.read_bytes()) != rec["sha256"]:
            raise ValueError(f"pinned {module} source changed")
    licenses = []
    for project, original, kept in [
        ("lean4", lean / "LICENSE", ROOT / "tests/fixtures/lean_export/LEAN-LICENSE.txt"),
        ("lean4export", exporter / "LICENSE", ROOT / "tests/fixtures/lean_export/EXPORTER-LICENSE.txt")]:
        if original.read_bytes() != kept.read_bytes():
            raise ValueError(f"preserved {project} license mismatch")
        licenses.append({"project": project, "license": "Apache-2.0",
                         "file": str(kept.relative_to(ROOT)), "sha256": digest(kept.read_bytes())})

    with tempfile.TemporaryDirectory(prefix="lim-gcd-closed-export-") as td:
        work = Path(td)
        env["LEAN_PATH"] = f"{work}:{lean}/lib/lean"
        for filename in ("Export.lean", "Main.lean"):
            shutil.copyfile(exporter / filename, work / filename)
        shutil.copyfile(SOURCE, work / "Source.lean")
        shutil.copyfile(ORIGIN, work / "Origins.lean")

        def lean_run(argv, out):
            path = work / out
            with path.open("wb") as handle:
                result = subprocess.run([*executable, "-j1", *argv], cwd=work, env=env,
                                        stdout=handle, stderr=subprocess.STDOUT, timeout=120)
            if result.returncode:
                raise ValueError(path.read_text(errors="replace"))
            if path.stat().st_size > 8 * 1024 * 1024:
                raise ValueError("producer output too large")
            return path

        for mod in ("Export", "Main", "Source"):
            lean_run(["-o", f"{mod}.olean", f"{mod}.lean"], f"{mod}.log")
        raw_path = lean_run(["--run", "Main.lean", "Source", "--", *TARGETS], "gcd-closed.ndjson")
        proof = work / "gcd-closed.lim"
        receipt_path = work / "receipt.json"
        checked = subprocess.run([str(lim), "--check-lean-export", str(raw_path), TARGET,
            *BUDGET_ARGS, "--emit-proof", str(proof), "--report", str(receipt_path)],
            capture_output=True, timeout=90)
        if checked.returncode:
            raise ValueError(checked.stderr.decode(errors="replace"))
        report = json.loads(receipt_path.read_bytes())
        if (report["axioms"] != [] or report["target_axioms"] != [] or
            report["foundations"] != [] or len(report["declarations"]) != EXPECTED_DECLARATIONS or
            report.get("proof_budget") != PROOF_BUDGET):
            raise ValueError("unexpected fixture inventory or proof budget receipt")
        originals = report["declarations"]
        names = [item["identity"] for item in originals]
        origin = lean_run(["--run", "Origins.lean", *names], "origins.jsonl")
        owners = {item["identity"]: item["module"]
                  for item in map(json.loads, origin.read_text().splitlines())}
        if len(owners) != len(originals) or set(owners) != set(names):
            raise ValueError("private source ownership does not cover every declaration exactly")
        native = proof.read_bytes()
        native_names = re.findall(r"^\(#(?:theorem|math-definition|math-opaque|math-inductive)\s+([A-Za-z0-9_-]+)",
                                  native.decode(), re.M)
        if len(native_names) != EXPECTED_DECLARATIONS or len(native_names) != len(set(native_names)):
            raise ValueError("native declaration mapping is incomplete or not unique")
        target_matches = [n for item, n in zip(originals, native_names) if item["name"] == TARGET]
        if len(target_matches) != 1:
            raise ValueError("native mapping must contain exactly one target")
        native_target = target_matches[0]
        if native_target != "lean-250-GcdProbe-closed":
            raise ValueError(f"unexpected native target name: {native_target}")
        budget_line = "proof budget: work=20000000 phase-bytes=1073741824 total-bytes=2147483648"
        if checked.stdout.decode().splitlines() != [
                f"checked Lean export theorem {TARGET} ({EXPECTED_DECLARATIONS} declarations)",
                budget_line, f"emitted native theorem {native_target} to {proof}"]:
            raise ValueError("final raw export stdout mismatch")
        if set(owners.values()) != OWNERS:
            raise ValueError(f"private source owner set differs: {sorted(set(owners.values()))}")
        raw_audit = subprocess.run([str(lim), "--check-lean-export", str(raw_path), TARGET,
            *BUDGET_ARGS, "--report", str(work / "target.json")], capture_output=True, timeout=90)
        if raw_audit.returncode or raw_audit.stdout.decode().splitlines() != [
                f"checked Lean export theorem {TARGET} ({EXPECTED_DECLARATIONS} declarations)", budget_line]:
            raise ValueError(f"raw target audit mismatch: {raw_audit.stdout.decode(errors='replace')}")
        target_report = json.loads((work / "target.json").read_bytes())
        if (target_report["axioms"] != [] or target_report["target_axioms"] != [] or
            target_report["foundations"] != [] or len(target_report["declarations"]) != EXPECTED_DECLARATIONS or
            target_report.get("proof_budget") != PROOF_BUDGET):
            raise ValueError("raw target basis or proof budget mismatch")
        native_check = subprocess.run([str(lim), "--check-theorem", str(proof), native_target,
            *BUDGET_ARGS], capture_output=True, timeout=90)
        if native_check.returncode or native_check.stdout.decode().splitlines() != [
                f"checked theorem {native_target}", budget_line]:
            raise ValueError(f"native target audit mismatch: {native_check.stdout.decode(errors='replace')}")

        declarations = []
        for item, native_decl in zip(originals, native_names):
            identity, owner = item["identity"], owners.get(item["identity"])
            if owner not in OWNERS:
                raise ValueError(f"unexpected private owner {owner!r}")
            declarations.append(dict(item, native_name=native_decl, module=owner,
                project="lim-fixture" if owner == "Source" else "lean4",
                source=str(SOURCE.relative_to(ROOT)) if owner == "Source" else source_records[owner]["source"],
                source_sha256=digest(source_bytes) if owner == "Source" else source_records[owner]["sha256"]))
        raw = raw_path.read_bytes()
        if digest(raw) != EXPECTED_RAW_SHA256:
            raise ValueError("closed raw export must match its pinned SHA-256")
        if digest(raw) != report["input_sha256"]:
            raise ValueError("raw input hash differs from checked receipt")

        # The measured default profile succeeds constructively for both forms.
        default_raw = subprocess.run([str(lim), "--check-lean-export", str(raw_path), TARGET,
            "--report", str(work / "default-target.json")],
            capture_output=True, timeout=90)
        if default_raw.returncode or default_raw.stdout.decode().splitlines() != [
                f"checked Lean export theorem {TARGET} ({EXPECTED_DECLARATIONS} declarations)"]:
            raise ValueError(f"default raw replay mismatch: {default_raw.stdout.decode(errors='replace')}; "
                             f"{default_raw.stderr.decode(errors='replace')}")
        default_report = json.loads((work / "default-target.json").read_bytes())
        if (default_report["axioms"] != [] or default_report["target_axioms"] != [] or
            default_report["foundations"] != [] or
            len(default_report["declarations"]) != EXPECTED_DECLARATIONS or
            default_report.get("proof_budget") != {"work_per_phase": 200_000,
                "transformation_bytes_per_phase": 67_108_864,
                "transformation_bytes_total": 268_435_456}):
            raise ValueError("default raw replay basis or budget mismatch")
        default_native = subprocess.run([str(lim), "--check-theorem", str(proof), native_target], capture_output=True, timeout=90)
        if default_native.returncode or default_native.stdout.decode().splitlines() != [
                f"checked theorem {native_target}"]:
            raise ValueError(f"default native replay mismatch: {default_native.stdout.decode(errors='replace')}; "
                             f"{default_native.stderr.decode(errors='replace')}")
        manifest = {"schema": "lim-lean-gcd-closed-fixture-v1", "axioms": [],
            "target_axioms": [], "foundations": [], "proof_budget": PROOF_BUDGET,
            "lean_version": "4.33.1", "lean_revision": PINS["LEAN_REVISION"],
            "exporter_revision": PINS["EXPORTER_REVISION"],
            "exporter_source_sha256": PINS["EXPORTER_FILES"], "format_version": "3.1.0",
            "source": {"file": str(SOURCE.relative_to(ROOT)), "sha256": digest(source_bytes)},
            "producer": {"file": str(Path(__file__).relative_to(ROOT)), "sha256": digest(Path(__file__).read_bytes())},
            "origin_reader": {"file": str(ORIGIN.relative_to(ROOT)), "sha256": digest(ORIGIN.read_bytes())},
            "upstream_sources": list(source_records.values()), "licenses": licenses,
            "export": {"file": str((FIXTURES / "gcd-closed.ndjson").relative_to(ROOT)),
                       "sha256": digest(raw), "bytes": len(raw)},
            "native": {"file": "theorems/lean_replay/gcd-closed.lim",
                       "sha256": digest(native), "bytes": len(native), "targets": {TARGET: native_target}},
            "targets": TARGETS, "target_inventories": TARGET_AXIOMS, "declarations": declarations}
        products = {FIXTURES / "gcd-closed.ndjson": raw,
                    ROOT / "theorems/lean_replay/gcd-closed.lim": native,
                    FIXTURES / "provenance.json": (json.dumps(manifest, indent=2, sort_keys=True) + "\n").encode()}
    for path, data in products.items():
        if path.exists() and path.read_bytes() == data:
            continue
        if args.check:
            raise ValueError(f"GCD closed fixture artifact differs: {path}")
        path.parent.mkdir(parents=True, exist_ok=True)
        with tempfile.NamedTemporaryFile(dir=path.parent, prefix=".gcd-closed-", delete=False) as handle:
            staged = Path(handle.name)
            handle.write(data)
        try:
            staged.chmod(0o644)
            staged.replace(path)
        finally:
            staged.unlink(missing_ok=True)
    print(f"{'verified' if args.check else 'generated'} GCD closed fixture artifacts; "
          f"peak child RSS {resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss} KiB")


if __name__ == "__main__":
    main()
