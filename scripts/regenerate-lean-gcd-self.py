#!/usr/bin/env python3
"""Reproduce the pinned single-target generic Nat.gcd self replay fixture."""
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
FIXTURES = ROOT / "tests/fixtures/lean_export_gcd_self"
SOURCE = FIXTURES / "Source.lean"
ORIGIN = ROOT / "scripts/lean-export-private-origins.lean"
TARGET = "GcdSelfSource.self"
TARGETS = [TARGET]
TARGET_AXIOMS = {TARGET: ["Quot.sound", "propext"]}
OWNERS = {"Init.Core", "Init.Data.Nat.Basic", "Init.Data.Nat.Div.Basic",
          "Init.Data.Nat.Gcd", "Init.Prelude", "Init.SimpLemmas",
          "Init.WF", "Source"}
EXPECTED_DECLARATIONS = 335
PROOF_BUDGET = {"work_per_phase": 1_000_000,
                "transformation_bytes_per_phase": 134_217_728,
                "transformation_bytes_total": 1_073_741_824}
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
    expected_source = ("import Init.Data.Nat.Gcd\nnamespace GcdSelfSource\n"
        "theorem self (n : Nat) : Nat.gcd n n = n := Nat.gcd_self n\n"
        "end GcdSelfSource\n").encode()
    if source_bytes != expected_source:
        raise ValueError("GCD self fixture source must match its pinned exact text")
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

    # Reuse the six established upstream pins from the adjacent GCD corpus;
    # add Div.Basic, which is part of this measured closure.
    old = json.loads((ROOT / "tests/fixtures/lean_export_gcd/provenance.json").read_bytes())
    needed = {"Init.Core": "src/Init/Core.lean",
              "Init.Data.Nat.Basic": "src/Init/Data/Nat/Basic.lean",
              "Init.Data.Nat.Gcd": "src/Init/Data/Nat/Gcd.lean",
              "Init.Prelude": "src/Init/Prelude.lean",
              "Init.SimpLemmas": "src/Init/SimpLemmas.lean",
              "Init.WF": "src/Init/WF.lean"}
    source_records = {module: next(x for x in old["upstream_sources"] if x["source"] == src)
                      for module, src in needed.items()}
    div_file = lean / "src/lean/Init/Data/Nat/Div/Basic.lean"
    div_bytes = div_file.read_bytes()
    if len(div_bytes) != 17368 or digest(div_bytes) != "67f894497257111dff81a5b3bab0f849cc53f31a3c62656333366ad62ab63a58":
        raise ValueError("pinned Init.Data.Nat.Div.Basic source changed")
    div_text = div_bytes.decode()
    if not div_text.startswith("/-") or "-/" not in div_text:
        raise ValueError("expected upstream license notice: Init.Data.Nat.Div.Basic")
    source_records["Init.Data.Nat.Div.Basic"] = {
        "project": "lean4", "source": "src/Init/Data/Nat/Div/Basic.lean",
        "sha256": "67f894497257111dff81a5b3bab0f849cc53f31a3c62656333366ad62ab63a58", "bytes": 17368, "url":
        f"https://github.com/leanprover/lean4/blob/{PINS['LEAN_REVISION']}/src/Init/Data/Nat/Div/Basic.lean",
        "license": "Apache-2.0", "notice": div_text[2:div_text.index("-/")].strip()}
    for module, rec in source_records.items():
        source_path = lean / "src/lean" / rec["source"].removeprefix("src/")
        if digest(source_path.read_bytes()) != rec["sha256"]:
            raise ValueError(f"pinned {module} source changed")
    if set(source_records) != OWNERS - {"Source"}:
        raise ValueError("could not recover all seven upstream source pins")

    licenses = []
    for project, original, kept in [
        ("lean4", lean / "LICENSE", ROOT / "tests/fixtures/lean_export/LEAN-LICENSE.txt"),
        ("lean4export", exporter / "LICENSE", ROOT / "tests/fixtures/lean_export/EXPORTER-LICENSE.txt")]:
        if original.read_bytes() != kept.read_bytes():
            raise ValueError(f"preserved {project} license mismatch")
        licenses.append({"project": project, "license": "Apache-2.0",
                         "file": str(kept.relative_to(ROOT)), "sha256": digest(kept.read_bytes())})

    products = {}
    with tempfile.TemporaryDirectory(prefix="lim-gcd-self-export-") as td:
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
        raw_path = lean_run(["--run", "Main.lean", "Source", "--", *TARGETS], "gcd-self.ndjson")
        proof = work / "gcd-self.lim"
        receipt_path = work / "receipt.json"
        raw_check = subprocess.run([str(lim), "--check-lean-export", str(raw_path), TARGET,
            "--lean-foundations", *BUDGET_ARGS, "--emit-proof", str(proof),
            "--report", str(receipt_path)], capture_output=True, timeout=60)
        if raw_check.returncode:
            raise ValueError(raw_check.stderr.decode(errors="replace"))
        report = json.loads(receipt_path.read_bytes())
        if (report["axioms"] != ["Quot.sound", "propext"] or
            report["target_axioms"] != TARGET_AXIOMS[TARGET] or
            report["foundations"] != ["quotient-computation-v1"] or
            len(report["declarations"]) != EXPECTED_DECLARATIONS or
            report.get("proof_budget") != PROOF_BUDGET):
            raise ValueError("unexpected fixture inventory or proof budget receipt")

        originals = report["declarations"]
        names = [item["identity"] for item in originals]
        origin = lean_run(["--run", "Origins.lean", *names], "origins.jsonl")
        owners = {item["identity"]: item["module"]
                  for item in map(json.loads, origin.read_text().splitlines())}
        if len(owners) != len(originals) or set(owners) != set(names):
            raise ValueError("private source ownership does not cover every exported declaration exactly")
        native = proof.read_bytes()
        native_names = re.findall(
            r"^\(#(?:theorem|math-definition|math-opaque|math-inductive)\s+([A-Za-z0-9_-]+)",
            native.decode(), re.M)
        if len(native_names) != EXPECTED_DECLARATIONS or len(native_names) != len(set(native_names)):
            raise ValueError("native declaration mapping is incomplete or not unique")
        target_matches = [native_name for item, native_name in zip(originals, native_names)
                          if item["name"] == TARGET]
        if len(target_matches) != 1:
            raise ValueError("native mapping must contain exactly one target name")
        native_target = target_matches[0]
        budget_line = ("proof budget: work=1000000 phase-bytes=134217728 "
                       "total-bytes=1073741824")
        emission_lines = raw_check.stdout.decode().splitlines()
        expected_emission = [f"checked Lean export theorem {TARGET} ({EXPECTED_DECLARATIONS} declarations)",
            budget_line, "declared Lean axioms: Quot.sound, propext",
            "target logical foundations: Quot.sound, propext",
            f"emitted native theorem {native_target} to {proof}"]
        if emission_lines != expected_emission:
            raise ValueError(f"final raw export stdout mismatch: {emission_lines}")
        if set(owners.values()) != OWNERS:
            raise ValueError(f"private source owner set differs: {sorted(set(owners.values()))}")

        # Check every raw target and the translated theorem with the same explicit budget.
        raw_audit = subprocess.run([str(lim), "--check-lean-export", str(raw_path), TARGET,
            "--lean-foundations", *BUDGET_ARGS, "--report", str(work / "target.json")],
            capture_output=True, timeout=60)
        raw_lines = raw_audit.stdout.decode().splitlines()
        expected_raw = [f"checked Lean export theorem {TARGET} ({EXPECTED_DECLARATIONS} declarations)",
            budget_line, "declared Lean axioms: Quot.sound, propext",
            "target logical foundations: Quot.sound, propext"]
        if raw_audit.returncode or raw_lines != expected_raw:
            raise ValueError(f"raw target audit mismatch: {raw_lines}; {raw_audit.stderr.decode(errors='replace')}")
        target_report = json.loads((work / "target.json").read_bytes())
        if (target_report["axioms"] != ["Quot.sound", "propext"] or
            target_report["target_axioms"] != TARGET_AXIOMS[TARGET] or
            target_report["foundations"] != ["quotient-computation-v1"] or
            len(target_report["declarations"]) != EXPECTED_DECLARATIONS or
            target_report.get("proof_budget") != PROOF_BUDGET):
            raise ValueError("raw target basis or proof budget mismatch")
        checked = subprocess.run([str(lim), "--check-theorem", str(proof), native_target,
                                  *BUDGET_ARGS], capture_output=True, timeout=60)
        native_lines = checked.stdout.decode().splitlines()
        expected_native = [f"checked theorem {native_target}", budget_line,
                           "logical foundations: Quot.sound, propext"]
        if checked.returncode or native_lines != expected_native:
            raise ValueError(f"native target audit mismatch: {native_lines}; {checked.stderr.decode(errors='replace')}")

        # Intentional policy check: the default no-axiom raw replay must refuse.
        refusal = subprocess.run([str(lim), "--check-lean-export", str(raw_path), TARGET],
                                 capture_output=True, timeout=60)
        if refusal.returncode == 0 or b"axioms are not authorized" not in refusal.stderr:
            raise ValueError("default raw replay must refuse the declared axioms")
        constructive = subprocess.run([str(lim), "--check-lean-export", str(raw_path), TARGET,
            *BUDGET_ARGS], capture_output=True, timeout=60)
        if constructive.returncode == 0 or b"axioms are not authorized" not in constructive.stderr:
            raise ValueError("constructive budgeted replay must refuse the declared axioms")
        insufficient = subprocess.run([str(lim), "--check-lean-export", str(raw_path), TARGET,
            "--lean-foundations"], capture_output=True, timeout=60)
        if insufficient.returncode == 0 or b"resource limit" not in insufficient.stderr:
            raise ValueError("the unchanged default work budget must reject this closure")
        native_insufficient = subprocess.run([str(lim), "--check-theorem", str(proof), native_target],
            capture_output=True, timeout=60)
        if native_insufficient.returncode == 0 or b"resource limit" not in native_insufficient.stderr:
            raise ValueError("native checking must also require the selected budget")
        declarations = []
        for item, native_decl in zip(originals, native_names):
            identity = item["identity"]
            owner = owners.get(identity)
            if owner not in OWNERS:
                raise ValueError(f"unexpected private owner {owner!r}")
            declarations.append(dict(item, native_name=native_decl, module=owner,
                project="lim-fixture" if owner == "Source" else "lean4",
                source=str(SOURCE.relative_to(ROOT)) if owner == "Source" else source_records[owner]["source"],
                source_sha256=digest(source_bytes) if owner == "Source" else source_records[owner]["sha256"]))
        raw = raw_path.read_bytes()
        if digest(raw) != report["input_sha256"]:
            raise ValueError("raw input hash differs from the checked receipt")
        manifest = {"schema": "lim-lean-gcd-self-fixture-v1",
            "axioms": report["axioms"], "target_axioms": report["target_axioms"],
            "foundations": ["quotient-computation-v1"], "proof_budget": PROOF_BUDGET,
            "lean_version": "4.33.1", "lean_revision": PINS["LEAN_REVISION"],
            "exporter_revision": PINS["EXPORTER_REVISION"],
            "exporter_source_sha256": PINS["EXPORTER_FILES"], "format_version": "3.1.0",
            "source": {"file": str(SOURCE.relative_to(ROOT)), "sha256": digest(source_bytes)},
            "producer": {"file": str(Path(__file__).relative_to(ROOT)),
                         "sha256": digest(Path(__file__).read_bytes())},
            "origin_reader": {"file": str(ORIGIN.relative_to(ROOT)), "sha256": digest(ORIGIN.read_bytes())},
            "upstream_sources": list(source_records.values()), "licenses": licenses,
            "export": {"file": str((FIXTURES / "gcd-self.ndjson").relative_to(ROOT)),
                       "sha256": digest(raw), "bytes": len(raw)},
            "native": {"file": "theorems/lean_replay/gcd-self.lim",
                       "sha256": digest(native), "bytes": len(native), "targets": {TARGET: native_target}},
            "targets": TARGETS, "target_inventories": TARGET_AXIOMS, "declarations": declarations}
        products[FIXTURES / "gcd-self.ndjson"] = raw
        products[ROOT / "theorems/lean_replay/gcd-self.lim"] = native
        products[FIXTURES / "provenance.json"] = (json.dumps(manifest, indent=2, sort_keys=True) + "\n").encode()

    for path, data in products.items():
        if path.exists() and path.read_bytes() == data:
            continue
        if args.check:
            raise ValueError(f"GCD self fixture artifact differs: {path}")
        path.parent.mkdir(parents=True, exist_ok=True)
        with tempfile.NamedTemporaryFile(dir=path.parent, prefix=".gcd-self-", delete=False) as handle:
            staged = Path(handle.name)
            handle.write(data)
        try:
            staged.chmod(0o644)
            staged.replace(path)
        finally:
            staged.unlink(missing_ok=True)
    print(f"{'verified' if args.check else 'generated'} GCD self fixture artifacts; "
          f"peak child RSS {resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss} KiB")


if __name__ == "__main__":
    main()
