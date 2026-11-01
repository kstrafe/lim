#!/usr/bin/env python3
"""Reproduce the explicitly audited logical-foundation fixture and its checked native translation.

Run under scripts/limited-run.sh. Requires the already downloaded pinned Lean
and exporter sources, plus a built Lim executable; never downloads tools.
"""
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
FIXTURES = ROOT / "tests/fixtures/lean_export_foundations"
SOURCE = FIXTURES / "Source.lean"
TARGETS = ["BasisProbe.choiceReflexive", "BasisProbe.propositionEquality",
           "BasisProbe.quotientRelated"]
EXPECTED_AXIOMS = ["Classical.choice", "Quot.sound", "propext"]
EXPECTED_TARGETS = dict(zip(TARGETS, [["Classical.choice"], ["propext"], ["Quot.sound"]]))


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-root", type=Path, required=True)
    parser.add_argument("--exporter-dir", type=Path, required=True)
    parser.add_argument("--lim", type=Path, required=True)
    parser.add_argument("--loader", type=Path)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    lean = args.lean_root.resolve(strict=True)
    exporter = args.exporter_dir.resolve(strict=True)
    lim = args.lim.resolve(strict=True)
    for filename, expected in PINS["EXPORTER_FILES"].items():
        if digest((exporter / filename).read_bytes()) != expected:
            raise ValueError(f"pinned exporter source mismatch: {filename}")
    executable = [str(lean / "bin/lean")]
    if args.loader:
        executable.insert(0, str(args.loader.resolve(strict=True)))
    environment = dict(os.environ, LEAN_SYSROOT=str(lean))
    version = subprocess.check_output([*executable, "--version"], env=environment,
                                      timeout=30, text=True)
    if "version 4.33.1," not in version or PINS["LEAN_REVISION"] not in version:
        raise ValueError("expected the pinned Lean 4.33.1 release")
    prior = json.loads((ROOT / "tests/fixtures/lean_export/real-provenance.json").read_bytes())
    source_pins = {item["source"]: item for item in prior["upstream_sources"]}
    for filename in ["src/Init/Prelude.lean", "src/Init/Core.lean"]:
        if digest((lean / "src/lean" / filename.removeprefix("src/")).read_bytes()) != source_pins[filename]["sha256"]:
            raise ValueError(f"pinned upstream source changed: {filename}")
    licenses = []
    for project, original, kept in [
        ("lean4", lean / "LICENSE", ROOT / "tests/fixtures/lean_export/LEAN-LICENSE.txt"),
        ("lean4export", exporter / "LICENSE", ROOT / "tests/fixtures/lean_export/EXPORTER-LICENSE.txt"),
    ]:
        if original.read_bytes() != kept.read_bytes():
            raise ValueError(f"preserved {project} license differs from the pinned tool")
        licenses.append({"project": project, "license": "Apache-2.0",
                         "file": str(kept.relative_to(ROOT)), "sha256": digest(kept.read_bytes())})
    origin = ROOT / "scripts/lean-export-origins.lean"
    products = {}
    with tempfile.TemporaryDirectory(prefix="lim-foundations-export-") as directory:
        work = Path(directory)
        environment["LEAN_PATH"] = f"{work}:{lean}/lib/lean"
        for filename in ["Export.lean", "Main.lean"]:
            shutil.copyfile(exporter / filename, work / filename)
        shutil.copyfile(SOURCE, work / "Source.lean")
        shutil.copyfile(origin, work / "Origins.lean")

        def run_lean(arguments, filename):
            output = work / filename
            with output.open("wb") as handle:
                result = subprocess.run([*executable, "-j1", *arguments], cwd=work,
                                        env=environment, stdout=handle, stderr=subprocess.STDOUT,
                                        timeout=120, check=False)
            if result.returncode:
                raise ValueError(output.read_text(errors="replace"))
            if output.stat().st_size > 8 * 1024 * 1024:
                raise ValueError("fixture producer output exceeds its byte budget")
            return output

        for module in ["Export", "Main", "Source"]:
            run_lean(["-o", f"{module}.olean", f"{module}.lean"], f"{module}.log")
        raw_path = run_lean(["--run", "Main.lean", "Source", "--", *TARGETS], "foundations.ndjson")
        proof = work / "foundations.lim"
        receipt = work / "receipt.json"
        result = subprocess.run([str(lim), "--check-lean-export", str(raw_path), TARGETS[-1],
                                 "--lean-foundations", "--emit-proof", str(proof), "--report", str(receipt)],
                                capture_output=True, timeout=60, check=False)
        if result.returncode:
            raise ValueError(result.stderr.decode(errors="replace"))
        report = json.loads(receipt.read_bytes())
        if report["axioms"] != EXPECTED_AXIOMS or report["target_axioms"] != EXPECTED_TARGETS[TARGETS[-1]] or report["foundations"] != ["quotient-computation-v1"]:
            raise ValueError("unexpected fixture foundation or axiom inventory")
        for target, expected in EXPECTED_TARGETS.items():
            result = subprocess.run([str(lim), "--check-lean-export", str(raw_path), target,
                                     "--lean-foundations", "--report", str(work / "target.json")],
                                    capture_output=True, timeout=60, check=True)
            if json.loads((work / "target.json").read_bytes())["target_axioms"] != expected:
                raise ValueError(f"wrong replay axiom closure: {target}")
        refused = subprocess.run([str(lim), "--check-lean-export", str(raw_path), TARGETS[-1]],
                                  capture_output=True, timeout=60)
        if refused.returncode == 0 or b"axioms are not authorized" not in refused.stderr:
            raise ValueError("default replay must reject the axiom corpus")
        originals = report["declarations"]
        origin_file = run_lean(["--run", "Origins.lean", *[item["name"] for item in originals]],
                               "origins.jsonl")
        owners = {item["declaration"]: item["module"]
                  for item in map(json.loads, origin_file.read_text().splitlines())}
        native = proof.read_bytes()
        names = re.findall(r"^\(#(?:theorem|math-definition|math-opaque|math-inductive)\s+([A-Za-z0-9_-]+)",
                           native.decode(), re.M)
        if len(names) != len(originals) or len(set(names)) != len(names):
            raise ValueError("native declaration mapping is incomplete")
        declarations = []
        native_targets = {}
        for item, name in zip(originals, names):
            owner = owners[item["name"]]
            if owner not in ["Source", "Init.Prelude", "Init.Core"]:
                raise ValueError(f"unexpected fixture source module: {owner}")
            source = str(SOURCE.relative_to(ROOT)) if owner == "Source" else "src/" + owner.replace(".", "/") + ".lean"
            source_hash = digest(SOURCE.read_bytes()) if owner == "Source" else source_pins[source]["sha256"]
            declarations.append(dict(item, native_name=name, module=owner, source=source,
                                     source_sha256=source_hash,
                                     project="lim-fixture" if owner == "Source" else "lean4"))
            if item["name"] in TARGETS:
                native_targets[item["name"]] = name
        for target, name in native_targets.items():
            result = subprocess.run([str(lim), "--check-theorem", str(proof), name], check=True,
                                    capture_output=True, timeout=60, text=True)
            inventory = [line.removeprefix("logical foundations: ").split(", ")
                         for line in result.stdout.splitlines() if line.startswith("logical foundations: ")]
            if inventory != [EXPECTED_TARGETS[target]]:
                raise ValueError(f"native axiom inventory differs: {target}")
        raw = raw_path.read_bytes()
        if digest(raw) != report["input_sha256"]:
            raise ValueError("fixture input hash differs from the checked receipt")
        manifest = {
            "schema": "lim-lean-foundation-fixture-v1", "axioms": report["axioms"],
            "target_axioms": report["target_axioms"], "target_inventories": EXPECTED_TARGETS,
            "foundations": report["foundations"], "lean_version": "4.33.1",
            "lean_revision": PINS["LEAN_REVISION"], "exporter_revision": PINS["EXPORTER_REVISION"],
            "exporter_source_sha256": PINS["EXPORTER_FILES"], "format_version": "3.1.0",
            "source": {"file": str(SOURCE.relative_to(ROOT)), "sha256": digest(SOURCE.read_bytes())},
            "producer": {"file": str(Path(__file__).relative_to(ROOT)), "sha256": digest(Path(__file__).read_bytes())},
            "origin_reader": {"file": str(origin.relative_to(ROOT)), "sha256": digest(origin.read_bytes())},
            "upstream_sources": [source_pins[filename] for filename in sorted(source_pins)], "licenses": licenses,
            "export": {"file": str((FIXTURES / "foundations.ndjson").relative_to(ROOT)),
                       "sha256": digest(raw), "bytes": len(raw)},
            "native": {"file": "theorems/lean_replay/foundations.lim", "sha256": digest(native),
                       "bytes": len(native), "targets": native_targets},
            "targets": TARGETS, "declarations": declarations,
        }
        products[FIXTURES / "foundations.ndjson"] = raw
        products[ROOT / "theorems/lean_replay/foundations.lim"] = native
        products[FIXTURES / "provenance.json"] = (json.dumps(manifest, indent=2, sort_keys=True) + "\n").encode()
    for path, data in products.items():
        if path.exists() and path.read_bytes() == data:
            continue
        if args.check:
            raise ValueError(f"foundations fixture artifact differs: {path}")
        path.parent.mkdir(parents=True, exist_ok=True)
        with tempfile.NamedTemporaryFile(dir=path.parent, prefix=".foundations-", delete=False) as handle:
            staged = Path(handle.name)
            handle.write(data)
        try:
            staged.chmod(0o644)
            staged.replace(path)
        finally:
            staged.unlink(missing_ok=True)
    print(f"{'verified' if args.check else 'generated'} {len(products)} foundations artifacts; "
          f"peak child RSS {resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss} KiB")


if __name__ == "__main__":
    main()
