#!/usr/bin/env python3
"""Reproduce the genuine, axiom-free Lean division composition replay fixture.

Run under scripts/limited-run.sh. Requires pinned Lean/exporter sources and a
built Lim executable; this script never downloads tools.
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
FIXTURES = ROOT / "tests/fixtures/lean_export_division_composition"
SOURCE = FIXTURES / "Source.lean"
ORIGIN = ROOT / "scripts/lean-export-private-origins.lean"
NAMESPACE = "DivisionCompositionSource"


def digest(data):
    return hashlib.sha256(data).hexdigest()


def targets_from_source():
    source = SOURCE.read_text()
    if re.search(r"\b(?:axiom|sorry|admit|native_decide)\b", source):
        raise ValueError("division source contains a forbidden proof escape")
    namespace = re.search(r"^namespace\s+([A-Za-z_][A-Za-z0-9_.]*)", source, re.M)
    if not namespace or namespace.group(1) != NAMESPACE:
        raise ValueError("unexpected division namespace")
    targets = [NAMESPACE + "." + name for name in re.findall(
        r"^theorem\s+([A-Za-z_][A-Za-z0-9_]*)", source, re.M)]
    if not targets:
        raise ValueError("no division targets found")
    return targets


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-root", type=Path, required=True)
    parser.add_argument("--exporter-dir", type=Path, required=True)
    parser.add_argument("--loader", type=Path)
    parser.add_argument("--lim", type=Path, required=True)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    targets = targets_from_source()
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
    prelude = lean / "src/lean/Init/Prelude.lean"
    prelude_pin = next(item for item in prior["upstream_sources"]
                       if item["source"] == "src/Init/Prelude.lean")
    if digest(prelude.read_bytes()) != prelude_pin["sha256"]:
        raise ValueError("pinned Init.Prelude source changed")
    foundations = json.loads((ROOT / "tests/fixtures/lean_export_foundations/provenance.json").read_bytes())
    core_pin = next(item for item in foundations["upstream_sources"]
                    if item["source"] == "src/Init/Core.lean")
    if digest((lean / "src/lean/Init/Core.lean").read_bytes()) != core_pin["sha256"]:
        raise ValueError("pinned Init.Core source changed")
    upstream_sources = {"Init.Prelude": prelude_pin, "Init.Core": core_pin}
    licenses = []
    for project, original, kept in [
        ("lean4", lean / "LICENSE", ROOT / "tests/fixtures/lean_export/LEAN-LICENSE.txt"),
        ("lean4export", exporter / "LICENSE", ROOT / "tests/fixtures/lean_export/EXPORTER-LICENSE.txt"),
    ]:
        if original.read_bytes() != kept.read_bytes():
            raise ValueError(f"preserved {project} license differs from the pinned tool")
        licenses.append({"project": project, "license": "Apache-2.0",
                         "file": str(kept.relative_to(ROOT)), "sha256": digest(kept.read_bytes())})
    products = {}
    with tempfile.TemporaryDirectory(prefix="lim-division-composition-export-") as directory:
        work = Path(directory)
        environment["LEAN_PATH"] = f"{work}:{lean}/lib/lean"
        for filename in ["Export.lean", "Main.lean"]:
            shutil.copyfile(exporter / filename, work / filename)
        shutil.copyfile(SOURCE, work / "Source.lean")
        shutil.copyfile(ORIGIN, work / "Origins.lean")

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
        raw_path = run_lean(["--run", "Main.lean", "Source", "--", *targets],
                            "division-composition.ndjson")
        proof = work / "division-composition.lim"
        report_path = work / "receipt.json"
        result = subprocess.run([str(lim), "--check-lean-export", str(raw_path), targets[-1],
                                 "--emit-proof", str(proof), "--report", str(report_path)],
                               capture_output=True, timeout=60, check=False)
        if result.returncode:
            raise ValueError(result.stderr.decode(errors="replace"))
        report = json.loads(report_path.read_bytes())
        if report["axioms"] or report["foundations"]:
            raise ValueError("unexpected fixture foundation or axiom inventory")
        originals = report["declarations"]
        origin_file = run_lean(["--run", "Origins.lean", *[item["identity"] for item in originals]],
                               "origins.jsonl")
        owners = {item["identity"]: item["module"]
                  for item in map(json.loads, origin_file.read_text().splitlines())}
        native = proof.read_bytes()
        names = re.findall(r"^\(#(?:theorem|math-definition|math-opaque|math-inductive)\s+([A-Za-z0-9_-]+)",
                           native.decode(), re.M)
        if len(names) != len(originals) or len(set(names)) != len(names):
            raise ValueError("native declaration mapping is incomplete")
        declarations = []
        native_targets = {}
        for item, name in zip(originals, names):
            owner = owners[item["identity"]]
            if item["name"] in {"Nat.div", "Nat.mod"} and owner != "Init.Prelude":
                raise ValueError(f"division declaration has unexpected owner: {item['name']} ({owner})")
            if owner not in ["Source", *upstream_sources]:
                raise ValueError(f"unexpected fixture source module: {owner}")
            source = str(SOURCE.relative_to(ROOT)) if owner == "Source" else upstream_sources[owner]["source"]
            source_hash = digest(SOURCE.read_bytes()) if owner == "Source" else upstream_sources[owner]["sha256"]
            declarations.append(dict(item, native_name=name, module=owner, source=source,
                                     source_sha256=source_hash,
                                     project="lim-fixture" if owner == "Source" else "lean4"))
            if item["name"] in targets:
                native_targets[item["name"]] = name
        if set(native_targets) != set(targets):
            raise ValueError("native mapping does not include every division target")
        # Independently ask Lim to validate every requested target and audit the
        # resulting native theorem in its own CLI invocation.
        for target in targets:
            receipt = work / (target.rsplit(".", 1)[-1] + "-receipt.json")
            checked_export = subprocess.run(
                [str(lim), "--check-lean-export", str(raw_path), target, "--report", str(receipt)],
                capture_output=True, timeout=60, check=False)
            if checked_export.returncode:
                raise ValueError(checked_export.stderr.decode(errors="replace"))
            audit = json.loads(receipt.read_bytes())
            if audit["axioms"] or audit["foundations"]:
                raise ValueError(f"target has nonempty axiom/foundation inventory: {target}")
            checked_native = subprocess.run([str(lim), "--check-theorem", str(proof), native_targets[target]],
                                            capture_output=True, timeout=60, check=False)
            if checked_native.returncode or checked_native.stdout.decode().strip() != f"checked theorem {native_targets[target]}":
                raise ValueError(f"native target failed independent check: {target}")
        raw = raw_path.read_bytes()
        if digest(raw) != report["input_sha256"]:
            raise ValueError("fixture input hash differs from checked receipt")
        manifest = {
            "schema": "lim-lean-division-composition-fixture-v1", "axioms": [],
            "foundations": report["foundations"], "lean_version": "4.33.1",
            "lean_revision": PINS["LEAN_REVISION"], "exporter_revision": PINS["EXPORTER_REVISION"],
            "exporter_source_sha256": PINS["EXPORTER_FILES"], "format_version": "3.1.0",
            "source": {"file": str(SOURCE.relative_to(ROOT)), "sha256": digest(SOURCE.read_bytes())},
            "producer": {"file": str(Path(__file__).relative_to(ROOT)), "sha256": digest(Path(__file__).read_bytes())},
            "origin_reader": {"file": str(ORIGIN.relative_to(ROOT)), "sha256": digest(ORIGIN.read_bytes())},
            "upstream_sources": list(upstream_sources.values()), "licenses": licenses,
            "export": {"file": str((FIXTURES / "division-composition.ndjson").relative_to(ROOT)),
                       "sha256": digest(raw), "bytes": len(raw)},
            "native": {"file": "theorems/lean_replay/division-composition.lim", "sha256": digest(native),
                       "bytes": len(native), "targets": native_targets},
            "targets": targets, "declarations": declarations,
        }
        products[FIXTURES / "division-composition.ndjson"] = raw
        products[ROOT / "theorems/lean_replay/division-composition.lim"] = native
        products[FIXTURES / "provenance.json"] = (json.dumps(manifest, indent=2, sort_keys=True) + "\n").encode()
    for path, data in products.items():
        if path.exists() and path.read_bytes() == data:
            continue
        if args.check:
            raise ValueError(f"division composition fixture artifact differs: {path}")
        path.parent.mkdir(parents=True, exist_ok=True)
        with tempfile.NamedTemporaryFile(dir=path.parent, prefix=".division-composition-", delete=False) as handle:
            staged = Path(handle.name)
            handle.write(data)
        try:
            staged.chmod(0o644)
            staged.replace(path)
        finally:
            staged.unlink(missing_ok=True)
    print(f"{'verified' if args.check else 'generated'} {len(products)} division composition artifacts; "
          f"peak child RSS {resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss} KiB")


if __name__ == "__main__":
    main()
