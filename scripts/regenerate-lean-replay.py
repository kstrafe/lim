#!/usr/bin/env python3
"""Regenerate small genuine Lean exports; never downloads a toolchain.

Run under scripts/limited-run.sh. Lean and lean4export are fixture-production
tools only: Lim's Rust replay reader does not invoke or trust either program.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import resource
import shutil
import subprocess
import tempfile


REPOSITORY = Path(__file__).resolve().parent.parent
LEAN_REVISION = "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
EXPORTER_REVISION = "15f6055e299ad5b89345e533cc2192f4cc00f659"
EXPORTER_FILES = {
    "Export.lean": "1c60d571dc24bfb99e7cbb218d8d489919bbc871238f6db9c76248521fbea998",
    "Main.lean": "bd8e350903f1382b25fe767f9086dd9882000f01085f7046ea06545e7848842a",
    "LICENSE": "c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4",
}
TARGETS = {
    "identity": ("ReplaySource.identityProof", "checked"),
    "inductives": ("ReplaySource.doubleTwo", "checked"),
    "projection": ("ReplaySource.projection", "checked"),
    "mutual": ("ReplaySource.mutualDepth", "checked"),
    "nested": ("ReplaySource.nestedLeaf", "unsupported-nested-inductive"),
}


def digest(path):
    with path.open("rb") as source:
        return hashlib.file_digest(source, "sha256").hexdigest()


def bounded_file(path, limit=8 * 1024 * 1024):
    if path.stat().st_size > limit:
        raise ValueError(f"output exceeds {limit} bytes: {path}")
    return path.read_bytes()


def declaration_names(path):
    """Recover producer names and declaration kinds, without claiming a check."""
    names = [""]
    simple_names = [True]
    declarations = []
    def declaration_name(index):
        if not simple_names[index]:
            raise ValueError("fixture origin lookup requires simple declaration names")
        return names[index]

    for line in bounded_file(path).splitlines():
        record = json.loads(line)
        if "in" in record:
            component = record.get("str", record.get("num"))
            if component is None or record["in"] != len(names):
                raise ValueError("fixture provenance requires contiguous interned names")
            segment = component.get("str", str(component.get("i")))
            prefix = names[component["pre"]]
            names.append(f"{prefix}.{segment}" if prefix else segment)
            simple_names.append(simple_names[component["pre"]] and "str" in component
                                and bool(segment) and all(c.isalnum() or c in "_'" for c in segment))
        elif "inductive" in record:
            for key, kind in [("types", "inductive"), ("ctors", "constructor"), ("recs", "recursor")]:
                declarations.extend((declaration_name(item["name"]), kind) for item in record["inductive"][key])
        else:
            for tag, kind in [("def", "definition"), ("thm", "theorem"), ("opaque", "opaque")]:
                if tag in record:
                    declarations.append((declaration_name(record[tag]["name"]), kind))
            if "axiom" in record or "quot" in record:
                raise ValueError("fixture unexpectedly acquired an axiom or quotient dependency")
    return declarations


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-root", type=Path, required=True)
    parser.add_argument("--exporter-dir", type=Path, required=True)
    parser.add_argument("--loader", type=Path, help="optional ELF loader for NixOS")
    parser.add_argument("--output", type=Path, default=REPOSITORY / "tests/fixtures/lean_export")
    parser.add_argument("--check", action="store_true", help="verify reproduction without publishing files")
    arguments = parser.parse_args()
    lean_root = arguments.lean_root.resolve()
    exporter = arguments.exporter_dir.resolve()
    destination = arguments.output.resolve()
    for name, expected in EXPORTER_FILES.items():
        if digest(exporter / name) != expected:
            raise ValueError(f"pinned exporter source hash mismatch: {name}")
    executable = [str(lean_root / "bin/lean")]
    if arguments.loader:
        executable.insert(0, str(arguments.loader.resolve()))
    environment = dict(os.environ, LEAN_SYSROOT=str(lean_root))
    version = subprocess.check_output([*executable, "--version"], env=environment, timeout=30, text=True)
    if "version 4.33.1," not in version or LEAN_REVISION not in version:
        raise ValueError("expected the pinned Lean 4.33.1 release")

    source_path = REPOSITORY / "tests/fixtures/lean_export/Source.lean"
    checks_path = REPOSITORY / "tests/fixtures/lean_export/NestedChecks.lean"
    origin_path = REPOSITORY / "scripts/lean-export-origins.lean"
    products = {}
    source_notices = {}
    with tempfile.TemporaryDirectory(prefix="lim-lean-export-") as directory:
        work = Path(directory)
        environment["LEAN_PATH"] = f"{work}:{lean_root}/lib/lean"
        for name in ["Export.lean", "Main.lean"]:
            shutil.copyfile(exporter / name, work / name)
        shutil.copyfile(source_path, work / "Source.lean")
        shutil.copyfile(checks_path, work / "NestedChecks.lean")
        shutil.copyfile(origin_path, work / "Origins.lean")

        def run(operands, output_name):
            path = work / output_name
            with path.open("wb") as output:
                result = subprocess.run([*executable, "-j1", *operands], cwd=work, env=environment,
                                        stdout=output, stderr=subprocess.STDOUT, timeout=120)
            if result.returncode:
                with path.open("rb") as output:
                    print(output.read(8192).decode(errors="replace"))
                result.check_returncode()
            return path

        # Lean counts mapped imported environments toward its internal -M
        # budget. The caller's cgroup bounds actual memory and CPU instead.
        run(["-o", "Export.olean", "Export.lean"], "compile-export.log")
        run(["-o", "Source.olean", "Source.lean"], "compile-source.log")
        run(["-o", "NestedChecks.olean", "NestedChecks.lean"], "nested-checks.log")
        fixture_records = []
        for label, (target, outcome) in TARGETS.items():
            filename = f"real-{label}.ndjson"
            artifact = run(["--run", "Main.lean", "Source", "--", target], filename)
            data = bounded_file(artifact)
            declarations = declaration_names(artifact)
            origin_output = run(["--run", "Origins.lean", *[name for name, _ in declarations]],
                                f"origins-{label}.jsonl")
            origins = {row["declaration"]: row["module"]
                       for row in map(json.loads, bounded_file(origin_output).splitlines())}
            if len(origins) != len(declarations):
                raise ValueError("source module map does not cover every exported declaration")
            entries = []
            for name, kind in declarations:
                module = origins[name]
                if module == "Source":
                    project, source_file = "lim-fixture", "Source.lean"
                    source_hash = digest(source_path)
                else:
                    project = "lean4"
                    source_file = "src/" + module.replace(".", "/") + ".lean"
                    original = lean_root / "src/lean" / (module.replace(".", "/") + ".lean")
                    source_hash = digest(original)
                    text = bounded_file(original).decode()
                    if not text.startswith("/-") or "-/" not in text:
                        raise ValueError(f"expected upstream license notice: {source_file}")
                    source_notices[source_file] = {
                        "project": "lean4", "source": source_file, "sha256": source_hash,
                        "license": "Apache-2.0", "notice": text[2:text.index("-/")].strip(),
                        "url": f"https://github.com/leanprover/lean4/blob/{LEAN_REVISION}/{source_file}",
                    }
                entries.append({"name": name, "kind": kind, "project": project,
                                "module": module, "source": source_file, "source_sha256": source_hash})
            fixture_records.append({"file": filename, "sha256": digest(artifact),
                                    "bytes": len(data), "target": target, "expected": outcome,
                                    "declarations": entries})
            products[filename] = data

    lean_license = lean_root / "LICENSE"
    products["LEAN-LICENSE.txt"] = bounded_file(lean_license)
    products["EXPORTER-LICENSE.txt"] = bounded_file(exporter / "LICENSE")
    manifest = {
        "schema": "lim-lean-fixtures-v1",
        "description": "Actual elaborated exports of original small fixtures; not the FLT proof.",
        "format_version": "3.1.0", "lean_version": "4.33.1", "lean_revision": LEAN_REVISION,
        "exporter_revision": EXPORTER_REVISION, "exporter_source_sha256": EXPORTER_FILES,
        "fixture_source": {"file": "Source.lean", "sha256": digest(source_path),
                           "license": "Apache-2.0", "copyright": "2026 Lim contributors"},
        "producer_checks": {"file": "NestedChecks.lean", "sha256": digest(checks_path)},
        "origin_reader": {"file": "../../../scripts/lean-export-origins.lean", "sha256": digest(origin_path)},
        "projects": [
            {"id": "lean4", "repository": "https://github.com/leanprover/lean4",
             "revision": LEAN_REVISION, "license": "Apache-2.0",
             "license_file": "LEAN-LICENSE.txt", "license_sha256": digest(lean_license)},
            {"id": "lean4export", "repository": "https://github.com/leanprover/lean4export",
             "revision": EXPORTER_REVISION, "license": "Apache-2.0",
             "license_file": "EXPORTER-LICENSE.txt", "license_sha256": digest(exporter / "LICENSE")},
        ],
        "upstream_sources": [source_notices[name] for name in sorted(source_notices)],
        "axioms": [], "fixtures": fixture_records,
    }
    products["real-provenance.json"] = (json.dumps(manifest, indent=2, sort_keys=True) + "\n").encode()
    if arguments.check:
        differences = [name for name, data in products.items()
                       if not (destination / name).is_file() or (destination / name).read_bytes() != data]
        if differences:
            raise ValueError("regenerated artifacts differ: " + ", ".join(differences))
        print(f"verified exact reproduction of {len(products)} files")
        return
    destination.mkdir(parents=True, exist_ok=True)
    for filename, data in products.items():
        path = destination / filename
        if not path.exists() or path.read_bytes() != data:
            with tempfile.NamedTemporaryFile(dir=destination, delete=False) as output:
                temporary = Path(output.name)
                output.write(data)
            try:
                temporary.chmod(0o644)
                temporary.replace(path)
            finally:
                temporary.unlink(missing_ok=True)
    print(f"generated {len(TARGETS)} fixtures; peak child RSS {resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss} KiB")


if __name__ == "__main__":
    main()
