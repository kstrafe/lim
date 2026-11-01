#!/usr/bin/env python3
"""Reproduce native Lim proofs from the pinned, genuine Lean export corpus.

Uses only Python's standard library and a previously built Lim executable.
Run through scripts/limited-run.sh so the compiler process tree is bounded.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parent.parent
PROVENANCE = ROOT / "tests/fixtures/lean_export/real-provenance.json"
DESTINATION = ROOT / "theorems/lean_replay"


def digest(data):
    return hashlib.sha256(data).hexdigest()


def command(lim, *arguments):
    result = subprocess.run([str(lim), *map(str, arguments)], capture_output=True,
                            timeout=30, check=False)
    if result.returncode:
        raise RuntimeError(result.stderr.decode("utf-8", errors="replace"))
    return result.stdout.decode("utf-8")


def products(lim):
    provenance_bytes = PROVENANCE.read_bytes()
    provenance = json.loads(provenance_bytes)
    entries = []
    outputs = {}
    with tempfile.TemporaryDirectory(prefix="lim-native-proof-") as directory:
        scratch = Path(directory)
        for fixture in provenance["fixtures"]:
            if fixture["expected"] != "checked":
                raise RuntimeError("genuine source fixture is not marked checked")
            source = PROVENANCE.parent / fixture["file"]
            original = source.read_bytes()
            if digest(original) != fixture["sha256"]:
                raise RuntimeError(f"pinned export changed: {source}")
            filename = source.stem.removeprefix("real-") + ".lim"
            proof = scratch / filename
            receipt_path = scratch / "receipt.json"
            command(lim, "--check-lean-export", source, fixture["target"],
                    "--emit-proof", proof, "--report", receipt_path)
            native = proof.read_bytes()
            text = native.decode("utf-8")
            match = re.search(r"^; Native theorem: ([A-Za-z0-9_-]+)$", text, re.M)
            if not match:
                raise RuntimeError("translation lacks its native theorem identity")
            target = match[1]
            command(lim, "--check-theorem", proof, target)
            receipt = json.loads(receipt_path.read_bytes())
            if receipt["input_sha256"] != fixture["sha256"] or receipt["axioms"]:
                raise RuntimeError("replay receipt does not match the pinned export")
            names = re.findall(r"^\(#(?:theorem|math-definition|math-opaque|math-inductive)\s+([A-Za-z0-9_-]+)", text, re.M)
            if len(names) != len(receipt["declarations"]) or len(set(names)) != len(names):
                raise RuntimeError("translation declaration mapping is incomplete")
            entries.append({
                "input": str(source.relative_to(ROOT)),
                "input_sha256": fixture["sha256"],
                "original_target": fixture["target"],
                "file": filename,
                "sha256": digest(native),
                "bytes": len(native),
                "native_target": target,
                "declarations": [dict(declaration, native_name=name)
                                 for declaration, name in zip(receipt["declarations"], names)],
            })
            outputs[filename] = native
    manifest = {
        "schema": "lim-lean-native-translations-v1",
        "description": "Rechecked translations of the small genuine export corpus; not the full FLT proof.",
        "provenance": str(PROVENANCE.relative_to(ROOT)),
        "provenance_sha256": digest(provenance_bytes),
        "lean_version": provenance["lean_version"],
        "lean_revision": provenance["lean_revision"],
        "exporter_revision": provenance["exporter_revision"],
        "format_version": provenance["format_version"],
        "axioms": [],
        "translations": entries,
    }
    outputs["manifest.json"] = (json.dumps(manifest, indent=2, sort_keys=True) + "\n").encode()
    return outputs


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lim", type=Path, required=True, help="previously built Lim compiler")
    parser.add_argument("--check", action="store_true", help="compare exact bytes without writing")
    args = parser.parse_args()
    generated = products(args.lim.resolve(strict=True))
    for name, expected in generated.items():
        path = DESTINATION / name
        actual = path.read_bytes() if path.exists() else None
        if actual == expected:
            continue
        if args.check:
            raise RuntimeError(f"native proof artifact is missing or stale: {path}")
        DESTINATION.mkdir(parents=True, exist_ok=True)
        # All exports and normal source checks succeeded before publication.
        with tempfile.NamedTemporaryFile(dir=DESTINATION, prefix=".native-proof-", delete=False) as handle:
            staged = Path(handle.name)
            try:
                handle.write(expected)
                os.fchmod(handle.fileno(), 0o644)
                handle.close()
                os.replace(staged, path)
            finally:
                staged.unlink(missing_ok=True)
    print(f"{'verified' if args.check else 'regenerated'} {len(generated)} native proof artifacts")


if __name__ == "__main__":
    main()
