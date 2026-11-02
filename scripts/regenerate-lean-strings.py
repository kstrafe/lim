#!/usr/bin/env python3
"""Reproduce the genuine Lean string-literal export and checked native replay.

Run under scripts/limited-run.sh. Requires the already pinned Lean,
lean4export, and Lim executable; this script never downloads tools.
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
FIXTURES = ROOT / "tests/fixtures/lean_export_strings"
SOURCE = FIXTURES / "Source.lean"
ORIGIN = ROOT / "scripts/lean-export-private-origins.lean"
TARGETS = [f"StringLiteralProbe.{name}" for name in
           ("empty", "ascii", "unicode", "nul", "balanced")]
OWNERS = {"Init.Prelude", "Source"}
PROOF_BUDGET = {"work_per_phase": 1_000_000,
                "transformation_bytes_per_phase": 134_217_728,
                "transformation_bytes_total": 1_073_741_824}
BUDGET_ARGS = ["--proof-work", str(PROOF_BUDGET["work_per_phase"]),
               "--proof-phase-bytes", str(PROOF_BUDGET["transformation_bytes_per_phase"]),
               "--proof-total-bytes", str(PROOF_BUDGET["transformation_bytes_total"])]
OUTPUT_LIMIT = 8 * 1024 * 1024


def digest(data):
    return hashlib.sha256(data).hexdigest()


def bounded(path):
    size = path.stat().st_size
    if size > OUTPUT_LIMIT:
        raise ValueError(f"producer output exceeds 8 MiB: {path.name}")
    return path.read_bytes()


def run_process(argv, *, timeout, output=None, cwd=None, env=None):
    if output is None:
        result = subprocess.run(argv, capture_output=True, timeout=timeout,
                                check=False, cwd=cwd, env=env)
        if result.returncode:
            detail = (result.stderr or result.stdout)[:4096].decode(errors="replace")
            raise ValueError(f"command failed ({result.returncode}): {detail.strip()}")
        return result
    with output.open("wb") as handle:
        result = subprocess.run(argv, cwd=cwd, env=env, stdout=handle,
                                stderr=subprocess.STDOUT, timeout=timeout, check=False)
    if output.stat().st_size > OUTPUT_LIMIT:
        raise ValueError(f"producer output exceeds 8 MiB: {output.name}")
    if result.returncode:
        excerpt = output.read_bytes()[:4096].decode(errors="replace")
        raise ValueError(f"Lean command failed ({result.returncode}): {excerpt.strip()}")
    return output


def native_declarations(data):
    pattern = re.compile(
        rb"^\(#(theorem|math-definition|math-opaque|math-inductive)\s+([A-Za-z0-9_-]+)", re.M)
    kinds = {"theorem": "theorem", "math-definition": "definition",
             "math-opaque": "opaque", "math-inductive": "inductive"}
    return [(match.group(2).decode(), kinds[match.group(1).decode()])
            for match in pattern.finditer(data)]


def run_lim(lim, args, *, timeout=120):
    return subprocess.run([str(lim), *map(str, args)], capture_output=True,
                          timeout=timeout, check=False)


def require_success(result, label):
    if result.returncode:
        detail = (result.stderr or result.stdout)[:4096].decode(errors="replace")
        raise ValueError(f"{label} failed ({result.returncode}): {detail.strip()}")


def audit_report(path, target):
    report = json.loads(path.read_bytes())
    if (report.get("axioms") != [] or report.get("target_axioms") != [] or
            report.get("foundations") != [] or report.get("target") != target or
            report.get("proof_budget") != PROOF_BUDGET):
        raise ValueError(f"unexpected raw replay inventory, selected target, or budget for {target}")
    declarations = report.get("declarations")
    if not isinstance(declarations, list) or not declarations:
        raise ValueError("raw replay report has no declarations")
    identities = [item.get("identity") for item in declarations]
    if any(not isinstance(name, str) for name in identities) or len(set(identities)) != len(identities):
        raise ValueError("raw declaration identities are missing or duplicated")
    matches = [item for item in declarations if item.get("name") == target]
    if len(matches) != 1 or matches[0].get("kind") != "theorem":
        raise ValueError(f"raw target is not exactly one original theorem: {target}")
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-root", type=Path, required=True)
    parser.add_argument("--exporter-dir", type=Path, required=True)
    parser.add_argument("--lim", type=Path, required=True)
    parser.add_argument("--loader", type=Path)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()

    lean, exporter, lim = (item.resolve(strict=True) for item in
                           (args.lean_root, args.exporter_dir, args.lim))
    source_bytes = SOURCE.read_bytes()
    for filename, expected in PINS["EXPORTER_FILES"].items():
        if digest((exporter / filename).read_bytes()) != expected:
            raise ValueError(f"pinned exporter source mismatch: {filename}")
    executable = [str(lean / "bin/lean")]
    if args.loader:
        executable.insert(0, str(args.loader.resolve(strict=True)))
    environment = dict(os.environ, LEAN_SYSROOT=str(lean))
    version = run_process([*executable, "--version"], timeout=30)
    version_text = (version.stdout + version.stderr).decode(errors="replace")
    if "version 4.33.1," not in version_text or PINS["LEAN_REVISION"] not in version_text:
        raise ValueError("expected the pinned Lean 4.33.1 release")

    prior = json.loads((ROOT / "tests/fixtures/lean_export/real-provenance.json").read_bytes())
    prelude_pin = next(row for row in prior["upstream_sources"]
                       if row["source"] == "src/Init/Prelude.lean")
    prelude = lean / "src/lean/Init/Prelude.lean"
    if digest(prelude.read_bytes()) != prelude_pin["sha256"]:
        raise ValueError("pinned Init.Prelude source changed")
    for project, original, kept in (
            ("lean4", lean / "LICENSE", ROOT / "tests/fixtures/lean_export/LEAN-LICENSE.txt"),
            ("lean4export", exporter / "LICENSE", ROOT / "tests/fixtures/lean_export/EXPORTER-LICENSE.txt")):
        if original.read_bytes() != kept.read_bytes():
            raise ValueError(f"preserved {project} license differs from the pinned tool")
    licenses = [{"project": project, "license": "Apache-2.0",
                 "file": str(kept.relative_to(ROOT)), "sha256": digest(kept.read_bytes())}
                for project, _, kept in (
                    ("lean4", lean / "LICENSE", ROOT / "tests/fixtures/lean_export/LEAN-LICENSE.txt"),
                    ("lean4export", exporter / "LICENSE", ROOT / "tests/fixtures/lean_export/EXPORTER-LICENSE.txt"))]

    products = {}
    with tempfile.TemporaryDirectory(prefix="lim-strings-export-") as temp_dir:
        work = Path(temp_dir)
        environment["LEAN_PATH"] = f"{work}:{lean}/lib/lean"
        for filename in ("Export.lean", "Main.lean"):
            shutil.copyfile(exporter / filename, work / filename)
        shutil.copyfile(SOURCE, work / "Source.lean")
        shutil.copyfile(ORIGIN, work / "Origins.lean")

        def lean_run(argv, output_name):
            return run_process([*executable, "-j1", *argv], timeout=120,
                               output=work / output_name, cwd=work, env=environment)

        for module in ("Export", "Main", "Source"):
            lean_run(["-o", f"{module}.olean", f"{module}.lean"], f"{module}.log")
        raw_path = lean_run(["--run", "Main.lean", "Source", "--", *TARGETS], "strings.ndjson")
        raw = bounded(raw_path)
        proof = work / "strings.lim"
        receipt_path = work / "receipt.json"
        final_target = TARGETS[-1]
        checked = run_lim(lim, ["--check-lean-export", raw_path, final_target,
                                *BUDGET_ARGS, "--emit-proof", proof, "--report", receipt_path])
        require_success(checked, "budgeted string export replay")
        report = audit_report(receipt_path, final_target)
        if digest(raw) != report.get("input_sha256"):
            raise ValueError("raw export hash differs from replay receipt")

        originals = report["declarations"]
        origin_path = lean_run(["--run", "Origins.lean",
                                *[item["identity"] for item in originals]], "origins.jsonl")
        origin_rows = [json.loads(line) for line in bounded(origin_path).splitlines()]
        owners = {}
        for row in origin_rows:
            identity = row.get("identity")
            if identity in owners:
                raise ValueError("private source ownership returned a duplicate identity")
            owners[identity] = row.get("module")
        if len(owners) != len(originals) or set(owners) != {item["identity"] for item in originals}:
            raise ValueError("private source ownership does not map each declaration exactly once")
        if set(owners.values()) != OWNERS:
            raise ValueError(f"private source owner set differs: {sorted(set(owners.values()))}")

        native = bounded(proof)
        native_map = native_declarations(native)
        if len(native_map) != len(originals) or len({name for name, _ in native_map}) != len(native_map):
            raise ValueError("native declaration mapping is incomplete or non-unique")
        targets_in_report = {target: [item for item in originals if item.get("name") == target]
                             for target in TARGETS}
        if any(len(matches) != 1 or matches[0].get("kind") != "theorem"
               for matches in targets_in_report.values()):
            raise ValueError("each requested string target must occur once as an original theorem")
        native_targets = {}
        for target in TARGETS:
            matches = [(original, name, kind) for original, (name, kind)
                       in zip(originals, native_map) if original.get("name") == target]
            if len(matches) != 1 or matches[0][2] != "theorem":
                raise ValueError(f"native theorem map does not contain target exactly once: {target}")
            native_targets[target] = matches[0][1]

        budget_line = "proof budget: work=1000000 phase-bytes=134217728 total-bytes=1073741824"
        expected_emission = [f"checked Lean export theorem {final_target} ({len(originals)} declarations)",
                             budget_line, f"emitted native theorem {native_targets[final_target]} to {proof}"]
        if checked.stdout.decode(errors="replace").splitlines() != expected_emission:
            raise ValueError("budgeted export replay receipt output differs from expected summary")

        # Check every raw target and every translated target under the same explicit budget.
        for target in TARGETS:
            target_receipt = work / f"raw-{TARGETS.index(target)}.json"
            audit = run_lim(lim, ["--check-lean-export", raw_path, target, *BUDGET_ARGS,
                                  "--report", target_receipt])
            require_success(audit, f"raw target check {target}")
            target_report = audit_report(target_receipt, target)
            if (target_report.get("input_sha256") != digest(raw) or
                    target_report.get("declarations") != originals):
                raise ValueError(f"raw target report differs from emitted declaration inventory: {target}")
            native_check = run_lim(lim, ["--check-theorem", proof, native_targets[target], *BUDGET_ARGS])
            require_success(native_check, f"native target check {target}")
            expected_lines = [f"checked theorem {native_targets[target]}", budget_line]
            if native_check.stdout.decode(errors="replace").splitlines() != expected_lines:
                raise ValueError(f"native theorem check summary differs for {target}")

        # The unchanged default budget is expected to refuse before any literal target succeeds.
        refusal = run_lim(lim, ["--check-lean-export", raw_path, TARGETS[0]])
        refusal_text = (refusal.stderr + refusal.stdout).decode(errors="replace")
        if refusal.returncode == 0 or "resource limit" not in refusal_text or "Char.ofNat._proof_2" not in refusal_text:
            excerpt = refusal_text[:1000]
            raise ValueError(f"default-budget replay did not report the expected resource refusal: {excerpt}")

        declarations = []
        for item, (native_name, native_kind) in zip(originals, native_map):
            module = owners[item["identity"]]
            if module == "Source":
                source_file = str(SOURCE.relative_to(ROOT))
                source_sha = digest(source_bytes)
                project = "lim-fixture"
            else:
                source_file = "src/Init/Prelude.lean"
                source_sha = prelude_pin["sha256"]
                project = "lean4"
            if item.get("kind") == "theorem" and native_kind != "theorem":
                raise ValueError(f"native declaration kind mismatch for {item['name']}")
            declarations.append(dict(item, native_name=native_name, module=module,
                                     source=source_file, source_sha256=source_sha, project=project))

        manifest = {
            "schema": "lim-lean-strings-fixture-v1", "axioms": [], "target_axioms": [],
            "target_inventories": {t: [] for t in TARGETS},
            "foundations": [], "proof_budget": PROOF_BUDGET,
            "lean_version": "4.33.1", "lean_revision": PINS["LEAN_REVISION"],
            "exporter_revision": PINS["EXPORTER_REVISION"],
            "exporter_source_sha256": PINS["EXPORTER_FILES"], "format_version": "3.1.0",
            "source": {"file": str(SOURCE.relative_to(ROOT)), "sha256": digest(source_bytes)},
            "producer": {"file": str(Path(__file__).relative_to(ROOT)),
                         "sha256": digest(Path(__file__).read_bytes())},
            "origin_reader": {"file": str(ORIGIN.relative_to(ROOT)), "sha256": digest(ORIGIN.read_bytes())},
            "upstream_sources": [prelude_pin], "licenses": licenses,
            "export": {"file": str((FIXTURES / "strings.ndjson").relative_to(ROOT)),
                       "sha256": digest(raw), "bytes": len(raw)},
            "native": {"file": "theorems/lean_replay/strings.lim",
                       "sha256": digest(native), "bytes": len(native), "targets": native_targets},
            "targets": TARGETS, "declarations": declarations,
            "resource_refusal": {"default_work_budget": "resource limit", "declaration": "Char.ofNat._proof_2"},
        }
        products[FIXTURES / "strings.ndjson"] = raw
        products[ROOT / "theorems/lean_replay/strings.lim"] = native
        products[FIXTURES / "provenance.json"] = (json.dumps(manifest, indent=2, sort_keys=True) + "\n").encode()

    differences = [path for path, data in products.items()
                  if not path.is_file() or path.read_bytes() != data]
    if args.check:
        if differences:
            raise ValueError("string fixture artifacts differ: " + ", ".join(str(p.relative_to(ROOT)) for p in differences))
        print(f"verified exact reproduction of {len(products)} string artifacts")
        return
    for path, data in products.items():
        if path.is_file() and path.read_bytes() == data:
            continue
        path.parent.mkdir(parents=True, exist_ok=True)
        with tempfile.NamedTemporaryFile(dir=path.parent, prefix=".strings-", delete=False) as handle:
            staged = Path(handle.name)
            handle.write(data)
        try:
            staged.chmod(0o644)
            staged.replace(path)
        finally:
            staged.unlink(missing_ok=True)
    print(f"generated {len(products)} string artifacts; peak child RSS "
          f"{resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss} KiB")


if __name__ == "__main__":
    try:
        main()
    except (OSError, subprocess.TimeoutExpired, ValueError, KeyError, StopIteration) as error:
        raise SystemExit(f"regenerate-lean-strings: {error}")
