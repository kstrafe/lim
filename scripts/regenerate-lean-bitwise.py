#!/usr/bin/env python3
"""Reproduce the genuine Lean bitwise export and checked native replay.

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
FIXTURES = ROOT / "tests/fixtures/lean_export_bitwise"
SOURCE = FIXTURES / "Source.lean"
ORIGIN = ROOT / "scripts/lean-export-private-origins.lean"
TARGETS = [f"BitwiseProbe.{name}" for name in ("and_small", "or_small", "xor_small")]
SOURCE_SHA256 = "715f897f1bca3ef9e31733e696a2ab709bcddb31c6ffb44817e8647c806e4c8e"
RAW_SHA256 = "2c469593f80363b7f60ed23b679ef2b07772214c4dd0cdc113d611fac4a0e91d"
DECLARATIONS = 385
SOURCE_PINS = {'Init.Core': '8537e234659a281a8f49cc91e2f48c17b6faeacb852d1c4ba3a09b6b5e45ab20',
 'Init.Data.Nat.Basic': '92edcd298633bc57f70cf6c9cea73a3b6f984b91b3c8cc8fcc72f57bada0ee36',
 'Init.Data.Nat.Bitwise.Basic': '0196b9eabcb97bd41b9ace0cfb828d2f0f0215085d2eb8972d2c541539c94df3',
 'Init.Data.Nat.Div.Basic': '67f894497257111dff81a5b3bab0f849cc53f31a3c62656333366ad62ab63a58',
 'Init.Prelude': '56de5780adc4358372fa9cfac270a70f2d03fd4f213a373aea4365483b31a544',
 'Init.SimpLemmas': 'fe0dc61e7380da95224dc4a7bb577a9395c5e64fbab93c62afaa2cf7883a8de5',
 'Init.WF': 'fe7c0a49de4a9c4b4fac24493f40598a1374837b17a6c334fc1ed03e23646e01'}
OWNERS = {*SOURCE_PINS, "Source"}
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
    if (report.get("axioms") != ["propext"] or report.get("target_axioms") != ["propext"] or
            report.get("foundations") != [] or report.get("target") != target or
            report.get("proof_budget") != PROOF_BUDGET):
        raise ValueError(f"unexpected raw replay inventory, selected target, or budget for {target}")
    declarations = report.get("declarations")
    if not isinstance(declarations, list) or len(declarations) != DECLARATIONS:
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

    if digest(source_bytes) != SOURCE_SHA256:
        raise ValueError("bitwise fixture source must match its pinned SHA-256")
    source_records = {}
    for module, expected in SOURCE_PINS.items():
        source_file = "src/" + module.replace(".", "/") + ".lean"
        data = (lean / "src/lean" / source_file.removeprefix("src/")).read_bytes()
        if digest(data) != expected:
            raise ValueError(f"pinned {module} source changed")
        text = data.decode("utf-8")
        if not text.startswith("/-") or "-/" not in text:
            raise ValueError(f"missing source notice for {module}")
        notice = text[2:text.index("-/")].strip()
        source_records[module] = {
            "project": "lean4", "license": "Apache-2.0", "notice": notice,
            "source": source_file, "sha256": expected,
            "url": f"https://github.com/leanprover/lean4/blob/{PINS['LEAN_REVISION']}/{source_file}",
        }
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
    with tempfile.TemporaryDirectory(prefix="lim-bitwise-export-") as temp_dir:
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
        raw_path = lean_run(["--run", "Main.lean", "Source", "--", *TARGETS], "bitwise.ndjson")
        raw = bounded(raw_path)
        proof = work / "bitwise.lim"
        receipt_path = work / "receipt.json"
        final_target = TARGETS[-1]
        checked = run_lim(lim, ["--check-lean-export", raw_path, final_target, "--lean-foundations",
                                *BUDGET_ARGS, "--emit-proof", proof, "--report", receipt_path])
        require_success(checked, "budgeted bitwise export replay")
        report = audit_report(receipt_path, final_target)
        if digest(raw) != RAW_SHA256 or digest(raw) != report.get("input_sha256"):
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
            raise ValueError("each requested bitwise target must occur once as an original theorem")
        native_targets = {}
        for target in TARGETS:
            matches = [(original, name, kind) for original, (name, kind)
                       in zip(originals, native_map) if original.get("name") == target]
            if len(matches) != 1 or matches[0][2] != "theorem":
                raise ValueError(f"native theorem map does not contain target exactly once: {target}")
            native_targets[target] = matches[0][1]

        budget_line = "proof budget: work=1000000 phase-bytes=134217728 total-bytes=1073741824"
        expected_emission = [f"checked Lean export theorem {final_target} ({len(originals)} declarations)",
                             budget_line, "declared Lean axioms: propext",
                             "target logical foundations: propext", f"emitted native theorem {native_targets[final_target]} to {proof}"]
        if checked.stdout.decode(errors="replace").splitlines() != expected_emission:
            raise ValueError("budgeted export replay receipt output differs from expected summary")

        # Check every raw target and every translated target under the same explicit budget.
        for target in TARGETS:
            target_receipt = work / f"raw-{TARGETS.index(target)}.json"
            audit = run_lim(lim, ["--check-lean-export", raw_path, target, "--lean-foundations", *BUDGET_ARGS,
                                  "--report", target_receipt])
            require_success(audit, f"raw target check {target}")
            target_report = audit_report(target_receipt, target)
            if (target_report.get("input_sha256") != digest(raw) or
                    target_report.get("declarations") != originals):
                raise ValueError(f"raw target report differs from emitted declaration inventory: {target}")
            native_check = run_lim(lim, ["--check-theorem", proof, native_targets[target], *BUDGET_ARGS])
            require_success(native_check, f"native target check {target}")
            expected_lines = [f"checked theorem {native_targets[target]}", budget_line,
                              "logical foundations: propext"]
            if native_check.stdout.decode(errors="replace").splitlines() != expected_lines:
                raise ValueError(f"native theorem check summary differs for {target}")

        # The default logical policy must not silently authorize propext.
        refusal = run_lim(lim, ["--check-lean-export", raw_path, TARGETS[0], *BUDGET_ARGS])
        refusal_text = (refusal.stderr + refusal.stdout).decode(errors="replace")
        if refusal.returncode == 0 or "not authorized" not in refusal_text:
            raise ValueError("constructive replay did not reject the explicit axiom")

        declarations = []
        for item, (native_name, native_kind) in zip(originals, native_map):
            module = owners[item["identity"]]
            if module == "Source":
                source_file = str(SOURCE.relative_to(ROOT))
                source_sha = digest(source_bytes)
                project = "lim-fixture"
            else:
                source_file = source_records[module]["source"]
                source_sha = source_records[module]["sha256"]
                project = "lean4"
            if item.get("kind") == "theorem" and native_kind != "theorem":
                raise ValueError(f"native declaration kind mismatch for {item['name']}")
            declarations.append(dict(item, native_name=native_name, module=module,
                                     source=source_file, source_sha256=source_sha, project=project))

        manifest = {
            "schema": "lim-lean-bitwise-fixture-v1", "axioms": ["propext"], "target_axioms": ["propext"],
            "target_inventories": {t: ["propext"] for t in TARGETS},
            "foundations": [], "proof_budget": PROOF_BUDGET,
            "lean_version": "4.33.1", "lean_revision": PINS["LEAN_REVISION"],
            "exporter_revision": PINS["EXPORTER_REVISION"],
            "exporter_source_sha256": PINS["EXPORTER_FILES"], "format_version": "3.1.0",
            "source": {"file": str(SOURCE.relative_to(ROOT)), "sha256": digest(source_bytes)},
            "producer": {"file": str(Path(__file__).relative_to(ROOT)),
                         "sha256": digest(Path(__file__).read_bytes())},
            "origin_reader": {"file": str(ORIGIN.relative_to(ROOT)), "sha256": digest(ORIGIN.read_bytes())},
            "upstream_sources": list(source_records.values()), "licenses": licenses,
            "export": {"file": str((FIXTURES / "bitwise.ndjson").relative_to(ROOT)),
                       "sha256": digest(raw), "bytes": len(raw)},
            "native": {"file": "theorems/lean_replay/bitwise.lim",
                       "sha256": digest(native), "bytes": len(native), "targets": native_targets},
            "targets": TARGETS, "declarations": declarations,
        }
        products[FIXTURES / "bitwise.ndjson"] = raw
        products[ROOT / "theorems/lean_replay/bitwise.lim"] = native
        products[FIXTURES / "provenance.json"] = (json.dumps(manifest, indent=2, sort_keys=True) + "\n").encode()

    differences = [path for path, data in products.items()
                  if not path.is_file() or path.read_bytes() != data]
    if args.check:
        if differences:
            raise ValueError("bitwise fixture artifacts differ: " + ", ".join(str(p.relative_to(ROOT)) for p in differences))
        print(f"verified exact reproduction of {len(products)} bitwise artifacts")
        return
    for path, data in products.items():
        if path.is_file() and path.read_bytes() == data:
            continue
        path.parent.mkdir(parents=True, exist_ok=True)
        with tempfile.NamedTemporaryFile(dir=path.parent, prefix=".bitwise-", delete=False) as handle:
            staged = Path(handle.name)
            handle.write(data)
        try:
            staged.chmod(0o644)
            staged.replace(path)
        finally:
            staged.unlink(missing_ok=True)
    print(f"generated {len(products)} bitwise artifacts; peak child RSS "
          f"{resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss} KiB")


if __name__ == "__main__":
    try:
        main()
    except (OSError, subprocess.TimeoutExpired, ValueError, KeyError, StopIteration) as error:
        raise SystemExit(f"regenerate-lean-bitwise: {error}")
