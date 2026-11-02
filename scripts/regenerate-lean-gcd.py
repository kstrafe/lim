#!/usr/bin/env python3
"""Reproduce the three-target pinned generic Nat.gcd replay fixture."""
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
FIXTURES = ROOT / "tests/fixtures/lean_export_gcd"
SOURCE = FIXTURES / "Source.lean"
ORIGIN = ROOT / "scripts/lean-export-private-origins.lean"
TARGETS = ["GcdSource.zeroLeft", "GcdSource.successor", "GcdSource.zeroRight"]
TARGET_AXIOMS = {TARGETS[0]: ["Quot.sound"], TARGETS[1]: ["Quot.sound"],
                 TARGETS[2]: ["Quot.sound", "propext"]}
OWNERS = {"Init.Core", "Init.Data.Nat.Basic", "Init.Data.Nat.Gcd",
          "Init.Prelude", "Init.SimpLemmas", "Init.WF", "Source"}

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
    expected_source = ("import Init.Data.Nat.Gcd\nnamespace GcdSource\n"
        "theorem zeroLeft (n : Nat) : Nat.gcd 0 n = n := Nat.gcd_zero_left n\n"
        "theorem successor (x y : Nat) : Nat.gcd (Nat.succ x) y = Nat.gcd (y % Nat.succ x) (Nat.succ x) := Nat.gcd_succ x y\n"
        "theorem zeroRight (n : Nat) : Nat.gcd n 0 = n := Nat.gcd_zero_right n\n"
        "end GcdSource\n").encode()
    if source_bytes != expected_source:
        raise ValueError("GCD fixture source must match its pinned exact text")
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
    # Reuse exactly the five source pins already established by the adjacent fixture.
    old = json.loads((ROOT / "tests/fixtures/lean_export_well_founded/provenance.json").read_bytes())
    source_records = {module: next(x for x in old["upstream_sources"] if x["source"] == src)
        for module,src in {"Init.Core":"src/Init/Core.lean","Init.Data.Nat.Basic":"src/Init/Data/Nat/Basic.lean",
            "Init.Prelude":"src/Init/Prelude.lean","Init.SimpLemmas":"src/Init/SimpLemmas.lean",
            "Init.WF":"src/Init/WF.lean"}.items()}
    for module,rec in source_records.items():
        if digest((lean/"src/lean"/rec["source"].removeprefix("src/")).read_bytes()) != rec["sha256"]:
            raise ValueError(f"pinned {module} source changed")
    gcd_pin = {"project":"lean4", "source":"src/Init/Data/Nat/Gcd.lean",
        "sha256":"672c96102205b59a47742be74c959ed780ba319713baaa8a2eeede2cdc46cbea",
        "url":f"https://github.com/leanprover/lean4/blob/{PINS['LEAN_REVISION']}/src/Init/Data/Nat/Gcd.lean",
        "license":"Apache-2.0", "notice":"Copyright (c) 2021 Microsoft Corporation. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Markus Himmel"}
    gcd_file = lean / "src/lean/Init/Data/Nat/Gcd.lean"
    if digest(gcd_file.read_bytes()) != gcd_pin["sha256"] or len(gcd_file.read_bytes()) != 20329:
        raise ValueError("pinned Init.Data.Nat.Gcd source mismatch")
    source_records["Init.Data.Nat.Gcd"] = gcd_pin
    if set(source_records) != OWNERS - {"Source"}:
        raise ValueError("could not recover all five prior upstream source pins")
    licenses=[]
    for project, original, kept in [("lean4",lean/"LICENSE",ROOT/"tests/fixtures/lean_export/LEAN-LICENSE.txt"),
                                    ("lean4export",exporter/"LICENSE",ROOT/"tests/fixtures/lean_export/EXPORTER-LICENSE.txt")]:
        if original.read_bytes()!=kept.read_bytes(): raise ValueError(f"preserved {project} license mismatch")
        licenses.append({"project":project,"license":"Apache-2.0","file":str(kept.relative_to(ROOT)),"sha256":digest(kept.read_bytes())})
    products={}
    with tempfile.TemporaryDirectory(prefix="lim-gcd-export-") as td:
        w=Path(td); env["LEAN_PATH"]=f"{w}:{lean}/lib/lean"
        for f in ("Export.lean","Main.lean"): shutil.copyfile(exporter/f,w/f)
        shutil.copyfile(SOURCE,w/"Source.lean"); shutil.copyfile(ORIGIN,w/"Origins.lean")
        def lean_run(argv,out):
            p=w/out
            with p.open("wb") as h: r=subprocess.run([*executable,"-j1",*argv],cwd=w,env=env,stdout=h,stderr=subprocess.STDOUT,timeout=120)
            if r.returncode: raise ValueError(p.read_text(errors="replace"))
            if p.stat().st_size>8*1024*1024: raise ValueError("producer output too large")
            return p
        for mod in ("Export","Main","Source"): lean_run(["-o",f"{mod}.olean",f"{mod}.lean"],f"{mod}.log")
        raw_path=lean_run(["--run","Main.lean","Source","--",*TARGETS],"gcd.ndjson")
        proof=w/"gcd.lim"
        final_target=TARGETS[-1]
        raw_check=subprocess.run([str(lim),"--check-lean-export",str(raw_path),final_target,"--lean-foundations","--emit-proof",str(proof),"--report",str(w/"receipt.json")],capture_output=True,timeout=60)
        if raw_check.returncode: raise ValueError(raw_check.stderr.decode(errors="replace"))
        report=json.loads((w/"receipt.json").read_bytes())
        if report["axioms"] != ["Quot.sound", "propext"] or report["target_axioms"] != TARGET_AXIOMS[final_target] or report["foundations"] != ["quotient-computation-v1"] or len(report["declarations"]) != 284:
            raise ValueError("unexpected fixture axiom/foundation inventory")
        originals=report["declarations"]
        names=[x["identity"] for x in originals]
        origin=lean_run(["--run","Origins.lean",*names],"origins.jsonl")
        owners={x["identity"]:x["module"] for x in map(json.loads,origin.read_text().splitlines())}
        native=proof.read_bytes(); decoded=native.decode()
        native_names=re.findall(r"^\(#(?:theorem|math-definition|math-opaque|math-inductive)\s+([A-Za-z0-9_-]+)",decoded,re.M)
        if len(native_names)!=len(originals) or len(native_names)!=len(set(native_names)): raise ValueError("native declaration mapping is incomplete or not unique")
        native_targets={target:next((n for item,n in zip(originals,native_names)
            if item["name"]==target),None) for target in TARGETS}
        if any(name is None for name in native_targets.values()): raise ValueError("native mapping misses a requested target")
        emission_lines=raw_check.stdout.decode().splitlines()
        expected_emission=[f"checked Lean export theorem {final_target} (284 declarations)",
            "declared Lean axioms: Quot.sound, propext",
            "target logical foundations: Quot.sound, propext",
            f"emitted native theorem {native_targets[final_target]} to {proof}"]
        if emission_lines != expected_emission:
            raise ValueError(f"final raw export stdout mismatch: {emission_lines}")
        if set(owners.values()) != OWNERS:
            raise ValueError(f"private source owner set differs: {sorted(set(owners.values()))}")
        # The target selectors all replay the same 284-declaration export. Only the
        # final target emits the shared native file above.
        for target in TARGETS:
            expected=TARGET_AXIOMS[target]
            raw_audit=subprocess.run([str(lim),"--check-lean-export",str(raw_path),target,"--lean-foundations","--report",str(w/(target.rsplit('.',1)[-1]+".json"))],capture_output=True,timeout=60)
            raw_lines=raw_audit.stdout.decode().splitlines()
            expected_raw=[f"checked Lean export theorem {target} (284 declarations)",
                "declared Lean axioms: Quot.sound, propext",
                "target logical foundations: "+", ".join(expected)]
            if raw_audit.returncode or raw_lines != expected_raw:
                raise ValueError(f"raw target audit mismatch for {target}: {raw_lines}; {raw_audit.stderr.decode(errors='replace')}")
            target_report=json.loads((w/(target.rsplit('.',1)[-1]+".json")).read_bytes())
            if target_report["axioms"] != ["Quot.sound","propext"] or target_report["target_axioms"] != expected or target_report["foundations"] != ["quotient-computation-v1"] or len(target_report["declarations"]) != 284:
                raise ValueError(f"raw target basis mismatch: {target}")
            native_target=native_targets[target]
            checked=subprocess.run([str(lim),"--check-theorem",str(proof),native_target],capture_output=True,timeout=60)
            native_lines=checked.stdout.decode().splitlines()
            expected_native=[f"checked theorem {native_target}","logical foundations: "+", ".join(expected)]
            if checked.returncode or native_lines != expected_native:
                raise ValueError(f"native target audit mismatch for {target}: {native_lines}; {checked.stderr.decode(errors='replace')}")
        refusal=subprocess.run([str(lim),"--check-lean-export",str(raw_path),final_target],capture_output=True,timeout=60)
        if refusal.returncode==0 or b"axioms are not authorized" not in refusal.stderr: raise ValueError("default raw replay must refuse the declared axioms")
        declarations=[]
        # Match native headers to checked declarations in their source order.
        for item,native_decl in zip(originals,native_names):
            identity=item["identity"]; owner=owners.get(identity)
            if owner not in OWNERS: raise ValueError(f"unexpected private owner {owner!r}")
            declarations.append(dict(item,native_name=native_decl,module=owner,
                project="lim-fixture" if owner=="Source" else "lean4",
                source=str(SOURCE.relative_to(ROOT)) if owner=="Source" else source_records[owner]["source"],
                source_sha256=digest(source_bytes) if owner=="Source" else source_records[owner]["sha256"]))
        raw=raw_path.read_bytes()
        if digest(raw) != report["input_sha256"]:
            raise ValueError("raw input hash differs from the checked receipt")
        manifest={"schema":"lim-lean-gcd-fixture-v1","axioms":report["axioms"],"target_axioms":report["target_axioms"],
            "foundations":["quotient-computation-v1"],"lean_version":"4.33.1","lean_revision":PINS["LEAN_REVISION"],
            "exporter_revision":PINS["EXPORTER_REVISION"],"exporter_source_sha256":PINS["EXPORTER_FILES"],"format_version":"3.1.0",
            "source":{"file":str(SOURCE.relative_to(ROOT)),"sha256":digest(source_bytes)},
            "producer":{"file":str(Path(__file__).relative_to(ROOT)),"sha256":digest(Path(__file__).read_bytes())},
            "origin_reader":{"file":str(ORIGIN.relative_to(ROOT)),"sha256":digest(ORIGIN.read_bytes())},
            "upstream_sources":list(source_records.values()),"licenses":licenses,
            "export":{"file":str((FIXTURES/"gcd.ndjson").relative_to(ROOT)),"sha256":digest(raw),"bytes":len(raw)},
            "native":{"file":"theorems/lean_replay/gcd.lim","sha256":digest(native),"bytes":len(native),"targets":native_targets},
            "targets":TARGETS,"target_inventories":TARGET_AXIOMS,"declarations":declarations}
        products[FIXTURES/"gcd.ndjson"]=raw; products[ROOT/"theorems/lean_replay/gcd.lim"]=native
        products[FIXTURES/"provenance.json"]=(json.dumps(manifest,indent=2,sort_keys=True)+"\n").encode()
    for path,data in products.items():
        if path.exists() and path.read_bytes()==data: continue
        if args.check: raise ValueError(f"GCD fixture artifact differs: {path}")
        path.parent.mkdir(parents=True,exist_ok=True)
        with tempfile.NamedTemporaryFile(dir=path.parent,prefix=".gcd-",delete=False) as f: staged=Path(f.name); f.write(data)
        try: staged.chmod(0o644); staged.replace(path)
        finally: staged.unlink(missing_ok=True)
    print(f"{'verified' if args.check else 'generated'} three GCD fixture artifacts; "
          f"peak child RSS {resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss} KiB")

if __name__=="__main__": main()
