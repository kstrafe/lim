#!/usr/bin/env python3
"""Compare checked arithmetic and well-founded replay under limited-run.sh.

Use compilers built with identical profiles. Cases that the old checker rejects
are reported as coverage gains, never as successful-check speedups.
Repeat --case NAME to measure selected cases within the resource guard.
"""
import argparse
import json
from pathlib import Path
import resource
import statistics
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parent.parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--before", type=Path, required=True)
    parser.add_argument("--after", type=Path, required=True)
    parser.add_argument("--iterations", type=int, default=25)
    parser.add_argument("--case", action="append", help="repeat to select individual cases")
    args = parser.parse_args()
    if not 1 <= args.iterations <= 1000:
        parser.error("iterations must be between 1 and 1000")
    executables = [str(path.resolve(strict=True)) for path in [args.before, args.after]]
    manifest = json.loads((ROOT / "tests/fixtures/lean_export_division/provenance.json").read_bytes())
    raw = (ROOT / manifest["export"]["file"]).read_text()
    native = (ROOT / manifest["native"]["file"]).read_text()
    control = next(d for d in manifest["declarations"] if d["name"] == "DivisionSource.zeroDivZero")
    with tempfile.TemporaryDirectory(prefix="lim-remainder-benchmark-") as directory:
        work = Path(directory)
        control_raw = work / "control.ndjson"
        control_raw.write_text("".join(raw.splitlines(keepends=True)[:control["line"]]))
        control_native = work / "control.lim"
        begin = native.index("\n(#theorem " + control["native_name"])
        end = native.find("\n(#", begin + 1)
        control_native.write_text(native[:end] if end != -1 else native)
        cases = {
            "raw_zero_control": ["--check-lean-export", str(control_raw), control["name"]],
            "native_zero_control": ["--check-theorem", str(control_native), control["native_name"]],
            "raw_division": ["--check-lean-export", manifest["export"]["file"], manifest["targets"][-1]],
            "native_division": ["--check-theorem", manifest["native"]["file"], manifest["native"]["targets"][manifest["targets"][-1]]],
            "raw_arithmetic": ["--check-lean-export", "tests/fixtures/lean_export_arithmetic/arithmetic.ndjson", "ArithmeticSource.equalZero"],
            "native_arithmetic": ["--check-theorem", "theorems/lean_replay/arithmetic.lim", "lean-77-ArithmeticSource-equalZero"],
            "native_discrimination": ["--check-theorem", "theorems/lean_replay/discrimination.lim", "lean-51-DiscriminationSource-mappedDiscrimination"],
            "native_subtraction": ["--check-theorem", "theorems/lean_replay/subtraction-bridge.lim", "lean-59-SubtractionBridgeSource-mappedCancellation"],
        }
        composition = json.loads((ROOT / "tests/fixtures/lean_export_division_composition/provenance.json").read_bytes())
        prefix = next(d for d in composition["declarations"] if d["name"] == "DivisionCompositionSource.zero")
        composed_raw = work / "composed-prefix.ndjson"
        composed_raw.write_text("".join((ROOT / composition["export"]["file"]).read_text().splitlines(keepends=True)[:prefix["line"]]))
        composed_source = (ROOT / composition["native"]["file"]).read_text()
        begin = composed_source.index("\n(#theorem " + prefix["native_name"])
        end = composed_source.find("\n(#", begin + 1)
        composed_native = work / "composed-prefix.lim"
        composed_native.write_text(composed_source[:end] if end != -1 else composed_source)
        cases.update({
            "raw_composed_prefix": ["--check-lean-export", str(composed_raw), prefix["name"]],
            "native_composed_prefix": ["--check-theorem", str(composed_native), prefix["native_name"]],
            "raw_division_composition": ["--check-lean-export", composition["export"]["file"], composition["targets"][-1]],
            "native_division_composition": ["--check-theorem", composition["native"]["file"], composition["native"]["targets"][composition["targets"][-1]]],
        })
        remainder = json.loads((ROOT / "tests/fixtures/lean_export_remainder/provenance.json").read_bytes())
        accepted = next(d for d in remainder["declarations"] if d["name"] == "RemainderSource.zeroDivisor")
        accepted_raw = work / "remainder-prefix.ndjson"
        accepted_raw.write_text("".join((ROOT / remainder["export"]["file"]).read_text().splitlines(keepends=True)[:accepted["line"]]))
        accepted_source = (ROOT / remainder["native"]["file"]).read_text()
        begin = accepted_source.index("\n(#theorem " + accepted["native_name"])
        end = accepted_source.find("\n(#", begin + 1)
        accepted_native = work / "remainder-prefix.lim"
        accepted_native.write_text(accepted_source[:end] if end != -1 else accepted_source)
        cases.update({
            "raw_remainder_prefix": ["--check-lean-export", str(accepted_raw), accepted["name"]],
            "native_remainder_prefix": ["--check-theorem", str(accepted_native), accepted["native_name"]],
        })
        cases.update({
            "raw_remainder": ["--check-lean-export", remainder["export"]["file"], remainder["targets"][-1]],
            "native_remainder": ["--check-theorem", remainder["native"]["file"], remainder["native"]["targets"][remainder["targets"][-1]]],
        })
        well_founded = json.loads((ROOT / "tests/fixtures/lean_export_well_founded/provenance.json").read_bytes())
        cases.update({
            "raw_well_founded": ["--check-lean-export", well_founded["export"]["file"], well_founded["targets"][-1], "--lean-foundations"],
            "native_well_founded": ["--check-theorem", well_founded["native"]["file"], well_founded["native"]["targets"][well_founded["targets"][-1]]],
        })
        gcd = json.loads((ROOT / "tests/fixtures/lean_export_gcd/provenance.json").read_bytes())
        cases.update({
            "raw_gcd": ["--check-lean-export", gcd["export"]["file"], gcd["targets"][-1], "--lean-foundations"],
            "native_gcd": ["--check-theorem", gcd["native"]["file"], gcd["native"]["targets"][gcd["targets"][-1]]],
        })
        gcd_self_path = ROOT / "tests/fixtures/lean_export_gcd_self/provenance.json"
        gcd_self = json.loads(gcd_self_path.read_bytes())
        selected = gcd_self["proof_budget"]
        budget_args = ["--proof-work", str(selected["work_per_phase"]),
                       "--proof-phase-bytes", str(selected["transformation_bytes_per_phase"]),
                       "--proof-total-bytes", str(selected["transformation_bytes_total"])]
        target = gcd_self["targets"][-1]
        cases.update({
            "raw_gcd_self": ["--check-lean-export", gcd_self["export"]["file"], target, "--lean-foundations", *budget_args],
            "native_gcd_self": ["--check-theorem", gcd_self["native"]["file"], gcd_self["native"]["targets"][target], *budget_args],
        })
        calculation = json.loads((ROOT / "tests/fixtures/lean_export_gcd_calculation/provenance.json").read_bytes())
        selected = calculation["proof_budget"]
        calculation_budget = ["--proof-work", str(selected["work_per_phase"]),
                              "--proof-phase-bytes", str(selected["transformation_bytes_per_phase"]),
                              "--proof-total-bytes", str(selected["transformation_bytes_total"])]
        target = calculation["targets"][-1]
        cases.update({
            "raw_gcd_calculation": ["--check-lean-export", calculation["export"]["file"], target, "--lean-foundations", *calculation_budget],
            "native_gcd_calculation": ["--check-theorem", calculation["native"]["file"], calculation["native"]["targets"][target], *calculation_budget],
        })
        computed = ROOT / "examples/proof_computed_subtraction.lim"
        computed_control = work / "computed-control.lim"
        computed_control.write_text(computed.read_text().split("(#theorem computed-subtraction-exhausted")[0])
        cases.update({
            "native_computed_subtraction": ["--check-theorem", str(computed_control), "computed-subtraction"],
            "native_computed_subtraction_exhausted": ["--check-theorem", str(computed), "computed-subtraction-exhausted"],
        })
        if args.case:
            unknown = set(args.case) - cases.keys()
            if unknown:
                parser.error("unknown case(s): " + ", ".join(sorted(unknown)))
            cases = {name: arguments for name, arguments in cases.items() if name in args.case}
        for name, arguments in cases.items():
            wall, cpu, statuses, diagnostics = [[], []], [[], []], [set(), set()], ["", ""]
            for iteration in range(args.iterations + 1):
                for index in [0, 1] if iteration % 2 == 0 else [1, 0]:
                    usage = resource.getrusage(resource.RUSAGE_CHILDREN)
                    start = time.perf_counter_ns()
                    result = subprocess.run([executables[index], *arguments], cwd=ROOT,
                                            capture_output=True, timeout=30, check=False)
                    elapsed = (time.perf_counter_ns() - start) / 1e6
                    after = resource.getrusage(resource.RUSAGE_CHILDREN)
                    if iteration:
                        wall[index].append(elapsed)
                        cpu[index].append(1000 * (after.ru_utime + after.ru_stime - usage.ru_utime - usage.ru_stime))
                    statuses[index].add(result.returncode)
                    if result.returncode:
                        diagnostics[index] = result.stderr.decode(errors="replace").strip()[:600]
                        if index == 1:
                            raise RuntimeError(diagnostics[index])
            medians = list(map(statistics.median, wall))
            entry = {"case": name, "samples": args.iterations,
                     "wall_median_ms": medians, "cpu_mean_ms": list(map(statistics.mean, cpu)),
                     "statuses": list(map(sorted, statuses))}
            if statuses == [{0}, {0}]:
                entry["wall_reduction_percent"] = 100 * (1 - medians[1] / medians[0])
            else:
                entry["coverage_gain"] = True
                entry["diagnostics"] = diagnostics
            print(json.dumps(entry), flush=True)


if __name__ == "__main__":
    main()
