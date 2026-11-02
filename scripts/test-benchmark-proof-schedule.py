"""Focused stdlib checks for the synthetic proof scheduling benchmark."""

import hashlib
import json
from pathlib import Path
import re
import runpy
import subprocess
import tempfile
import unittest
from unittest import mock


ROOT = Path(__file__).resolve().parent.parent
SCRIPT = ROOT / "scripts/benchmark-proof-schedule.py"
MODULE = runpy.run_path(str(SCRIPT))


class ProofScheduleBenchmarkTests(unittest.TestCase):
    def test_generator_is_deterministic_and_has_exact_nested_lets(self):
        with tempfile.TemporaryDirectory() as directory:
            first, second = Path(directory) / "first.lim", Path(directory) / "second.lim"
            fingerprint = MODULE["generate_source"](first, 2, 3)
            self.assertEqual(fingerprint, MODULE["generate_source"](second, 2, 3))
            self.assertEqual(first.read_bytes(), second.read_bytes())
            self.assertEqual(fingerprint,
                             (first.stat().st_size,
                              hashlib.sha256(first.read_bytes()).hexdigest()))
            rows = first.read_text(encoding="utf-8").splitlines()
            self.assertEqual(len(rows), 2)
            for index, row in enumerate(rows):
                self.assertTrue(row.startswith(f"(#theorem theorem-{index} "))
                self.assertEqual(row.count("(#pt-let "), 3)
                self.assertEqual(row.count("(#parameter scratch-"), 3)
                self.assertEqual(row.count(" #pt-nat) #pt-zero"), 3)
                self.assertEqual(row.count("("), row.count(")"))
                names = re.findall(r"#parameter (scratch-\d+) #pt-nat", row)
                self.assertEqual(names, ["scratch-0", "scratch-1", "scratch-2"])
                proof = row.split("(#proof ", 1)[1][:-2]
                expected = "(#pt-refl #pt-nat #pt-zero)"
                for name in reversed(names):
                    expected = f"(#pt-let (#parameter {name} #pt-nat) #pt-zero {expected})"
                self.assertEqual(proof, expected)

    def test_options_and_source_byte_bound(self):
        validate = MODULE["validate_parameters"]
        validate(1, 1, 1)
        validate(3000, 32, 5)
        for values, option in (((0, 1, 1), "declarations"),
                               ((3001, 1, 1), "declarations"),
                               ((1, 0, 1), "lets"),
                               ((1, 33, 1), "lets"),
                               ((1, 1, 0), "iterations"),
                               ((1, 1, 6), "iterations")):
            with self.subTest(values=values), self.assertRaisesRegex(ValueError, option):
                validate(*values)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "bounded.lim"
            with mock.patch.dict(MODULE["generate_source"].__globals__,
                                 {"MAX_SOURCE_BYTES": 1}):
                with self.assertRaisesRegex(ValueError, "8 MiB"):
                    MODULE["generate_source"](path, 1, 1)
            self.assertFalse(path.exists())

    def test_preflight_rejects_failure_diagnostics_and_wrong_target(self):
        verify = MODULE["verify_preflight"]
        compilers = {"before": Path("before"), "after": Path("after")}
        failed = subprocess.CompletedProcess([], 1, b"", b"error")
        with mock.patch.dict(verify.__globals__, {"run_bounded": lambda _: failed}):
            with self.assertRaisesRegex(RuntimeError, "failed theorem-check"):
                verify(compilers, Path("source"), 1)

        success = (b"checked theorem theorem-0\n"
                   b"proof budget: work=200000 phase-bytes=67108864 "
                   b"total-bytes=1073741824\n")
        diagnostic = subprocess.CompletedProcess([], 0, success, b"warning")
        with mock.patch.dict(verify.__globals__, {"run_bounded": lambda _: diagnostic}):
            with self.assertRaisesRegex(RuntimeError, "unexpected theorem-check output"):
                verify(compilers, Path("source"), 1)

        wrong_target = subprocess.CompletedProcess(
            [], 0, success.replace(b"theorem-0", b"theorem-wrong"), b"")
        with mock.patch.dict(verify.__globals__, {"run_bounded": lambda _: wrong_target}):
            with self.assertRaisesRegex(RuntimeError, "unexpected theorem-check output"):
                verify(compilers, Path("source"), 1)

        calls = []
        passed = subprocess.CompletedProcess([], 0, success, b"")
        def record(command):
            calls.append(command)
            return passed
        with mock.patch.dict(verify.__globals__, {"run_bounded": record}):
            self.assertEqual(verify(compilers, Path("source"), 1), "theorem-0")
        self.assertEqual(len(calls), 2)
        self.assertTrue(all(command[1] == "--check-theorem" and
                            command[3] == "theorem-0" for command in calls))

    def test_worker_failure_is_reported(self):
        run_sample = MODULE["run_sample"]
        failed = subprocess.CompletedProcess([], 1, b'{"case":"synthetic_proof_schedule","status":"ok"}', b"")
        with mock.patch.dict(run_sample.__globals__, {"run_bounded": lambda _: failed}), \
                mock.patch("builtins.print") as output:
            self.assertFalse(run_sample("before", Path("lim"), 1, Path("source"),
                                        "theorem-0", (10, "a" * 64), {"declarations": 1}))
        record = json.loads(output.call_args.args[0])
        self.assertEqual(record["status"], "worker_error")
        self.assertIsNone(record["wall_ms"])


if __name__ == "__main__":
    unittest.main()
