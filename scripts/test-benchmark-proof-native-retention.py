"""Focused stdlib checks for the native retention benchmark."""

import hashlib
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile
import unittest
from unittest import mock


ROOT = Path(__file__).resolve().parent.parent
SCRIPT = ROOT / "scripts/benchmark-proof-native-retention.py"
MODULE = runpy.run_path(str(SCRIPT))


class NativeRetentionBenchmarkTests(unittest.TestCase):
    def test_generator_is_repeatable_and_hashes_source(self):
        with tempfile.TemporaryDirectory() as directory:
            first, second = Path(directory) / "one.ndjson", Path(directory) / "two.ndjson"
            fp1 = MODULE["generate_source"](first, 3, 2, 5)
            fp2 = MODULE["generate_source"](second, 3, 2, 5)
            self.assertEqual(first.read_bytes(), second.read_bytes())
            self.assertEqual(fp1, fp2)
            self.assertEqual(fp1, (first.stat().st_size,
                                   hashlib.sha256(first.read_bytes()).hexdigest()))

    def test_parameter_bounds_and_expression_limit(self):
        validate = MODULE["validate_parameters"]
        validate(1, 1, 0, 1)
        validate(500, 16, 190000, 5)
        for values, option in (((0, 1, 0, 1), "declarations"),
                               ((1, 17, 0, 1), "lets"),
                               ((1, 1, 190001, 1), "unused-expressions"),
                               ((1, 1, 0, 6), "iterations")):
            with self.subTest(values=values), self.assertRaisesRegex(ValueError, option):
                validate(*values)

    def test_source_limit_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            with mock.patch.dict(MODULE["generate_source"].__globals__, {"MAX_SOURCE_BYTES": 1}):
                with self.assertRaisesRegex(ValueError, "64 MiB"):
                    MODULE["generate_source"](Path(directory) / "source.ndjson", 1, 1, 0)

    def test_preflight_rejects_failure_and_mismatched_proof_or_report(self):
        verify = MODULE["verify_preflight"]
        compilers = {"before": Path("before"), "after": Path("after")}
        failed = subprocess.CompletedProcess([], 1, b"")
        with mock.patch.dict(verify.__globals__, {"run_compiler": lambda *args: failed}):
            with self.assertRaisesRegex(RuntimeError, "failed emission preflight"):
                verify(compilers, Path("source"), "target", Path("tmp"))

        passed = subprocess.CompletedProcess([], 0, b"")
        for reports, proofs in (
                ([(10, "a" * 64), (11, "a" * 64)],
                 [(20, "b" * 64), (20, "b" * 64)]),
                ([(10, "a" * 64), (10, "a" * 64)],
                 [(20, "b" * 64), (20, "c" * 64)])):
            report_iter, proof_iter = iter(reports), iter(proofs)
            with mock.patch.dict(verify.__globals__, {
                    "run_compiler": lambda *args: passed,
                    "receipt_digest": lambda _: next(report_iter),
                    "file_fingerprint": lambda _: next(proof_iter)}):
                with self.assertRaisesRegex(RuntimeError, "fingerprint differs"):
                    verify(compilers, Path("source"), "target", Path("tmp"))

    def test_cli_rejects_out_of_range_without_compiler_invocation(self):
        command = [sys.executable, str(SCRIPT), "--before", "/bin/true", "--after", "/bin/true"]
        for option, value in (("--declarations", "501"), ("--lets", "17"),
                              ("--unused-expressions", "190001"), ("--iterations", "6")):
            result = subprocess.run([*command, option, value], cwd=ROOT,
                                     capture_output=True, text=True, timeout=5, check=False)
            self.assertEqual(result.returncode, 2, result.stderr)
            self.assertIn(option.removeprefix("--"), result.stderr)
            self.assertEqual(result.stdout, "")


if __name__ == "__main__":
    unittest.main()
