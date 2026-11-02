"""Focused stdlib checks for the synthetic closure benchmark generator."""

import hashlib
import json
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile
import unittest
from unittest import mock


ROOT = Path(__file__).resolve().parent.parent
SCRIPT = ROOT / "scripts/benchmark-proof-closure.py"
MODULE = runpy.run_path(str(SCRIPT))


class ClosureBenchmarkTests(unittest.TestCase):
    def test_deterministic_pinned_export_and_backward_frontier(self):
        declarations, width = 9, 3
        with tempfile.TemporaryDirectory() as directory:
            one, two = Path(directory) / "one.ndjson", Path(directory) / "two.ndjson"
            fingerprint = MODULE["generate_export"](one, declarations, width)
            self.assertEqual(fingerprint, MODULE["generate_export"](two, declarations, width))
            raw = one.read_bytes()
            self.assertEqual(raw, two.read_bytes())
            self.assertEqual(fingerprint, (len(raw), hashlib.sha256(raw).hexdigest()))
            fixture = MODULE["FIXTURE"].read_bytes()
            self.assertEqual(hashlib.sha256(fixture).hexdigest(), MODULE["FIXTURE_SHA256"])
            self.assertTrue(raw.startswith(fixture))
            rows = [json.loads(line) for line in raw[len(fixture):].splitlines()]
            self.assertEqual(rows.pop(0), {"const": {"name": 3, "us": []}, "ie": 20})
            names = {0, 1, 2, 3, 4}
            exprs = set(range(21))
            theorem_consts = []
            next_name, next_expr = 5, 21
            cursor = 0
            for index in range(declarations):
                name_row = rows[cursor]
                cursor += 1
                self.assertEqual(name_row, {"str": {"pre": 1, "str": f"Closure{index:04d}".ljust(64, "x")}, "in": next_name})
                names.add(next_name)
                next_name += 1
                expected_values = theorem_consts[max(0, index - width):index] or [20]
                body = 19
                for expected_value in expected_values:
                    row = rows[cursor]
                    cursor += 1
                    self.assertEqual(row, {"letE": {"name": 0, "type": 12,
                                                    "value": expected_value, "body": body,
                                                    "nondep": True}, "ie": next_expr})
                    self.assertLess(expected_value, next_expr)
                    self.assertLess(body, next_expr)
                    exprs.add(next_expr)
                    body = next_expr
                    next_expr += 1
                theorem = rows[cursor]
                cursor += 1
                self.assertEqual(theorem, {"thm": {"name": next_name - 1,
                                                    "levelParams": [], "type": 12,
                                                    "value": body, "all": [next_name - 1]}})
                const = rows[cursor]
                cursor += 1
                self.assertEqual(const, {"const": {"name": next_name - 1, "us": []}, "ie": next_expr})
                exprs.add(next_expr)
                theorem_consts.append(next_expr)
                next_expr += 1
            self.assertEqual(cursor, len(rows))
            self.assertEqual(len(names), 5 + declarations)
            self.assertEqual(len(exprs), next_expr)

    def test_parameter_boundaries(self):
        validate = MODULE["validate_parameters"]
        for values in ((1, 1, 1), (2500, 32, 5), (1000, 16, 3)):
            validate(*values)
        for values, message in (((0, 1, 1), "declarations"),
                                ((2501, 1, 1), "declarations"),
                                ((1, 0, 1), "width"),
                                ((1, 33, 1), "width"),
                                ((1, 1, 0), "iterations"),
                                ((1, 1, 6), "iterations")):
            with self.subTest(values=values), self.assertRaisesRegex(ValueError, message):
                validate(*values)

    def test_rejects_fixture_hash_mismatch_before_writing(self):
        with tempfile.TemporaryDirectory() as directory:
            fixture = Path(directory) / "bad.ndjson"
            fixture.write_bytes(b"{}\n")
            destination = Path(directory) / "output.ndjson"
            with mock.patch.dict(MODULE["generate_export"].__globals__, {"FIXTURE": fixture}):
                with self.assertRaisesRegex(ValueError, "SHA256"):
                    MODULE["generate_export"](destination, 2, 1)
            self.assertFalse(destination.exists())

    def test_cli_rejects_out_of_range_parameters(self):
        common = [sys.executable, str(SCRIPT), "--before", "/bin/true", "--after", "/bin/true"]
        for option, value in (("--declarations", "2501"), ("--width", "33"),
                              ("--iterations", "6")):
            result = subprocess.run([*common, option, value], cwd=ROOT,
                                     capture_output=True, text=True, timeout=5, check=False)
            self.assertEqual(result.returncode, 2, result.stderr)
            self.assertIn(option, result.stderr)
            self.assertEqual(result.stdout, "")

    def test_source_byte_limit_fails_without_a_success_fingerprint(self):
        with tempfile.TemporaryDirectory() as directory:
            with mock.patch.dict(MODULE["generate_export"].__globals__,
                                 {"MAX_SOURCE_BYTES": len(MODULE["FIXTURE"].read_bytes()) + 1}):
                with self.assertRaisesRegex(ValueError, "source exceeds"):
                    MODULE["generate_export"](Path(directory) / "source.ndjson", 2, 1)

    def test_preflight_rejects_compiler_failure_and_different_full_receipts(self):
        function = MODULE["verify_receipts"]
        compilers = {"before": Path("before"), "after": Path("after")}
        source = Path("source.ndjson")
        failed = subprocess.CompletedProcess([], 1, b"")
        with mock.patch.dict(function.__globals__, {"run_bounded": lambda _: failed}):
            with self.assertRaisesRegex(RuntimeError, "failed receipt preflight"):
                function(compilers, source, "target", Path("directory"))
        passed = subprocess.CompletedProcess([], 0, b"")
        digests = iter(((100, "a" * 64), (100, "b" * 64)))
        with mock.patch.dict(function.__globals__, {
                "run_bounded": lambda _: passed,
                "receipt_digest": lambda _: next(digests)}):
            with self.assertRaisesRegex(RuntimeError, "SHA-256 differs"):
                function(compilers, source, "target", Path("directory"))


if __name__ == "__main__":
    unittest.main()
