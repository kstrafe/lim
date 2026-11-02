#!/usr/bin/env python3
"""Focused stdlib tests; defer execution to main serial validation::

    bash scripts/limited-run.sh python3 scripts/test-benchmark-proof-levels.py
"""

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
BENCHMARK = ROOT / "scripts/benchmark-proof-levels.py"
MODULE = runpy.run_path(str(BENCHMARK))
COMMON_ARGS = ["--before", "/bin/true", "--after", "/bin/true"]


class LevelsBenchmarkTests(unittest.TestCase):
    def test_distinct_values_keep_names_unique_and_validate_their_payload(self):
        generate = MODULE["generate_export"]
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "distinct.ndjson"
            first = generate(path, 40, 16, distinct=True)
            raw = path.read_bytes()
            self.assertEqual(first, generate(path, 40, 16, distinct=True))
            self.assertEqual(raw, path.read_bytes())
            rows = [json.loads(line) for line in raw.splitlines()]
            names = {row["in"]: row["str"]["str"] for row in rows if "in" in row}
            for index in range(40):
                self.assertTrue(names[index + 5].startswith(f"v{index}"))
                self.assertEqual(len(names[index + 5]), 16)
                self.assertIn({"il": index + 2, "param": index + 5}, rows)
            self.assertEqual(len(set(names.values())), len(names))
            path.unlink()
            for count, size in [(1, 1), (19000, 480)]:
                with self.assertRaises(ValueError):
                    generate(path, count, size, distinct=True)
                self.assertFalse(path.exists())

    def test_determinism_and_backward_name_and_level_references(self):
        levels, parameter_bytes = 7, 32
        with tempfile.TemporaryDirectory() as directory:
            first = Path(directory) / "first.ndjson"
            second = Path(directory) / "second.ndjson"
            fingerprint = MODULE["generate_export"](first, levels, parameter_bytes)
            self.assertEqual(fingerprint,
                             MODULE["generate_export"](second, levels, parameter_bytes))
            raw = first.read_bytes()
            self.assertEqual(raw, second.read_bytes())
            self.assertEqual(fingerprint, (len(raw), hashlib.sha256(raw).hexdigest()))
            fixture = MODULE["FIXTURE"].read_bytes()
            self.assertTrue(raw.startswith(fixture))
            appended = [json.loads(line) for line in raw[len(fixture):].splitlines()]
            self.assertEqual(len(appended), levels + 1)
            self.assertEqual(appended[0]["in"], 5)
            self.assertEqual(appended[0]["str"]["pre"], 0)
            self.assertEqual(len(appended[0]["str"]["str"].encode("ascii")), parameter_bytes)
            self.assertEqual(appended[1:], [{"il": level_id, "param": 5}
                                            for level_id in range(2, levels + 2)])

            names = {0}
            known_levels = {0}
            rows = [json.loads(line) for line in raw.splitlines()]
            for row in rows:
                if "in" in row:
                    self.assertEqual(row["in"], len(names))
                    self.assertIn(row["str"]["pre"], names)
                    self.assertLess(row["str"]["pre"], row["in"])
                    names.add(row["in"])
                if "il" in row:
                    self.assertEqual(row["il"], len(known_levels))
                    self.assertIn(row["param"], names)
                    known_levels.add(row["il"])
                if "sort" in row:
                    self.assertIn(row["sort"], known_levels)
                if "const" in row:
                    self.assertIn(row["const"]["name"], names)
                    for level_id in row["const"]["us"]:
                        self.assertIn(level_id, known_levels)
            self.assertEqual(len(names), 6)
            self.assertEqual(len(known_levels), levels + 2)
            self.assertEqual(sum("ie" in row for row in rows), 20)
            self.assertEqual(sum("def" in row or "thm" in row for row in rows), 2)

    def test_exact_combined_payload_includes_lean_prefix(self):
        # Independent accounting of the pinned fixture's primitive rows.
        rows = [json.loads(line) for line in MODULE["FIXTURE"].read_bytes().splitlines()]
        keys = {0: "$lean:"}
        weights = {0: 0}
        fixture_payload = 0
        for row in rows:
            if "in" in row:
                part = row["str"]["str"]
                keys[row["in"]] = keys[row["str"]["pre"]] + f"s{len(part)}:" + part
            if "il" in row:
                weight = 96 + len(keys[row["param"]].encode("ascii"))
                weights[row["il"]] = weight
                fixture_payload += weight
            if "ie" in row:
                fixture_payload += 128
                if "sort" in row:
                    fixture_payload += weights[row["sort"]]
                if "const" in row:
                    fixture_payload += len(keys[row["const"]["name"]].encode("ascii"))
                    fixture_payload += sum(weights[level] for level in row["const"]["us"])
        self.assertEqual(fixture_payload, 2797)
        for parameter_bytes, expected_key_bytes in ((1, 10), (9, 18), (10, 20),
                                                    (99, 109), (100, 111), (480, 491)):
            with self.subTest(parameter_bytes=parameter_bytes):
                part = MODULE["parameter_component"](parameter_bytes)
                key = f"$lean:s{parameter_bytes}:" + part
                self.assertEqual(len(key.encode("ascii")), expected_key_bytes)
                self.assertEqual(MODULE["parameter_key_bytes"](parameter_bytes), expected_key_bytes)
                self.assertEqual(MODULE["projected_primitive_payload"](7, parameter_bytes),
                                 fixture_payload + 7 * (96 + len(key.encode("ascii"))))

    def test_valid_defaults_boundaries_and_one_byte_name(self):
        _, defaults = MODULE["parse_args"](COMMON_ARGS)
        self.assertEqual((defaults.levels, defaults.parameter_bytes, defaults.iterations),
                         (19_000, 256, 5))
        for options in (["--levels", "1", "--parameter-bytes", "1", "--iterations", "1"],
                        ["--levels", "19998", "--parameter-bytes", "480", "--iterations", "25"]):
            MODULE["parse_args"]([*COMMON_ARGS, *options])
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "minimum.ndjson"
            MODULE["generate_export"](path, 1, 1)
            root_components = [row["str"]["str"]
                               for row in map(json.loads, path.read_bytes().splitlines())
                               if "in" in row and row["str"]["pre"] == 0]
            self.assertEqual(len(root_components), len(set(root_components)))

    def test_cli_rejects_invalid_bounds_before_compilers(self):
        for option, value in (("--levels", "0"), ("--levels", "19999"),
                              ("--parameter-bytes", "0"), ("--parameter-bytes", "481"),
                              ("--iterations", "0"), ("--iterations", "26"),
                              ("--invalid", None)):
            with self.subTest(option=option, value=value):
                options = [option] if value is None else [option, value]
                result = subprocess.run(
                    [sys.executable, str(BENCHMARK), *COMMON_ARGS, *options],
                    cwd=ROOT, capture_output=True, text=True, timeout=5, check=False)
                self.assertEqual(result.returncode, 2, result.stderr)
                self.assertIn(option, result.stderr)
                self.assertEqual(result.stdout, "")

    def test_rejects_bounds_payload_and_bad_fixture_before_write(self):
        generate = MODULE["generate_export"]
        with tempfile.TemporaryDirectory() as directory:
            destination = Path(directory) / "must-not-exist.ndjson"
            for levels, parameter_bytes in ((0, 256), (19999, 256), (1, 0), (1, 481)):
                with self.assertRaises(ValueError):
                    generate(destination, levels, parameter_bytes)
                self.assertFalse(destination.exists())
            # The supported parameter ranges fit the real cap. Lower it here
            # to exercise the pre-write payload rejection and exact boundary.
            payload = MODULE["projected_primitive_payload"](1, 1)
            with mock.patch.dict(generate.__globals__, {"MAX_PRIMITIVE_PAYLOAD_BYTES": payload - 1}):
                with self.assertRaisesRegex(ValueError, "64 MiB"):
                    generate(destination, 1, 1)
            self.assertFalse(destination.exists())
            with mock.patch.dict(generate.__globals__, {"MAX_PRIMITIVE_PAYLOAD_BYTES": payload}):
                generate(destination, 1, 1)
            destination.unlink()
            fixture = Path(directory) / "wrong-fixture.ndjson"
            fixture.write_bytes(b"{}\n")
            with mock.patch.dict(generate.__globals__, {"FIXTURE": fixture}):
                with self.assertRaisesRegex(ValueError, "SHA256"):
                    generate(destination, 1, 1)
            self.assertFalse(destination.exists())

    def test_receipt_preflight_compares_complete_bytes_and_hash(self):
        verify = MODULE["verify_receipts"]
        compilers = {"before": "before-compiler", "after": "after-compiler"}
        for after_suffix in (b"a", b"b", b"aa"):
            with self.subTest(after_suffix=after_suffix), tempfile.TemporaryDirectory() as directory:
                prefix = b"x" * (64 * 1024)

                def fake_run(command):
                    report = Path(command[command.index("--report") + 1])
                    suffix = b"a" if command[0] == "before-compiler" else after_suffix
                    report.write_bytes(prefix + suffix)
                    return subprocess.CompletedProcess(command, 0)

                with mock.patch.dict(verify.__globals__, {"run_bounded": fake_run}):
                    if after_suffix == b"a":
                        fingerprint = verify(compilers, Path(directory) / "input", directory)
                        self.assertEqual(fingerprint, (
                            len(prefix) + 1, hashlib.sha256(prefix + b"a").hexdigest()))
                    else:
                        with self.assertRaisesRegex(RuntimeError, "byte count or SHA-256 differs"):
                            verify(compilers, Path(directory) / "input", directory)


if __name__ == "__main__":
    unittest.main()
