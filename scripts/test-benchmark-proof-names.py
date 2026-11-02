#!/usr/bin/env python3
"""Focused stdlib tests; run under the main serial resource guard::

    bash scripts/limited-run.sh python3 scripts/test-benchmark-proof-names.py
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
BENCHMARK = ROOT / "scripts/benchmark-proof-names.py"
MODULE = runpy.run_path(str(BENCHMARK))
COMMON_ARGS = ["--before", "/bin/true", "--after", "/bin/true"]


class NamesBenchmarkTests(unittest.TestCase):
    def test_deterministic_bytes_and_only_backward_primitive_names(self):
        names, name_bytes = 17, 32
        with tempfile.TemporaryDirectory() as directory:
            first = Path(directory) / "first.ndjson"
            second = Path(directory) / "second.ndjson"
            fingerprint = MODULE["generate_export"](first, names, name_bytes)
            self.assertEqual(fingerprint,
                             MODULE["generate_export"](second, names, name_bytes))
            raw = first.read_bytes()
            self.assertEqual(raw, second.read_bytes())
            self.assertEqual(fingerprint, (len(raw), hashlib.sha256(raw).hexdigest()))
            fixture = MODULE["FIXTURE"].read_bytes()
            self.assertTrue(raw.startswith(fixture))
            rows = [json.loads(line) for line in raw[len(fixture):].splitlines()]
            self.assertEqual(len(rows), names)
            spellings = {0: ("$lean:", "")}
            payload_bytes = 0
            for row in [json.loads(line) for line in raw.splitlines()]:
                if "in" not in row:
                    continue
                part = row["str"]["str"]
                parent = row["str"]["pre"]
                parent_key, parent_display = spellings[parent]
                key = parent_key + f"s{len(part.encode('utf-8'))}:" + part
                display = part if parent == 0 else parent_display + "." + part
                spellings[row["in"]] = (key, display)
                payload_bytes += len(key.encode("utf-8")) + len(display.encode("utf-8"))
            self.assertEqual(payload_bytes, MODULE["projected_name_payload"](names, name_bytes))
            known_names = {0, 1, 2, 3, 4}
            components = set()
            for index, row in enumerate(rows):
                self.assertEqual(set(row), {"in", "str"})
                self.assertEqual(set(row["str"]), {"pre", "str"})
                self.assertEqual(row["in"], 5 + index)
                self.assertEqual(row["str"]["pre"], 1)
                self.assertIn(row["str"]["pre"], known_names)
                self.assertLess(row["str"]["pre"], row["in"])
                self.assertNotIn(row["in"], known_names)
                known_names.add(row["in"])
                component = row["str"]["str"]
                self.assertTrue(component.startswith(f"name{index}"))
                self.assertEqual(len(component.encode("utf-8")), name_bytes)
                self.assertNotIn(component, components)
                components.add(component)

    def test_defaults_and_valid_boundaries_without_compilers(self):
        _, defaults = MODULE["parse_args"](COMMON_ARGS)
        self.assertEqual((defaults.names, defaults.name_bytes, defaults.iterations),
                         (12_000, 512, 5))
        for options in (["--names", "1", "--name-bytes", "5", "--iterations", "1"],
                        ["--names", "50000", "--name-bytes", "9", "--iterations", "25"],
                        ["--names", "8089", "--name-bytes", "1024"]):
            with self.subTest(options=options):
                MODULE["parse_args"]([*COMMON_ARGS, *options])

    def test_invalid_cli_options_exit_with_finite_timeout(self):
        cases = [(["--names", "0"], "--names"),
                 (["--names", "50001"], "--names"),
                 (["--name-bytes", "0"], "--name-bytes"),
                 (["--name-bytes", "1025"], "--name-bytes"),
                 (["--iterations", "0"], "--iterations"),
                 (["--iterations", "26"], "--iterations"),
                 (["--names", "11", "--name-bytes", "5"], "prefix"),
                 (["--names", "8090", "--name-bytes", "1024"], "16 MiB"),
                 (["--invalid"], "unrecognized arguments")]
        for options, expected in cases:
            with self.subTest(options=options):
                result = subprocess.run(
                    [sys.executable, str(BENCHMARK), *COMMON_ARGS, *options],
                    cwd=ROOT, capture_output=True, text=True, timeout=5, check=False)
                self.assertEqual(result.returncode, 2, result.stderr)
                self.assertIn(expected, result.stderr)
                self.assertEqual(result.stdout, "")

    def test_rejects_payload_and_fixture_mismatch_before_writing(self):
        generate = MODULE["generate_export"]
        with tempfile.TemporaryDirectory() as directory:
            destination = Path(directory) / "must-not-exist.ndjson"
            with self.assertRaisesRegex(ValueError, "16 MiB"):
                generate(destination, 8090, 1024)
            self.assertFalse(destination.exists())
            fixture = Path(directory) / "wrong-fixture.ndjson"
            fixture.write_bytes(b"{}\n")
            with mock.patch.dict(generate.__globals__, {"FIXTURE": fixture}):
                with self.assertRaisesRegex(ValueError, "SHA256"):
                    generate(destination, 1, 5)
            self.assertFalse(destination.exists())

    def test_preflight_hashes_complete_receipts(self):
        verify = MODULE["verify_receipts"]
        compilers = {"before": "before-compiler", "after": "after-compiler"}
        for matching in (True, False):
            with self.subTest(matching=matching), tempfile.TemporaryDirectory() as directory:
                prefix = b"x" * (64 * 1024)

                def fake_run(command):
                    report = Path(command[command.index("--report") + 1])
                    suffix = b"a" if matching or command[0] == "before-compiler" else b"b"
                    report.write_bytes(prefix + suffix)
                    return subprocess.CompletedProcess(command, 0)

                with mock.patch.dict(verify.__globals__, {"run_bounded": fake_run}):
                    if matching:
                        fingerprint = verify(compilers, Path(directory) / "input", directory)
                        self.assertEqual(fingerprint, (
                            len(prefix) + 1, hashlib.sha256(prefix + b"a").hexdigest()))
                    else:
                        with self.assertRaisesRegex(RuntimeError, "SHA-256 differs"):
                            verify(compilers, Path(directory) / "input", directory)


if __name__ == "__main__":
    unittest.main()
