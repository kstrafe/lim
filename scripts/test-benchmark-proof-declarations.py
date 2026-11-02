#!/usr/bin/env python3
"""Focused tests for the synthetic declaration proof benchmark."""

import json
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parent.parent
BENCHMARK = ROOT / "scripts/benchmark-proof-declarations.py"
MODULE = runpy.run_path(str(BENCHMARK))


class DeclarationBenchmarkTests(unittest.TestCase):
    def test_generation_is_deterministic_and_references_are_backward(self):
        declarations, lets = 7, 5
        with tempfile.TemporaryDirectory() as directory:
            first = Path(directory) / "first.ndjson"
            second = Path(directory) / "second.ndjson"
            target = MODULE["generate_export"](first, declarations, lets)
            second_target = MODULE["generate_export"](second, declarations, lets)
            self.assertEqual(first.read_bytes(), second.read_bytes())
            self.assertEqual(target, second_target)
            self.assertEqual(target, f"Audit.declaration_{declarations - 1}")

            rows = [json.loads(line) for line in first.read_text().splitlines()]
            expression_ids = [row["ie"] for row in rows if "ie" in row]
            self.assertEqual(expression_ids, list(range(21 + declarations * (1 + lets))))
            self.assertEqual(sum("def" in row for row in rows), declarations + 1)
            self.assertEqual(sum("thm" in row for row in rows), declarations + 1)
            self.assertEqual(sum("letE" in row for row in rows), declarations * lets)
            self.assertEqual(next(row["sort"] for row in rows
                                  if row.get("ie") == 20), 2)

            known_names = set()
            known_expressions = set()
            marker_strings = []
            for row in rows:
                if "in" in row:
                    name_id = row["in"]
                    name_info = row["str"]
                    if name_info["pre"] != 0:
                        self.assertIn(name_info["pre"], known_names)
                    known_names.add(name_id)
                    if name_info["str"].startswith("Marker_"):
                        marker_strings.append(name_info["str"])
                if "ie" in row:
                    expression_id = row["ie"]
                    payload = {key: value for key, value in row.items() if key != "ie"}
                    node = next(iter(payload.values()))
                    if isinstance(node, dict):
                        for field in ("type", "value", "body", "fn", "arg"):
                            if field in node:
                                self.assertLess(node[field], expression_id)
                    known_expressions.add(expression_id)
                for key in ("name",):
                    if key in row and isinstance(row[key], int):
                        self.assertIn(row[key], known_names)
                for key in ("def", "thm"):
                    if key in row:
                        declaration = row[key]
                        self.assertIn(declaration["name"], known_names)
                        self.assertIn(declaration["type"], known_expressions)
                        if key == "def":
                            self.assertIn(declaration["value"], known_expressions)
                        else:
                            self.assertIn(declaration["value"], known_expressions)
                if "letE" in row:
                    let = row["letE"]
                    self.assertIn(let["type"], known_expressions)
                    self.assertIn(let["value"], known_expressions)
                    self.assertIn(let["body"], known_expressions)

            self.assertEqual(marker_strings,
                             [f"Marker_{index}" for index in range(declarations)])

    def test_invalid_cli_bounds_exit_before_running_compilers(self):
        common = [sys.executable, str(BENCHMARK), "--before", "/bin/true",
                  "--after", "/bin/true"]
        for option, value in (("--iterations", "0"),
                              ("--declarations", "1801"),
                              ("--lets", "65")):
            with self.subTest(option=option):
                result = subprocess.run(
                    [*common, option, value], cwd=ROOT, capture_output=True,
                    text=True, timeout=5, check=False)
                self.assertEqual(result.returncode, 2, result.stderr)
                self.assertIn(option, result.stderr)


if __name__ == "__main__":
    unittest.main()
