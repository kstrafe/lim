"""Small standard-library tests for the source-only Lean export inspector."""

import hashlib
import importlib.util
import io
from pathlib import Path
import subprocess
import sys
import unittest


SCRIPT = Path(__file__).resolve().parents[1] / "audit-lean-export.py"
SPEC = importlib.util.spec_from_file_location("audit_lean_export", SCRIPT)
AUDIT = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(AUDIT)


class OneByteStream:
    def __init__(self, data):
        self.stream = io.BytesIO(data)

    def read(self, size=-1):
        return self.stream.read(1 if size else size)


class BrokenStream:
    def read(self, size=-1):
        raise OSError("fixture read failed")


class AuditLeanExportTests(unittest.TestCase):
    def test_exact_fixture_metrics_and_one_byte_chunks(self):
        source = (b'{"meta":{"name":"x"}}\n'
                  b'{"in":7,"str":{"pre":0,"str":"Nat"}}\n'
                  b'{"def":{"name":1,"type":2,"value":3,"safety":"safe"}}\n')
        report = AUDIT.inspect_stream(OneByteStream(source), len(source), 128, 1)
        self.assertEqual(report["sha256"], hashlib.sha256(source).hexdigest())
        self.assertEqual(report["bytes"], len(source))
        self.assertEqual(report["records"], 3)
        self.assertEqual(report["record_tags"], {
            "axiom": 0, "def": 1, "ie": 0, "il": 0, "in": 1,
            "inductive": 0, "meta": 1, "opaque": 0, "quot": 0,
            "thm": 0, "unknown": 0,
        })
        self.assertEqual(report["declaration_kinds"], {
            "def": 1, "thm": 0, "opaque": 0, "axiom": 0,
            "inductive": 0, "quot": 0,
        })
        self.assertEqual(report["maximum_numeric_ids"], {"in": 7, "il": None, "ie": None})
        self.assertEqual(report["largest_line_bytes"], max(map(len, source.splitlines(keepends=True))))
        self.assertEqual(report["largest_direct_utf8_string_bytes"], 4)
        self.assertEqual(report["authority"], "source-inspection-only")

    def test_trailing_primitive_change_changes_hash(self):
        left = AUDIT.inspect_stream(io.BytesIO(b'{"x":true}\n'))
        right = AUDIT.inspect_stream(io.BytesIO(b'{"x":false}\n'))
        self.assertNotEqual(left["sha256"], right["sha256"])

    def test_bad_records_are_rejected_with_line(self):
        cases = [b'{bad}\n', b'{"x":1,"x":2}\n', b'{"x":"\xff"}\n', b'[]\n']
        for source in cases:
            with self.subTest(source=source), self.assertRaises(AUDIT.InspectionError) as caught:
                AUDIT.inspect_stream(io.BytesIO(source))
            self.assertIn("line 1:", str(caught.exception))

    def test_read_failure_and_exact_bounds(self):
        with self.assertRaisesRegex(AUDIT.InspectionError, "line 1: read failure"):
            AUDIT.inspect_stream(BrokenStream())
        source = b'{"x":1}\n'
        self.assertEqual(AUDIT.inspect_stream(io.BytesIO(source), len(source), len(source))["bytes"], len(source))
        with self.assertRaisesRegex(AUDIT.InspectionError, "total input byte limit"):
            AUDIT.inspect_stream(io.BytesIO(source), len(source) - 1, len(source))
        with self.assertRaisesRegex(AUDIT.InspectionError, "line byte limit"):
            AUDIT.inspect_stream(io.BytesIO(source), len(source), len(source) - 1)

    def test_summary_stays_bounded_for_unknown_tags(self):
        keys = ",".join(f'"tag-{index}":0' for index in range(500))
        report = AUDIT.inspect_stream(io.BytesIO(("{" + keys + "}\n").encode()))
        self.assertEqual(len(report["record_tags"]), len(AUDIT.PROTOCOL_TAGS) + 1)
        self.assertEqual(report["record_tags"]["unknown"], 1)
        self.assertEqual(len(report["declaration_kinds"]), len(AUDIT.DECLARATION_KINDS))
        self.assertEqual(set(report["maximum_numeric_ids"]), set(AUDIT.TABLE_TAGS))

    def test_identity_fixture_protocol_metrics(self):
        fixture = Path(__file__).resolve().parents[2] / "tests/fixtures/lean_export/identity.ndjson"
        with fixture.open("rb") as source:
            report = AUDIT.inspect_stream(source)
        self.assertEqual(report["records"], 28)
        self.assertEqual(report["sha256"], "ad05e4153b542ea6dcd88e4a92d0a8e42ad2d757bdbc19552e3229a979c974ec")
        self.assertEqual(report["record_tags"], {
            "axiom": 0, "def": 1, "ie": 20, "il": 1, "in": 4,
            "inductive": 0, "meta": 1, "opaque": 0, "quot": 0,
            "thm": 1, "unknown": 0,
        })
        self.assertEqual(report["maximum_numeric_ids"], {"in": 4, "il": 1, "ie": 19})

    def test_depth_surrogate_and_internal_bounds(self):
        deep = (b'{"x":' * 65) + b'0' + (b'}' * 65) + b'\n'
        with self.assertRaisesRegex(AUDIT.InspectionError, "line 1: JSON nesting"):
            AUDIT.inspect_stream(io.BytesIO(deep))
        with self.assertRaisesRegex(AUDIT.InspectionError, "line 2: JSON string contains an unpaired surrogate"):
            AUDIT.inspect_stream(io.BytesIO(b'{"x":1}\n{"x":"\\ud800"}\n'))
        for kwargs in ({"max_input_bytes": 0}, {"max_line_bytes": 0},
                       {"chunk_bytes": 0}, {"chunk_bytes": AUDIT.CHUNK_BYTES + 1}):
            with self.subTest(kwargs=kwargs), self.assertRaises(ValueError):
                AUDIT.inspect_stream(io.BytesIO(b'{"x":1}\n'), **kwargs)

    def test_diagnostics_do_not_echo_keys_and_invalid_streams_are_not_eof(self):
        secret_key = "private-" + "x" * 2048
        source = ('{"' + secret_key + '":0,"' + secret_key + '":1}\n').encode()
        with self.assertRaises(AUDIT.InspectionError) as caught:
            AUDIT.inspect_stream(io.BytesIO(source))
        self.assertLess(len(str(caught.exception)), 120)
        self.assertNotIn(secret_key, str(caught.exception))
        class InvalidStream:
            def read(self, _size):
                return None
        with self.assertRaisesRegex(AUDIT.InspectionError, "line 1: input stream"):
            AUDIT.inspect_stream(InvalidStream())

    def test_total_limit_reports_line_where_crossed(self):
        first = b'{"x":1}\n'
        second = b'{"x":2}\n'
        with self.assertRaisesRegex(AUDIT.InspectionError, "line 2: total input byte limit"):
            AUDIT.inspect_stream(io.BytesIO(first + second), len(first) + 1, 64, 64)

    def test_cli_rejects_invalid_limits(self):
        for option, value in (("--max-input-bytes", "0"),
                              ("--max-input-bytes", str(AUDIT.MAX_INPUT_BYTES + 1)),
                              ("--max-line-bytes", str(AUDIT.MAX_LINE_BYTES + 1)),
                              ("--max-line-bytes", "-1")):
            result = subprocess.run([sys.executable, str(SCRIPT), option, value, "unused"],
                                    stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
            self.assertEqual(result.returncode, 2)
            self.assertEqual(result.stdout, b"")


if __name__ == "__main__":
    unittest.main()
