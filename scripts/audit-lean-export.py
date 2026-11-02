#!/usr/bin/env python3
"""Bounded-memory metrics for a Lean4Export NDJSON source file.

This is source inspection only. It does not check Lean terms, signatures,
export schema correctness, or provide proof-checking/receipt authority.
"""

import argparse
import hashlib
import json
from pathlib import Path
import runpy
import sys
from collections import Counter


DEFAULT_LINE_BYTES = 8 * 1024 * 1024
DEFAULT_INPUT_BYTES = 64 * 1024 * 1024
MAX_LINE_BYTES = 8 * 1024 * 1024
MAX_INPUT_BYTES = 64 * 1024 * 1024 * 1024
CHUNK_BYTES = 64 * 1024
MAX_JSON_DEPTH = 64
TABLE_TAGS = ("in", "il", "ie")
PROTOCOL_TAGS = ("meta", *TABLE_TAGS, "def", "thm", "opaque", "axiom",
                 "inductive", "quot")
DECLARATION_KINDS = ("def", "thm", "opaque", "axiom", "inductive", "quot")
UNKNOWN = "unknown"


class InspectionError(Exception):
    def __init__(self, line, message):
        super().__init__(f"line {line}: {message}")
        self.line = line


def _unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError("duplicate JSON key")
        result[key] = value
    return result


def _parse_constant(value):
    raise ValueError(f"invalid JSON number {value}")


def inspect_stream(stream, max_input_bytes=DEFAULT_INPUT_BYTES,
                   max_line_bytes=DEFAULT_LINE_BYTES, chunk_bytes=CHUNK_BYTES,
                   targets=()):
    """Inspect a stream with bounded metrics and optional target summaries."""
    for label, bound in (("max_input_bytes", max_input_bytes),
                         ("max_line_bytes", max_line_bytes),
                         ("chunk_bytes", chunk_bytes)):
        if type(bound) is not int or bound <= 0:
            raise ValueError(f"{label} must be a positive integer")
    if max_input_bytes > MAX_INPUT_BYTES or max_line_bytes > MAX_LINE_BYTES:
        raise ValueError("inspection bound exceeds the supported maximum")
    if chunk_bytes > CHUNK_BYTES:
        raise ValueError("chunk_bytes exceeds the supported maximum")
    inventory = inventory_class()(targets) if targets else None
    digest = hashlib.sha256()
    counts = Counter({tag: 0 for tag in (*PROTOCOL_TAGS, UNKNOWN)})
    kinds = Counter({kind: 0 for kind in DECLARATION_KINDS})
    maximum_ids = {tag: None for tag in TABLE_TAGS}
    total = records = largest_line = largest_string = 0
    pending = bytearray()
    line_number = 0

    def process(raw, number):
        nonlocal records, largest_line, largest_string
        if inventory is not None:
            # Targets need the prefix through this exact record, even when
            # the input chunk already contains later records or a partial line.
            digest.update(raw)
        content = raw[:-1] if raw.endswith(b"\n") else raw
        if content.endswith(b"\r"):
            content = content[:-1]
        try:
            source = content.decode("utf-8")
            value = json.loads(source, object_pairs_hook=_unique_object,
                               parse_constant=_parse_constant)
            _validate_tree(value, number)
        except (UnicodeDecodeError, json.JSONDecodeError, ValueError,
                RecursionError) as exc:
            raise InspectionError(number, f"invalid UTF-8/JSON ({exc})") from exc
        if not isinstance(value, dict):
            raise InspectionError(number, "record must be a JSON object")
        records += 1
        largest_line = max(largest_line, len(raw))
        for item in _walk_values(value):
            if isinstance(item, str):
                largest_string = max(largest_string, len(item.encode("utf-8")))
        primary = [key for key in PROTOCOL_TAGS if key in value]
        category = primary[0] if len(primary) == 1 else UNKNOWN
        counts[category] += 1
        if category in DECLARATION_KINDS:
            kinds[category] += 1
        for key in TABLE_TAGS:
            item = value.get(key)
            if type(item) is int and item >= 0:
                previous = maximum_ids[key]
                maximum_ids[key] = item if previous is None else max(previous, item)
        if inventory is not None:
            try:
                inventory.observe(value, number, digest)
            except ValueError as exc:
                raise InspectionError(number, str(exc)) from exc

    try:
        while True:
            chunk = stream.read(chunk_bytes)
            if not isinstance(chunk, (bytes, bytearray)):
                raise InspectionError(line_number + 1, "input stream did not return bytes")
            if not chunk:
                break
            available = max_input_bytes - total
            exceeded = len(chunk) > available
            accepted = chunk[:available] if exceeded else chunk
            total += len(accepted)
            if inventory is None:
                digest.update(accepted)
            start = 0
            while True:
                end = accepted.find(b"\n", start)
                part = accepted[start:] if end < 0 else accepted[start:end + 1]
                if len(pending) + len(part) > max_line_bytes:
                    raise InspectionError(line_number + 1, "line byte limit exceeded")
                pending.extend(part)
                if end < 0:
                    break
                line_number += 1
                process(bytes(pending), line_number)
                pending.clear()
                start = end + 1
            if exceeded:
                raise InspectionError(line_number + 1, "total input byte limit exceeded")
        if pending:
            line_number += 1
            process(bytes(pending), line_number)
    except InspectionError:
        raise
    except (OSError, UnicodeError) as exc:
        raise InspectionError(line_number + 1, f"read failure ({exc})") from exc

    report = {
        "schema": "lean4export-source-inspection-v1",
        "authority": "source-inspection-only",
        "sha256": digest.hexdigest(),
        "bytes": total,
        "records": records,
        "record_tags": {key: counts[key] for key in sorted(counts)},
        "declaration_kinds": {key: kinds[key] for key in DECLARATION_KINDS},
        "maximum_numeric_ids": maximum_ids,
        "largest_line_bytes": largest_line,
        "largest_direct_utf8_string_bytes": largest_string,
    }
    if inventory is not None:
        report["source_inventory"] = inventory.snapshot()
    return report


def inventory_class():
    # File-relative loading also supports importlib-based callers outside
    # scripts/. This is repository code, never a module from the inspected file.
    path = Path(__file__).with_name("lean_export_inventory.py")
    return runpy.run_path(str(path))["SourceInventory"]


def _walk_values(value):
    pending = [value]
    while pending:
        current = pending.pop()
        if isinstance(current, dict):
            pending.extend(current.values())
        elif isinstance(current, list):
            pending.extend(current)
        else:
            yield current


def _validate_tree(root, line_number):
    """Check nesting and UTF-8 string encodability with iterative traversal."""
    pending = [(root, 1)]
    while pending:
        value, depth = pending.pop()
        if depth > MAX_JSON_DEPTH:
            raise InspectionError(line_number, f"JSON nesting exceeds {MAX_JSON_DEPTH}")
        if isinstance(value, dict):
            for key, item in value.items():
                try:
                    key.encode("utf-8")
                except UnicodeEncodeError as exc:
                    raise InspectionError(line_number, "JSON string contains an unpaired surrogate") from exc
                pending.append((item, depth + 1))
        elif isinstance(value, list):
            pending.extend((item, depth + 1) for item in value)
        elif isinstance(value, str):
            try:
                value.encode("utf-8")
            except UnicodeEncodeError as exc:
                raise InspectionError(line_number, "JSON string contains an unpaired surrogate") from exc


def positive_decimal(text):
    if not text.isascii() or not text.isdecimal() or int(text) <= 0:
        raise argparse.ArgumentTypeError("must be a positive decimal integer")
    return int(text)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", help="Lean4Export NDJSON source file")
    parser.add_argument("--max-input-bytes", type=positive_decimal,
                        default=DEFAULT_INPUT_BYTES,
                        help="total input bound, up to 64 GiB (default: 64 MiB)")
    parser.add_argument("--max-line-bytes", type=positive_decimal,
                        default=DEFAULT_LINE_BYTES,
                        help="line bound, up to 8 MiB (default: 8 MiB)")
    parser.add_argument("--target", action="append", default=[],
                        help="observe a simple dotted declaration name "
                             "(repeat up to 32 times); no proof checking")
    args = parser.parse_args(argv)
    if args.max_input_bytes > MAX_INPUT_BYTES:
        parser.error("--max-input-bytes cannot exceed 64 GiB")
    if args.max_line_bytes > MAX_LINE_BYTES:
        parser.error("--max-line-bytes cannot exceed 8 MiB")
    if args.target:
        try:
            inventory_class()(args.target)
        except ValueError as exc:
            parser.error(str(exc))
    try:
        with open(args.input, "rb") as source:
            report = inspect_stream(source, args.max_input_bytes, args.max_line_bytes,
                                    targets=args.target)
    except (OSError, InspectionError) as exc:
        print(f"audit-lean-export: {exc}", file=sys.stderr)
        return 1
    print(json.dumps(report, sort_keys=True, separators=(",", ":")))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
