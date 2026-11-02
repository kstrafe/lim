"""Standard-library regression tests for source-only Lean export inventory."""

import hashlib
import json
from pathlib import Path
import unittest

from lean_export_inventory import SourceInventory


FIXTURE = Path(__file__).resolve().parents[1] / "tests/fixtures/lean_export/identity.ndjson"
IDENTITY_SHA256 = "ad05e4153b542ea6dcd88e4a92d0a8e42ad2d757bdbc19552e3229a979c974ec"
METADATA = {
    "meta": {
        "exporter": {"name": "lean4export", "version": "3.1.0"},
        "lean": {
            "version": "4.33.1",
            "githash": "819816b2e0a3bf405af45ae5c7af2491d8f5bee6",
        },
        "format": {"version": "3.1.0"},
    }
}


class Source:
    """Feed records with their actual line numbers and inclusive raw-byte hash."""

    def __init__(self, selectors, metadata=True):
        self.inventory = SourceInventory(selectors)
        self.prefix = hashlib.sha256()
        self.line = 0
        self.next_name = 1
        self.next_expression = 0
        if metadata:
            self.observe(METADATA)

    def observe(self, record, raw=None):
        if raw is None:
            raw = (json.dumps(record, separators=(",", ":")) + "\n").encode("utf-8")
        self.line += 1
        self.prefix.update(raw)
        self.inventory.observe(record, self.line, self.prefix)

    def name(self, part, prefix=0):
        index = self.next_name
        self.observe({"in": index, "str": {"pre": prefix, "str": part}})
        self.next_name += 1
        return index

    def numeric_name(self, number, prefix=0):
        index = self.next_name
        self.observe({"in": index, "num": {"pre": prefix, "i": number}})
        self.next_name += 1
        return index

    def sort(self, level=0):
        index = self.next_expression
        self.observe({"ie": index, "sort": level})
        self.next_expression += 1
        return index

    def declare(self, tag, name, ty=0, value=0, parameters=()):
        body = {"name": name, "levelParams": list(parameters), "type": ty}
        if tag == "axiom":
            body["isUnsafe"] = False
        else:
            body.update(value=value, all=[name])
            if tag == "def":
                body.update(hints="abbrev", safety="safe")
            elif tag == "opaque":
                body["isUnsafe"] = False
        self.observe({tag: body})
        return {
            "kind": {"thm": "theorem", "def": "definition"}.get(tag, tag),
            "line": self.line,
            "type_expression_id": ty,
            "value_expression_id": None if tag == "axiom" else value,
            "prefix_sha256": self.prefix.hexdigest(),
            "universe_parameter_count": len(parameters),
        }

    def snapshot(self):
        return self.inventory.snapshot()


def empty_snapshot(selectors):
    return {
        "authority": "source-inspection-only",
        "targets": {
            selector: {"name_id": None, "declaration": None} for selector in selectors
        },
        "axioms": {"propext": None, "Classical.choice": None, "Quot.sound": None},
        "unrecognized_axioms": {"count": 0, "examples": []},
        "admissions": {"sorryAx": None},
    }


def retained_items(value, seen=None):
    """Loose container-size check, independent of private attribute names."""
    if seen is None:
        seen = set()
    if id(value) in seen:
        return 0
    seen.add(id(value))
    if isinstance(value, dict):
        return len(value) + sum(
            retained_items(key, seen) + retained_items(item, seen)
            for key, item in value.items()
        )
    if isinstance(value, (list, tuple, set, frozenset)):
        return len(value) + sum(retained_items(item, seen) for item in value)
    if type(value).__module__ == SourceInventory.__module__:
        attributes = getattr(value, "__dict__", None)
        if attributes is not None:
            return retained_items(attributes, seen)
    return 1


class SourceInventoryTests(unittest.TestCase):
    def test_identity_fixture_has_exact_declaration_evidence_and_inclusive_hash(self):
        selector = "Audit.identity.theorem"
        source = Source([selector], metadata=False)
        raw_fixture = FIXTURE.read_bytes()
        self.assertEqual(hashlib.sha256(raw_fixture).hexdigest(), IDENTITY_SHA256)
        for raw in raw_fixture.splitlines(keepends=True):
            source.observe(json.loads(raw), raw)

        expected = empty_snapshot([selector])
        expected["targets"][selector] = {
            "name_id": 3,
            "declaration": {
                "kind": "theorem",
                "line": 28,
                "type_expression_id": 12,
                "value_expression_id": 19,
                "prefix_sha256": IDENTITY_SHA256,
                "universe_parameter_count": 0,
            },
        }
        self.assertEqual(source.snapshot(), expected)
        source.observe({"ie": 20, "bvar": 0})
        self.assertNotEqual(source.prefix.hexdigest(), IDENTITY_SHA256)
        self.assertEqual(source.snapshot(), expected)

    def test_literal_dot_segment_does_not_match_a_hierarchical_selector(self):
        source = Source(["A.b"])
        literal = source.name("A.b")
        source.sort()
        source.declare("thm", literal)
        self.assertEqual(source.snapshot()["targets"]["A.b"], {
            "name_id": None, "declaration": None,
        })
        prefix = source.name("A")
        actual = source.name("b", prefix)
        declaration = source.declare("thm", actual)
        self.assertEqual(source.snapshot()["targets"]["A.b"], {
            "name_id": actual, "declaration": declaration,
        })

    def test_numeric_component_does_not_disappear_into_a_string_path(self):
        source = Source(["A.b"])
        prefix = source.name("A")
        numeric = source.numeric_name(0, prefix)
        nested = source.name("b", numeric)
        source.sort()
        source.declare("thm", nested)
        self.assertIsNone(source.snapshot()["targets"]["A.b"]["name_id"])
        actual = source.name("b", prefix)
        declaration = source.declare("thm", actual)
        self.assertEqual(source.snapshot()["targets"]["A.b"], {
            "name_id": actual, "declaration": declaration,
        })

    def test_duplicate_tracked_name_or_tracked_prefix_is_rejected(self):
        for selector, part in [("Target", "Target"), ("A.b", "A"), ("propext", "propext")]:
            with self.subTest(selector=selector):
                source = Source([selector])
                source.name(part)
                with self.assertRaises(ValueError):
                    source.name(part)

    def test_duplicate_tracked_declaration_is_rejected_even_if_kind_changes(self):
        for tag in ["thm", "def", "axiom"]:
            with self.subTest(tag=tag):
                source = Source(["Target"])
                target = source.name("Target")
                source.sort()
                source.declare("thm", target)
                with self.assertRaises(ValueError):
                    source.declare(tag, target)

    def test_primitive_ids_must_be_contiguous_unsigned_integers_not_booleans(self):
        cases = []
        for index in [0, 2, -1, True, "1", 1.0]:
            cases.append({"in": index, "str": {"pre": 0, "str": "Target"}})
            cases.append({"il": index, "succ": 0})
        for index in [1, -1, False, "0", 0.0]:
            cases.append({"ie": index, "sort": 0})
        for record in cases:
            with self.subTest(record=record):
                source = Source(["Target"])
                with self.assertRaises(ValueError):
                    source.observe(record)

    def test_forward_references_and_boolean_reference_ids_are_rejected(self):
        bad_declaration = {
            "name": 1, "levelParams": [], "type": 0, "value": 0, "all": [1],
        }
        cases = [
            {"in": 2, "str": {"pre": 2, "str": "child"}},
            {"in": 2, "str": {"pre": True, "str": "child"}},
            {"il": 1, "succ": 1},
            {"il": 1, "max": [0, 1]},
            {"il": 1, "imax": [1, 0]},
            {"il": 1, "param": 2},
            {"il": 1, "succ": False},
            {"ie": 1, "sort": 1},
            {"ie": 1, "sort": False},
            {"ie": 1, "const": {"name": 2, "us": []}},
            {"ie": 1, "const": {"name": True, "us": []}},
            {"ie": 1, "const": {"name": 1, "us": [1]}},
            {"ie": 1, "const": {"name": 1, "us": [False]}},
            {"ie": 1, "app": {"fn": 1, "arg": 0}},
            {"ie": 1, "app": {"fn": False, "arg": 0}},
            {"ie": 1, "lam": {"name": 0, "type": 0, "body": 1, "binderInfo": "default"}},
        ]
        for key, value in [
            ("name", 2), ("name", True), ("type", 1), ("type", False),
            ("value", 1), ("value", False), ("levelParams", [2]),
            ("levelParams", [True]),
        ]:
            cases.append({"thm": dict(bad_declaration, **{key: value})})
        for record in cases:
            with self.subTest(record=record):
                source = Source(["Target"])
                source.name("Target")
                source.sort()
                with self.assertRaises(ValueError):
                    source.observe(record)

    def test_malformed_primitive_and_declaration_forms_are_rejected(self):
        cases = [
            {"in": 2, "str": {"str": "missing-prefix"}},
            {"il": 1, "unknown": 0},
            {"il": 1, "max": [0]},
            {"ie": 1, "unknown": 0},
            {"ie": 1, "sort": 0, "bvar": 0},
            {"ie": 1, "app": {"fn": 0}},
            {"thm": {"name": 1, "levelParams": [], "type": 0, "all": [1]}},
            {"def": {"name": 1, "levelParams": [], "type": 0, "all": [1], "hints": "abbrev", "safety": "safe"}},
            {"axiom": {"name": 1, "levelParams": [], "type": 0}},
        ]
        for record in cases:
            with self.subTest(record=record):
                source = Source(["Target"])
                source.name("Target")
                source.sort()
                with self.assertRaises(ValueError):
                    source.observe(record)

    def test_malformed_selectors_and_selector_resource_limits_are_rejected(self):
        for selector in ["", ".A", "A.", "A..b", "A b", "A/b", "A\nb"]:
            with self.subTest(selector=selector), self.assertRaises(ValueError):
                SourceInventory([selector])
        with self.assertRaises(ValueError):
            SourceInventory(["A" * 65537])
        with self.assertRaises(ValueError):
            SourceInventory([".".join(["A"] * 1025)])
        with self.assertRaises(ValueError):
            SourceInventory([f"Target{index}" for index in range(4097)])

    def test_matching_target_definition_is_reported_as_a_definition(self):
        source = Source(["Target"])
        target = source.name("Target")
        source.sort()
        declaration = source.declare("def", target)
        expected = empty_snapshot(["Target"])
        expected["targets"]["Target"] = {"name_id": target, "declaration": declaration}
        self.assertEqual(source.snapshot(), expected)
        self.assertEqual(declaration["kind"], "definition")

    def test_three_exact_basis_paths_and_sorry_ax_admission_are_separate(self):
        source = Source([])
        parameter = source.name("u")
        source.sort()
        propext = source.name("propext")
        classical = source.name("Classical")
        choice = source.name("choice", classical)
        quot = source.name("Quot")
        sound = source.name("sound", quot)
        sorry = source.name("sorryAx")
        expected = empty_snapshot([])
        expected["axioms"]["propext"] = source.declare("axiom", propext)
        expected["axioms"]["Classical.choice"] = source.declare("axiom", choice, parameters=[parameter])
        expected["axioms"]["Quot.sound"] = source.declare("axiom", sound, parameters=[parameter])
        expected["admissions"]["sorryAx"] = source.declare("axiom", sorry, parameters=[parameter])
        expected["unrecognized_axioms"] = {
            "count": 1, "examples": [{"name_id": sorry, "line": source.line}]
        }
        self.assertEqual(source.snapshot(), expected)

    def test_dotted_literal_nested_and_numeric_axiom_names_do_not_spoof_basis(self):
        source = Source([])
        source.sort()
        literal_choice = source.name("Classical.choice")
        literal_sound = source.name("Quot.sound")
        other = source.name("Other")
        nested_propext = source.name("propext", other)
        nested_sorry = source.name("sorryAx", other)
        classical = source.name("Classical")
        number = source.numeric_name(0, classical)
        numeric_choice = source.name("choice", number)
        names = [literal_choice, literal_sound, nested_propext, nested_sorry, numeric_choice]
        examples = []
        for name in names:
            source.declare("axiom", name)
            examples.append({"name_id": name, "line": source.line})
        expected = empty_snapshot([])
        expected["unrecognized_axioms"] = {"count": len(names), "examples": examples}
        self.assertEqual(source.snapshot(), expected)

    def test_unrecognized_axiom_count_is_exact_and_examples_are_bounded(self):
        source = Source([])
        source.sort()
        observed = []
        for index in range(24):
            name = source.name(f"Unrecognized{index}")
            source.declare("axiom", name)
            observed.append({"name_id": name, "line": source.line})
        result = source.snapshot()["unrecognized_axioms"]
        self.assertEqual(result["count"], 24)
        self.assertGreater(len(result["examples"]), 0)
        self.assertLessEqual(len(result["examples"]), 8)
        self.assertEqual(len({item["name_id"] for item in result["examples"]}), len(result["examples"]))
        for item in result["examples"]:
            self.assertIn(item, observed)

    def test_irrelevant_name_prefix_does_not_grow_retained_inventory_state(self):
        sizes = []
        for count in [64, 4096]:
            source = Source(["A.b"])
            for index in range(count):
                source.name(f"Irrelevant{index}")
            prefix = source.name("A")
            target = source.name("b", prefix)
            source.sort()
            declaration = source.declare("thm", target)
            snapshot = source.snapshot()
            self.assertEqual(snapshot["targets"]["A.b"], {
                "name_id": count + 2, "declaration": declaration,
            })
            sizes.append((retained_items(source.inventory), len(json.dumps(snapshot))))
        self.assertLessEqual(sizes[1][0], sizes[0][0] + 128)
        self.assertLessEqual(sizes[1][1], sizes[0][1] + 128)


if __name__ == "__main__":
    unittest.main()
