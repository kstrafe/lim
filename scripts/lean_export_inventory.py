"""Bounded optional inventory of Lean4Export source records.

This observer supplies source inspection only, never a kernel judgment or a
proof receipt. The caller bounds and parses each input record and supplies a
SHA-256 hash updated through that record's raw bytes. Only selected name
prefixes, primitive counters, and scalar declaration summaries are retained.
Reference checks here do not constitute full export schema or term checking.
Selectors summarize only simple def/thm/opaque/axiom declarations. Inductive
types, constructors, recursors, and quotient declarations are not summarized.
The snapshot's axioms section contains fixed name candidates and preserves
each observed declaration kind; it validates neither signatures nor an axiom
basis, and a definition at one of those names remains a definition.
"""

from __future__ import annotations


MAX_TARGETS = 32
MAX_SELECTOR_BYTES = 512
MAX_SELECTOR_DEPTH = 64
MAX_PREFIXES = 2048
MAX_AXIOM_EXAMPLES = 8
U64_LIMIT = 1 << 64

_AXIOMS = {
    "propext": ("propext",),
    "Classical.choice": ("Classical", "choice"),
    "Quot.sound": ("Quot", "sound"),
}
_AXIOM_PATHS = frozenset(_AXIOMS.values())
_ADMISSION_PATH = ("sorryAx",)
_KINDS = {
    "def": "definition",
    "thm": "theorem",
    "opaque": "opaque",
    "axiom": "axiom",
}
_TABLE_STARTS = {"in": 1, "il": 1, "ie": 0}
_PRIMARY_TAGS = (*_TABLE_STARTS, *_KINDS, "meta", "inductive", "quot")
_VARIANTS = {
    "in": frozenset(("str", "num")),
    "il": frozenset(("succ", "max", "imax", "param")),
    "ie": frozenset(("bvar", "sort", "const", "app", "lam", "forallE",
                      "letE", "proj", "mdata", "natVal", "strVal")),
}


def _index(value, label):
    if type(value) is not int or not 0 <= value < U64_LIMIT:
        raise ValueError(f"{label} must be an unsigned 64-bit integer")
    return value


def _object(value, label):
    if not isinstance(value, dict):
        raise ValueError(f"{label} must be an object")
    return value


def _array(value, label):
    if not isinstance(value, list):
        raise ValueError(f"{label} must be an array")
    return value


def _selector_path(selector):
    if not isinstance(selector, str):
        raise ValueError("target selector must be a string")
    # Bound the encoding allocation before checking its exact UTF-8 size.
    if len(selector) > MAX_SELECTOR_BYTES:
        raise ValueError("target selector exceeds the UTF-8 byte limit")
    try:
        size = len(selector.encode("utf-8"))
    except UnicodeEncodeError:
        raise ValueError("target selector must be valid UTF-8") from None
    if size > MAX_SELECTOR_BYTES:
        raise ValueError("target selector exceeds the UTF-8 byte limit")
    path = tuple(selector.split("."))
    if len(path) > MAX_SELECTOR_DEPTH:
        raise ValueError("target selector exceeds the depth limit")
    for part in path:
        if (not part or not (part[0].isalpha() or part[0] == "_")
                or not all(char.isalnum() or char in "_'" for char in part)):
            raise ValueError("target selector must be a simple dotted identifier")
    return path


def _prefix_sha256(digest):
    try:
        result = digest.hexdigest()
    except (AttributeError, TypeError, ValueError):
        raise ValueError("inventory digest must be a SHA-256 hash") from None
    if (not isinstance(result, str) or len(result) != 64
            or any(char not in "0123456789abcdef" for char in result)):
        raise ValueError("inventory digest must be a SHA-256 hash")
    return result


class PrefixNameMap:
    """Retain IDs only for prefixes of the already bounded selector paths."""

    def __init__(self, paths):
        self._children = {(): {}}
        self._by_id = {0: ()}
        self._by_path = {(): 0}
        for path in paths:
            parent = ()
            for component in path:
                child = parent + (component,)
                if child not in self._children:
                    # Include the implicit root in the bounded prefix map.
                    if len(self._children) >= MAX_PREFIXES:
                        raise ValueError("tracked name prefix limit exceeded")
                    self._children[child] = {}
                    self._children[parent][component] = child
                parent = child

    def observe_string(self, name_id, parent_id, component):
        parent = self._by_id.get(parent_id)
        if parent is None:
            return
        path = self._children[parent].get(component)
        if path is None:
            return
        if path in self._by_path:
            raise ValueError("duplicate tracked name path")
        # Use the configured path, never retain the incoming string object.
        self._by_id[name_id] = path
        self._by_path[path] = name_id

    def path_for(self, name_id):
        return self._by_id.get(name_id)

    def id_for(self, path):
        return self._by_path.get(path)


class SourceInventory:
    """Observe selected declarations without granting checker authority."""

    def __init__(self, targets: list[str]):
        if not isinstance(targets, list) or len(targets) > MAX_TARGETS:
            raise ValueError("targets must be a list of at most 32 selectors")
        self._targets = {}
        for selector in targets:
            path = _selector_path(selector)
            if selector in self._targets:
                raise ValueError("duplicate target selector")
            self._targets[selector] = path
        paths = [*self._targets.values(), *_AXIOMS.values(), _ADMISSION_PATH]
        self._names = PrefixNameMap(paths)
        self._tracked = frozenset(paths)
        self._next_ids = dict(_TABLE_STARTS)
        self._declarations = {}
        self._unknown_axioms = 0
        self._axiom_examples = []

    def _reference(self, value, table, label):
        value = _index(value, label)
        if value >= self._next_ids[table]:
            raise ValueError(f"{label} must refer to an earlier record")
        return value

    def _name_record(self, record, name_id):
        if ("str" in record) == ("num" in record):
            raise ValueError("name record must have one string or numeric component")
        numeric = "num" in record
        component = _object(record["num" if numeric else "str"], "name component")
        parent = self._reference(component.get("pre"), "in", "name prefix")
        if numeric:
            # Numeric Name components cannot match any string selector segment.
            number = component.get("i")
            if type(number) is not int or number < 0:
                raise ValueError("numeric name component must be an unsigned integer")
            return
        part = component.get("str")
        if not isinstance(part, str):
            raise ValueError("string name component must be a string")
        self._names.observe_string(name_id, parent, part)

    def _level_references(self, record):
        if "succ" in record:
            self._reference(record["succ"], "il", "universe predecessor")
        for tag in ("max", "imax"):
            if tag in record:
                pair = _array(record[tag], "universe pair")
                if len(pair) != 2:
                    raise ValueError("universe pair must contain two references")
                for item in pair:
                    self._reference(item, "il", "universe operand")
        if "param" in record:
            self._reference(record["param"], "in", "universe parameter name")

    def _expression_references(self, record):
        if "bvar" in record:
            _index(record["bvar"], "bound variable index")
        if "sort" in record:
            self._reference(record["sort"], "il", "sort universe")
        if "const" in record:
            body = _object(record["const"], "constant expression")
            self._reference(body.get("name"), "in", "constant name")
            for item in _array(body.get("us"), "constant universes"):
                self._reference(item, "il", "constant universe")
        for tag, fields in (("app", ("fn", "arg")),
                            ("lam", ("type", "body")),
                            ("forallE", ("type", "body")),
                            ("letE", ("type", "value", "body"))):
            if tag in record:
                body = _object(record[tag], "compound expression")
                if tag != "app":
                    self._reference(body.get("name"), "in", "binder name")
                for field in fields:
                    self._reference(body.get(field), "ie", "expression operand")
        if "proj" in record:
            body = _object(record["proj"], "projection expression")
            self._reference(body.get("typeName"), "in", "projection family name")
            _index(body.get("idx"), "projection index")
            self._reference(body.get("struct"), "ie", "projection subject")
        if "mdata" in record:
            body = _object(record["mdata"], "metadata expression")
            self._reference(body.get("expr"), "ie", "metadata expression operand")

    def _parameter_count(self, body):
        parameters = _array(body.get("levelParams"), "universe parameters")
        for item in parameters:
            self._reference(item, "in", "universe parameter name")
        return len(parameters)

    def _declaration(self, tag, body, line, digest):
        body = _object(body, "declaration")
        if tag in ("axiom", "opaque") and type(body.get("isUnsafe")) is not bool:
            raise ValueError("declaration isUnsafe flag must be a boolean")
        name_id = self._reference(body.get("name"), "in", "declaration name")
        type_id = self._reference(body.get("type"), "ie", "declaration type")
        value_id = None
        if tag != "axiom" and "value" not in body:
            raise ValueError("declaration initializer is required")
        if "value" in body:
            value_id = self._reference(body["value"], "ie", "declaration initializer")
        parameter_count = self._parameter_count(body)
        path = self._names.path_for(name_id)
        if path in self._tracked:
            if path in self._declarations:
                raise ValueError("duplicate declaration of tracked name")
            self._declarations[path] = {
                "kind": _KINDS[tag],
                "line": line,
                "type_expression_id": type_id,
                "value_expression_id": value_id,
                "universe_parameter_count": parameter_count,
                "prefix_sha256": _prefix_sha256(digest),
            }
        if tag == "axiom" and path not in _AXIOM_PATHS:
            # Every axiom outside the three fixed names is counted, including
            # sorryAx, which also has its dedicated admission summary.
            if self._unknown_axioms >= U64_LIMIT - 1:
                raise ValueError("unrecognized axiom count exceeds the integer limit")
            self._unknown_axioms += 1
            if len(self._axiom_examples) < MAX_AXIOM_EXAMPLES:
                self._axiom_examples.append({"name_id": name_id, "line": line})

    def observe(self, record, line, digest):
        """Observe one parsed record; errors are plain ValueError messages."""
        line = _index(line, "source line")
        if line == 0:
            raise ValueError("source line must be positive")
        record = _object(record, "source record")
        tag = None
        for candidate in _PRIMARY_TAGS:
            if candidate in record:
                if tag is not None:
                    raise ValueError("source record has multiple primary tags")
                tag = candidate
        if tag in _TABLE_STARTS:
            payloads = set(record) - {tag}
            if len(payloads) != 1 or not payloads <= _VARIANTS[tag]:
                raise ValueError("primitive record must have exactly one known variant")
            index = _index(record[tag], "primitive ID")
            if index != self._next_ids[tag]:
                raise ValueError("primitive IDs must be contiguous from their implicit roots")
            if tag == "in":
                self._name_record(record, index)
            elif tag == "il":
                self._level_references(record)
            else:
                self._expression_references(record)
            self._next_ids[tag] += 1
        elif tag in _KINDS:
            self._declaration(tag, record[tag], line, digest)
        elif tag == "quot":
            body = _object(record[tag], "quotient declaration")
            self._reference(body.get("name"), "in", "declaration name")
        elif tag == "inductive":
            body = _object(record[tag], "inductive declaration")
            # The pinned producer groups these three arrays in one record.
            # Inspect member name references without retaining group payloads.
            for field in ("types", "ctors", "recs"):
                if field in body:
                    for member in _array(body[field], "inductive declarations"):
                        member = _object(member, "inductive member")
                        self._reference(member.get("name"), "in", "declaration name")

    def _summary(self, path):
        declaration = self._declarations.get(path)
        return None if declaration is None else dict(declaration)

    def snapshot(self) -> dict:
        """Return detached source summaries containing only bounded scalars."""
        return {
            "authority": "source-inspection-only",
            "targets": {
                selector: {
                    "name_id": self._names.id_for(path),
                    "declaration": self._summary(path),
                }
                for selector, path in self._targets.items()
            },
            "axioms": {name: self._summary(path) for name, path in _AXIOMS.items()},
            "unrecognized_axioms": {
                "count": self._unknown_axioms,
                "examples": [dict(example) for example in self._axiom_examples],
            },
            "admissions": {"sorryAx": self._summary(_ADMISSION_PATH)},
        }
