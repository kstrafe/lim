#!/usr/bin/env python3
"""Bounded, offline effect-declaration inventory and migration for Lim sources.

Defaults to a JSON review plan; --write installs explicit declarations in the
listed .lim files only. This is not a compiler pass, proof, or compatibility
switch. Unknown callbacks remain explicit effects-of references. Generator
fragments are listed for review; no fixture or Rust string is changed implicitly.
"""
import argparse
from collections import defaultdict
from dataclasses import dataclass, field
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("lim_record_migration", HERE / "migrate-record-functions.py")
reader = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = reader
spec.loader.exec_module(reader)
MAX_BYTES = 2 * 1024 * 1024
MAX_TOKENS = 300_000
MAX_FUNCTIONS = 10_000
MAX_DEPTH = 200
WRITES = {"#atomic-store", "#atomic-fetch-add", "#atomic-exchange",
          "#atomic-compare-exchange", "#atomic-compare-exchange-weak",
          "#deref-set", "#pin-write", "#pin-set-field", "#borrow-mut",
          "#pin-borrow-mut", "#pin", "#borrow-slice-mut"}
RAW = {"#asm", "#linux-syscall", "#ptr-read", "#ptr-write", "#ptr-borrow",
       "#ptr-borrow-mut", "#pin-ptr-borrow", "#pin-ptr-borrow-mut",
       "#word-view", "#word-read", "#word-take", "#word-forget", "#word-write",
       "#pin-shared-borrow", "#pin-shared-borrow-mut", "#pin-shared-release"}


@dataclass
class Node:
    start: int
    end: int
    text: str
    children: list = field(default_factory=list)
    kind: str = ""

    @property
    def head(self):
        return self.children[0].text if self.children else ""


@dataclass
class Function:
    path: Path
    name: str
    body: list
    insert: int
    record: bool
    indent: str
    line: int
    existing: bool
    declared: set = field(default_factory=set)
    direct: set = field(default_factory=set)
    calls: dict = field(default_factory=dict)
    fragments: set = field(default_factory=set)
    mutations: set = field(default_factory=set)
    origins: dict = field(default_factory=dict)
    effects: set = field(default_factory=set)


class Source:
    def __init__(self, path):
        self.path = path.resolve()
        if path.stat().st_size > MAX_BYTES:
            raise ValueError(f"{path}: exceeds {MAX_BYTES} byte review limit")
        self.text = path.read_text()
        if len(self.text.encode()) > MAX_BYTES:
            raise ValueError(f"{path}: exceeds {MAX_BYTES} byte review limit")
        lex = reader.Migration(self.text)
        if len(lex.tokens) > MAX_TOKENS:
            raise ValueError(f"{path}: exceeds token limit")
        self.tokens = lex.tokens

        def parse(index, depth=0):
            if depth > MAX_DEPTH:
                raise ValueError(f"{path}: exceeds structural depth limit")
            token = self.tokens[index]
            if token.text in ("'", "`", ",", ",@"):
                child, end = parse(index + 1, depth + 1)
                return Node(token.start, child.end, self.text[token.start:child.end], [child], token.text), end
            if token.text in reader.OPEN:
                end = lex.pairs[index]
                children = []
                cursor = index + 1
                while cursor < end:
                    child, cursor = parse(cursor, depth + 1)
                    children.append(child)
                finish = self.tokens[end].end
                return Node(token.start, finish, self.text[token.start:finish], children, token.text), end + 1
            return Node(token.start, token.end, token.text), index + 1

        children = []
        cursor = 0
        while cursor < len(self.tokens):
            child, cursor = parse(cursor)
            children.append(child)
        self.root = Node(0, len(self.text), self.text, children, "root")
        self.functions = []
        self.aliases = {}
        self.globals = set()
        self.helpers = {}
        self._discover(self.root)
        if len(self.functions) > MAX_FUNCTIONS:
            raise ValueError(f"{path}: exceeds function review limit")
        ranges = [(f.body[0].start, f.body[-1].end) for f in self.functions if f.body]
        for i, node in enumerate(self.root.children):
            if node.text == "#alias" and i + 3 < len(self.root.children):
                self.aliases[self.root.children[i + 1].text] = self.root.children[i + 3].text
        for node in self.nodes(self.root):
            xs = node.children
            for i, child in enumerate(xs[:-1]):
                if child.text in ("#static", "#let") and not any(a <= child.start < b for a, b in ranges):
                    if not xs[i + 1].children:
                        self.globals.add(xs[i + 1].text)
                if child.text in ("#gn-fn", "#gn") and i + 3 < len(xs):
                    self.helpers[xs[i + 1].text] = xs[i + 3]

    @staticmethod
    def nodes(node):
        yield node
        for child in node.children:
            yield from Source.nodes(child)

    def _discover(self, node):
        xs = node.children
        for i, child in enumerate(xs):
            if child.text not in ("#fn", "#unsafe-fn", "#extern-fn") or i + 2 >= len(xs):
                continue
            external = child.text == "#extern-fn"
            name = xs[i + 1]
            signature = xs[i + 2]
            if signature.kind == "{":
                sections = {}
                fields = signature.children
                j = 0
                while j < len(fields):
                    if fields[j].text == ";":
                        j += 1
                        continue
                    if j + 2 >= len(fields) or fields[j + 1].text != "=":
                        raise ValueError(f"{self.path}: record needs manual section classification")
                    sections[fields[j].text] = (fields[j], fields[j + 2])
                    j += 3
                body = [sections["#body"][1]] if "#body" in sections else []
                position = sections["#body"][0].start if "#body" in sections else signature.end - 1
                existing = "#effects" in sections
                written = sections["#effects"][1].children if existing else []
                params = sections.get("#params", (None, Node(0, 0, "")))[1]
                record = True
            else:
                if i != 0 or node.kind != "(":
                    raise ValueError(f"{self.path}: positional function boundary needs manual classification")
                offset = 1 if external else 0
                if len(xs) < 4 + offset:
                    raise ValueError(f"{self.path}: incomplete generated function signature")
                name = xs[1 + offset]
                params = xs[2 + offset]
                returns = xs[3 + offset]
                body = xs[4 + offset:]
                position = returns.end
                existing = bool(body and body[0].head == "#effects")
                written = body[0].children[1].children if existing else []
                record = False
            line_start = self.text.rfind("\n", 0, position) + 1
            before = self.text[line_start:position]
            origin_line = self.text.rfind("\n", 0, child.start) + 1
            leading = self.text[origin_line:child.start]
            indent = before if not before.strip() else " " * (len(leading) - len(leading.lstrip()) + 2)
            function = Function(self.path, name.text, body, position, record, indent,
                                self.text.count("\n", 0, child.start) + 1, existing)
            function.declared = {n.text for n in written}
            if external:
                function.direct.update(("#io", "#global-access"))
            if params.kind == "{":
                j = 0
                while j < len(params.children):
                    if params.children[j].text == ";":
                        j += 1
                        continue
                    if j + 2 >= len(params.children) or params.children[j + 1].text != "=":
                        raise ValueError(f"{self.path}: parameter record needs manual classification")
                    binder = params.children[j].text
                    function.origins[binder] = {"param:" + binder}
                    j += 3
            else:
                for parameter in params.children:
                    if parameter.children:
                        binder = parameter.children[1 if parameter.head == "#mut" else 0].text
                        function.origins[binder] = {"param:" + binder}
            self.functions.append(function)
        for child in xs:
            self._discover(child)


def key(text):
    return re.sub(r"\s+", " ", text).strip()


class Plan:
    def __init__(self, paths):
        self.sources = {p.resolve(): Source(p) for p in paths}
        self.functions = [f for s in self.sources.values() for f in s.functions]
        if len(self.functions) > MAX_FUNCTIONS:
            raise ValueError("combined plan exceeds function limit; split the input")
        self.named = defaultdict(list)
        for f in self.functions:
            self.named[(f.path, key(f.name))].append(f)
        for f in self.functions:
            self.scan(f)
        for _ in range(len(self.functions) + 1):
            changed = False
            for f in self.functions:
                effects = set(f.direct) | f.declared
                for spelling, node in f.calls.items():
                    targets = self.lookup(f.path, spelling)
                    if not targets or any(t.effects or t.direct for t in targets):
                        effects.add(f"(#effects-of {node.text})")
                if effects != f.effects:
                    f.effects = effects
                    changed = True
            if not changed:
                break
        else:
            raise ValueError("effect dependency closure exceeded review budget")

    def canonical(self, path, spelling, active=None):
        active = set() if active is None else active
        spelling = spelling.lstrip("@")
        identity = path, key(spelling)
        if identity in active:
            return identity
        active.add(identity)
        source = self.sources.get(path)
        alias = source.aliases.get(spelling) if source else None
        target = alias or spelling
        if ".lim::" in target:
            file, name = target.split(".lim::", 1)
            file += ".lim"
            if file.startswith("/<lim-std>/"):
                file = str(HERE.parent / "library" / Path(file).name)
            resolved = (path.parent / file).resolve()
            return self.canonical(resolved, name, active)
        return identity

    def lookup(self, path, spelling):
        return self.named.get(self.canonical(path, spelling), [])

    def scan(self, f):
        source = self.sources[f.path]

        def origins(node):
            if not node.children:
                if node.text in f.origins:
                    return f.origins[node.text]
                path, name = self.canonical(f.path, node.text)
                other = self.sources.get(path)
                if other and name in other.globals:
                    return {node.text}
                return set()
            return set().union(*(origins(n) for n in node.children))

        def visit(node, active=None):
            active = set() if active is None else active
            if node.head in ("#effects", "#requires", "#ensures", "#preserves"):
                return
            xs = node.children
            if node.head in ("#call", "#unsafe-call") and len(xs) >= 2:
                f.calls[key(xs[1].text)] = xs[1]
            if (node.kind == "(" and len(xs) == 2 and xs[1].kind == "{"
                    and node.head and not node.head.startswith("#")):
                f.calls[key(xs[0].text)] = xs[0]
                f.fragments.add("surface application: " + xs[0].text)
            if node.head == "#println":
                f.calls["std-println"] = Node(0, 0, "std-println")
            if node.head in RAW:
                f.direct.update(("#io", "#global-access"))
            if node.head == "#io-input-byte":
                f.direct.add("#io-input")
            if node.head == "#io-output-byte":
                f.direct.add("#io-output")
            if node.head == "#gn-call" and len(xs) >= 2:
                helper = xs[1].text
                f.fragments.add(helper)
                if helper in source.helpers and helper not in active:
                    # A generator fragment can emit primitive operations, but
                    # its parameter bindings require human review. Do not copy
                    # helper-local callback spellings into runtime interfaces.
                    fragment = source.helpers[helper]
                    if any(n.head in RAW for n in Source.nodes(fragment)):
                        f.direct.update(("#io", "#global-access"))
                return
            if node.head in WRITES and len(xs) >= 2:
                for target in origins(xs[1]):
                    if target.startswith("param:"):
                        f.mutations.add(target[6:])
                    else:
                        f.direct.discard(f"(#read-global {target})")
                        f.direct.add(f"(#write-global {target})")
            if node.head in ("#let", "#let-mut", "#const") and len(xs) >= 4:
                f.origins[xs[1].text] = origins(xs[3])
            if not xs:
                for target in origins(node):
                    if not target.startswith("param:") and f"(#write-global {target})" not in f.direct:
                        f.direct.add(f"(#read-global {target})")
            for child in xs:
                visit(child, active)
        for body in f.body:
            visit(body)

    def rows(self):
        return [{"path": str(f.path), "line": f.line, "function": f.name,
                 "direct": sorted(f.direct), "effects": sorted(f.effects),
                 "written": sorted(f.declared),
                 "unknown_callees_to_review": sorted(spelling for spelling in f.calls if not self.lookup(f.path, spelling)),
                 "fragments_to_review": sorted(f.fragments),
                 "already_annotated": f.existing,
                 "parameter_mutations_to_review": sorted(f.mutations)} for f in self.functions]

    def write(self):
        for source in self.sources.values():
            edits = []
            for f in source.functions:
                if f.existing or not f.effects:
                    continue
                value = "(" + " ".join(sorted(f.effects)) + ")"
                declaration = f"#effects = {value};\n{f.indent}" if f.record else f"\n{f.indent}(#effects {value})"
                edits.append((f.insert, declaration))
            text = source.text
            for position, declaration in sorted(edits, reverse=True):
                text = text[:position] + declaration + text[position:]
            if text != source.text:
                source.path.write_text(text)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("paths", nargs="+", type=Path)
    parser.add_argument("--write", action="store_true", help="install reviewed declarations in the listed .lim files")
    args = parser.parse_args()
    if len(args.paths) > 128 or any(p.suffix != ".lim" for p in args.paths):
        parser.error("pass at most 128 explicit .lim paths; extract/classify Rust fixtures separately")
    try:
        if sum(p.stat().st_size for p in args.paths) > 8 * MAX_BYTES:
            raise ValueError("combined input exceeds the 16 MiB review limit")
        plan = Plan(args.paths)
        if args.write:
            plan.write()
        json.dump(plan.rows(), sys.stdout, indent=2)
        print()
    except (ValueError, OSError) as error:
        parser.exit(1, f"migration stopped: {error}\n")


if __name__ == "__main__":
    main()
