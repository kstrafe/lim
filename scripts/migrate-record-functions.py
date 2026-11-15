#!/usr/bin/env python3
"""One-shot migration of authored function declarations to named records.

API: migrate_source(program: str) -> str; MigrationError leaves input untouched.
Callers must classify programs separately from Rust strings, Markdown syntax
examples, quoted generator trees and intentionally malformed fixtures first.
Only root declarations and #cfg-if/#cfg-else declaration branches are visited.
In particular, #generate ... (function (#fn ...)) is generator data, not an
authored function declaration. Function bodies, parameter binders and comments
are preserved; existing contract clauses remain at the front of #body.
This is not a compiler reader, a compatibility flag or a migration-on-load path.
"""

import argparse
from dataclasses import dataclass
from pathlib import Path
import re
import sys


class MigrationError(ValueError):
    pass


TOKEN = re.compile(
    r'//[^\n]*|"(?:\\.|[^"\\])*"|#\\(?:u\{[0-9a-fA-F]+\}|[^\s(){}\[\]]+|.)'
    r'''|[(){}\[\];]|,@|['`,]|(?:(?!//)[^\s(){}\[\];'`,"])+'''
)
OPEN = {"(": ")", "{": "}", "[": "]"}
CLOSE = set(OPEN.values())
FUNCTIONS = {"#fn", "#unsafe-fn", "#extern-fn"}
SECTIONS = {"#params", "#returns", "#requires", "#ensures", "#preserves", "#body"}


@dataclass(frozen=True)
class Token:
    text: str
    start: int
    end: int


class Migration:
    def __init__(self, source):
        self.source = source
        self.tokens = []
        previous = 0
        for match in TOKEN.finditer(source):
            if source[previous:match.start()].strip():
                raise MigrationError(f"unrecognized or unterminated literal at character {previous}")
            if not match.group().startswith("//"):
                self.tokens.append(Token(match.group(), match.start(), match.end()))
            previous = match.end()
        if source[previous:].strip():
            raise MigrationError(f"unrecognized or unterminated literal at character {previous}")
        self.pairs = {}
        stack = []
        for index, token in enumerate(self.tokens):
            if token.text in OPEN:
                stack.append(index)
            elif token.text in CLOSE:
                if not stack or OPEN[self.tokens[stack[-1]].text] != token.text:
                    raise MigrationError(f"mismatched delimiter at character {token.start}")
                opening = stack.pop()
                self.pairs[opening] = index
        if stack:
            raise MigrationError(f"unclosed delimiter at character {self.tokens[stack[-1]].start}")
        self.edits = []

    def indentation(self, offset):
        line = self.source.rfind("\n", 0, offset) + 1
        return len(self.source[line:offset]) - len(self.source[line:offset].lstrip(" \t"))

    def form_end(self, index, limit):
        if index >= limit:
            raise MigrationError("incomplete declaration header")
        text = self.tokens[index].text
        if text in ("'", "`", ",", ",@"):
            return self.form_end(index + 1, limit)
        if text in OPEN:
            end = self.pairs[index] + 1
            if end > limit:
                raise MigrationError("declaration boundary splits a delimiter")
            return end
        return index + 1

    def text(self, start, end):
        return self.source[self.tokens[start].start:self.tokens[end - 1].end]

    def roots(self):
        index = 0
        while index < len(self.tokens):
            if self.tokens[index].text == ";":
                index += 1
                continue
            start = index
            baseline = self.indentation(self.tokens[start].start)
            while index < len(self.tokens):
                if index > start:
                    token = self.tokens[index]
                    gap = self.source[self.tokens[index - 1].end:token.start]
                    nested_line = (self.source.find("\n", self.tokens[start].end, token.start) != -1
                                   and self.indentation(token.start) > baseline)
                    if ((token.text == ";" and not nested_line)
                            or ("\n" in gap and self.indentation(token.start) <= baseline)):
                        break
                index = self.form_end(index, len(self.tokens))
            yield start, index

    def declaration(self, start, end, nested=False):
        if start >= end:
            return
        if self.tokens[start].text in ("'", "`", ",", ",@"):
            return
        if self.tokens[start].text == "(":
            if not nested:
                raise MigrationError("explicit root wrapper: classify syntax data/negative fixture first")
            if self.pairs[start] != end - 1:
                raise MigrationError("cfg branch must contain exactly one declaration form")
            start += 1
            end -= 1
        if start >= end:
            return
        head = self.tokens[start].text
        if head in FUNCTIONS:
            self.function(start, end)
        elif head in ("#cfg-if", "#cfg-else"):
            index = start + 1
            if head == "#cfg-if":
                index = self.form_end(index, end)
            while index < end:
                if self.tokens[index].text in (":", ";"):
                    index += 1
                    continue
                branch_end = self.form_end(index, end)
                # Declaration branches have a grouping list; an ungrouped
                # function needs manual boundary classification, not guessing.
                if self.tokens[index].text in FUNCTIONS:
                    raise MigrationError("ungrouped cfg declaration: classify its layout boundary manually")
                self.declaration(index, branch_end, nested=True)
                index = branch_end
        elif not head.startswith("#"):
            raise MigrationError(f"source root '{head}' at character {self.tokens[start].start} is not a bare declaration; classify the input first")

    def separator(self, gap, indent):
        return gap if gap.strip() else "\n" + indent

    def function(self, start, end):
        head = self.tokens[start].text
        external = head == "#extern-fn"
        name = start + 1
        if name + 1 >= end:
            raise MigrationError("incomplete function declaration")
        # New records are idempotent. Legacy externs put the ABI before name.
        if self.tokens[name + 1].text == "{" and not (external and self.tokens[name].text.startswith("#abi-")):
            return
        abi = None
        if external:
            abi = name
            name += 1
        parameters = name + 1
        parameters_end = self.form_end(parameters, end)
        if self.tokens[parameters].text == "(" and parameters + 1 < parameters_end and self.tokens[parameters + 1].text in SECTIONS:
            if external:
                raise MigrationError("legacy extern sections are unsupported; rewrite its signature manually")
            self.section_function(start, name, parameters, end)
            return
        returns = parameters_end
        returns_end = self.form_end(returns, end)
        if external and returns_end != end:
            raise MigrationError("external declaration has trailing forms; preserve its negative-test intent manually")
        if not external and returns_end == end:
            raise MigrationError("function has no body; classify its header fragment/negative-test intent manually")
        if not external and returns_end < end and self.tokens[returns_end].text == ":":
            raise MigrationError("positional function with a layout body: classify its body collection manually")
        token = self.tokens[start]
        indent = " " * self.indentation(token.start)
        field = indent + "  "
        if external:
            gap = self.source[token.end:self.tokens[abi].start] + self.source[self.tokens[abi].end:self.tokens[name].start]
            prefix = token.text + gap + self.tokens[name].text
        else:
            prefix = self.source[token.start:self.tokens[name].end]
        output = prefix + " {"
        if external:
            output += "\n" + field + "#abi = " + self.tokens[abi].text + ";"
        gap = self.source[self.tokens[name].end:self.tokens[parameters].start]
        output += self.separator(gap, field) + "#params = " + self.text(parameters, parameters_end) + ";"
        gap = self.source[self.tokens[parameters_end - 1].end:self.tokens[returns].start]
        output += self.separator(gap, field) + "#returns = " + self.text(returns, returns_end) + ";"
        finish = self.tokens[end].start if end < len(self.tokens) and self.tokens[end].text == ")" else self.tokens[end - 1].end
        if not external:
            # Original statements and leading contract clauses are a list
            # value. The source reader lowers it to exactly the former body.
            body = self.source[self.tokens[returns_end - 1].end:finish]
            output += "\n" + field + "#body = (" + body + "\n" + field + ");"
        output += "\n" + indent + "}"
        self.edits.append((token.start, finish, output))

    def section_function(self, start, name, index, end):
        token = self.tokens[start]
        indent = " " * self.indentation(token.start)
        field = indent + "  "
        output = self.source[token.start:self.tokens[name].end] + " {"
        previous = self.tokens[name].end
        seen = set()
        while index < end:
            section_end = self.form_end(index, end)
            if self.tokens[index].text != "(" or index + 1 >= section_end:
                raise MigrationError("function sections must be explicit lists")
            key = self.tokens[index + 1].text
            if key not in SECTIONS or key in seen:
                raise MigrationError("unknown/duplicate function section; preserve the diagnostic manually")
            seen.add(key)
            gap = self.source[previous:self.tokens[index].start]
            inner = self.source[self.tokens[index + 1].end:self.tokens[section_end - 1].start]
            value = inner.strip() if key in ("#params", "#returns") else "(" + inner + ")"
            output += self.separator(gap, field) + key + " = " + value + ";"
            previous = self.tokens[section_end - 1].end
            index = section_end
        finish = self.tokens[end].start if end < len(self.tokens) and self.tokens[end].text == ")" else previous
        output += self.source[previous:finish] + "\n" + indent + "}"
        self.edits.append((token.start, finish, output))

    def run(self):
        for start, end in self.roots():
            self.declaration(start, end)
        output = self.source
        for start, end, replacement in sorted(self.edits, reverse=True):
            output = output[:start] + replacement + output[end:]
        return output


def migrate_source(source):
    """Migrate one classified complete program, or raise without changing it."""
    return Migration(source).run()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("paths", nargs="+", type=Path)
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--check", action="store_true", help="report files needing migration; do not write")
    args = parser.parse_args()
    if args.write and args.check:
        parser.error("--write and --check are mutually exclusive")
    changed = False
    failed = False
    for path in args.paths:
        source = path.read_text()
        try:
            result = migrate_source(source)
        except MigrationError as error:
            print(f"{path}: {error}", file=sys.stderr)
            failed = True
            continue
        if result != source:
            changed = True
            if args.check:
                print(path)
        if args.write:
            path.write_text(result)
        elif not args.check:
            print(result, end="")
    sys.exit(2 if failed else int(args.check and changed))


if __name__ == "__main__":
    main()
