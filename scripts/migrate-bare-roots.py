#!/usr/bin/env python3
"""One-shot source migration; never imported by the compiler.

migrate_source accepts a *program*, not arbitrary syntax data. Callers must
classify Rust strings / Markdown fences first. Nested lists and quotations stay
unchanged. Malformed/unbalanced roots are reported rather than repaired.
Run once against the original revision and review the diff. This helper is
not a parser, formatter, compatibility mode, or a migration-on-load facility.
"""
import argparse
from pathlib import Path
import re

HEADS = set('fn unsafe-fn extern-fn struct enum type let let-mut const static opaque unsafe-impl alias export std cfg-if gn gn-fn capability syntax distributed-enum enum-contribute thread-task generate generated-context require-generated'.split())
TOKEN = re.compile(r'//[^\n]*|#(?!(?:[A-Za-z_!+*/%&|^<>=-]|\\))[^\n]*|"(?:\\.|[^"\\])*"|#\\(?:u\{[0-9a-fA-F]+\}|[^\s(){}\[\]]+|.)|[(){}\[\]]|,@|[\'`,]|[^\s(){}\[\]\'`,"]+')


def migrate_source(source):
    tokens = [(m.group(), m.start(), m.end()) for m in TOKEN.finditer(source)
              if not m.group().startswith('//') and not re.match(r'#(?!(?:[A-Za-z_!+*/%&|^<>=-]|\\))', m.group())]
    stack = []
    roots = []
    root = None
    quoted = False
    bare = None
    closing = {'(': ')', '{': '}', '[': ']'}
    for index, (text, start, end) in enumerate(tokens):
        if not stack:
            line_start = source.rfind('\n', 0, start) + 1
            indent = len(source[line_start:start]) - len(source[line_start:start].lstrip(' \t'))
            if bare is not None and line_start > bare[1] and indent <= bare[0]:
                bare = None
            if text in ("'", '`', ',', ',@'):
                quoted = True
                continue
            if text == '(':
                head = tokens[index + 1][0] if index + 1 < len(tokens) else ''
                root = start if bare is None and not quoted and head.startswith('#') and head[1:] in HEADS else None
            if bare is None and not quoted and text.startswith('#') and text[1:] in HEADS:
                bare = (indent, line_start)
            quoted = False
        if text in closing:
            stack.append(closing[text])
        elif text in closing.values():
            if not stack or stack.pop() != text:
                raise ValueError(f'unbalanced delimiter at byte {start}')
            if not stack and root is not None:
                roots.append((root, end))
                root = None
    if stack:
        raise ValueError('unclosed delimiter; classify/fix the fixture manually')
    output = []
    cursor = 0
    for start, end in roots:
        prefix = source[cursor:start].rstrip(' \t')
        output.append(prefix)
        lines = source[start + 1:end - 1].lstrip().splitlines()
        replacement = lines[0].lstrip()
        if len(lines) > 1:
            replacement += '\n' + '\n'.join('  ' + line for line in lines[1:])
        replacement = replacement.rstrip()
        # Canonical roots previously needed no whitespace between them. A
        # physical newline now provides their unambiguous source boundary.
        if end == len(source) or source[end] not in '\r\n':
            replacement += '\n'
        output.append(replacement)
        cursor = end
        # A canonical root may have been followed by a bare record declaration
        # on the same line. Its old inter-form space is not new indentation.
        adjacent = re.match(r'[ \t]+(?=#(?:fn|unsafe-fn|static|const|generate)\b)', source[end:])
        if adjacent:
            cursor += adjacent.end()
    output.append(source[cursor:])
    return ''.join(output)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('paths', nargs='+', type=Path)
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    for path in args.paths:
        source = path.read_text()
        result = migrate_source(source)
        if args.write:
            path.write_text(result)
        else:
            print(result, end='')

if __name__ == '__main__':
    main()
