#!/usr/bin/env python3
"""Build a deterministic, self-contained manual with Pandoc; no browser scripts."""
import argparse
import html
import json
from html.parser import HTMLParser
from pathlib import Path
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent.parent
DOCS = ROOT / 'docs'
SOURCES = ['introduction.md', 'tutorial.md', 'language.md', 'program-verification.md', 'compiler-limits.md', 'webassembly.md']
TARGETS = ['index.html']


def slug(text):
    text = re.sub(r'\[([^]]+)\]\([^)]*\)', r'\1', text)
    return re.sub(r'\s', '-', re.sub(r'[^\w\s-]', '', text.lower()))


def manuscript():
    documents = []
    used = set()
    anchors = {}
    roots = {}
    for name in SOURCES:
        text = (DOCS / name).read_text()
        if name == 'language.md':
            text = text.replace('# Lim language reference', '# Language reference {#language-reference}', 1)
        elif name == 'program-verification.md':
            text = text.replace('# Predicate evidence and contracts', '# Verification notes {#verification-notes}', 1)
        elif name == 'compiler-limits.md':
            text = text.replace('# Bounded compilation and limit diagnostics', '# Compiler limits {#compiler-limits}', 1)
        lines = []
        fenced = False
        for line in text.splitlines():
            if line.startswith('```'):
                fenced = not fenced
                # Native test metadata stays in Markdown; display ordinary code.
                line = re.sub(r'^```(?:lisp|lim)\b.*', '```lisp', line)
            match = None if fenced else re.match(r'^(#{1,6}) (.+)$', line)
            if match:
                level, title = match.groups()
                explicit = re.search(r'\s*\{#([^}]+)\}$', title)
                title = title[:explicit.start()] if explicit else title
                original = slug(title)
                base = explicit.group(1) if explicit else original
                anchor = base
                suffix = 1
                while anchor in used:
                    anchor = f'{base}-{suffix}'
                    suffix += 1
                used.add(anchor)
                anchors.setdefault((name, original), anchor)
                anchors[(name, base)] = anchor
                roots.setdefault(name, anchor)
                line = f'{level} {title} {{#{anchor}}}'
            lines.append(line)
        documents.append((name, lines))
    result = []
    for name, lines in documents:
        fenced = False
        for line in lines:
            if line.startswith('```'):
                fenced = not fenced
            if not fenced:
                def link(match):
                    label, target = match.groups()
                    file, _, fragment = target.partition('#')
                    if not file and fragment:
                        return f'[{label}](#{anchors.get((name, fragment), fragment)})'
                    if file in SOURCES:
                        return f'[{label}](#{anchors.get((file, fragment), fragment) if fragment else roots[file]})'
                    if file in TARGETS and fragment:
                        return f'[{label}](#{fragment})'
                    if file in TARGETS:
                        return f'[{label}](#main)'
                    return match.group(0)
                line = re.sub(r'\[([^]\n]+)\]\(([^)\s]+)\)', link, line)
            result.append(line)
        result.append('')
    return '\n'.join(result)


class Inspect(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.ids = set()
        self.links = []
        self.scripts = []
        self.resources = []
        self.errors = []

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if 'id' in attrs:
            if attrs['id'] in self.ids:
                self.errors.append(f'duplicate anchor {attrs["id"]}')
            self.ids.add(attrs['id'])
        if tag == 'a' and attrs.get('href', '').startswith('#'):
            self.links.append(attrs['href'][1:])
        if tag == 'script':
            self.scripts.append(attrs)
        if tag in ('img', 'iframe', 'link') and ('src' in attrs or 'href' in attrs):
            self.resources.append(attrs)


def highlight_code(output):
    # Pandoc emits escaped plain text with --no-highlight. Color only Lim fences;
    # decoding then escaping in the colorizer preserves copy/search text exactly.
    pattern = re.compile(r'(<pre\b[^>]*\bclass="(?:[^" ]+ )*(?:lim|lisp)(?: [^"]+)?"[^>]*><code>)([\s\S]*?)(</code>)')
    blocks = list(pattern.finditer(output))
    if not blocks:
        return output
    colored = json.loads(subprocess.check_output(
        ['node', str(ROOT / 'scripts/highlight-code.mjs')],
        input=json.dumps([html.unescape(block[2]) for block in blocks]), text=True))
    replacements = iter(colored)
    return pattern.sub(lambda match: match[1] + next(replacements) + match[3], output)


def build():
    with tempfile.TemporaryDirectory(prefix='lim-reference-') as directory:
        source = Path(directory) / 'manual.md'
        source.write_text(manuscript())
        command = ['pandoc', str(source), '--from=markdown-smart-tex_math_dollars', '--to=html5', '--standalone',
                   '--section-divs', '--toc', '--toc-depth=3', '--no-highlight', '--embed-resources',
                   '--template=' + str(DOCS / 'reference.template.html'), '--css=' + str(DOCS / 'reference.css'),
                   '--resource-path=' + str(DOCS), '--wrap=none']
        output = subprocess.check_output(command, text=True)
    output = highlight_code(output)
    inspect = Inspect()
    inspect.feed(output)
    inspect.errors += [f'broken anchor #{link}' for link in inspect.links if link not in inspect.ids]
    if inspect.scripts or inspect.resources:
        inspect.errors.append('manual must not load scripts or external resources')
    if inspect.errors:
        raise ValueError('\n'.join(sorted(set(inspect.errors))))
    return output


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true', help='fail if the committed HTML is stale')
    args = parser.parse_args()
    output = build()
    if args.check:
        stale = [name for name in TARGETS if not (DOCS / name).exists() or (DOCS / name).read_text() != output]
        if stale:
            sys.exit(f'{", ".join("docs/" + name for name in stale)} is stale; run scripts/build-reference.py')
        print('Homepage is current; all anchors resolve; no scripts or external resources.')
    else:
        for name in TARGETS:
            target = DOCS / name
            target.write_text(output)
            print(f'Wrote {target.relative_to(ROOT)} ({len(output.encode()):,} bytes)')


if __name__ == '__main__':
    main()
