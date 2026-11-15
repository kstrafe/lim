#!/usr/bin/env python3
"""Check generated spans preserve Pandoc text and touch only Lim code fences."""
import importlib.util
import sys
from html.parser import HTMLParser
from pathlib import Path

sys.dont_write_bytecode = True

spec = importlib.util.spec_from_file_location('reference', Path(__file__).with_name('build-reference.py'))
reference = importlib.util.module_from_spec(spec)
spec.loader.exec_module(reference)

class Text(HTMLParser):
    def __init__(self):
        super().__init__()
        self.text = []
    def handle_data(self, data):
        self.text.append(data)

source = '<pre class="lisp"><code>(#fn x () #u64) // &lt;script&gt; &amp; &quot;x&quot;\n</code></pre><pre class="sh"><code>echo &lt;hi&gt;</code></pre>'
colored = reference.highlight_code(source)
a, b = Text(), Text()
a.feed(source)
b.feed(colored)
assert a.text != b.text  # Spans split text into pieces.
assert ''.join(a.text) == ''.join(b.text)
assert '<span class="lim-keyword">#fn</span>' in colored
assert '<pre class="sh"><code>echo &lt;hi&gt;</code>' in colored
assert '<script>' not in colored
assert reference.highlight_code('<code>plain &amp; text</code>') == '<code>plain &amp; text</code>'
print('Handbook highlighting: text preservation, fence selection and escaping passed.')
