#!/usr/bin/env node
import assert from 'node:assert/strict';
import { highlightLim, escapeHTML } from '../docs/lim-highlight.mjs';
function plain(html) {
  return html.replace(/<span class="lim-[a-z]+">|<\/span>/g, '')
    .replace(/&(?:amp|lt|gt|quot|#39);/g, text => ({'&amp;':'&','&lt;':'<','&gt;':'>','&quot;':'"','&#39;':"'"})[text]);
}
const span = (kind, text) => `<span class="lim-${kind}">${escapeHTML(text)}</span>`;
for (const [source, kind] of [
  ['#fn','keyword'], ['#let-mut','keyword'], ['#u64','type'], ['#usize','type'],
  ['#bool','type'], ['#u64::add-wrap','operator'], ['>=','operator'],
  ['42u64','literal'], ['-1i64','literal'], ['0xffu8','literal'], ['0b101u8','literal'],
  ['1e+3f64','literal'], ['1.5f64','literal'], ['true','literal'], ['false','literal'],
  ['// #fn <script> "x"','comment'], ['"escaped \\" // #fn <&>"','string'],
  ['"unfinished <script>','string'], ['#\\a','string'], ['#\\u{1F642}','string'], ['#\\)','string'],
]) assert.equal(highlightLim(source), span(kind, source), source);
for (const source of ['trueish', 'thing42u64', 'x#fn', '42u64x', 'x::thing']) {
  assert.equal(highlightLim(source), escapeHTML(source), source);
}
assert.equal(highlightLim('#u64ish'), span('keyword', '#u64ish'));
assert.equal(highlightLim('name// hi'), 'name' + span('comment', '// hi'));
const fixtures = ['(#fn main () #u64 (#return 42u64))\n',
  '// comment\r\n"<&>\\\\\\"" #\\u{41} 1.5f64\n',
  '</code><img src=x onerror="alert(1)"> &amp; \' "',
  '#fn main { #params = {}; #body: #return [#u64 #wrap; n + 1]; }',
  '\t🙂\r\n\n', '#\\" #\\; #\\( #\\}'];
for (const source of fixtures) {
  assert.equal(plain(highlightLim(source)), source, 'lossless text');
  assert.doesNotMatch(highlightLim(source), /<(?!span class="lim-[a-z]+">|\/span>)/, 'only span tags');
}
console.log('Highlighting: lexical categories, boundaries, escaping and lossless text passed.');
