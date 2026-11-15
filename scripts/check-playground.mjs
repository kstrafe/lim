#!/usr/bin/env node
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { createCompiler, displayResult } from '../docs/compiler.mjs';

const binary = await readFile(new URL('../docs/lim-compiler.wasm', import.meta.url));
const compiler = await createCompiler(binary);
assert.deepEqual(WebAssembly.Module.imports(new WebAssembly.Module(binary)), [], 'compiler needs no JS host imports');
const html = await readFile(new URL('../docs/playground.html', import.meta.url), 'utf8');
function example(name) {
  const match = html.match(new RegExp(`<template id="example-${name}">([\\s\\S]*?)</template>`));
  assert.ok(match, `missing example ${name}`);
  return match[1].replaceAll('&gt;', '>').replaceAll('&lt;', '<').replaceAll('&amp;', '&');
}
async function run(source) {
  const result = compiler.compile(source);
  assert.ok(result.ok, result.message);
  assert.ok(WebAssembly.validate(result.bytes), 'backend must emit valid WebAssembly');
  assert.deepEqual(WebAssembly.Module.imports(new WebAssembly.Module(result.bytes)), []);
  const { instance } = await WebAssembly.instantiate(result.bytes, {});
  return displayResult(instance.exports.main(), result.returnType);
}
for (const [name, expected] of [['answer', '42'], ['loop', '55'], ['contract', '42']]) {
  assert.equal(await run(example(name)), expected, name);
}
assert.equal(compiler.compile(example('invalid')).ok, false);
assert.match(compiler.compile(example('invalid')).message, /E4000/);
assert.equal(compiler.compile(example('array'), { checkOnly: true }).ok, true);
assert.equal(compiler.compile(example('array')).ok, false);
assert.match(compiler.compile(example('array')).message, /does not yet support/);
assert.equal(await run('(#fn main () #u64 (#return 18446744073709551615u64))'), '18446744073709551615');
assert.equal(await run('(#fn main () #i64 (#return -9223372036854775808i64))'), '-9223372036854775808');
assert.equal(await run('(#fn main () #bool (#return false))'), 'false');
assert.equal(await run('(#fn main () () (#return ()))'), '()');
assert.equal(compiler.compile('(#alias secret = /tmp/private.lim::value)').ok, false);
assert.equal(compiler.compile(' '.repeat(32769)).ok, false);
assert.match(compiler.compile('"unfinished').message, /E1000/);
assert.match(compiler.compile('(#fn main').message, /E2000/);
const badPromise = '(#fn liar () #u64 (#ensures (#u64::eq (#result) 0u64)) (#return 42u64)) (#fn main () #u64 (#return (#call liar ())))';
await assert.rejects(() => run(badPromise), WebAssembly.RuntimeError, 'postconditions must be audited');
const outOfRangeShift = '(#fn shift ((n #u64)) #u64 (#return (#u64::shl 1u64 n))) (#fn main () #u64 (#return (#call shift ((n 64u64)))))';
await assert.rejects(() => run(outOfRangeShift), WebAssembly.RuntimeError, 'shift counts must trap rather than get masked');
console.log('Browser compiler: all example, ABI, diagnostic, audit and trap checks passed.');
