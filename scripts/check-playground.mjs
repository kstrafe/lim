#!/usr/bin/env node
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { createCompiler, displayResult } from '../docs/compiler.mjs';
import { createStdout, MAX_STDOUT_CHARS } from '../docs/playground-host.mjs';

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
assert.equal(await run("#fn main () #u64 (#return 18446744073709551615u64)\n"), '18446744073709551615');
assert.equal(await run("#fn main () #i64 (#return -9223372036854775808i64)\n"), '-9223372036854775808');
assert.equal(await run("#fn main () #bool (#return false)\n"), 'false');
assert.equal(await run("#fn main () () (#return ())\n"), '()');
assert.equal(compiler.compile("#alias secret = /tmp/private.lim::value\n").ok, false);
assert.equal(compiler.compile(' '.repeat(32769)).ok, false);
assert.match(compiler.compile('"unfinished').message, /E1000/);
assert.match(compiler.compile("#fn main (").message, /E2000/);
const badPromise = "#fn liar () #u64 (#ensures (#u64::eq (#result) 0u64)) (#return 42u64)\n#fn main () #u64 (#return (#call liar ()))\n";
await assert.rejects(() => run(badPromise), WebAssembly.RuntimeError, 'postconditions must be audited');
const outOfRangeShift = "#fn shift ((n #u64)) #u64 (#return (#u64::shl 1u64 n))\n#fn main () #u64 (#return (#call shift ((n 64u64))))\n";
await assert.rejects(() => run(outOfRangeShift), WebAssembly.RuntimeError, 'shift counts must trap rather than get masked');
async function print(source) {
  const result = compiler.compile(source);
  assert.ok(result.ok, result.message);
  const module = new WebAssembly.Module(result.bytes);
  assert.deepEqual(WebAssembly.Module.imports(module), [{ module: 'lim', name: 'print_u64', kind: 'function' }]);
  assert.deepEqual(WebAssembly.Module.exports(module).map(entry => entry.name), ['main'], 'guest must not expose host memory');
  let stdout = '';
  let messages = 0;
  const host = createStdout(text => { stdout += text; messages++; });
  const instance = new WebAssembly.Instance(module, host.imports);
  let value, error;
  try { value = displayResult(instance.exports.main(), result.returnType); }
  catch (caught) { error = caught; }
  host.flush();
  return { stdout, value, error, messages };
}
const printed = await print(example('print'));
assert.equal(printed.error, undefined);
assert.equal(printed.value, '()');
assert.equal(printed.stdout, '1\n2\n3\n4\n5\n6\n7\n8\n9\n10\n', 'compiled loop must write real stdout');
const binding = "#extern-fn #abi-c browser-print-u64 ((value #u64)) ()\n";
const beforeTrap = await print(`${binding}#fn main () #u64 (#unsafe (#unsafe-call browser-print-u64 ((value 18446744073709551615u64)))) (#return (#panic))
`);
assert.equal(beforeTrap.stdout, '18446744073709551615\n');
assert(beforeTrap.error instanceof WebAssembly.RuntimeError);
const flooded = await print(`${binding}#fn main () () (#for-range (number #u64) 0u64 100000u64 (#unsafe (#unsafe-call browser-print-u64 ((value number))))) (#return ())
`);
assert.match(flooded.error?.message || '', /64 KiB output limit/);
assert(flooded.stdout.length <= MAX_STDOUT_CHARS && flooded.stdout.length > MAX_STDOUT_CHARS - 21);
assert(flooded.messages < 200, 'large output must be batched rather than flooding the UI');
assert.equal(compiler.compile("#extern-fn #abi-c unknown-output ((value #u64)) ()\n#fn main () () (#unsafe (#unsafe-call unknown-output ((value 1u64)))) (#return ())\n").ok, false);
assert.equal(compiler.compile(`${binding}#fn main () () (#call browser-print-u64 ((value 1u64))) (#return ())
`).ok, false);
console.log('Browser compiler: examples, ABI, diagnostics, audits, traps, real stdout, unsigned output and bounded batching passed.');
