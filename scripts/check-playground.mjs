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
const selectable = [...html.matchAll(/<option value="([^"]+)" data-stdout="([^"]*)"( data-runtime-error="true")?>(.*?)<\/option>/g)];
assert.equal(selectable.length, (html.match(/<option\b/g) || []).length, 'every selectable example must declare its expected stdout');
for (const [, name, encodedStdout, runtimeError] of selectable) {
  const printed = await print(example(name));
  assert.equal(printed.stdout, encodedStdout.replaceAll('&#10;', '\n'), `${name} stdout`);
  if (runtimeError) assert(printed.error instanceof WebAssembly.RuntimeError, `${name} must trap after printing`);
  else {
    assert.equal(printed.error, undefined, `${name} must run successfully`);
    assert.equal(printed.value, '()', `${name} must use an explicit unit return`);
  }
}
const invalid = '#fn main { #params = {}; #returns = #u64; #body: #let answer #u64 false; #return answer; }';
assert.equal(compiler.compile(invalid).ok, false);
assert.match(compiler.compile(invalid).message, /E4000/);
const array = `#fn main {
  #params = {}; #returns = #u64;
  #body:
    #let items (#array #u64 2) : #array-of (#array #u64 2) 20 42;
    #let view (#ref (#array #u64 2)) : #borrow items;
    #let index #usize 1;
    #return : #if-valid [#usize; index < 2] (#index-proven view index) 0u64;
}
`;
const checkedArray = compiler.compile(array, { checkOnly: true });
assert.ok(checkedArray.ok && checkedArray.checked, checkedArray.message);
assert.equal(compiler.compile(array).ok, false);
assert.match(compiler.compile(array).message, /does not yet support/);
const missingBounds = array.replace(
  '#return : #if-valid [#usize; index < 2] (#index-proven view index) 0u64;',
  '#return : #index-proven view index;',
);
assert.notEqual(missingBounds, array, 'bounds-evidence negative control must change the example');
const missingEvidence = compiler.compile(missingBounds, { checkOnly: true });
assert.equal(missingEvidence.ok, false, 'array access must require branch evidence');
assert.match(missingEvidence.message, /evidence/);
assert.equal(await run('#fn main { #params = {}; #returns = #u64; #body: #return 18446744073709551615u64; }'), '18446744073709551615');
assert.equal(await run('#fn main { #params = {}; #returns = #i64; #body: #return -9223372036854775808i64; }'), '-9223372036854775808');
assert.equal(await run('#fn main { #params = {}; #returns = #bool; #body: #return false; }'), 'false');
assert.equal(await run('#fn main { #params = {}; #returns = (); #body: #return (); }'), '()');
assert.equal(compiler.compile("#alias secret = /tmp/private.lim::value\n").ok, false);
assert.equal(compiler.compile(' '.repeat(32769)).ok, false);
assert.match(compiler.compile('"unfinished').message, /E1000/);
assert.match(compiler.compile('#fn main {').message, /E2000/);
for (const legacy of [
  '#fn main () #u64 (#return 42u64)',
  '#unsafe-fn main () #u64 (#return 42u64)',
  '#extern-fn #abi-c foreign () ()',
  '#fn main (#params {}) (#returns #u64) (#body (#return 42u64))',
]) {
  for (const options of [{}, { checkOnly: true }]) {
    const result = compiler.compile(legacy, options);
    assert.equal(result.ok, false, 'authored functions must use declaration records');
    assert.match(result.message, /require a named record/);
  }
}
for (const mixed of [
  '#fn main { #params = {}; #returns = #u64; #body: #return 42u64; } ()',
  '#unsafe-fn main { #params = {}; #returns = #u64; #body: #return 42u64; } #u64 (#return 0u64)',
  '#extern-fn foreign { #abi = #abi-c; #params = {}; #returns = (); } ()',
]) {
  for (const options of [{}, { checkOnly: true }]) {
    const result = compiler.compile(mixed, options);
    assert.equal(result.ok, false, 'a declaration record must contain the entire signature');
    assert.match(result.message, /must end after its record/);
  }
}
const badPromise = `#fn liar {
  #params = {}; #returns = #u64;
  #ensures: [#u64; (#result) == 0];
  #body: #return 42;
}
#fn main { #params = {}; #returns = #u64; #body: #return liar {}; }
`;
await assert.rejects(() => run(badPromise), WebAssembly.RuntimeError, 'postconditions must be audited');
const outOfRangeShift = `#fn shift {
  #params = { n = #u64; }; #returns = #u64;
  #body: #return : #u64::shl 1 n;
}
#fn main { #params = {}; #returns = #u64; #body: #return shift { n = 64; }; }
`;
await assert.rejects(() => run(outOfRangeShift), WebAssembly.RuntimeError, 'shift counts must trap rather than get masked');
const binding = example('print').split('#fn main {')[0];
const beforeTrap = await print(`${binding}#fn main {
  #params = {}; #returns = #u64;
  #body:
    #unsafe : #unsafe-call browser-print-u64 { value = 18446744073709551615u64; };
    #return : #panic;
}
`);
assert.equal(beforeTrap.stdout, '18446744073709551615\n');
assert(beforeTrap.error instanceof WebAssembly.RuntimeError);
const flooded = await print(`${binding}#fn main {
  #params = {}; #returns = ();
  #body:
    #for-range (number #u64) 0 100000:
      #unsafe : #unsafe-call browser-print-u64 { value = number; };
    #return ();
}
`);
assert.match(flooded.error?.message || '', /64 KiB output limit/);
assert(flooded.stdout.length <= MAX_STDOUT_CHARS && flooded.stdout.length > MAX_STDOUT_CHARS - 21);
assert(flooded.messages < 200, 'large output must be batched rather than flooding the UI');
const unknownHost = `#extern-fn unknown-output {
  #abi = #abi-c; #params = { value = #u64; }; #returns = ();
}
#fn main {
  #params = {}; #returns = ();
  #body:
    #unsafe : #unsafe-call unknown-output { value = 1; };
    #return ();
}
`;
assert.equal(compiler.compile(unknownHost, { checkOnly: true }).ok, true);
const unknownOutput = compiler.compile(unknownHost);
assert.equal(unknownOutput.ok, false);
assert.match(unknownOutput.message, /cannot call external function 'unknown-output'/);
const missingUnsafe = compiler.compile(`${binding}#fn main {
  #params = {}; #returns = ();
  #body:
    browser-print-u64 { value = 1; };
    #return ();
}
`);
assert.equal(missingUnsafe.ok, false);
assert.match(missingUnsafe.message, /unsafe/);
console.log('Browser compiler: examples, ABI, diagnostics, audits, traps, real stdout, unsigned output and bounded batching passed.');
