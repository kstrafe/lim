#!/usr/bin/env node
// Browser smoke test with Chromium's built-in debugging protocol; no npm packages.
import assert from 'node:assert/strict';
import { spawn } from 'node:child_process';
import { createServer } from 'node:http';
import { readFile, mkdtemp, rm, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { dirname, extname, resolve, sep } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const root = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const profile = await mkdtemp(resolve(tmpdir(), 'lim-browser-ui-'));
const types = { '.html': 'text/html', '.mjs': 'text/javascript', '.css': 'text/css', '.wasm': 'application/wasm' };
const server = createServer(async (request, response) => {
  // Match published hosting: docs at /, repository examples at /examples/.
  const pathname = decodeURIComponent(new URL(request.url, 'http://localhost').pathname);
  const directory = pathname.startsWith('/examples/') ? root : resolve(root, 'docs');
  const path = resolve(directory, '.' + (pathname === '/' ? '/index.html' : pathname));
  if (!path.startsWith(directory + sep)) { response.writeHead(403).end(); return; }
  try { const bytes = await readFile(path); response.writeHead(200, { 'Content-Type': types[extname(path)] || 'application/octet-stream' }).end(bytes); }
  catch { response.writeHead(404).end(); }
});
await new Promise(resolve => server.listen(0, '127.0.0.1', resolve));
const base = `http://127.0.0.1:${server.address().port}`;
const browser = spawn(process.env.CHROMIUM || 'chromium', ['--headless', '--no-sandbox', '--single-process', '--no-zygote', '--disable-dev-shm-usage', '--disable-extensions', '--num-raster-threads=1', '--js-flags=--wasm-num-compilation-tasks=1', '--disable-gpu', '--no-first-run', '--disable-background-networking', '--remote-debugging-port=0', `--user-data-dir=${profile}`, 'about:blank'], { detached: true, stdio: ['ignore', 'ignore', 'pipe'] });
let socket;
try {
  const endpoint = await new Promise((resolve, reject) => {
    let text = '';
    const timeout = setTimeout(() => reject(new Error('Chromium did not start in 15 seconds')), 15000);
    browser.on('error', reject);
    browser.stderr.on('data', data => { text += data; const match = text.match(/DevTools listening on (ws:\/\/[^\s]+)/); if (match) { clearTimeout(timeout); resolve(match[1]); } });
  });
  socket = new WebSocket(endpoint);
  await new Promise((resolve, reject) => { socket.addEventListener('open', resolve); socket.addEventListener('error', reject); });
  let id = 0;
  const pending = new Map();
  const pageErrors = [];
  socket.addEventListener('message', ({ data }) => {
    const message = JSON.parse(data); if (message.method === "Runtime.exceptionThrown") pageErrors.push(message.params); const callback = pending.get(message.id);
    if (callback) { pending.delete(message.id); message.error ? callback.reject(new Error(JSON.stringify(message.error))) : callback.resolve(message.result); }
  });
  function cdp(method, params = {}, sessionId) {
    return new Promise((resolve, reject) => { const timeout = setTimeout(() => { pending.delete(request.id); reject(new Error(`CDP request timed out: ${method}`)); }, 5000); const finish = (callback) => value => { clearTimeout(timeout); callback(value); }; const request = { id: ++id, method, params }; if (sessionId) request.sessionId = sessionId; pending.set(id, { resolve: finish(resolve), reject: finish(reject) }); socket.send(JSON.stringify(request)); });
  }
  const { targetId } = await cdp('Target.createTarget', { url: 'about:blank' });
  const { sessionId } = await cdp('Target.attachToTarget', { targetId, flatten: true });
  const send = (method, params = {}) => cdp(method, params, sessionId);
  await send('Page.enable'); await send('Runtime.enable');
  await send('Emulation.setDeviceMetricsOverride', { width: 1440, height: 1000, deviceScaleFactor: 1, mobile: false });
  async function evaluate(expression) {
    const result = await send('Runtime.evaluate', { expression, awaitPromise: true, returnByValue: true });
    if (result.exceptionDetails) throw new Error(JSON.stringify(result.exceptionDetails));
    return result.result.value;
  }
  async function until(expression, milliseconds = 15000) {
    const end = Date.now() + milliseconds;
    while (Date.now() < end) { if (await evaluate(expression)) return; await new Promise(resolve => setTimeout(resolve, 40)); }
    throw new Error(`Timed out: ${expression}; errors: ${JSON.stringify(pageErrors)}; page: ${await evaluate('document.body.innerText.slice(-2500)')}`);
  }
  await send('Page.navigate', { url: base + '/playground.html' });
  await until('document.readyState === "complete" && document.querySelector("#run") && typeof Worker === "function"');
  async function choose(name) { await evaluate(`document.querySelector('#example').value=${JSON.stringify(name)};document.querySelector('#example').dispatchEvent(new Event('change'))`); }
  async function click(button) { await evaluate(`document.querySelector('#${button}').click()`); }
  console.log('Checking the default program');
  await click('run'); await until('document.querySelector("#status").textContent === "Compiled and ran"');
  assert.equal(await evaluate('document.querySelector("#stdout").textContent'), '42\n');
  assert.match(await evaluate('document.querySelector("#output").textContent'), /main returned \(\)/);
  console.log('Checking stdout for every selectable example');
  const demos = await evaluate(`Array.from(document.querySelector('#example').options, option => ({ value: option.value, stdout: option.dataset.stdout, runtimeError: option.dataset.runtimeError === 'true' }))`);
  assert(demos.length > 0 && demos.every(demo => typeof demo.stdout === 'string'), 'every selectable example must declare expected stdout');
  for (const demo of demos) {
    await choose(demo.value); await click('run');
    await until(`document.querySelector("#status").textContent === ${JSON.stringify(demo.runtimeError ? 'Needs attention' : 'Compiled and ran')}`);
    assert.equal(await evaluate('document.querySelector("#stdout").textContent'), demo.stdout, `${demo.value} stdout`);
    if (demo.runtimeError) assert.match(await evaluate('document.querySelector("#output").textContent'), /Runtime trap/);
    else assert.match(await evaluate('document.querySelector("#output").textContent'), /main returned \(\)/);
    assert.equal(await evaluate('document.querySelector("#download").hidden'), false);
  }
  const playgroundShot = await send('Page.captureScreenshot', { format: 'png', captureBeyondViewport: false });
  await writeFile('/tmp/lim-playground-preview.png', Buffer.from(playgroundShot.data, 'base64'));
  console.log('Checking diagnostics and check-only arrays');
  const invalid = '#fn main { #params = {}; #returns = #u64; #body = ((#let answer #u64 false) (#return answer)); }';
  await evaluate(`document.querySelector('#source').value=${JSON.stringify(invalid)}`);
  await click('run'); await until('document.querySelector("#status").textContent === "Needs attention"');
  assert.match(await evaluate('document.querySelector("#output").textContent'), /E4000/);
  const checkOnlyArray = `#fn main {
    #params = {}; #returns = #u64;
    #body:
      #let items (#array #u64 2) : #array-of (#array #u64 2) 20 42;
      #let view (#ref (#array #u64 2)) : #borrow items;
      #let index #usize 1;
      #return : #if-valid [#usize; index < 2] (#index-proven view index) 0u64;
  }`;
  await evaluate(`document.querySelector('#source').value=${JSON.stringify(checkOnlyArray)}`);
  await click('check'); await until('document.querySelector("#status").textContent === "Checks passed"');
  await click('run'); await until('document.querySelector("#status").textContent === "Needs attention"');
  assert.match(await evaluate('document.querySelector("#output").textContent'), /does not yet support/);
  console.log('Checking contracts and worker cancellation');
  await choose('contract'); await click('run'); await until('document.querySelector("#status").textContent === "Compiled and ran"');
  assert.match(await evaluate('document.querySelector("#output").textContent'), /main returned \(\)/);
  assert.equal(await evaluate('document.querySelector("#stdout").textContent'), '42\n');
  const binding = await evaluate('document.querySelector("#example-print").content.textContent.split("#fn main {")[0]');
  const printThenTrap = `${binding}#fn main {
    #params = {}; #returns = #u64;
    #body:
      #unsafe : #unsafe-call browser-print-u64 { value = 7; };
      #return : #panic;
  }`;
  await evaluate(`document.querySelector('#source').value=${JSON.stringify(printThenTrap)}`);
  await click('run'); await until('document.querySelector("#status").textContent === "Needs attention"');
  assert.equal(await evaluate('document.querySelector("#stdout").textContent'), '7\n');
  assert.equal(await evaluate('document.querySelector("#download").hidden'), false);
  const floodOutput = `${binding}#fn main {
    #params = {}; #returns = ();
    #body:
      #for-range (number #u64) 0 100000:
        #unsafe : #unsafe-call browser-print-u64 { value = number; };
      #return ();
  }`;
  await evaluate(`document.querySelector('#source').value=${JSON.stringify(floodOutput)}`);
  await click('run'); await until('document.querySelector("#status").textContent === "Needs attention"');
  assert.match(await evaluate('document.querySelector("#output").textContent'), /64 KiB output limit/);
  assert.equal(await evaluate('document.querySelector("#stdout").textContent.length <= 65536'), true);
  const printThenLoop = `${binding}#fn main {
    #params = {}; #returns = #u64;
    #body:
      #unsafe : #unsafe-call browser-print-u64 { value = 7; };
      #loop : #continue;
      #return 0;
  }`;
  await evaluate(`document.querySelector('#source').value=${JSON.stringify(printThenLoop)}`);
  await click('run'); await until('document.querySelector("#status").textContent === "Running…" && document.querySelector("#stdout").textContent === "7\\n"'); await click('stop');
  assert.equal(await evaluate('document.querySelector("#status").textContent'), 'Stopped');
  assert.equal(await evaluate('document.querySelector("#run").disabled'), false);
  assert.equal(await evaluate('document.querySelector("#stdout").textContent'), '7\n');
  console.log('Checking deadline');
  await click('run'); await until('document.querySelector("#status").textContent === "Stopped"');
  assert.match(await evaluate('document.querySelector("#output").textContent'), /10-second time limit/);
  assert.equal(await evaluate('document.querySelector("#stdout").textContent'), '7\n');
  await send('Emulation.setDeviceMetricsOverride', { width: 390, height: 844, deviceScaleFactor: 1, mobile: true });
  assert.equal(await evaluate('document.documentElement.scrollWidth <= innerWidth'), true, 'playground overflows on mobile');
  console.log('Checking manual and mobile layout');
  await send('Page.navigate', { url: base + '/' });
  await until('document.querySelector("#language-reference") && document.querySelector("#browser-abi")');
  assert.equal(await evaluate('document.scripts.length'), 0);
  assert.equal(await evaluate('document.documentElement.scrollWidth <= innerWidth'), true, 'manual overflows on mobile');
  assert.equal(await evaluate('document.querySelectorAll("details, [hidden]").length'), 0, 'reference content must stay findable');
  assert.equal(await evaluate('performance.getEntriesByType("resource").filter(r => ["script", "css", "img", "link"].includes(r.initiatorType)).length'), 0);
  assert.deepEqual(await evaluate('["introduction", "tutorial", "language-reference"].map(id => document.getElementById(id)).map((node, i, nodes) => i === 0 || !!(nodes[i - 1].compareDocumentPosition(node) & Node.DOCUMENT_POSITION_FOLLOWING))'), [true, true, true]);
  assert.equal(await evaluate('["language", "safety", "start"].every(id => !!document.getElementById(id))'), true);
  assert.equal((await fetch(base + '/examples/print_numbers.lim')).status, 200, 'published example links must resolve');
  await send('Emulation.setDeviceMetricsOverride', { width: 1440, height: 1000, deviceScaleFactor: 1, mobile: false });
  await evaluate('scrollTo(0,0)');
  const manualShot = await send('Page.captureScreenshot', { format: 'png', captureBeyondViewport: false });
  await writeFile('/tmp/lim-reference-preview.png', Buffer.from(manualShot.data, 'base64'));
  assert.equal(await evaluate('window.find("#preserves",false,false,true)'), true, 'browser Find must reach contract text');
  await send('Page.navigate', { url: pathToFileURL(resolve(root, 'docs/index.html')).href });
  await until('location.protocol === "file:" && document.readyState === "complete" && document.querySelector("#language-reference")');
  assert.equal(await evaluate('window.find("#preserves",false,false,true)'), true, 'offline homepage must support browser Find');
  assert.equal(await evaluate('document.scripts.length + performance.getEntriesByType("resource").length'), 0, 'offline manual must be self-contained');
  console.log('Browser UI: run, real stdout, output bounds/traps, diagnostics, check-only, contracts, cancellation, deadline, mobile layout, published homepage and offline Find passed.');
} finally {
  socket?.close();
  try { process.kill(-browser.pid, 'SIGKILL'); } catch (error) { if (error.code !== 'ESRCH') throw error; }
  server.closeAllConnections(); await new Promise(resolve => server.close(resolve));
  await new Promise(resolve => setTimeout(resolve, 150));
  await rm(profile, { recursive: true, force: true });
}
