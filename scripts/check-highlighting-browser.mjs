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

  assert.ok(await evaluate('document.querySelectorAll("#source-colors .lim-keyword").length > 0'));
  for (const width of [320, 390, 1440]) {
    await send('Emulation.setDeviceMetricsOverride', { width, height: 844, deviceScaleFactor: 1, mobile: width < 500 });
    const source = '// <img src=x onerror=alert(1)>\n' + '(#let value #u64 42u64)\n'.repeat(90) + 'x'.repeat(240);
    await evaluate(`document.querySelector('#source').value=${JSON.stringify(source)};document.querySelector('#source').dispatchEvent(new Event('input'))`);
    assert.equal(await evaluate('document.querySelector("#source-colors code").textContent'), source + '\n');
    assert.equal(await evaluate('document.querySelectorAll("#source-colors img").length'), 0);
    assert.equal(await evaluate('document.documentElement.scrollWidth <= innerWidth'), true, `editor page overflow at ${width}`);
    assert.equal(await evaluate(`(() => { const a=getComputedStyle(document.querySelector('#source')); const b=getComputedStyle(document.querySelector('#source-colors')); return ['fontFamily','fontSize','lineHeight','paddingTop','paddingLeft','tabSize'].every(k=>a[k]===b[k]); })()`), true, 'overlay metrics');
    await evaluate(`{ const editor=document.querySelector('#source');editor.scrollTop=250;editor.scrollLeft=80;editor.dispatchEvent(new Event('scroll')); }`);
    assert.equal(await evaluate('document.querySelector("#source-colors").scrollTop === document.querySelector("#source").scrollTop && document.querySelector("#source-colors").scrollLeft === document.querySelector("#source").scrollLeft'), true, 'scroll synchronization');
  }
  await evaluate(`document.querySelector('#example').value='loop';document.querySelector('#example').dispatchEvent(new Event('change'))`);
  assert.equal(await evaluate('document.querySelector("#source-colors code").textContent === document.querySelector("#source").value + String.fromCharCode(10)'), true);
  await send('Page.navigate', { url: pathToFileURL(resolve(root, 'docs/index.html')).href });
  await until('location.protocol === "file:" && document.readyState === "complete" && document.querySelector(".manual .lim-keyword")');
  assert.equal(await evaluate('document.scripts.length + performance.getEntriesByType("resource").length'), 0);
  assert.equal(await evaluate('window.find("#preserves",false,false,true)'), true, 'offline Find');
  assert.equal(await evaluate('document.querySelectorAll("details, [hidden]").length'), 0);
  for (const width of [320, 390]) {
    await send('Emulation.setDeviceMetricsOverride', { width, height: 844, deviceScaleFactor: 1, mobile: true });
    assert.equal(await evaluate('document.documentElement.scrollWidth <= innerWidth'), true, `manual page overflow at ${width}`);
  }
  assert.equal(await evaluate(`(() => { const code=document.querySelector('pre code'); const range=document.createRange(); range.selectNodeContents(code); return range.toString()===code.textContent; })()`), true, 'copyable source');
  for (const scheme of ['light', 'dark']) {
    await send('Emulation.setEmulatedMedia', { features: [{ name: 'prefers-color-scheme', value: scheme }] });
    assert.equal(await evaluate(`(() => {
      const rgb = color => color.match(/[\\d.]+/g).slice(0,3).map(Number).map(x => { x/=255; return x<=.04045 ? x/12.92 : ((x+.055)/1.055)**2.4; });
      const luminance = color => { const c=rgb(color); return .2126*c[0]+.7152*c[1]+.0722*c[2]; };
      return [...document.querySelectorAll('pre code span[class^="lim-"]')].every(span => {
        const fg=luminance(getComputedStyle(span).color), bg=luminance(getComputedStyle(span.closest('pre')).backgroundColor);
        return (Math.max(fg,bg)+.05)/(Math.min(fg,bg)+.05)>=4.5;
      });
    })()`), true, scheme + ' code contrast');
  }
  const shot = await send('Page.captureScreenshot', { format: 'png', captureBeyondViewport: false });
  await writeFile('/tmp/lim-highlighting-mobile.png', Buffer.from(shot.data, 'base64'));
  console.log('Highlight browser: live examples, escaping, scroll metrics, 320/390px layouts and offline Find passed.');
} finally {
  socket?.close();
  try { process.kill(-browser.pid, 'SIGKILL'); } catch (error) { if (error.code !== 'ESRCH') throw error; }
  server.closeAllConnections(); await new Promise(resolve => server.close(resolve));
  await new Promise(resolve => setTimeout(resolve, 150));
  await rm(profile, { recursive: true, force: true });
}
