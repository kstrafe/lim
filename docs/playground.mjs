const editor = document.querySelector('#source');
const output = document.querySelector('#output');
const status = document.querySelector('#status');
const run = document.querySelector('#run');
const check = document.querySelector('#check');
const stop = document.querySelector('#stop');
const download = document.querySelector('#download');
let active = null;
let timer = null;
let downloadUrl = null;

function finish() {
  clearTimeout(timer);
  active?.terminate(); active = null;
  run.disabled = false; check.disabled = false; stop.disabled = true;
}
function clearDownload() {
  if (downloadUrl) URL.revokeObjectURL(downloadUrl);
  downloadUrl = null;
  download.hidden = true;
  download.removeAttribute('href');
}
function compile(checkOnly) {
  finish(); clearDownload();
  if (location.protocol === 'file:') {
    status.textContent = 'Serve this playground over HTTP';
    output.textContent = 'From the repository root: python3 -m http.server 8000\nThen open http://localhost:8000/docs/playground.html';
    return;
  }
  if (!globalThis.WebAssembly || !globalThis.Worker) { output.textContent = 'This browser needs WebAssembly and Web Workers.'; return; }
  status.textContent = 'Loading compiler…'; output.textContent = '';
  run.disabled = true; check.disabled = true; stop.disabled = false;
  const worker = new Worker(new URL('./playground-worker.mjs', import.meta.url), { type: 'module' });
  active = worker;
  // Includes startup. Compilation and guest execution both remain off the UI thread.
  timer = setTimeout(() => { finish(); status.textContent = 'Stopped'; output.textContent = 'The 10-second time limit was reached. Try a smaller program, or check for an infinite loop.'; }, 10000);
  worker.onmessage = ({ data }) => {
    if (worker !== active) return;
    if (data.phase) { status.textContent = data.phase; return; }
    if (data.bytes) {
      downloadUrl = URL.createObjectURL(new Blob([data.bytes], { type: 'application/wasm' }));
      download.href = downloadUrl; download.hidden = false;
    }
    status.textContent = data.ok ? (data.checked ? 'Checks passed' : 'Compiled and ran') : 'Needs attention';
    output.textContent = data.value !== undefined ? `main returned ${data.value}\n\n${data.bytes.length} bytes · standalone WebAssembly · no host imports` : data.message;
    finish();
  };
  worker.onerror = (event) => { if (worker !== active) return; output.textContent = event.message || 'The compiler worker stopped unexpectedly.'; status.textContent = 'Worker stopped'; finish(); };
  worker.postMessage({ source: editor.value, checkOnly });
}
run.addEventListener('click', () => compile(false));
check.addEventListener('click', () => compile(true));
stop.addEventListener('click', () => { finish(); clearDownload(); status.textContent = 'Stopped'; output.textContent = 'Compilation or execution was cancelled.'; });
document.querySelector('#example').addEventListener('change', ({ target }) => {
  const template = document.querySelector(`#example-${target.value}`);
  if (template) { finish(); clearDownload(); editor.value = template.content.textContent.trim(); output.textContent = 'Choose Compile & run or Check only.'; status.textContent = 'Ready'; }
});
editor.addEventListener('keydown', (event) => { if ((event.ctrlKey || event.metaKey) && event.key === 'Enter') { event.preventDefault(); compile(false); } });
window.addEventListener('pagehide', finish);
