import { createCompiler, displayResult } from './compiler.mjs';

self.onmessage = async ({ data: { source, checkOnly } }) => {
  try {
    const response = await fetch(new URL('./lim-compiler.wasm', import.meta.url));
    if (!response.ok) throw new Error('Compiler artifact is missing. Run scripts/build-playground.sh, then serve the repository over HTTP.');
    const compiler = await createCompiler(await response.arrayBuffer());
    self.postMessage({ phase: 'Compiling and checking…' });
    const result = compiler.compile(source, { checkOnly });
    if (!result.ok || result.checked) { self.postMessage(result); return; }
    self.postMessage({ phase: 'Running…' });
    const { instance } = await WebAssembly.instantiate(result.bytes, {});
    try {
      const value = displayResult(instance.exports.main(), result.returnType);
      self.postMessage({ ok: true, value, bytes: result.bytes }, [result.bytes.buffer]);
    } catch (error) {
      // Keep the compiled artifact downloadable even if its execution traps.
      self.postMessage({ ok: false, message: `Runtime trap: ${error.message}`, bytes: result.bytes }, [result.bytes.buffer]);
    }
  } catch (error) {
    self.postMessage({ ok: false, message: error.message });
  }
};
