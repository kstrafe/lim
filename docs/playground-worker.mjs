import { createCompiler, displayResult } from './compiler.mjs';
import { createStdout } from './playground-host.mjs';

self.onmessage = async ({ data: { source, checkOnly } }) => {
  try {
    const response = await fetch(new URL('./lim-compiler.wasm', import.meta.url));
    if (!response.ok) throw new Error('Compiler artifact is missing. Run scripts/build-playground.sh, then serve the repository over HTTP.');
    const compiler = await createCompiler(await response.arrayBuffer());
    self.postMessage({ phase: 'Compiling and checking…' });
    const result = compiler.compile(source, { checkOnly });
    if (!result.ok || result.checked) { self.postMessage(result); return; }
    self.postMessage({ phase: 'Running…' });
    const stdout = createStdout(text => self.postMessage({ stdout: text }));
    const module = new WebAssembly.Module(result.bytes);
    const hostOutput = WebAssembly.Module.imports(module).length !== 0;
    const instance = new WebAssembly.Instance(module, stdout.imports);
    try {
      const value = displayResult(instance.exports.main(), result.returnType);
      stdout.flush();
      self.postMessage({ ok: true, value, hostOutput, bytes: result.bytes }, [result.bytes.buffer]);
    } catch (error) {
      stdout.flush();
      // Keep the compiled artifact downloadable even if its execution traps.
      self.postMessage({ ok: false, message: `Runtime trap: ${error.message}`, bytes: result.bytes }, [result.bytes.buffer]);
    }
  } catch (error) {
    self.postMessage({ ok: false, message: error.message });
  }
};
