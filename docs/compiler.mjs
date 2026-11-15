// Small, versioned bridge shared by the browser worker and engine tests.
export async function createCompiler(bytes) {
  const { instance } = await WebAssembly.instantiate(bytes, {});
  const api = instance.exports;
  if (api.lim_abi_version() !== 1) throw new Error('Unsupported Lim compiler ABI. Rebuild the playground.');
  const encoder = new TextEncoder();
  const decoder = new TextDecoder();
  return {
    compile(source, { checkOnly = false } = {}) {
      const input = encoder.encode(source);
      if (input.length > 32768) return { ok: false, message: 'Playground source exceeds 32 KiB.' };
      const pointer = api.lim_input_resize(input.length);
      if (!pointer) throw new Error('Compiler could not allocate the source buffer.');
      new Uint8Array(api.memory.buffer, pointer, input.length).set(input);
      const status = api.lim_compile(checkOnly ? 1 : 0);
      // Copy: a later compiler call can grow memory or replace the output buffer.
      const output = new Uint8Array(api.memory.buffer, api.lim_output_ptr(), api.lim_output_len()).slice();
      if (status === 2) return { ok: false, message: decoder.decode(output) };
      if (status === 1) return { ok: true, checked: true, message: decoder.decode(output) };
      if (status !== 0) throw new Error('Invalid response from the Lim compiler.');
      return { ok: true, bytes: output, returnType: api.lim_return_type() };
    },
  };
}

export function displayResult(result, returnType) {
  if (returnType === 0) return '()';
  if (returnType === 1) return result ? 'true' : 'false';
  return String(returnType === 2 ? BigInt.asUintN(64, result) : result);
}
