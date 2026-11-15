// The teaching module's only optional host capability: bounded decimal output.
export const MAX_STDOUT_CHARS = 64 * 1024;

export function createStdout(write) {
  let length = 0;
  let pending = '';
  let calls = 0;
  function flush() {
    if (pending) { write(pending); pending = ''; }
  }
  return {
    imports: {
      lim: {
        print_u64(value) {
          const line = `${BigInt.asUintN(64, value)}\n`;
          if (length + line.length > MAX_STDOUT_CHARS) {
            flush();
            throw new Error('stdout exceeded the 64 KiB output limit');
          }
          length += line.length;
          pending += line;
          // Small teaching examples stream immediately. Large output is
          // batched so a fast loop cannot flood the UI with tiny messages.
          if (++calls <= 64 || pending.length >= 1024) flush();
        },
      },
    },
    flush,
  };
}
