# Browser compiler {#browser-compiler}

The [playground](playground.html) compiles Lim inside a browser worker. It uses
the Rust compiler built for `wasm32-unknown-unknown`, then emits a second,
standalone WebAssembly module for the example. The worker instantiates that
module and calls its exported `main` function. Source is not sent to a server.

The [homepage and handbook](index.html) is a self-contained HTML document with
no JavaScript or external resources. Reading it does not download the compiler.
The playground loads the compiler artifact only after an action is requested.

## Build and serve {#build-browser-compiler}

The Nix shell includes the Rust WebAssembly standard library, Node and Pandoc.
No npm packages, wasm-bindgen, JavaScript frameworks or Rust crates from a
registry are required.

```sh
bash scripts/limited-run.sh nix develop -c bash scripts/build-playground.sh
python3 -m http.server 8000
# Open http://localhost:8000/docs/playground.html
# Read http://localhost:8000/docs/
```

Serve the repository root so links to examples also work. The HTML handbook can
also be opened directly from disk. The playground needs HTTP because browsers
restrict local module workers and fetching WebAssembly from `file:` URLs.

`docs/lim-compiler.wasm` is generated output, excluded from Git. Static hosting
needs this file alongside the HTML, CSS and `.mjs` files. The release profile is
`wasm`; the build script copies the resulting artifact into `docs/`.

`docs/index.html` is the website homepage: design introduction, tutorial and
full reference. A static host can serve `docs/`
at `/`, with the repository's examples mounted at `/examples/`.

Rebuild the handbook after changing its Markdown sources or styling.
The check verifies synchronization, every internal anchor, and the absence of
scripts or fetched resources:

```sh
bash scripts/limited-run.sh nix develop -c python3 scripts/build-reference.py
bash scripts/limited-run.sh nix develop -c python3 scripts/build-reference.py --check
```

## Supported browser programs {#browser-support}

The backend emits from validated typed bodies. It runs the same type, ownership,
borrow and predicate-evidence checks as native compilation. Contract runtime
audits are enabled. It does not reinterpret source in JavaScript or bypass the
checker when it encounters a feature it cannot emit.

| Feature | Compile & run | Check only |
| --- | --- | --- |
| `#u64`, `#i64`, `#usize`, `#isize`, `#bool`, `()` | Yes | Yes |
| Safe functions and named arguments | Yes; declaration-order argument evaluation | Yes |
| Local bindings, mutation, scalar blocks and branches | Yes | Yes |
| `#while`, `#for`, `#for-range`, unit loops, `#break`, `#continue` | Yes | Yes |
| Wrapping integer arithmetic, comparisons, bit operations | Yes | Yes |
| Short-circuit Boolean operators | Yes | Yes |
| Scalar predicate contracts and runtime audits | Yes | Yes |
| Arrays, references, structs, enums, constrained storage | Not yet | Yes for self-contained programs |
| Narrow integers, floats, saturation, globals, matching | Not yet | Yes for self-contained programs |
| Labeled loops and value-carrying break | Not yet | Yes |
| External functions, native syscalls, host I/O | No | Declarations can be checked; no host calls execute |
| Authored file imports | No | No |

`#usize` and `#isize` retain their existing 64-bit Lim scalar meaning here;
they are not browser linear-memory addresses. Unsigned 64-bit results display
without truncation, using JavaScript BigInt at the boundary. Unit displays as
`()`. The native backend remains the route for the full runtime language.

The emitted example module has no memory or host imports. The first backend
is intentionally a teaching subset, not a portable implementation of the native
standard library, an FFI, or a WASI runtime. Unsupported code generation produces
an explicit diagnostic. **Check only** does not require a runnable `main`.

## Bounds, cancellation and failure {#browser-limits}

- Source input is limited to 32 KiB of UTF-8.
- Runnable output is limited to 64 reachable functions and 16,384 typed nodes
  per reachable function. Unused functions are checked but not emitted.
- The Rust compiler module has an 8 MiB stack and a 256 MiB linear-memory cap.
  Memory exhaustion, stack overflow or a compiler trap stops that worker.
- Compilation and example execution run off the page’s main thread. Each action
  uses a fresh worker, which is terminated when complete, cancelled, or after
  the 10-second total deadline. **Stop** can interrupt an infinite example loop.
- These limits supplement the compiler’s own analysis budgets. No result is
  accepted by weakening a failed proof or skipping ownership checking.

A runtime trap can come from `#panic`, `#assert`, a failed contract audit,
division by zero or an invalid shift count. A compiled module is still available
for download when execution traps. A compile diagnostic has the native error
code, source position and excerpt. Editing the source does not change an
already-running example; rerun it for a new result.

## Compiler interface {#browser-abi}

`lim-browser` is a small `cdylib` wrapper over the `lim` crate. Its exported ABI
version is 1. Only the following entry points and compiler linear memory are
needed by the host:

| Export | Meaning |
| --- | --- |
| `lim_abi_version() -> u32` | Returns 1. |
| `lim_input_resize(bytes: u32) -> u32` | Resize the compiler-owned input buffer; return its pointer, or zero for an oversized request. |
| `lim_compile(mode: u32) -> u32` | Mode 0 compiles; mode 1 checks. Status 0 means emitted module, 1 means successful check, 2 means diagnostic text. |
| `lim_output_ptr() -> u32` | Pointer to the current output buffer. |
| `lim_output_len() -> u32` | Current output byte count. |
| `lim_return_type() -> u32` | After compilation: 0 unit, 1 Boolean, 2 unsigned 64-bit, 3 signed 64-bit. |

Write UTF-8 into the input buffer, call `lim_compile`, then copy the output.
A later call or memory growth can invalidate earlier buffer views. The wrapper
never dereferences a caller-supplied pointer. Status 0 contains raw Wasm bytes;
statuses 1 and 2 contain UTF-8 text. A compiler trap invalidates that worker;
create a fresh one instead of resuming it.

Native Rust callers can use `lim::wasm::check(source)` and
`lim::wasm::compile(source)`. `compile` returns module bytes plus a `ReturnType`;
both functions return regular `Diagnostic` errors. Neither uses a disk cache.

## Verification and extending the backend {#browser-testing}

```sh
bash scripts/limited-run.sh nix develop -c \
  env CARGO_PROFILE_TEST_DEBUG=0 CARGO_INCREMENTAL=0 \
  cargo test --test wasm_backend
bash scripts/limited-run.sh nix develop -c node scripts/check-playground.mjs
# Optional UI smoke test; requires Chromium on PATH (or set CHROMIUM).
bash scripts/limited-run.sh nix develop -c node scripts/check-browser-ui.mjs
```

The engine tests execute emitted modules, check integer boundaries, branches,
loop control, short-circuit evaluation and contract evidence, and reject
unsupported features. The artifact test loads the actual Rust compiler Wasm,
compiles the page’s example templates, checks diagnostics and unsigned results,
and verifies runtime postcondition and shift traps. The Chromium test also
checks the worker deadline, cancellation, mobile layout, browser Find and the
manual’s absence of scripts or fetched resources. Its process/thread flags keep
headless Chromium within the development runner’s process limit.

`src/wasm.rs` consumes checked `typed_body` nodes, rather than adding a second
type checker. Extend its explicit supported cases and add execution tests before
advertising another feature. Memory-backed values and aggregate layout need a
separate design; silently representing references as integers would lose the
language’s guarantees.

Background specifications: [Rust’s browser target](https://doc.rust-lang.org/rustc/platform-support/wasm32-unknown-unknown.html),
[WebAssembly binary instructions](https://webassembly.github.io/spec/core/binary/instructions.html),
[instantiating a module](https://developer.mozilla.org/en-US/docs/WebAssembly/Reference/JavaScript_interface/instantiate_static)
and [terminating a worker](https://developer.mozilla.org/en-US/docs/Web/API/Worker/terminate).
