# Lim

Lim is an experimental, compiled Lisp designed to make programs explicit and
readable to both people and LLMs. It has strong static types, no type
inference, linear-by-default values, explicit returns and arithmetic behavior,
and a dependency-free Rust compiler. The native backend emits inspectable
x86-64 System V assembly, then encodes and links ELF binaries internally.

Lim uses concrete generated code instead of user-facing generic types. A
generator invocation such as `(@optional (: type #u64 : name MaybeU64))` emits a concrete type
and its functions. Generators are pure, interpreted at compile time, and use
the restricted `#gn-*` operation set.

Builtin type keywords require `#`, such as `#u8`, `#u64`, and `#bool`.
Numeric literal suffixes remain unchanged (`42u64`), as do explicitly typed
operators (`#u64.+.wrap`).

The language has free-standing functions, not methods or `impl` blocks. It
does not support recursion, function pointers, closures, traits, or implicit
returns. See [docs/language.md](docs/language.md) for the implemented syntax,
ownership rules, and current limitations. The allocator design is described
in [docs/allocator.md](docs/allocator.md).

The internal typed-representation migration is documented in
[docs/compiler-ir.md](docs/compiler-ir.md).

Frozen syntax collections, allocation-free error enums, and the initial
cooperative task API are documented in
[docs/collections-and-tasks.md](docs/collections-and-tasks.md).

See [explicit error propagation](docs/error-propagation.md),
[owned files and buffered readers](docs/files.md), and
[semantic checking without native emission](docs/check-command.md).

## Build the compiler

The repository's Nix development shell provides Rust. Lim itself does not
invoke a system assembler or linker:

```sh
nix develop
cargo test --all-targets
```

Compile an example to a native executable (the default output is beside the
input file, without `.lim`):

```sh
nix develop --command cargo run -- examples/fibonacci.lim
./examples/fibonacci
```

Choose an output path, emit assembly for inspection, or check the examples:

```sh
nix develop --command cargo run -- examples/fibonacci.lim -o /tmp/fibonacci
nix develop --command cargo run -- --emit-asm examples/fibonacci.lim /tmp/fibonacci.s
nix develop --command cargo run -- --check-examples examples
```

Compile-time configuration is passed with `--cfg key=value`; use
`--collect-cfgs` to list configuration keys used by a source file and its
imports. See `cargo run -- --help` for the CLI options.
Editors can request `--diagnostic-format=json`; the versioned schema is
described in [docs/diagnostics.md](docs/diagnostics.md).

Executable builds emit only functions reachable from `main`, including thread
workers and symbols referenced by inline assembly. Every imported definition
is still type-, borrow-, and linearity-checked. `--emit-asm` retains all functions
for library/export use; builds with linked objects or libraries also retain all
exports because external code may call them. Generated `.lim` source remains
fully inspectable even when its unused functions are omitted from the binary.

Run `nix develop --command bash scripts/native-sweep.sh` to compile and run
every example against `examples/outcomes.txt`. Each entry declares an exact
exit code, intentional signal, or compile-only module, plus stdout/stderr
fixtures (`-` means empty). Missing entries, unexpected signals, wrong output,
compiler/linker failures, and timeouts fail the suite. Exit codes above 128
are not treated as signals. New examples must declare their expected outcome.

## A small Lim program

```lisp run=42
(#fn main () #u64
  (#let answer #u64 (#u64.+.wrap 40u64 2u64))
  (#return answer))
```

Builtins and special forms are prefixed with `#`; numeric operators are
qualified by type and explicitly select wrapping or saturation behavior.
Bindings declare their types, and every function exit uses `#return` (including
`(#return ())` for unit-returning functions).

An explicit type mismatch is rejected (this example is tested as `E4000`):

```lisp error=E4000
(#fn main () #u64
  (#let answer #u64 false)
  (#return answer))
```
### Explaining generated-code reuse

Run `lim --explain-cache INPUT [--cfg KEY=VALUE]...` to check the program and
print a versioned JSON cache report to stdout without linking a binary. Errors
stay on stderr; `--diagnostic-format=json` still applies to errors only. Each
event identifies a syntax or inspectable-source artifact, its key digest,
full key material (including invocation/dependency inputs), and `hit`,
`missing-entry`, `invalid-entry`, or `key-collision` decision.

A changed helper, input, cfg, or compiler normally creates a different key.
The report deliberately says `missing-entry` when that key has no artifact:
it does not guess which previous invocation it replaced. Comparing retained
reports reveals changed key material. Damaged existing entries report
`invalid-entry`. One command can show a miss followed by a hit because
materialization and checking share the cache. Reports are opt-in and can
contain source code; they do not alter cache keys or add metadata files.
Checksums detect damage, not an attacker rewriting cache data and metadata.

# Compiler timings

Pass `--timings` to a compile, check, or assembly emission command to print
elapsed stages to stderr. With `--diagnostic-format=json`, timings are emitted
as a JSON object on stderr. Timings are opt-in; without the flag the compiler
does not collect events. The flag is accepted for compile, `--check`, and
`--emit-asm` commands; it is not available on `--stack-usage` or other commands.

Stages cover input reading; import loading, root lexing/parsing, cfg selection,
and user-defined generator preparation; user-defined and native builtin
generator expansion; generated-source materialization; semantic validation;
native assembly emission; and total command time. Binary builds
also report `native_assembly`, `native_link`, and `output_write`.
`native_assembly` parses the generated Intel assembly and encodes its
instructions. `native_link` covers object processing, symbol/relocation
resolution, and ELF construction; `output_write` covers publishing the
resulting binary. Assembly builds report output writing separately. Nested
instrumented work is included in its outer stage and is not reported as an
overlapping event. Failed commands report stages reached before the failure.

## Language server

Run `lim lsp` to serve LSP over stdin/stdout. It provides live compiler
diagnostics for unsaved buffers and imports, formatting, document symbols,
and explicit `#call` and type definitions across the selected import graph,
including external import prefixes. Navigation on an import path or keyword
opens the imported file, using the compiler's module-path search order and
unsaved buffers. Ordinary declarations remain navigable despite unrelated
type errors. Generated call/type definitions are also supported.
Generated navigation publishes inspectable `.lim/generated/editor-*.lim` source
snapshots on demand, including expansions from unsaved buffers.
It discovers project module paths
and accepts `--cfg KEY=VALUE` and `--module-path PATH` for session settings.
Checks do not write source files or generator caches. See the
[Neovim setup and feature limits](utilities/nvim/README.md#language-server).

### Compilation context for editor checks

Record the effective entry file, native target, cfg values (including builtin
defaults), and project/CLI module paths after a successful compilation or check:

```sh
lim --check src/main.lim --cfg feature=logging --write-lsp-config lim.lsp
```

The same flag works with native compilation and `--emit-asm`. Failed commands
leave the previous context intact; identical settings do not rewrite the file.
Generated paths are absolute. Handwritten relative paths resolve beside `lim.lsp`:

```text
schema-version = 1
entry = "src/main.lim"
target = "x86_64-sysv"
cfg = "platform=linux"
cfg = "arch=x86_64"
cfg = "feature=logging"
module-path = "src"
```

The server discovers the nearest `lim.lsp` to the document, falling back to its
initialized workspace root for imported files outside that directory. This file
is authoritative: it replaces session cfg/module-path settings rather than
merging incompatible configurations. Checks and definition navigation use the
entry's complete import graph, overlaid with unsaved buffers. Files outside the
selected graph produce an explicit diagnostic. Malformed contexts do not silently
fall back to isolated checking. Without `lim.lsp`, the existing per-file behavior
and `lim.project` module-path discovery remain available.

One file selects one active compilation context. Regenerate it to change entry
points or flags. The server requests `lim.lsp` file watching when the client
supports dynamic watcher registration, rechecking open documents on changes;
otherwise settings are reread on the next buffer event or definition request.
The file stores settings only: no shell commands, linker commands, or executable
hooks are run by the server. The current native target remains Linux x86-64 SysV.
