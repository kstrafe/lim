# Lim

Lim is an experimental, compiled Lisp designed to make programs explicit and
readable to both people and LLMs. It has strong static types, no type
inference, linear-by-default values, explicit returns and arithmetic behavior,
and a dependency-free Rust compiler. The native backend emits inspectable
x86-64 System V assembly, then encodes and links ELF binaries internally.
An experimental AArch64 Linux backend has its own instruction encoder and
static ELF writer; supported programs can be tested with `qemu-aarch64` in the
Nix shell. See [AArch64 coverage and testing](docs/aarch64-testing.md).

Lim uses concrete generated code instead of user-facing generic types. A
generator invocation such as `(#generate #optional (: type #u64 : name MaybeU64))` emits a concrete type
and its functions. Generators are pure, interpreted at compile time, and use
the restricted `#gn-*` operation set.

Language and standard-library generators use reserved names (`#generate #optional`,
`#generate #cell`); user generators use ordinary names (`#generate make-record`). The entire
`#`-prefixed name space is reserved against user declarations.

Builtin type keywords require `#`, such as `#u8`, `#u64`, and `#bool`.
Numeric literal suffixes remain unchanged (`42u64`), as do explicitly typed
operators (`#u64::add-wrap`).

The language has free-standing functions, not methods or `impl` blocks. It
does not support recursion, function pointers, closures, traits, or implicit
returns. See [docs/language.md](docs/language.md) for the implemented syntax,
ownership rules, and current limitations. The allocator design is described
in [docs/allocator.md](docs/allocator.md).
Cross-feature guarantees and their executable regression coverage are recorded
in [the semantic contracts](docs/semantic-contracts.md).
The symbolic program proof checker and its current limits are described in
[the program verification checklist](docs/program-verification.md).
See [compiler limits and bounded benchmarks](docs/compiler-limits.md) for
analysis budgets, fail-closed behavior, and resource-limited development commands.

The concrete pin, pinned allocation, and borrowed UTF-8 view generators are
documented in [docs/language.md](docs/language.md#raw-pointers-and-unsafe-blocks) and
[the borrowed UTF-8 view section](docs/language.md#borrowed-utf-8-views).
These generators join API names with `::`, such as
`PinnedFrame::Read::value` or `Utf8Slice::from-owner`.

The internal typed-representation migration is documented in
[docs/compiler-ir.md](docs/compiler-ir.md).

Frozen syntax collections, allocation-free error enums, and the initial
cooperative task API are documented in
[docs/collections-and-tasks.md](docs/collections-and-tasks.md).
The default graph async lowering and its source-named cancellation interface are
documented in [docs/async-graph-production.md](docs/async-graph-production.md);
the implementation history and remaining removal work are recorded there.

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
dependencies. See `cargo run -- --help` for the CLI options.
Editors can request `--diagnostic-format=json`; the versioned schema is
described in [docs/diagnostics.md](docs/diagnostics.md).

All declared struct fields, enum payloads, and aliases are checked, even when
unused. Unknown types and infinitely sized by-value cycles are errors; forward
references and cycles broken by references or pointers are supported.

Compilation and `--check` report `warning[W8000]` for unused structs, enums, and
type aliases, underlining the declaration name. A type is used when referenced
by a function signature/body or a global, following type dependencies; all
functions are considered entry points for this warning, including library and
generated functions. Self-references alone do not count. Warnings are nonfatal,
also appear in JSON/LSP diagnostics, and are not emitted by artifact lookup.

Executable builds emit only functions reachable from `main`, including thread
workers and symbols referenced by inline assembly. Every imported definition
is still type-, borrow-, and linearity-checked. `--emit-asm` retains all functions
for library/export use; builds with linked objects or libraries also retain all
exports because external code may call them. Generated `.lim` source remains
fully inspectable even when its unused functions are omitted from the binary.

Run `nix develop --command bash scripts/native-sweep.sh` to compile and run
every example against `examples/outcomes.txt`. Each entry declares an exact
exit code, intentional signal, or compile-only module, plus stdout/stderr
fixtures. A module's expected column may name its complete entry graph
instead of `-`, so distributed-enum declaration fragments are checked with
their contributors. The harness verifies that the entry references the module.
`graph-exit` selects `--cfg async-lowering=graph` for explicit
graph-route coverage; graph lowering is also the default.
`-` means empty output. Missing entries, unexpected signals, wrong output,
compiler/linker failures, and timeouts fail the suite. Exit codes above 128
are not treated as signals. New examples must declare their expected outcome.

## A small Lim program

```lisp run=42
(#fn main () #u64
  (#let answer #u64 (#u64::add-wrap 40u64 2u64))
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
stay on stderr; `--diagnostic-format=json` applies to diagnostics, not cache-report events. Each
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

### Checked library inference summaries

Final checking and compilation cache imported/generated function parameter
summaries in `.lim/cache/semantic/summaries-<hash>.bin`. This is a separate,
versioned, bounded binary cache; generated Lim sources remain inspectable in
the generated-source directory. Each validation session reads its artifact
once into RAM. Warm hits do not rewrite it.

The initial key conservatively includes the entire expanded program, all
loaded source dependencies, generator validation witnesses, sorted cfg values,
module search paths, target and compiler fingerprint/version. Even an unrelated
root or dependency change invalidates it; this is not yet per-library incremental
checking. Exact stored key material guards hash collisions, and a payload checksum
detects damage. Declaration identities are remapped by name, not arena index.
Missing, truncated, incompatible or corrupt artifacts are recomputed. Cache I/O
failure is nonfatal. New summaries are published atomically only after successful
whole-program validation; all type, ownership, borrowing and unsafe checks still
run on warm builds. Build caches are trusted compiler-owned artifacts, not a
security boundary against malicious cache replacement.

`--explain-cache` also reports `semantic-summary` events with function, analysis
mode and context digest in `key_material`, using `hit` or `miss` decisions.

# Compiler timings

Pass `--timings` to a compile, check, or assembly emission command to print
elapsed stages to stderr. With `--diagnostic-format=json`, timings are emitted
as a JSON object on stderr. Timings are opt-in; without the flag the compiler
does not collect events. The flag is accepted for compile, `--check`, and
`--emit-asm` commands; it is not available on `--stack-usage` or other commands.

The `semantic.*` events break validation down into type/signature checking,
lowering, initial and contents-aware summaries, linear ownership, referent
contracts, provenance, outcome graphs, consumption, borrowing and unsafe
checks. Repeated per-function work is aggregated by category. These detail
times are inclusive and overlap (for example, provenance is part of summary
inference); do not add them together. `total` remains the command's wall time.
Semantic work during generator planning is included too, so a category can
span more than the final `semantic_validate` stage. Cache sessions also report
`semantic.cache_load` and `semantic.cache_publish`.

Stages cover input reading; import loading, root lexing/parsing, cfg selection,
and user-defined generator preparation; user-defined and native builtin
generator expansion; generated-source materialization; semantic validation;
native assembly emission; and total command time. Binary builds
also report `native_assembly`, `native_link`, and `output_write`.
`native_assembly` parses the generated Intel assembly and encodes its
instructions. `native_link` covers object processing, symbol/relocation
resolution, and ELF construction; `output_write` covers publishing the
resulting binary. Assembly builds report output writing separately. Nested
top-level stages are included in their outer stage and are not reported as an
overlapping event. Failed commands report stages reached before the failure.

### Finding a generator's output

Use the compilation entry point and a location in any of its imported files:

```sh
lim main.lim --locate-generated path/to/file.lim:42
lim main.lim --locate-generated path/to/file.lim:42:5
lim main.lim --locate-generated path/to/file.lim:42:5-45:2
```

Lines and columns are one-based; columns count Unicode characters, and explicit
range ends are exclusive. A line, position, or range overlapping any
part of a generator invocation selects its output; the selection need not
start on `#generate`. A whole-line range such as `file.lim:42-45` also works. The
command prints each current generated source path with its generator name and
relationship to the selection, without building a native binary:

```text
direct #generate #pin-box -> /project/examples/.lim/generated/generated-<hash>.lim
nested #generate #allocator-for -> /project/examples/.lim/generated/generated-<hash>.lim
```

`direct` identifies output from a selected invocation; `nested` identifies
output from a generator called during its expansion. Direct results come first,
then nested results; paths within each group are sorted. Duplicate paths are
printed only once, with direct selection taking precedence. A selection with
no active invocation produces no paths.

The entry point determines the file dependency graph. Supply the same `--cfg`
and `--target` options as for compilation. Lookup uses the
current expansion and its content-addressed cache, not historical source
locations in cached file headers. Changed generator inputs therefore resolve
to the new artifact even when older files remain in `.lim/generated`.

## Language server

Run `lim lsp` to serve LSP over stdin/stdout. It provides live compiler
diagnostics for unsaved buffers and imports, formatting, document symbols,
and source-role definitions across the selected dependency graph.
Navigation on an alias target or direct file reference opens its declaration,
including declarations in unsaved buffers. Relative `./` paths use the source
file's directory; `//` paths use the entry point's nearest `lim.project`
directory, or its own directory when no manifest exists. Ordinary declarations remain navigable despite unrelated
type errors. Enum variants in `#case`, `#case-ref`, `#case-ref-mut`, `#case-pin`,
and `#case-pin-mut` navigate to their exact declaration names, including
generated variants and distributed-enum contributions. Payload bindings and
wildcards are not treated as variant references. Parameters, locals, destructured
bindings, loop variables, labels, named arguments, and aggregate fields navigate
through their lexical scope or concrete owner type. Constructors and conditional
patterns also resolve enum variants. Generator parameters, helper calls, active
unquotes, and syntax-bundle references have their own navigation roles; quoted
data and arbitrary literal generator arguments deliberately do not resolve.
Generated definitions and bundled standard-library sources are also supported.
Generated navigation publishes inspectable `.lim/generated/editor-*.lim` source
snapshots on demand, including expansions from unsaved buffers.
Go-to-definition on an invocation's `#generate` opens its current generated source
artifact, using the same lookup as `--locate-generated` and the editor's
compilation context. Navigation on the generator name instead opens its
declaration.
It discovers project module paths
and accepts `--cfg KEY=VALUE` and `--module-path PATH` for session settings.
Checks do not write source files or generator caches. See the
[Neovim setup and feature limits](utilities/nvim/README.md#language-server).
New or changed syntax must include navigation roles and exact-range regression
tests as specified in the [LSP design checklist](docs/lsp-design.md#new-syntax-acceptance-checklist).
An independent keyword inventory test enforces an explicit navigation review
when parser keywords are added.

### Compilation context for editor checks

Record the effective entry file, native target, cfg values (including builtin
defaults), and project/CLI module paths after a successful compilation or check:

```sh
lim --check src/main.lim --cfg feature=logging --write-lsp-config lim.lsp
lim --check tests/main.lim --cfg feature=testing --write-lsp-config lim.lsp
```

The same flag works with native compilation and `--emit-asm`. Each successful
invocation adds an independent compilation context; it does not replace existing
entries. Different flags or targets for the same entry are distinct contexts.
Failed commands leave the previous contexts intact; identical effective settings
do not rewrite the file. Parallel builds serialize their read/merge/publication
using an OS-released lock in `.lim/cache`, so entries are not lost.
Generated paths are absolute. Handwritten relative paths resolve beside `lim.lsp`:

```text
schema-version = 2

[[context]]
entry = "src/main.lim"
target = "x86_64-sysv"
cfg = "feature=logging"
module-path = "src"

[[context]]
entry = "tests/main.lim"
target = "x86_64-sysv"
cfg = "feature=testing"
module-path = "src"
```

`cfg` entries are optional: builtin keys default to the selected target.
`target` is optional too and defaults to the host target, as on the CLI.
Explicit cfg entries override individual defaults; custom feature flags must
still be specified when needed.

The server discovers the nearest `lim.lsp` to the document, falling back to its
initialized workspace root for imported files outside that directory. This file
is authoritative: each context replaces session cfg/module-path settings rather
than merging incompatible configurations. Contexts never share a symbol table.
For an open file, the server checks every entry whose active import graph includes
it, overlaid with all unsaved buffers. Definition navigation returns all distinct
locations across those contexts. Thus a library call to a function supplied by
both the application and test binary offers both implementations; a definition
shared by both graphs is shown only once. This applies to imported functions and
types, generator declarations, generated definitions, and navigation on `#generate`.
Context-specific diagnostics identify the entry and settings that produced them.
An invalid entry does not discard definition results from other valid contexts.
Files outside every selected graph produce an explicit diagnostic. Malformed contexts do not silently
fall back to isolated checking. Without `lim.lsp`, the existing per-file behavior
and `lim.project` module-path discovery remain available.

Remove obsolete `[[context]]` blocks explicitly when changing configurations;
recording new settings intentionally preserves existing configurations. The file
is limited to 128 contexts and 1 MiB. The server requests `lim.lsp` file watching when the client
supports dynamic watcher registration, rechecking open documents on changes;
otherwise settings are reread on the next buffer event or definition request.
The file stores settings only: no shell commands, linker commands, or executable
hooks are run by the server. Ordinary checks remain free of source/cache writes;
generated-definition navigation materializes inspectable sources on demand.
