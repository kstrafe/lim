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
