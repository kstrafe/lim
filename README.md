# Lim

Lim is an experimental, compiled Lisp designed to make programs explicit and
readable to both people and LLMs. It has strong static types, no type
inference, linear-by-default values, explicit returns and arithmetic behavior,
and a dependency-free Rust compiler. The native backend emits x86-64 System V
assembly and uses the system assembler and linker to produce a binary.

Lim uses concrete generated code instead of user-facing generic types. A
generator invocation such as `(@optional u64 MaybeU64)` emits a concrete type
and its functions. Generators are pure, interpreted at compile time, and use
the restricted `#gn-*` operation set.

The language has free-standing functions, not methods or `impl` blocks. It
does not support recursion, function pointers, closures, traits, or implicit
returns. See [docs/language.md](docs/language.md) for the implemented syntax,
ownership rules, and current limitations. The allocator design is described
in [docs/allocator.md](docs/allocator.md).

## Build the compiler

The repository's Nix development shell provides Rust and the native build
tools:

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

Run `nix develop --command bash scripts/native-sweep.sh` to compile and run
every example against `examples/outcomes.txt`. Each entry declares an exact
exit code, intentional signal, or compile-only module, plus stdout/stderr
fixtures (`-` means empty). Missing entries, unexpected signals, wrong output,
compiler/linker failures, and timeouts fail the suite. Exit codes above 128
are not treated as signals. New examples must declare their expected outcome.

## A small Lim program

```lisp run=42
(#fn main () u64
  (#let answer u64 (#u64.+.wrap 40u64 2u64))
  (#return answer))
```

Builtins and special forms are prefixed with `#`; numeric operators are
qualified by type and explicitly select wrapping or saturation behavior.
Bindings declare their types, and every function exit uses `#return` (including
`(#return ())` for unit-returning functions).

An explicit type mismatch is rejected (this example is tested as `E4000`):

```lisp error=E4000
(#fn main () u64
  (#let answer u64 false)
  (#return answer))
```
