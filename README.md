# Lim

Lim is an experimental, compiled Lisp intended to make generated code
explicit for LLM-written programs. The current implementation is the
dependency-free lexer/parser foundation.

## Development

The repository uses the Rust toolchain from the copied Liftoff Nix flake:

```sh
nix develop
cargo test
```

The command-line parser reads a file passed as its first argument, or reads
standard input, and prints the parsed AST:

```sh
printf '%s\n' '(@optional MyType MyType?)' | nix develop --command cargo run
```

## Syntax currently recognized

- Lists: `(fn name ((arg i32)) i32 (body...))`
- Symbols, including names such as `MyType?` and `-construct`
- Signed decimal integers
- Strings with `\\n`, `\\r`, `\\t`, `\\\\`, and `\\"` escapes
- Quote syntax (`'form`)
- `#` and `;` line comments
- The generated-code sigil `@` as a first-class AST node

Every token and top-level expression has a byte span plus line and column
information. Expansion, type checking, monomorphization, and native assembly
code generation are intentionally subsequent compiler stages.
