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

Emit x86-64 assembly with the native backend:

```sh
nix develop --command cargo run -- --emit-asm examples/fibonacci.lim /tmp/fibonacci.s
cc /tmp/fibonacci.s -o /tmp/fibonacci
/tmp/fibonacci
# exits with 55
```

## Syntax currently recognized

- Lists: `(fn name ((arg i32)) i32 (body...))`
- Symbols, including names such as `MyType?` and `-construct`
- Signed decimal integers
- Strings with `\\n`, `\\r`, `\\t`, `\\\\`, and `\\"` escapes
- Quote syntax (`'form`)
- `#` and `;` line comments
- The generated-code sigil `@` as a first-class AST node

The typed declaration pass recognizes primitive Rust-style types (`u8` through
`u128`, `usize`, signed integers, `f32`, `f64`, `bool`, `char`, and `()`), as
well as named types. Local variables use explicit types:

```lisp
(fn add ((left u32) (right u32)) u32
  (let total u32 (+ left right))
  total)
```

Mutable locals, assignment, and `while` are also supported:

```lisp
(fn sum ((n u64)) u64
  (let mut i u64 0)
  (let mut total u64 0)
  (while (< i n)
    (set total (+ total i))
    (set i (+ i 1)))
  total)
```

Value structs can be declared and checked without pointers or traits:

```lisp
(struct Point ((x u64) (y u64)))
(fn point-x () u64
  (get (Point 7 9) x))
```

The native backend flattens scalar struct fields into stack slots. Struct
parameters, nested aggregate fields, and aggregate returns are reserved for a
later ABI-lowering stage.

Payload-free enums use integer discriminants and support exhaustive `match`:

```lisp
(enum Color (Red Green Blue))
(fn color-value () u64
  (match Green
    (Red 10)
    (Green 20)
    (_ 30)))
```

Top-level `let` declarations use the same form. Function bodies are currently
represented as statements, while their expressions remain generic S-expressions
for the type checker and later compiler stages.

Every token and top-level expression has a byte span plus line and column
information. Expansion, type checking, monomorphization, and native assembly
code generation are intentionally subsequent compiler stages.
