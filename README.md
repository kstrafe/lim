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
- Binary (`0b`), octal (`0o`), hexadecimal (`0x`), and underscore-separated integer literals
- Strings with `\\n`, `\\r`, `\\t`, `\\\\`, and `\\"` escapes
- Quote syntax (`'form`)
- Lisp character literals (`#\a`, `#\space`, `#\newline`)
- `#` and `;` line comments
- The generated-code sigil `@` as a first-class AST node

The first built-in generated declaration is `@optional`, which expands to a
scalar-payload enum:

```lisp
(@optional u64 Maybe?)
(fn identity ((value Maybe?)) Maybe? value)
(fn main () u64
  (let value Maybe? (identity (Maybe?-some 42)))
  (match value ((Maybe?-some payload) payload) (Maybe?-none 0)))
```

The typed declaration pass recognizes primitive Rust-style types (`u8` through
`u128`, `usize`, signed integers, `f32`, `f64`, `bool`, `char`, and `()`), as
well as named types. Local variables use explicit types:

```lisp
(fn add ((left u32) (right u32)) u32
  (let total u32 (+ left right))
  total)
```

Conversions are explicit casts between integer, character, and floating-point
scalar types:

```lisp
(fn main () u64
  (as (as 42 u32) u64))
```

Native `f32` and `f64` locals, homogeneous parameters, mixed scalar parameters,
arithmetic, comparisons, and returns use SSE registers where appropriate.

Character literals have the Rust `char` type and lower to native scalar values:

```lisp
(fn is-a () u64
  (if (== #\a #\a) 1 0))
```

Named type aliases are explicit and resolve to their target type:

```lisp
(type UserId u64)
(fn add_one ((id UserId)) UserId (+ id 1))
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

Function parameters can be explicitly mutable with `(mut name Type)`:

```lisp
(fn increment ((mut value u64)) u64
  (set value (+ value 1))
  value)
```

Unit functions use `()` and can be called for side effects:

```lisp
(fn noop () () ())
(fn main () u64
  (noop)
  42)
```

Value structs can be declared and checked without pointers or traits:

```lisp
(struct Point ((x u64) (y u64)))
(fn point-x () u64
  (get (Point 7 9) x))
```

Scalar structs with at most two fields can also cross function boundaries;
their values use consecutive integer ABI words (`rdi`/`rsi` for parameters and
`rax`/`rdx` for returns).

Fixed arrays of up to six scalar elements use the same flattened value ABI and
can also be passed and returned by functions.

The native backend flattens scalar struct fields into stack slots. Struct
parameters, nested aggregate fields, and aggregate returns are reserved for a
later ABI-lowering stage.

Mutable struct locals support field writes with `set-field`.

Payload-free enums use integer discriminants and support exhaustive `match`:

```lisp
(enum Color (Red Green Blue))
(fn color-value () u64
  (match Green
    (Red 10)
    (Green 20)
    (_ 30)))
```

Enums can also carry one scalar payload:

```lisp
(enum Maybe ((Some u64) None))
(fn main () u64
  (let value Maybe (Some 42))
  (match value ((Some payload) payload) (None 7)))
```

Payload variants may contain multiple scalar fields and bind them in order:

```lisp
(enum Pair ((Pair u64 u64) Empty))
(fn sum () u64
  (let value Pair (Pair 20 22))
  (match value
    ((Pair left right) (+ left right))
    (Empty 0)))
```

Multi-payload enums can also be passed to and returned from native functions
when their payloads fit the scalar integer ABI.

`match` can inspect a constructor or enum-returning call directly; the
compiler stages its discriminant and payload words before selecting an arm.

Fixed-size arrays are value types with stack storage:

```lisp
(fn main () u64
  (let mut values (array u64 3) (array 1 2 3))
  (set-index values 1 40)
  (+ (index values 0) (index values 1)))
```

Scalar floating-point fields and array elements are stored and loaded with
width-correct SSE instructions as well.

When every element is the same, `(array-repeat value)` uses the expected array
type and fills all positions.

Array reads and writes perform native unsigned bounds checks before touching
the stack slot; an out-of-range index traps with `ud2`.

Integer arrays returned from functions can be indexed directly as well:

```lisp
(fn values () (array u64 3) (array 10 20 30))
(fn main () u64 (index (values) 1))
```

Scalar functions also support more than six arguments using the x86-64 SysV
stack-argument convention.

`i128` and `u128` values use two native words (`rax`/`rdx` for results) and
support local storage, parameters, returns, arithmetic, bitwise operations,
comparisons, shifts, and division/remainder.
128-bit multiplication is lowered to the low 128 bits using native multiply
and carry accumulation. Unsigned division and remainder use an emitted
shift/subtract routine with divide-by-zero trapping.

Unsigned integer comparisons and right shifts use unsigned native instructions
when their operands have an unsigned type; unsigned division and remainder use
the native `div` instruction.

Counted loops use explicit init, condition, step, and body forms:

```lisp
(for (let mut i u64 0)
     (< i 10)
     (set i (+ i 1))
  (set total (+ total i)))
```

Infinite loops support `break` and `continue`:

```lisp
(loop
  (set value (+ value 1))
  (break))
```

`block` expressions allow statement sequences inside expression branches:

```lisp
(if true
    (block (set value 40) value)
    (block value))
```

Top-level immutable scalar `let` bindings are emitted in read-only data and
can be referenced by functions:

```lisp
(let ANSWER u64 40)
(fn main () u64 (+ ANSWER 2))
```

Top-level `let` declarations use the same form. Integer, character, and
floating-point constants are emitted in read-only data and can be referenced
by functions.

Every token and top-level expression has a byte span plus line and column
information. Expansion, type checking, monomorphization, and native assembly
code generation are intentionally subsequent compiler stages.
