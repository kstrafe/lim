# Lim

Lim is an experimental, compiled Lisp intended to make generated code
explicit for LLM-written programs. It has a dependency-free parser, a
strict static type checker, generic monomorphization, and a native x86-64
assembly backend. The value representation deliberately excludes references,
pointers, slices, traits, and other indirection mechanisms.

## Development

The repository uses the Rust toolchain from the copied Liftoff Nix flake:

```sh
nix develop
cargo test --all-targets
```

The command-line parser reads a file passed as its first argument, or reads
standard input, and prints the parsed AST. Use `--strict` for the canonical
fully explicit syntax:

```sh
printf '%s\n' '(@optional MyType MyType?)' | nix develop --command cargo run
printf '%s\n' '(#fn main () u64 (#return 42))' | nix develop --command cargo run -- --strict
```

Emit x86-64 assembly with the native backend:

```sh
nix develop --command cargo run -- --emit-asm examples/fibonacci.lim /tmp/fibonacci.s
cc /tmp/fibonacci.s -o /tmp/fibonacci
/tmp/fibonacci
# exits with 55
```

The compiler can require the fully explicit syntax at the command line:

```sh
nix develop --command cargo run -- --emit-asm --strict examples/fibonacci.lim /tmp/fibonacci.s
```

## Syntax currently recognized

The `#`-prefixed forms are canonical. `parse_program` continues to accept
unprefixed forms as compatibility input, while `parse_program_strict` and the
CLI's `--strict` option reject them. This keeps old source readable while
making new keywords unambiguous and leaving future identifiers available.

- Lists: `(#fn name ((arg i32)) i32 (#return value))`
- Symbols, including names such as `MyType?` and `-construct`
- Signed decimal integers
- Binary (`0b`), octal (`0o`), hexadecimal (`0x`), and underscore-separated integer literals
- Explicit integer suffixes such as `42u32`, `-1i8`, and `0xffffu128`
- Explicit floating-point suffixes such as `1.5f32` and `0.25f64`
- Strings with `\\n`, `\\r`, `\\t`, `\\\\`, and `\\"` escapes
- Quote syntax (`'form`)
- Lisp character literals (`#\a`, `#\space`, `#\newline`)
- `#` and `;` line comments
- The generated-code sigil `@` as a first-class AST node

The first built-in generated declaration is `@optional`, which expands to a
enum and generated `-construct`, `-is-some`, and `-unwrap-or` helpers:

`@result` generates a two-payload result enum and explicit `-ok`, `-err`,
`-is-ok`, `-unwrap-or`, and `-unwrap-err-or` helpers:

The assembly CLI materializes each generated declaration as inspectable Lim
source under a `.lim/` directory beside the input file.

```lisp
(@optional u64 Maybe?)
(#fn identity ((value Maybe?)) Maybe?
  (#return value))
(#fn main () u64
  (#let value Maybe? (identity (Maybe?-construct 42)))
  (#return (#match value
    ((Maybe?-some payload) payload)
    (Maybe?-none 0))))
```

```lisp
(@result u64 u32 Result)
(#fn main () u64
  (#let value Result (Result-ok 42))
  (#return (Result-unwrap-or value 0)))
```

The typed declaration pass recognizes primitive Rust-style types (`u8` through
`u128`, `usize`, signed integers, `f32`, `f64`, `bool`, `char`, `()`, and the
diverging `!` type), as well as named types. Local variables use explicit
types:

Later local bindings may shadow earlier bindings, including inside a block. The
initializer is evaluated against the earlier binding, while subsequent
expressions use the new binding. Match payload bindings follow the same lexical
scope rule.

String literals have a fixed compile-time length and their type is an explicit
fixed array of `char`. They do not introduce pointers, slices, or implicit
allocation:

```lisp
(#fn first () u64
  (#let letters (#array char 2) "Hi")
  (#return (#if (#char.== (#index letters 0) #\\H) 1 0)))
```

Fixed-string expressions can also be evaluated for their value words and
discarded as statements; they remain stack-free value data rather than hidden
references.

```lisp
(#fn add ((left u32) (right u32)) u32
  (#let total u32 (#u32.+.wrap left right))
  (#return total))
```

Builtin forms may be written with a `#` prefix, which keeps them distinct from
user-defined symbols. Numeric operators are explicitly qualified by their
operand type:

    (#fn add ((left u32) (right u32)) u32
      (#let total u32 (#u32.+.wrap left right))
      (#return total))

The dot is not a namespace or member-access operator. It is simply part of an
identifier, so a function may be named `math.add.one`; builtin arithmetic names
such as `#u64.+.wrap` are recognized as special forms only because they match a
known builtin spelling.

Integer arithmetic must also specify overflow behavior: use `.wrap` for
modular arithmetic or `.saturate` for clamping arithmetic. Plain integer
arithmetic identifiers such as `#u64.+` are rejected.

Function calls must form an acyclic call graph; recursion is rejected so the
native backend can calculate call-stack requirements ahead of time.

Generic functions declare type parameters explicitly, and calls provide explicit
type arguments such as `(identity<u64> 42)`; type inference is not used.
Integer literals may carry their type directly when contextual typing would be
too implicit:

```lisp
(#fn main () u64
  (#return (#as (#u32.+.wrap 1u32 41u32) u64)))
```

Floating-point literals use the same explicit suffix convention:

```lisp
(#const Scale f32 1.5f32)
(#const Offset f64 0.25f64)
```

Value structs and enums may also declare explicit type parameters. Concrete uses
are specialized before type checking and native code generation:

```lisp
(struct Box (T) ((value T)))
(fn main () u64
  (let boxed Box<u64> (Box<u64> 42))
  (get boxed value))
```

Conversions are explicit casts between integer, character, and floating-point
scalar types:

```lisp
(fn main () u64
  (as (as 42 u32) u64))
```

Integer casts also support the two-word `i128` and `u128` representations,
including sign extension when widening signed values.

The backend exposes representation sizes as a typed `usize` expression:

```lisp
(fn main () u64
(as (size-of (tuple u64 u32)) u64))
```

The unit type `()` and never type `!` are zero-sized and have alignment one.
Zero-sized values can be used in locals, function parameters, tuples, structs,
and fixed arrays without consuming native ABI words.

Empty structs are unit-like zero-sized values:

```lisp
(#struct Marker ())
(#fn make () Marker
  (#return (Marker)))
```

Zero-sized globals do not emit backing storage:

```lisp
(#let UNIT () ())
```

`align-of` reports the corresponding native alignment:

```lisp
(as (align-of u128) u64)
```

Integer arithmetic normalizes results to the operand width, so operations on
`u8`, `u16`, `u32`, and the signed narrow types have Rust-style low-width
semantics.
The same explicit `.wrap` and `.saturate` modes are honored when evaluating
typed integer constants.
Unary integer negation also requires an explicit mode and saturates signed
minimum values to the corresponding maximum (unsigned negation saturates to
zero):

```lisp
(#fn main () u64
  (#return (#as (#i8.-.saturate -128) u64)))
```

This includes the signed minimum-value divided by `-1` saturation case.
Wrapping signed machine-width division and remainder also handle the minimum
value divided by -1 without relying on a trapping native idiv case.
Compile-time wrapping `i128` constants use the same result for that edge case:
the quotient is `i128::MIN` and the remainder is zero.
Saturating signed machine-width division maps that same overflow to the
maximum representable value; saturating remainder remains zero.

Native `f32` and `f64` locals, homogeneous parameters, mixed scalar parameters,
arithmetic, comparisons, and returns use SSE registers where appropriate.
Floating-point remainder uses the native x87 `fprem` instruction and is supported
for both widths.

Functions may freely mix `f32` and `f64` parameters; each argument keeps its
own SSE width.

Floating-point `if` and `match` branches also preserve the expression’s
expected `f32` or `f64` width.

Floating comparisons explicitly handle unordered NaN results: equality and
ordering are false, while inequality is true.

Integer shifts validate their count against the operand width; statically
known out-of-range counts are rejected and dynamic violations trap with `ud2`.

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

Compile-time constants use explicit types and constant initializers:

```lisp
(const Answer u64 (+ 40 2))
(fn main () u64 Answer)
```

Constants may also be declared inside function bodies with the same explicit
type syntax; local constants are immutable.

Floating-point constants support typed arithmetic, including forward
references, remainder, and division while preserving the declared `f32` or
`f64` precision.

Immutable named global storage can be declared with `static`:

```lisp
(static BuildId u64 7)
(fn main () u64 BuildId)
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

Unit-valued `if` expressions may omit their else branch; a value-producing
if still requires both branches.

Boolean assertions lower directly to a native trap on failure:

```lisp
(assert (== value expected))
(debug-assert (>= value 0))
```

`#panic` and `#unreachable` are explicit diverging expressions. They lower to
the native `ud2` trap and can inhabit a branch with any expected static type:

```lisp
(#if condition value (#unreachable))
```

The Rust-like never type is written `!`. A function returning `!` must diverge
explicitly, and calls to it can occupy a branch that otherwise produces a
value:

```lisp
(#fn abort () !
  (#return (#unreachable)))
(#fn choose ((condition bool)) u64
  (#return (#if condition 42 (abort))))
```

Unary `!` negates booleans and performs a bitwise complement on integer
values:

```lisp
(fn main () u32
  (& (! 0) 42))
```

Value structs can be declared and checked without pointers or traits:

```lisp
(struct Point ((x u64) (y u64)))
(fn point-x () u64
  (get (Point 7 9) x))
```

Tuples are value types with explicit element types and positional `get`:

```lisp
(fn main () u64
  (let value (tuple u64 f32) (tuple 40 2.5))
(+ (get value 0) (as (get value 1) u64)))
```

Tuple values can also be destructured in `match` patterns. Bindings are
explicit value bindings, and an aggregate match requires a wildcard arm:

```lisp
(#match value
  ((#tuple first second) (#u64.+.wrap first second))
  (_ 0))
```

Mutable tuple locals support positional writes with `set-field`:
`(set-field value 0 new-value)`.

Scalar structs with at most six fields can also cross function boundaries;
their values use consecutive flattened ABI words in the native value-register
set.

Fixed arrays of up to six scalar elements use the same flattened value ABI and
can also be passed and returned by functions.

Direct tuple, array, and struct return expressions may contain nested value
aggregates when their flattened representation fits the six-word native ABI.
Nested tuple locals and fixed-array locals can also be stored and indexed using
their flattened stack layout. Nested aggregate parameters now use the same
flattened six-word ABI when every leaf value is natively representable. Nested
fixed-array returns from local storage now use the flattened ABI when their
total representation fits six words. Nested tuple/struct field mutation and
aggregate array element replacement use the same flattened representation;
aggregate arrays can also be passed through function calls using that same
flattened representation, including repeated aggregate values and aggregate
array returns.
Aggregate-valued `#if` and `#match` expressions also preserve all flattened
value words across their branches.
Aggregate expressions may be used as discarded statements; their flattened
value words are evaluated and safely discarded without treating constructors as
function calls.
Value-producing `#loop` expressions can likewise break with aggregate values.
Conditional loop paths may carry the aggregate break value while alternate
paths diverge explicitly.
Break values are scoped to their innermost loop; a nested loop’s value break
does not turn an enclosing statement loop into a value expression.
Aggregate control-flow expressions can also be passed directly to functions
through the flattened value ABI.
Aggregate values in `#block` expressions preserve the block's preceding local
statements before lowering the final value.
Enum payloads can be updated explicitly by naming the active variant and
payload field index:

```lisp
(#let mut value Pair (Pair 20 22))
(#set-payload value Pair 1 30)
```

The native backend traps if the value is not currently the named variant.

The native backend flattens scalar struct fields into stack slots and supports
up to six scalar ABI words for struct parameters and returns.

Mutable struct locals support field writes with `set-field`.

Typed tuple and struct `let` bindings may destructure value aggregates
explicitly. Prefix the pattern with `mut` to make all bindings mutable:

```lisp
(#let (#tuple first second) (#tuple u64 u64) value)
(#let (Point x y) Point point)
(#let mut (#tuple first second) (#tuple u64 u64) value)
```

Destructuring patterns may recurse through nested tuple, array, and struct
constructors:

```lisp
(#let (Outer (Inner left right) tail) Outer
      (Outer (Inner 10 20) 30))
```

Fixed arrays support the same explicit form:

```lisp
(#let (#array first second third) (#array u64 3)
      (#array (#array u64 3) 10 20 12))
```

Array values can also be matched with literal, binding, and wildcard
patterns, for example `((#array 10 middle _) middle)`.
Zero-length arrays are valid value types and can be matched with `(#array)`.

Payload-free enums use integer discriminants and support exhaustive `match`:

```lisp
(enum Color (Red Green Blue))
(fn color-value () u64
(match Green
    (Red 10)
    (Green 20)
    (_ 30)))
```

Fieldless enum values can be explicitly cast to integer types to read their
discriminant. Payload enums cannot be cast this way:

```lisp
(#as Green u64)
```

Enum variants may specify an explicit non-negative `u64` discriminant as their
first list value, for example `(#enum Code ((Ready 10) (Failed 42)))`.
Unspecified variants continue from the preceding discriminant.

Enums can also carry one scalar payload:

```lisp
(enum Maybe ((Some u64) None))
(fn main () u64
  (let value Maybe (Some 42))
(match value ((Some payload) payload) (None 7)))
```

`if-let` is syntactic sugar for a two-arm match:

```lisp
(if-let (Some payload) value payload 0)
```

`#let-else` performs a checked destructuring match and keeps successful
bindings in scope. Its else body must diverge explicitly:

```lisp
(#let-else (Some payload) Maybe value
  (#return 0))
(#return payload)
```

The terminal else statement may also be `#panic` or `#unreachable`.

The same aggregate patterns used by `match` are also valid in `if-let` and
`while-let`, including tuple and struct constructor patterns.

`while-let` repeats while its pattern matches and breaks on the first failure:

```lisp
(while-let (Some payload) value
  (set total (+ total payload))
  (set value None))
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

Enum payload fields may also be nested tuples, arrays, or structs when their
flattened discriminant-plus-payload representation fits the six-word native
ABI. Nested payload patterns bind recursively.

Multi-payload enums can also be passed to and returned from native functions
when their payloads fit the scalar integer ABI.

Scalar floating-point enum payloads are also preserved through local storage,
function calls, returns, and `match` bindings.

Wide integer payload patterns compare both native words, so `i128` and `u128`
values can be matched inside enum and aggregate patterns.

`match` can inspect a constructor or enum-returning call directly; the
compiler stages its discriminant and payload words before selecting an arm.
Integer matches also support unsigned literals, including full-width `u128`
patterns.

Match arms may include an explicit boolean guard after their pattern. The
guard can use bindings introduced by that pattern:

```lisp
(#match value
  ((Some payload) (#when (#u64.>.wrap payload 40))
    (#u64.+.wrap payload 8))
  ((Some _) 0)
  (None 0))
```

Guarded patterns do not count as exhaustive until an unguarded arm covers the
same pattern.

Scalar matches use literal patterns and require a wildcard for open-ended
integer and character domains. Boolean matches may cover both `true` and
`false` without a wildcard:

```lisp
(fn classify ((value u64)) u64
  (match value
    (0 10)
    (1 20)
    (_ 30)))
```

Fixed-size arrays are value types with stack storage:

```lisp
(fn main () u64
  (let mut values (array u64 3) (array 1 2 3))
  (set-index values 1 40)
  (+ (index values 0) (index values 1)))
```

Scalar floating-point fields and array elements are stored and loaded with
width-correct SSE instructions as well, including when floating-point arrays
are passed to or returned from functions.

When every element is the same, `(array-repeat value)` uses the expected array
type and fills all positions.

Array reads and writes perform native unsigned bounds checks before touching
the stack slot; an out-of-range index traps with `ud2`.

Computed indexing also supports aggregate array elements when their flattened
representation fits the native six-word value ABI.

Direct array constructors must carry their element type and length explicitly;
there is no element-type inference:

```lisp
(#fn main () u64
  (#return (#index (#array (#array u64 3) 10 20 42) 2)))
```

Repeated direct arrays use the same explicit descriptor:
`(#array-repeat (#array u64 3) 42)`.

Direct tuple constructors likewise require an explicit tuple type:
`(#tuple (#tuple u64 u64) 40 2)`.
These explicit tuple values can be returned from and passed to functions using
the same flattened value ABI.

Integer arrays returned from functions can be indexed directly as well:

```lisp
(fn values () (array u64 3) (array 10 20 30))
(fn main () u64 (index (values) 1))
```

Floating-point arrays returned from functions can be indexed directly too;
the selected element is restored to the appropriate SSE register.

Integer fields can likewise be selected directly from returned structs:

```lisp
(fn point () Point (Point 7 9))
(fn main () u64 (get (point) y))
```

Scalar floating-point struct fields also use their bit-preserving native ABI
words when structs are returned or passed to functions.

Flattened aggregate values can also be passed alongside direct floating-point
parameters; aggregate words use integer registers while direct floats use SSE
registers.

Scalar functions also support more than six arguments using the x86-64 SysV
stack-argument convention.

`i128` and `u128` values use two native words (`rax`/`rdx` for results) and
support local storage, parameters, returns, arithmetic, bitwise operations,
comparisons, shifts, and division/remainder.
Top-level `i128` and `u128` constants and immutable globals use the same
two-word representation in read-only data and can be loaded by functions.
This includes unsigned literals above `i128::MAX` when the declared type is
`u128`.
Compile-time `u128` arithmetic evaluates in the unsigned two-word domain, so
wrapping and saturating constant expressions preserve the same semantics as
native `u128` operations.
Signed `i128` constant saturation uses the exact `i128::MIN` and `i128::MAX`
bounds as well.
Positive literals above `i128::MAX` are represented as `u128` literals and can
be used in explicitly typed `u128` positions.
128-bit multiplication is lowered to the low 128 bits using native multiply
and carry accumulation. Unsigned division and remainder use an emitted
shift/subtract routine with divide-by-zero trapping.
Saturating `i128`/`u128` addition and subtraction clamp to their full two-word
numeric bounds. Saturating `u128` multiplication also detects overflow in its
full 256-bit intermediate. Signed wide multiplication uses absolute magnitudes
and clamps against the signed two-word bounds.
Saturating wide division handles signed minimum-value divided by `-1` by
returning `i128::MAX`; the corresponding remainder is zero.

Unsigned integer comparisons and right shifts use unsigned native instructions
when their operands have an unsigned type; unsigned division and remainder use
the native `div` instruction.
Integer division and remainder explicitly trap with `ud2` when the divisor is
zero.

Counted loops use explicit init, condition, step, and body forms:

```lisp
(for (let mut i u64 0)
     (< i 10)
     (set i (+ i 1))
  (set total (+ total i)))
```

Half-open range loops lower to the same checked, typed loop form:

```lisp
(for-range (i u64) 0 10
  (set total (+ total i)))
```

Infinite loops support `break` and `continue`:

```lisp
(loop
  (set value (+ value 1))
  (break))
```

Loops can also produce values when used as expressions. The result must be
provided explicitly by `#break` with a value:

```lisp
(#return
  (#loop
    (#break 42)))
```

Value breaks may occur inside conditional or block expressions; the loop
continues when the break path is not taken.

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
by functions. Integer constant expressions may reference earlier constants and
use the supported integer, comparison, and boolean operators. They are
normalized to their declared width before emission.
Machine-width unsigned constants are evaluated in their declared unsigned
domain, including wrapping and saturating multiplication at the full `u64`
range.
Wide integer constant left shifts match the native two-word shift lowering when
high bits are discarded.

Immutable static values may also be fixed arrays, tuples, or structs, including
nested value aggregates. Their elements and fields remain value data in
read-only storage and can be read with index and get:

```lisp
(#static Values (#array u64 3)
  (#array (#array u64 3) 10 20 30))
(#fn main () u64
  (#return (#index Values 1)))
```

Floating-point aggregate statics use the same typed value representation:

```lisp
(#static Values (#array f32 2)
  (#array (#array f32 2) 1.5 2.5))
```

Explicit integer casts are also folded in constant initializers.
Constant references may also point to a later top-level declaration; cycles
are rejected during constant evaluation.
Boolean constant expressions preserve the runtime short-circuit behavior of
`&&` and `||`, so an unreachable right-hand expression is not evaluated.

Every token and top-level expression has a byte span plus line and column
information. Expansion, type checking, monomorphization, and native assembly
code generation are intentionally subsequent compiler stages.
