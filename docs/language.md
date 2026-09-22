# Lim language reference

Lim is a compiled, statically typed Lisp.  Its syntax is made of
S-expressions, but its type and evaluation rules are deliberately explicit.
The compiler currently targets native x86-64 assembly for the host system.

This document describes the language implemented by this crate.  The
canonical spelling uses `#` before every builtin form. Unprefixed builtin
forms are rejected.

## Design and scope

Lim currently provides:

- strong static types and explicit types on bindings and parameters;
- no type inference and explicit generic type arguments;
- value structs, enums, tuples, and fixed-size arrays;
- free-standing functions, including monomorphized generic functions;
- explicit integer width and overflow behavior;
- native x86-64 code generation using the System V ABI;
- compile-time constants and read-only statics;
- source-level generated declarations such as `@optional` and `@result`;
- pure user-defined syntax generators with a restricted `#gn-*` operation set;
- no recursion, allowing the compiler to calculate a finite call depth.

Slices, traits, methods, closures, and other source-level indirection
mechanisms are not part of the current language. References and raw pointers
are currently limited to scalar values. Large
aggregate values may use hidden storage pointers at an ABI boundary, but
those pointers cannot be written in Lim source.

## Inferred lexical borrows

Lim's initial borrow model checks lexical borrow scopes without lifetime
annotations. A shared borrow is written as:

```lisp
(#borrow value (#u64.+.wrap value 2))
```

and a mutable borrow as:

```lisp
(#borrow-mut value (#block (#set value 42) value))
```

The three-expression form borrows the owner for the duration of the body.
The two-expression form produces a reference:

```lisp
(#fn first ((value (#ref u64))) (#ref u64)
  (#return value))
```

Multiple shared borrows may overlap, but a mutable borrow cannot overlap any
other borrow, and a shared borrow cannot overlap a mutation. References to
locals cannot escape their function; references returned from parameters and
globals are supported. `#deref` reads through a reference. Mutable reference
writes are reserved for the next reference-operation extension.

## Raw pointers and unsafe blocks

Raw pointers are explicit and distinct from references. `(#ptr T)` is an
immutable raw pointer and `(#ptr-mut T)` is a mutable raw pointer. Taking an
address and reading or writing through a raw pointer must occur inside an
`#unsafe` block:

```lisp
(#fn main () u64
  (#let-mut value u64 40)
  (#return
    (#unsafe
      (#block
        (#let pointer (#ptr-mut u64) (#addr-of-mut value))
        (#ptr-write pointer 42)
        (#ptr-read pointer)))))
```

The operations are `#addr-of`, `#addr-of-mut`, `#ptr-read`, and `#ptr-write`.
Writing requires `(#ptr-mut T)`. Raw pointer operations are unchecked beyond
their static pointee type and are rejected outside `#unsafe`.

## Building and running

The repository contains a Nix flake with the Rust toolchain:

```sh
nix develop
nix develop --command cargo test --all-targets
nix develop --command cargo doc --no-deps --open
```

To compile Lim source to a native executable, first emit assembly and then
assemble/link it with the compiler toolchain in the dev shell:

```sh
nix develop --command cargo run -- \
  --emit-asm examples/fibonacci.lim /tmp/fibonacci.s
nix develop --command clang /tmp/fibonacci.s -o /tmp/fibonacci
/tmp/fibonacci
echo $? # 55 for the Fibonacci example
```

`--emit-asm` takes `INPUT OUTPUT`. Generated `@` declarations are
materialized under `.lim/` beside the input source.

## User-defined generators

Generators are compile-time syntax functions. Their parameters receive the
invocation arguments literally; generator values are immutable syntax nodes:
symbols, literals, or lists. A generator returns a list of top-level forms,
which are expanded before ordinary Lim parsing and type checking.

```lisp
(#generator aliases (pairs)
  (#gn-for-each pair pairs
    (#gn-list
      (#gn-symbol "#type")
      (#gn-first pair)
      (#gn-first (#gn-rest pair)))))

(@aliases ((Byte u8) (Word u16)))
```

The initial generator builtins are `#gn-if`, `#gn-equal`, `#gn-symbol?`,
`#gn-list?`, `#gn-symbol`, `#gn-list`, `#gn-first`, `#gn-rest`,
`#gn-for-each`, and `#gn-error`. `#gn-for-each` is the only iteration
construct; there are no general loops or mutable generator values. `#gn-error`
fails expansion with the supplied message. Generators cannot perform IO or
call runtime functions. Recursive expansion is rejected. Repeating an
invocation with the same generator name and structurally identical literal
syntax arguments emits its output only once. Each compilation allows at most
200,000 generator evaluation steps, 128 nested expansions, and 1,000,000
generated syntax nodes; exceeding a limit is a compile-time error. Unknown
`#gn-*` operations are reported as generator errors with invocation and
definition locations.

Generated identifiers are ordinary identifiers, not hygienic or gensym'd
names. Pass intended declaration names as literal arguments; generated output
then goes through the usual duplicate-name, parsing, type, and borrow checks.
Generators should use distinct explicit names when different invocations are
intended to declare distinct items.

## Imports

Imports load Lim source relative to the importing file. Internal imports keep
identifiers unchanged. External imports prefix user identifiers from the
imported source (including types, functions, fields, variants, and local
bindings); builtin forms and primitive types are unchanged:

```lisp
(#import "shared.lim")
(#import-external "compat.lim" compat-)
```

The external prefix is a symbol prefix, conventionally ending in `-`. Imports
are expanded before generator expansion and ordinary type checking. Repeated
imports of the same canonical path with the same mode and prefix are
deduplicated; cycles are rejected. Imported declarations participate in the
same compilation and duplicate-name checks as declarations in the root file.
See `examples/imports.lim`.

## Lexical syntax

Whitespace separates tokens.  `;` starts a line comment.  A line beginning
with bare `#` is also a comment unless the `#` begins a keyword, operator, or
character literal.

The lexer recognizes:

- `(` and `)` for lists;
- `'form` quote syntax;
- `@` as the generated-code sigil;
- symbols;
- signed and unsigned integer literals;
- floating-point literals;
- strings and character literals.

`.` is an ordinary character in a symbol, not a namespace or member-access
operator.  `-` is also an ordinary symbol character.  Thus these are single
identifiers:

```lisp
math.add.one
my-value
Maybe?-unwrap-or
```

Builtin forms are distinguished by their `#` prefix:

```lisp
(#fn main () u64
  (#return 42u64))
```

The character literal syntax is `#\a`, `#\space`, `#\newline`, and so on.
Unicode escapes use `#\u{03bb}`.  Strings support `\n`, `\r`, `\t`, `\\`,
`\"`, and `\u{...}` escapes.

Integer literals may use binary, octal, hexadecimal, and underscores:

```lisp
42u32  -1i8  0b1010u16  0o77u8  0xffffu128
```

Floating-point literals carry an explicit width when used in canonical code:
`1.5f32` and `0.25f64`.

## Types

The builtin scalar types are:

| Category | Types |
| --- | --- |
| unsigned integers | `u8`, `u16`, `u32`, `u64`, `u128`, `usize` |
| signed integers | `i8`, `i16`, `i32`, `i64`, `i128`, `isize` |
| floating point | `f32`, `f64` |
| other scalars | `bool`, `char` |
| zero-sized | `()` |
| diverging | `!` |

Fixed aggregates are written explicitly:

```lisp
(#tuple u64 bool char)
(#array u32 4)
```

User-defined names refer to structs, enums, and aliases.  Generic type
arguments are written with angle brackets and must be supplied explicitly:
`Box<u64>` and `identity<u64>`.

`()` is the unit value and `!` is the never type.  A function returning `!`
must not reach a normal return.  A void function returns explicitly with
`(#return ())`.

## Top-level declarations

### Functions

Functions are always free-standing; Lim has no methods or `impl` blocks.
The canonical form is:

```lisp
(#fn add ((left u32) (right u32)) u32
  (#let total u32 (#u32.+.wrap left right))
  (#return total))
```

The parameter list is a list of `(name Type)` pairs.  Parameters may be
marked mutable:

```lisp
(#fn increment ((#mut value u64)) u64
  (#set value (#u64.+.wrap value 1u64))
  (#return value))
```

Generic functions declare their type parameters in a list immediately after
the function name.  Calls provide the arguments explicitly:

```lisp
(#fn identity (T) ((value T)) T
  (#return value))

(#fn main () u64
  (#return (#as (identity<u32> 41u32) u64)))
```

There are no implicit returns.  Every reachable function path must use
`#return`; a unit return must use `(#return ())`.

Native functions can be declared with `#extern-fn`.  External functions must
use directly passed scalar types:

```lisp
(#extern-fn abs ((value i32)) i32)
(#fn main () u64
  (#return (#as (abs -42i32) u64)))
```

### Type aliases

```lisp
(#type UserId u64)
(#type Pair (tuple u64 bool))
(#type Matrix (array f32 4))
```

Aliases may be generic.  Recursive aliases are rejected.

### Structs

Structs are value types with named fields:

```lisp
(#struct Point ((x u64) (y u64)))

(#fn main () u64
  (#let point Point (Point 7u64 9u64))
  (#return (#get point y)))
```

Structs may be generic:

```lisp
(#struct Box (T) ((value T)))
(#let boxed Box<u64> (Box<u64> 42u64))
```

### Enums

Variants may be fieldless or carry one or more values:

```lisp
(#enum Message
  (Quit
   (Move i32 i32)
   (Write (#array char 8))))
```

Discriminants are assigned from zero, or can be explicitly supplied using a
numeric value after the variant name.  Variant names are global within a
program and must be unique.

### Globals and statics

Top-level `#const`/`#let` values are immutable compile-time values.  `#static`
also creates immutable read-only storage and is useful for aggregate data:

```lisp
(#const Answer u64 42u64)
(#static Values (#array u64 3)
  (#array (#array u64 3) 10u64 20u64 30u64))
```

Initializers must be compile-time values.  Constant references, arithmetic,
casts, conditionals, tuples, arrays, structs, enums, and floating-point
values are supported.  Cyclic constant references are rejected.

## Variables and mutation

Local bindings always state their type:

```lisp
(#let count u32 0u32)
(#let-mut total u64 0u64)
```

`#let` creates an immutable binding; use `#let-mut` for a mutable binding. Later bindings
may shadow earlier bindings lexically.  `#set` assigns a mutable scalar or
aggregate local:

```lisp
(#set total (#u64.+.wrap total 1u64))
```

Aggregate projections can be updated with `#set-index`, `#set-field`, and
`#set-payload`:

```lisp
(#set-index values 0u64 10u64)
(#set-field point x 11u64)
(#set-field pair 1 12u64)
(#set-payload choice Move 0 5i32)
```

Local destructuring and `#let-else` support tuples, arrays, structs, and enum
patterns.  The `else` body must diverge, for example with `#return`,
`#break`, or `#panic`.

## Operators

Numeric operators are never unqualified in canonical syntax.  The operand
type is part of the identifier, and integer arithmetic must also specify its
overflow mode:

```lisp
(#u64.+.wrap left right)
(#i32.-.saturate left right)
(#u128.*.wrap left right)
(#u128./.wrap dividend divisor)
(#u128.%.wrap dividend divisor)
```

The available integer arithmetic operations are `+`, `-`, `*`, `/`, and `%`.
The modes are:

- `.wrap`: modular two's-complement or unsigned wrapping behavior;
- `.saturate`: clamp to the representable bounds.

There is no plain integer arithmetic spelling.  `#u64.+` and `#u128./` are
rejected because they omit the overflow mode.

Floating-point arithmetic uses the type-qualified operator without an
overflow mode:

```lisp
(#f64.+ left right)
(#f32./ numerator denominator)
(#f64.% left right)
```

The remaining type-qualified operator families are bitwise operations
(`&`, `|`, `^`, `!`, `<<`, `>>`), comparisons (`<`, `<=`, `>`, `>=`, `==`,
`!=`), and boolean short-circuit operations (`#bool.&&`, `#bool.||`).  The
operand type must match the qualifier.  Shifts are checked against the width
of the left operand when the count is statically known; invalid dynamic
counts trap at runtime.

Unary negation is written, for example, as `#i128.-.wrap value`.

All conversions are explicit with `#as`:

```lisp
(#as value u64)
```

Conversions cover integer, character, boolean, and floating-point scalar
representations subject to the type checker’s range rules.

## Expressions and builtin forms

Builtin forms are ordinary Lisp lists whose first symbol begins with `#`.
The following forms are currently implemented:

| Form | Purpose |
| --- | --- |
| `#if` | conditional expression |
| `#if-let` | conditional pattern match |
| `#match` | exhaustive pattern match |
| `#when` | match-arm guard |
| `#block` | statement sequence as an expression |
| `#loop` | infinite loop, or value-producing loop |
| `#while` | conditional loop |
| `#while-let` | pattern-controlled loop |
| `#for` | explicit init/condition/step loop |
| `#for-range` | typed range-loop shorthand |
| `#let`, `#let-else` | local bindings |
| `#set`, `#set-index`, `#set-field`, `#set-payload` | mutation |
| `#break`, `#continue` | loop control |
| `#break-to`, `#continue-to` | labeled loop control |
| `#return` | explicit function return |
| `#tuple`, `#array`, `#array-repeat` | aggregate construction |
| `#index`, `#get` | aggregate projection |
| `#range` | range value for matching and iteration |
| `#as` | explicit cast |
| `#size-of`, `#align-of` | compile-time layout queries |
| `#assert`, `#debug-assert` | runtime assertions |
| `#panic`, `#unreachable` | diverging expressions |
| `#literal` | explicitly typed literal form |

### Conditionals and blocks

An `#if` without an else branch must have unit type.  Value-producing
conditionals require both branches:

```lisp
(#return (#if (#u64.>.wrap value 0u64)
              value
              0u64))
```

`#block` permits statements in an expression position.  Its final expression
is its value; a block used only for side effects has unit type.

### Loops

Statement loops use `#break` without a value:

```lisp
(#while (#u64.< i 10u64)
  (#set i (#u64.+.wrap i 1u64)))
```

A loop expression has a value only when a reachable break supplies one:

```lisp
(#let result u64
  (#loop
    (#if done
         (#break 42u64)
         (#continue))))
```

The explicit `#for` form is:

```lisp
(#for (#let-mut i u64 0u64)
      (#u64.< i 10u64)
      (#set i (#u64.+.wrap i 1u64))
  (#set total (#u64.+.wrap total i)))
```

`#for-range` is shorthand with a typed binding, start, and end.  Its bounds
are explicit and the range is half-open:

```lisp
(#for-range (i u64) 0u64 10u64
  (#set total (#u64.+.wrap total i)))
```

Labels wrap statement loops with `#label`, and value-loop breaks can target an
outer value loop:

```lisp
(#label outer
  (#while condition
    (#if done
         (#break-to outer 42u64)
         (#continue-to outer))))
```

Recursive calls are rejected.  Mutual recursion is rejected as well.

## Patterns and matching

`#match` is exhaustive for enums and scalar booleans; `_` supplies a wildcard.
Enum payloads are written as constructor patterns:

```lisp
(#match value
  ((Some payload) payload)
  (None 0u64))
```

Tuple, struct, array, scalar, range, typed-literal, and `#or` patterns are
supported.  Guards use `#when`:

```lisp
(#match value
  ((Some payload) (#when (#u64.>.wrap payload 40u64)) payload)
  ((Some _) 0u64)
  (None 0u64))
```

Destructuring uses the same aggregate pattern shapes:

```lisp
(#let (#tuple left right) (#tuple u64 u64) pair)
```

The pattern syntax is checked against the explicitly declared type; bindings
are not inferred.

## Generated declarations

`@` marks a generated declaration.  The built-in generated forms are
top-level `@optional` and `@result`.

```lisp
(@optional u64 Maybe?)
(@result u64 u32 Result)
```

`@optional T Name` creates an enum with `Name-some` and `Name-none`, plus
free-standing helpers:

- `Name-construct`
- `Name-is-some`
- `Name-unwrap-or`

`@result Ok Err Name` creates `Name-ok-value` and `Name-err-value`, plus:

- `Name-ok` and `Name-err` constructors;
- `Name-is-ok`;
- `Name-unwrap-or` and `Name-unwrap-err-or`.

Expansion is part of program parsing.  The command-line assembly path also
writes readable generated Lim source files into `.lim/` beside the input.
Generated declarations are not methods and do not introduce namespaces.
Nested generated expressions are reserved for future generated forms.

## Value representation and native backend

The backend emits Intel-syntax x86-64 assembly and follows the host System V
calling convention.  Scalar integer and pointer-sized ABI words use general
purpose registers; `f32` and `f64` values use SSE registers.  `i128` and
`u128` use two machine words.

Tuples, arrays, structs, and enums remain value types.  Small aggregates can
be flattened through the native argument and result registers.  Larger
aggregates use compiler-generated caller storage at the ABI boundary and are
copied as value data; Lim source still exposes no pointers.

Zero-sized values such as `()` and empty structs/arrays occupy no value words.
The compiler computes each function’s maximum call depth after type checking.
Because recursion is forbidden, this gives a finite static stack requirement.

Division by zero, invalid dynamic shifts, failed assertions, `#panic`, and
`#unreachable` lower to runtime traps.  Intentional trap examples are kept
separate by the repository’s native sweep.

## Compiler pipeline

The library exposes these stages:

1. `lex` converts source into tokens with byte and line/column spans.
2. `parse` builds untyped S-expressions and preserves `@` as `Expr::At`.
3. `parse_program` or `parse_program` lowers declarations and builtin
   forms into the typed program representation, including generated forms and
   generic specialization.
4. `check_types` validates declarations, expressions, layouts, patterns,
   calls, constants, mutability, and the acyclic call graph.
5. `generate_assembly` emits native x86-64 assembly.

## Public Rust API

The crate is dependency-free.  Its primary public types and functions are:

- `lex(&str) -> Result<Vec<Token>, LexError>`;
- `parse(&str) -> Result<Vec<SpannedExpr>, String>`;
- `parse_program(&str) -> Result<Program, String>` for canonical syntax;
- `check_types(&Program) -> Result<(), String>`;
- `generate_assembly(&Program) -> Result<String, String>`;
- `write_generated_sources(&str, &Path) -> Result<(), String>`;
- AST and metadata types: `Span`, `Token`, `TokenKind`, `Expr`, `Type`,
  `Statement`, `Function`, `Item`, and `Program`.

`Span` offsets are byte offsets into the original UTF-8 source.  `line` and
`column` are one-based.  Lexer failures carry a `LexError`; parser failures
from the lower-level parser carry source spans in `ParseError` when using the
parser internals exposed by the AST path.

## Examples and verification

The `examples/` directory contains programs covering arithmetic, all integer
widths, floating point, constants, statics, arrays, tuples, structs, enums,
patterns, loops, generated optional/result types, aggregate ABI paths, and
external functions.  `examples/fibonacci.lim` computes Fibonacci(10) and
exits with `55`.

Run the complete native check with:

```sh
nix develop --command ./scripts/native-sweep.sh
```

The sweep compiles and links every example, executes it, and reports ordinary
successes, intentional traps, and compiler/linker/timeout failures separately.
