# Lim language reference

Lim is a compiled, statically typed Lisp.  Its syntax is made of
S-expressions, but its type and evaluation rules are deliberately explicit.
The compiler currently targets native x86-64 assembly for the host system and
assembles/links binaries directly with the system `as` and `ld` tools.

This document describes the language implemented by this crate.  The
canonical spelling uses `#` before every builtin form. Unprefixed builtin
forms are rejected.

## Design and scope

Lim currently provides:

- strong static types and explicit types on bindings and parameters;
- no type inference and explicit types on all bindings and calls;
- value structs, enums, tuples, and fixed-size arrays;
- immutable borrowed slices with checked indexing;
- free-standing functions; concrete specialization is generator-driven;
- explicit integer width and overflow behavior;
- native x86-64 code generation using the System V ABI;
- compile-time constants and read-only statics;
- source-level generated declarations such as `@optional` and `@result`;
- pure user-defined syntax generators with a restricted `#gn-*` operation set;
- no recursion, allowing the compiler to calculate a finite call depth.

User-defined traits, methods, closures, and other source-level
indirection mechanisms are not part of the current language. Built-in `Send`
and `Sync` properties are structural. References and raw pointers may point to aggregate values; `#get` projects fields through a reference.
Direct `#deref` and `#deref-set` support scalar values and aggregates that fit
the native value registers. Large aggregate returns, arguments, dereferences,
and reference projections use the compiler's explicit indirect aggregate
storage path.

## Shared allocator state and cells

Dynamic allocation follows the concrete allocator ABI in
[allocator.md](allocator.md). Allocator values are passed explicitly and
generated collections retain an immutable allocator reference; interior
mutability belongs to the allocator implementation.

`(#cell T)` is a single-threaded interior-mutable storage cell for supported
scalar values (`T` must be numeric, `bool`, `char`, a raw pointer, or a
fieldless enum). `(#cell T value)` constructs one, `#cell-get` reads its
current value, and `#cell-set` replaces that value. A cell never returns a
reference to its contents, so allocator state may be shared immutably while a
cursor changes through the cell:

```lisp
(#struct Arena ((cursor (#cell u64))))
(#struct VecU64Arena ((allocator (#ref Arena)) (length u64)))

(#fn VecU64Arena-reserve ((vector (#ref VecU64Arena)) (count u64)) u64
  (#cell-set
    (#get (#get vector allocator) cursor)
    (#u64.+.wrap (#cell-get (#get (#get vector allocator) cursor)) count))
  (#return (#cell-get (#get (#get vector allocator) cursor))))
```

An aggregate that stores a reference retains a borrow of its owner for the
rest of the containing function. It cannot be returned if that borrow points
to a local, and reference-bearing fields cannot be replaced. Mutable
references may be stored in structs and enum payloads; they retain an
exclusive borrow of their source and cannot be cloned. `#cell` is not
thread-safe and provides no synchronization.

Borrows of struct fields are tracked as places. While `point.x` is borrowed,
an access to `point.y` is allowed, but an access to `point.x` or to the whole
`point` is rejected. A field reference derived through a mutable reference
temporarily suspends that parent reference; `#drop` releases the derived loan
and restores the parent borrow.

## Send and Sync properties

`Send` means a value may be transferred to another thread; `Sync` means a
shared reference to the value may be used from another thread. The compiler
derives both properties recursively for structs, enums, tuples, and arrays:

- Scalar types are `Send + Sync`.
- Raw pointers are neither `Send` nor `Sync`.
- `(#cell T)` is `Send` when `T` is `Send`, but is never `Sync`.
- `(#ref T)` is `Send` when `T` is `Sync`, and is `Sync` when `T` is `Sync`.
- `(#ref-mut T)` is `Send` when `T` is `Send`, and `Sync` when `T` is `Sync`.
- An aggregate has a property only when all of its stored fields/payloads
  have that property.

Unsafe native or opaque types may opt in explicitly:

```lisp
(#struct NativeResource ((handle (#ptr u8))))
(#unsafe-impl #send NativeResource)
(#unsafe-impl #sync NativeResource)
```

These declarations are promises by the author and override the structural
result for that property. They must only be used when the type's invariants
make cross-thread transfer or shared access sound. Generic-type overrides are
currently rejected; duplicate or undeclared targets are errors. The
`@thread-spawn TaskType worker-function` declaration validates a monomorphic
worker's parameter and return types against `Send`. It generates
`TaskType-spawn` and `TaskType-join` functions and a private native thread entry
point; user code never passes a function pointer. Spawn arguments are copied
into a private task packet before the worker starts. Scalar and aggregate
arguments/results use the compiler's native calling convention. Spawn returns
`TaskType-spawn-result`: `TaskType-spawn-ok` carries the opaque task handle and
`TaskType-spawn-error` carries an allocation or thread-creation error. Join
returns `TaskType-join-result`: `TaskType-join-ok` carries the worker result;
`TaskType-join-error` carries the still-owned task handle and native error code.
This distinguishes runtime failure from valid zero-valued results and allows
the caller to retry a failed join. A failed join does not release captured
borrows or free the task packet.

For inspection, `@thread-spawn TaskType worker` materializes in `.lim/` as a
`#thread-task` declaration containing explicit `#thread-task-spawn` and
`#thread-task-join` builtin signatures, followed by `#enum` declarations for
their results. The spawn signature exposes `TaskType-spawn`; its result enum
contains `TaskType-spawn-ok` and `TaskType-spawn-error`. The join signature
exposes `TaskType-join`, and its result enum contains `TaskType-join-ok` and
`TaskType-join-error`. The compiler validates and reuses matching signatures
and enums rather than synthesizing duplicates.

Task handles are affine: match spawn results, and join each successful task
handle exactly once. The join error arm must retain or retry the returned
handle; discarding either generated result is rejected. References captured by
a worker remain borrowed until a successful join; shared captures require
`Sync`, mutable captures exclude parent access until join. These restrictions
are checked statically.
Unsafe `#send`/`#sync` overrides are promises, not synchronization: the author
must ensure the underlying resource remains sound under concurrent access.

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
globals are supported. `#deref` reads through a reference, and `#deref-set`
writes through a mutable reference when the target fits the native value
registers. A field reference can
be derived from a named reference to a struct with `(#borrow (#get reference
field))` or `#borrow-mut` for an exclusive field reference. The derived
reference retains the original referent's borrow: it cannot escape when that
referent is local, and a mutable parent reference is suspended while its
derived field reference remains live. Tuple and array projections use `#get`
and `#index`; enum payloads use
`(#get-payload reference Variant index)`.
Reference-valued fields may be projected through nested aggregates; their
original source borrow remains active for as long as the containing aggregate
is live.

```lisp
(#struct Point ((x u64) (y u64)))
(#fn main () u64
  (#let-mut point Point (#struct-literal Point ((x 1) (y 2))))
  (#let point-ref (#ref-mut Point) (#borrow-mut point))
  (#let y-ref (#ref-mut u64) (#borrow-mut (#get point-ref y)))
  (#deref-set y-ref 42)
  (#return (#deref y-ref)))
```

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

The operations are `#addr-of`, `#addr-of-mut`, `#ptr-read`, `#ptr-write`, and
`(#ptr-offset pointer element-index)`. `(#ptr-null (#ptr-mut T))` or
`(#ptr-null (#ptr T))` constructs a typed null pointer; constructing one is
safe, but dereferencing it is not. `(#ptr-is-null pointer)` safely tests
whether a raw pointer is null without consuming it. The offset consumes a raw
pointer and returns a pointer with the same mutability and pointee type; its
index must be `usize`. Byte-offset multiplication and address addition are
checked for overflow and trap on overflow. Writing requires `(#ptr-mut T)`. Reads and
writes do not check allocation bounds, and raw-pointer operations are rejected
outside `#unsafe`; callers must uphold pointer validity and bounds themselves.
`#ptr-borrow` and `#ptr-borrow-mut` also require `#unsafe`; their first
argument is a reference used as the inferred lifetime anchor, and the second
is the pointer to the referenced value. The caller must ensure the pointer is
valid for that anchor's lifetime and, for mutable borrows, uniquely accessible.

## Building and running

The repository contains a Nix flake with the Rust toolchain:

```sh
nix develop
nix develop --command cargo test --all-targets
nix develop --command cargo doc --no-deps --open
```

Compile Lim source directly to a native executable from the Nix development
shell. The backend emits assembly and invokes the system assembler and linker.
By default, the output is placed beside the input and uses
the input filename without its extension. `-o` selects a different path:

```sh
nix develop --command cargo run -- examples/fibonacci.lim
nix develop --command cargo run -- examples/fibonacci.lim -o /tmp/fibonacci
/tmp/fibonacci
echo $? # 55 for the Fibonacci example
nix develop --command cargo run -- --check-examples examples
nix develop --command cargo run -- examples/fibonacci.lim --target x86_64-sysv
```

Native compilation carries an explicit target description. The supported
target/ABI matrix currently has one entry:

| Target spellings | OS/object format | CPU ABI | Backend/linker |
| --- | --- | --- | --- |
| `x86_64-sysv`, `x86_64-unknown-linux-gnu` | Linux ELF | x86-64 System V | native x86-64 assembly, GNU `as` and `ld` |

All other target names (including other operating systems using the System V
calling convention) are rejected. Host selection requires both Linux and
x86-64. The Rust API exposes
`TargetDescription` and `generate_assembly_for_target`; the existing
`generate_assembly` API selects the supported host target.

`--check-examples` recursively parses, type-checks, borrow-checks, and lowers
every `.lim` file under the selected directory. It reports each source file
individually and returns failure if any example fails.

`--emit-asm INPUT OUTPUT` remains available to inspect backend output.
Every generated `@` expansion is materialized as a readable, content-addressed
`.lim` entry under `.lim/cache/`, regardless of whether it uses a built-in or a
user-defined generator. The digest is derived from the normalized invocation,
compiler version, target, complete loaded import forms, and compiler cfg
values. A neighboring key file verifies the full key before a cache hit, so a
digest collision cannot return unrelated generated source. User-generator
evaluation also keeps its lower-level syntax cache in the same directory.
There are no numbered generated-source files; deleting `.lim/` only causes
generators to run and materialized entries to be recreated.

## Compile-time configuration

`#cfg-if` includes only the selected top-level forms. Its condition is built
from `#cfg-is`, `#cfg-not`, `#cfg-and`, and `#cfg-or`; branches contain forms
directly, with an optional final `#cfg-else` branch:

```lisp
(#cfg-if (#cfg-and (#cfg-is #platform linux) (#cfg-is #feature fast))
  (#fn selected () u64 (#return 1u64))
  (#cfg-else
    (#fn selected () u64 (#return 0u64))))
```

`#platform` is populated automatically from the compiler host OS (`linux`,
`macos`, or `windows`, where applicable). Other keys must be passed with
`--cfg KEY=VALUE`; for example, `--cfg feature=fast`. Command-line settings
override automatic values, so `--cfg platform=...` can select another
platform-specific declaration set. Configured values are literal symbols or
strings in `#cfg-is`. Excluded forms are removed before imports, generators,
name checks, and type checking are processed.

Pass `--cfg` repeatedly to set several keys. It works in both binary and
assembly-output modes; a key supplied more than once uses its last value.

Use `--collect-cfgs INPUT` to print the sorted, unique cfg keys referenced by
the source and its imports. Collection scans every cfg branch, including
inactive branches, and follows imports found inside those branches:

```sh
nix develop --command cargo run -- --collect-cfgs examples/cfg_platform.lim
# prints: #platform
```

## User-defined generators

Generators are compile-time syntax functions. Their parameters receive the
invocation arguments literally; generator values are immutable syntax nodes:
symbols, literals, or lists. A generator returns a list of top-level forms,
which are expanded before ordinary Lim parsing and type checking.

Capabilities are explicit declarations for generator requirements. A concrete
type opts in with `#capability`, and a generator parameter can require one:

```lisp
(#fn u64-less ((left (#ref u64)) (right (#ref u64))) bool
  (#return (#u64.< (#deref left) (#deref right))))
(#capability sortable u64
  ((u64-less ((#ref u64) (#ref u64)) bool)))
(#generator make-sortable ((element sortable))
  `((#type Sortable ,element)))
(@make-sortable u64)
```

Each capability declaration lists concrete free-standing operations and their
full argument/return types. Before any generator runs, the compiler verifies
that every named function exists and exactly matches its declared signature.
A missing capability reports the parameter, capability, and concrete type;
there are no implicit structural or interface requirements hidden inside a
generator. Capability definitions are part of the generated-code cache key, so
changing an operation contract cannot reuse expansions made under an older
contract.

```lisp
(#generator aliases (pairs)
  (#gn-for-each pair pairs
    (#gn-list
      (#gn-symbol "#type")
      (#gn-first pair)
      (#gn-first (#gn-rest pair)))))

(@aliases ((Byte u8) (Word u16)))
```

Generator helpers can be declared with `#gn-fn` and called with `#gn-call`.
They take and return only syntax values (symbols, literals, or lists), so
predicate booleans remain internal to conditionals. Helpers may call other
helpers, but direct or indirect recursive calls are rejected. For example:

```lisp
(#gn-fn make-alias (name target)
  `(#type ,name ,target))

(#generator aliases (pairs)
  `(,@(#gn-for-each pair pairs
       (#gn-call make-alias
         (#gn-first pair)
         (#gn-first (#gn-rest pair))))))
```

Backtick starts a syntax template, comma evaluates one generator expression
inside it, and comma-at splices a list of syntax values into a template list.
Unquote and splice are valid only within a backtick template, and splicing a
non-list is an error. Nested templates preserve nested unquotes. These reader
forms are generator-only; they do not evaluate Lim code or add runtime values.
The lower-level `#gn-list` and `#gn-symbol` operations remain available.

The initial generator builtins are `#gn-if`, `#gn-equal`, `#gn-symbol?`,
`#gn-list?`, `#gn-symbol`, `#gn-list`, `#gn-first`, `#gn-rest`,
`#gn-for-each`, `#gn-call`, and `#gn-error`. `#gn-for-each` is the only iteration
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

The compiler first resolves an import relative to the importing file, then
searches module roots added with `CompileConfig::add_module_path` or the
command-line `--module-path DIRECTORY` option. Search order is deterministic;
the first existing file wins.

Projects may add a `lim.project` manifest beside the root source:

```text
schema-version = 1
name = "example"
source-root = "src"
output-dir = "build"
module-path = "modules"
target = "x86_64-sysv"
link-lib = "m"
link-object = "native/support.o"
```

All paths are relative to the manifest. The CLI adds the source root and
module paths to import search, defaults binary output into the output
directory, and applies the manifest target unless `--target` overrides it.
Repeated `link-lib` and `link-object` entries add linker inputs. Schema version
1 validates required name/version, supported target names, existing source and
module directories, duplicate module roots, and existing object files; unknown
keys are errors.

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

Construct a fixed-size array value with `#array-of`, keeping it visually
distinct from the `#array` type form:

```lisp
(#let values (#array u32 3)
  (#array-of (#array u32 3) 10u32 20u32 30u32))
```

An immutable slice type is written `(#slice T)`. Create a full-array view with
`(#slice-of (#borrow array))`; the array's borrow is retained by the slice. Use
`(#slice-len view)` for its runtime length and
`(#slice-idx view index)` to get a shared reference to an element. Indexing
checks the index against the slice length and traps if it is out of bounds.
Slices are immutable for now; ranged subslices are not yet supported.

User-defined names refer to concrete structs, enums, and aliases.  Generic
declarations and angle-bracket applications are not part of Lim.  Generators
create concrete specializations explicitly, such as `(@vec u64 Alloc VecU64)`.
Allocator-backed collections add their concrete operations explicitly with
`(@vec-alloc u64 Alloc VecU64 AllocResult AllocError alloc grow dealloc destroy)`;
the generated API includes `VecU64-new`, `-reserve`, `-push`, `-get`,
`-get-mut`, `-set`, `-pop`, and `-free`. `(@vec-sort u64 VecU64 compare-u64)`
adds `VecU64-sort`; its named comparator accepts two immutable element
references and returns `bool`. Allocation failure and capacity
overflow are returned in generated result types. See [the allocator ABI](allocator.md)
for the allocator and destruction function signatures.

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

Function calls also name every argument explicitly. Use `#call` with a
`#fn-args` list; each argument label must match a parameter in the declaration:

```lisp
(#call add (#fn-args (left 20u32) (right 22u32)))
```

This is the only function-call spelling. Positional call forms are rejected,
including calls with no arguments, which use `(#call function (#fn-args))`.

Generic function declarations and angle-bracket calls are rejected.  Use a
generator to emit a concrete function for each required type combination.

There are no implicit returns.  Every reachable function path must use
`#return`; a unit return must use `(#return ())`.

Native functions declare their calling convention explicitly. `#abi-c` selects
the target's C ABI; external signatures currently accept scalar values and raw
pointers only. By-value aggregate FFI signatures remain rejected. Calls are unsafe FFI boundaries and must be enclosed in
`#unsafe`:

```lisp
(#extern-fn #abi-c abs ((value i32)) i32)
(#fn main () u64
  (#return (#as (#unsafe (abs -42i32)) u64)))
```

Binary compilation always links libc and pthread. Additional native link inputs
can be supplied repeatedly with `--link-lib NAME` and `--link-object PATH`;
object files are passed to `ld` before libraries, and libraries are emitted as
`-lNAME` arguments. These options apply to binary output, not `--emit-asm`.

### C aggregate layout

`#repr-c` opts a struct or enum into the x86-64 System V C layout for layout
queries only; it does not change the Lim runtime representation or grant FFI
compatibility. Struct
fields follow declaration order, with natural field alignment and tail
padding. `#size-of` and `#align-of` report this layout for marked types;
`#offset-of Type field` reports a marked struct field's byte offset. Payload
enums use a signed 32-bit C `int` tag followed by a maximally sized and aligned
union of variant payload structs; fieldless enums use the same 32-bit tag.
Discriminants must fit in signed 32-bit C `int`. These guarantees currently
apply to layout queries only: Lim's runtime aggregate storage still uses its
internal flattened representation, so `#repr-c` values must not be reinterpreted
as C memory or passed through FFI. `#size-of`, `#align-of`, and `#offset-of`
report a C layout description, not the in-memory layout of a Lim value. By-value
aggregate FFI and field access through external aggregate pointers remain
rejected. Only the native x86-64 System V target is currently supported.

### Type aliases

```lisp
(#type UserId u64)
(#type Pair (tuple u64 bool))
(#type Matrix (array f32 4))
```

Aliases are concrete.  Recursive aliases are rejected.

### Structs

Structs are value types with named fields:

```lisp
(#struct Point ((x u64) (y u64)))

(#fn main () u64
  (#let point Point (#struct-literal Point ((x 7u64) (y 9u64))))
  (#return (#get point y)))
```

Use a generator to emit concrete struct declarations when a family of
structs is needed.

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

Top-level `#const`/`#let` values are immutable compile-time values. `#static`
creates immutable read-only storage and is useful for aggregate data. Every
read of a static must occur inside `#unsafe`, including reads used to create a
reference to it:

```lisp
(#const Answer u64 42u64)
(#static Values (#array u64 3)
  (#array (#array u64 3) 10u64 20u64 30u64))

(#fn first-value () u64
  (#return (#unsafe (#index Values 0u64))))
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

Struct types are not constructors. Create a value with `#struct-literal`, or
write a named free-standing constructor function that returns one. Every field
must be supplied exactly once; fields may appear in any order, and omitted
fields are not defaulted:

```lisp
(#struct Point ((x u64) (y u64)))
(#let point Point
  (#struct-literal Point
    ((y 22u64) (x 20u64))))
```

Unknown, duplicate, or missing fields are compile-time errors. A type name in
call position, such as `(Point 20u64 22u64)`, is rejected; give constructor
functions distinct names such as `make-point`.

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

### Linear values and explicit cloning

Local values and function parameters are linear unless their type is plain-old
data or a reference. Built-in scalar values, raw pointers, and structs, enums,
tuples, or arrays whose fields/elements are all copyable are structurally
`Copy`; they can be used without consuming the binding. Resource-bearing
aggregates remain linear and must be consumed exactly once. A moved value
cannot be read or cloned again. Use `#clone` at the point where an additional
value is intended:

```lisp
(#let count u64 40u64)
(#let total u64 (#u64.+.wrap (#clone count) count))
```

Assignments reinitialize mutable bindings only after the previous linear value
has been consumed. A common update pattern moves the old value into the update
and installs the replacement:

```lisp
(#let-mut count u64 0u64)
(#set count (#u64.+.wrap count 1u64))
```

Loop conditions run repeatedly; any outer value they inspect must be explicitly
cloned so it remains available on the next iteration. Both sides of a branch
are checked, and a value moved on either path is unavailable after the join.
`#clone` cannot duplicate mutable references or thread-task handles. If a
function named `<Type>-clone` exists with signature `(<Type>) -> <Type>`,
`#clone` dispatches to it; use that function to define deep-copy behavior for
resource-owning types. Otherwise the backend clones the value representation.
Every function return checks that all still-live linear bindings have been
consumed. Pass an owned value to another function, or explicitly consume it
with `#forget`. `#forget` does not run cleanup; it is intended for use after a
user-written destruction function has released a value's resources. For
example:

```lisp
(#struct Buffer ((allocation Allocation)))
(#fn Buffer-destroy ((buffer Buffer)) ()
  (Allocation-release (#get buffer allocation))
  (#forget buffer)
  (#return ()))
```

Destruction is an ordinary explicit call, not a type hook. A destructor takes
the owned value by value, destructures resource-bearing fields, and calls the
appropriate field destructors before forgetting any remaining representation.
Moving or returning a value transfers the caller's cleanup responsibility;
every explicit `#return` is checked for still-live linear locals. Early-return
paths must likewise consume the values they own before returning. The compiler
never inserts a destructor, so discarding resources with `#forget` remains an
intentional leak rather than hidden cleanup. Generated collections follow the
same rule: their generated `-free` function explicitly destroys each remaining
element and releases storage once, and consuming the vector prevents a second
free.

`#drop` also consumes a value and remains useful for explicitly ending a
reference's borrow. A value cannot be silently overwritten, abandoned at a
scope exit, or consumed on only some control-flow paths. The compiler does not
insert destruction calls or silently discard linear values.
For a struct, tuple, array, or enum containing references, the borrow checker
tracks the provenance of every contained reference. Dropping the aggregate
releases each recorded field loan, so all owners become available again only
after the aggregate itself is dropped. Code generation does not emit runtime
work for references because they are non-owning values.

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
| `#index`, `#get`, `#get-payload` | aggregate and enum projection |
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

Expansion is part of program parsing. Readable generated Lim sources for both
built-in and user-defined `@` invocations are stored as hash-named `.lim` files
under `.lim/cache/`. Their keys include the invocation, compiler version,
target, loaded imports, and cfg values; user-generator execution also caches
raw emitted syntax there using the generator and transitive `#gn-fn` hashes.
Invalid or stale cache entries are ignored and recomputed. The `.lim/`
directory is build output; deleting it only causes generators to run again.
Generated declarations are not methods and do not introduce namespaces.
Nested generated expressions are reserved for future generated forms.

## Permanent non-goals

Lim intentionally has no closures, function-pointer values, methods or `impl`
blocks, traits, or user-defined interfaces. Functions are named, free-standing
declarations; generators create concrete declarations when specialization or
operation families are needed. Thread spawning likewise names the worker at
compile time rather than passing a callable value. This keeps call targets
explicit, preserves whole-program recursion and ownership checks, and avoids
implicit dispatch in generated code.

## Value representation and native backend

The backend emits Intel-syntax x86-64 assembly and follows the explicit
`x86_64-sysv` target description. Scalar integer and pointer-sized ABI words use general
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
   concrete generator expansions.
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
- `render_diagnostic(&Diagnostic, source, filename) -> String` and
  `render_error(source, filename, error) -> String` for Rust-style terminal
  source excerpts;
- `format_source(&str) -> Result<String, String>`;
- `compile_source_to_assembly` and `link_native_binary`, which return
  `Result<_, Diagnostic>` with stable phase codes for lexer, parser, generator,
  analysis, code generation, assembler, and linker failures;
- `write_generated_sources_diagnostic` for recoverable generator-materializing
  diagnostics;
- `write_generated_sources(&str, &Path) -> Result<(), String>`;
- AST and metadata types: `Span`, `Token`, `TokenKind`, `Expr`, `Type`,
  `Statement`, `Function`, `Item`, and `Program`.

Tooling can use `Diagnostic` and `DiagnosticCode` for stable high-level error
categories (`E1000` lexing, `E2000` parsing, `E3000` generators, `E4000`
typing, `E4100` borrowing, `E4200` linear ownership, `E4300` unsafe checks,
`E5000` code generation, and `E6000` linking). Diagnostics carry an optional
source span and structured notes; legacy string-returning APIs remain
available for compatibility.

Borrow failures include the `E4100` code, function and statement context, and
source locations for recognized borrow operators and the conflicting access.
Function-body type errors retain parsed expression trees and generally point
at the offending value or identifier; some checks still report the enclosing
expression or statement. Generated forms retain source context through
parsing, so generator failures remain associated with their invocation.
For mismatched operands of explicitly typed builtin expressions, the
diagnostic mapper uses the reported types and typed syntax to underline the
incompatible operand when it can identify one; this also works for top-level
initializers and typed numeric literals.
Named-call and struct-literal validation retains source spans through lowering,
so unknown or duplicate names and missing-argument/field forms underline the
responsible identifier or argument/field list.
Declaration uniqueness and unsafe-impl validation likewise underline the
repeated or invalid name instead of the whole declaration. C-layout
discriminant and thread-task declaration diagnostics target the invalid
discriminant, worker name, result type, or aggregate field type.
Thread-task handles in function signatures and type aliases underline the
generated task type token.
Import resolution errors underline the path string, and unknown cfg keys
underline the referenced key.
Thread-worker `Send` errors underline the failing parameter type.
Unknown named types in local `#let` annotations underline the type token,
including diagnostics formatted as expected-type mismatches.
Immutable-assignment diagnostics underline the target binding.
Named-type mismatches in destructuring lets underline the annotation, even when
the pattern constructor has the same name.
Mutable-borrow-through-immutable-reference diagnostics underline the owner.
Invalid condition, array-index, and shift-count diagnostics underline the
offending operand.
Type errors for invalid `index`, `slice-of`, `slice-len`, `get`, `get-payload`, and
`deref-set` operands underline the argument with the incompatible shape.
Builtin arity errors underline the operator identifier, retaining its qualified
spelling in source.
Unresolved function calls underline the callee name.
Non-exhaustive match diagnostics underline the `#match` keyword.
Generator capability-contract errors underline the implicated operation name,
including the second spelling in a duplicate-operation error.
Generator-function recursion errors underline the recursive `#gn-call` target.
Duplicate generator parameters underline the repeated parameter name.
Duplicate capability/type pairs and duplicate generator declarations underline
the repeated type or generator name.
Invalid array/struct assignment targets underline the named target.
Missing fields and enum payload variants in `get` expressions underline the
unresolved member name.
Unknown enum variants in match arms underline the pattern token.
Unknown enum variants in `#let-else` patterns do likewise.
Repeated boolean, enum, and wildcard match patterns underline the later
duplicate.
Out-of-range and repeated integer match patterns underline the offending
literal.
Range-pattern diagnostics underline the invalid range, or its upper bound when
the bounds are reversed.
Duplicate character match patterns underline the later character literal.
Enum match payload-arity errors underline the affected variant pattern.

The CLI renders errors with an available span or line/column as a source hunk
with an underline. The parsed source tree retains recursive spans, and the
type, ownership, borrow, unsafe, generator, and code-generation phases use
them where their checks identify a source expression. Statement-level checks
prefer their value expression over the enclosing statement when a more
precise node is not available. Some diagnostics still highlight an enclosing
expression or declaration when an analysis error does not retain its
responsible AST node. Complete exact-span propagation through every analysis
result remains tracked work.
Diagnostic source hunks expand tabs at four-column stops before aligning the
underline, so the displayed code and caret use the same columns.
When a global constant expression contains a function call, its codegen
diagnostic highlights the nested `#call` form rather than the whole initializer.
Imported parser diagnostics use the reported position to underline the full
offending token when it can be read from the imported source.

`Span` offsets are byte offsets into the original UTF-8 source.  `line` and
`column` are one-based.  Lexer failures carry a `LexError`; parser failures
from the lower-level parser carry source spans in `ParseError` when using the
parser internals exposed by the AST path.

## Grammar and builtin semantics

The core grammar is:

```text
program       = { form } ;
form          = atom | list | quote | quasiquote | unquote | splice ;
list          = "(" { form } ")" ;
quote         = "'" form ;
quasiquote    = "`" form ;
unquote       = "," form ;
splice        = ",@" form ;
atom          = symbol | integer | float | character | string | "@" ;
symbol        = identifier ;
identifier    = { letter | digit | "_" | "-" | "." | "?" | "!" | "+" | "*" | "/" | "<" | ">" | "=" | "&" | "|" | "^" } ;
```

Whitespace and semicolon-to-end-of-line comments may occur between tokens.
Builtin declaration and statement forms are the `#`-prefixed forms described
in the tables and sections above; arithmetic and comparison forms include
their type and overflow mode in the identifier. `#let`, `#let-mut`, `#borrow`,
`#borrow-mut`, `#return`, `#unsafe`, `#drop`, `#forget`, and `#clone` define ownership and
borrow behavior; `#cfg-*` is compile-time only; `#gn-*` is generator-time only;
and `@` declarations expand before ordinary parsing, type checking, and borrow
checking. Unknown prefixed forms are rejected rather than treated as future
keywords.

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
