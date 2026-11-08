# Lim language reference

Lim code fences carry explicit test metadata: `run=N` compiles and runs with
exit code N; `library` compiles through native emission; `fragment=NAME` uses
the named function wrapper in `tests/language_docs.rs`; `error=CODE` must
fail with that diagnostic. `syntax` marks schematic forms or signatures
with intentionally undefined placeholders; these are parsed, not type-checked.
The documentation tests cover this reference, README, allocator notes, and
the soundness audit, and reject unclassified Lim fences.

Lim is a compiled, statically typed Lisp.  Its syntax is made of
S-expressions, but its type and evaluation rules are deliberately explicit.
The compiler currently targets Linux x86-64 System V. It emits inspectable
assembly, then encodes and links ELF binaries internally, including supported
ELF objects and shared-library calls. Unsupported assembly or object features
produce a link diagnostic; the compiler does not invoke `as` or `ld`.

This document describes the language implemented by this crate. Builtin forms
and all sixteen scalar types use a leading `#`, such as `#u64` or `#bool`;
unprefixed builtin forms and scalar types are rejected. Numeric literal
suffixes keep their established spelling, such as `42u64`. User-defined type
names remain ordinary identifiers and never receive a `#` prefix.

Declaration spelling identifies its role. Every `::` component in a type name
starts with an ASCII uppercase letter (`Reading`, `Work::Frame`). Functions,
parameters, fields and variables start lowercase or with `_`; a function can
have uppercase type prefixes (`Work::poll`). A dot is reserved for enum variants:
`Work::Poll.Ready` is variant `Ready` of enum `Work::Poll`. These are single
global identifiers, not namespace or field-access operations. The compiler
enforces the same rules on generated declarations and handwritten code.
Compiler-issued hygienic `#gn-gensym` names occupy a separate reserved domain;
they can also name private types without colliding with public declarations.

User function names retain their identity when called with `#call`, even
when a name also spells a builtin. For example, `(#call panic (: value
reference))` calls the declared user function named `panic`; `(#panic)` remains
the builtin trap. `#call` requires named arguments, evaluates their expressions
in parameter declaration order, and applies the declared function signature
and ordinary eager-call ownership rules. `#call` accepts only safe functions,
even inside `#unsafe`. Use `#unsafe-call` for unsafe or external functions;
it requires an enclosing `#unsafe` block and uses the same named arguments,
evaluation order, signature checks, and ownership rules.

For syntax, contextual examples, and semantics of every builtin, see the
[alphabetical builtin reference](#complete--builtin-reference-alphabetical)
and its [typed operator families](#typed-operator-families-alphabetical).

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
- source-level generated declarations such as `#generate #optional` and `#generate #result`;
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

`#generate #cell` is a standard-library generator in `library/cell.lim`, not a builtin
type. Each invocation explicitly names the concrete type and three
free-standing functions. It currently accepts the integer widths supported
by `#atomic` (`#i8/#i16/#i32/#i64`, `#u8/#u16/#u32/#u64`, and `#usize`); it does not
support floats, pointers, or enums. The generated get/set functions take a
shared reference to the concrete cell and never return a reference to its
contents:

```lisp library
(#alias cell-generator = ../library/cell.lim::#cell)
(#generate cell-generator #u64 CellU64 CellU64::create CellU64::get CellU64::set)
(#struct Arena () ((cursor CellU64)))
(#fn advance ((cursor (#ref CellU64))) #u64
  (#let next #u64 (#u64::add-wrap
    (#call CellU64::get (: cell (#clone cursor))) 1u64))
  (#call CellU64::set (: cell (#clone cursor) : value next))
  (#return next))
```

An aggregate that stores a reference retains a borrow of its owner for the
rest of the containing function. It cannot be returned if that borrow points
to a local, and reference-bearing fields cannot be replaced. Mutable
references may be stored in structs and enum payloads; they retain an
exclusive borrow of their source and cannot be cloned. The generated cell is
linear, but its relaxed atomic storage makes it both `Send` and `Sync`. A
read-modify-write sequence such as `advance` is not an atomic increment; use
`#atomic-fetch-add` when multiple threads must update one counter.

For coordinated shared mutable state, use explicit atomic operations.
The atomic API supports `#i8/#i16/#i32/#i64`, `#u8/#u16/#u32/#u64`, and
`#usize`. Each operation uses the width's naturally aligned x86 memory access;
Lim's current local and aggregate storage is at least eight-byte aligned:

```lisp fragment=atomics
(#let-mut counter (#atomic #u64) (#atomic-init #u64 0u64))
(#atomic-fetch-add (#borrow counter) 1u64 #memory-acq-rel)
(#let observed #u64 (#atomic-load (#borrow counter) #memory-acquire))
(#atomic-store (#borrow counter) observed #memory-release)
```

`(#atomic-exchange reference desired #memory-order)` replaces the value and
returns the old scalar. Compare-exchange has these explicit forms:

```lisp syntax
(#atomic-compare-exchange reference expected desired #memory-acq-rel #memory-acquire)
(#atomic-compare-exchange-weak reference expected desired #memory-release #memory-relaxed)
```

Both return `(#tuple #bool ScalarType)`: success followed by the observed
old value. On failure memory is unchanged; the observed value can be used
for an explicit retry. Expected and desired must match the atomic scalar.
Success accepts every `#memory-*` order; failure accepts relaxed, acquire,
or seq-cst, and cannot be stronger than success. In particular, release
success permits only relaxed failure; acquire failure requires acquire,
acq-rel, or seq-cst success. Release/acq-rel failure orders are invalid.

The x86-64 backend emits memory `xchg` for exchange (implicitly locked),
and `lock cmpxchg` for both compare-exchange forms. Narrow observed values
are sign- or zero-extended according to the scalar type. These instructions
provide stronger hardware ordering than relaxed operations require. Weak
compare-exchange is currently implemented without spurious failure; callers
must still allow spurious failure for future backends. Atomic operations
provide no scheduling fairness or starvation guarantee. See
`examples/atomic_claim.lim` for two workers claiming the same state; both
tasks are spawned before either is joined.

Loads accept `#memory-relaxed`, `#memory-acquire`, or `#memory-seq-cst`;
stores accept `#memory-relaxed`, `#memory-release`, or `#memory-seq-cst`.
Fetch-add accepts any of those plus `#memory-acq-rel`. Invalid order/operation
combinations are compile-time errors. The native `x86_64-sysv` backend relies
on aligned 8-bit, 16-bit, 32-bit, and 64-bit x86 atomic accesses; acquire and
release loads/stores use x86 TSO ordering, seq-cst stores use an exchanging
instruction, and read-modify-write uses a locked instruction. This API is not
available for `#i128` or `#u128`. Unsafe `#send`/`#sync` overrides remain the
author's soundness promise and do not replace atomic operations.

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
- Generated `#generate #cell` types use relaxed atomic storage and are `Send + Sync` for
  their supported integer widths.
- `(#atomic T)` is both `Send` and `Sync` only for the supported atomic integer
  widths listed below.
- `(#ref T)` is `Send` when `T` is `Sync`, and is `Sync` when `T` is `Sync`.
- `(#ref-mut T)` is `Send` when `T` is `Send`, and `Sync` when `T` is `Sync`.
- An aggregate has a property only when all of its stored fields/payloads
  have that property.

Unsafe native or opaque types may opt in explicitly:

```lisp library
(#struct NativeResource () ((handle (#ptr #u8))))
(#unsafe-impl #send NativeResource)
(#unsafe-impl #sync NativeResource)
```

These declarations are promises by the author and override the structural
result for that property. They must only be used when the type's invariants
make cross-thread transfer or shared access sound. Generic-type overrides are
currently rejected; duplicate or undeclared targets are errors. The
`#generate #thread-spawn` with `(: task TaskType : worker worker-function)` validates a monomorphic
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

On the Linux x86-64 backend, generated threads use direct kernel calls, not
libc or pthreads. `mmap` reserves a stack and task packet; `mprotect` leaves
the bottom page inaccessible. The compiler sizes each worker's stack from its
emitted call graph, rounded to pages with a 64-KiB minimum and allowances for
the entry trampoline and red zone. An unknown or unbounded worker call path
is a compilation error rather than a guessed stack size.

The native `clone` trampoline starts execution on the new stack. The parent
and child share a kernel-managed TID word: parent-TID publication avoids an
immediate-exit race, and child-TID clearing wakes a shared futex after exit.
Join waits for that clearing before copying the result and unmapping the
stack/packet. `EINTR` and `EAGAIN` retry internally; other futex errors retain
the task handle in the join-error result. Allocation/protection and creation
failures keep the existing distinct spawn-error variants. See the Linux
[clone contract](https://man7.org/linux/man-pages/man2/clone.2.html) and
[clear-child-TID contract](https://man7.org/linux/man-pages/man2/set_tid_address.2.html).

Workers have no libc TLS: their FS base is explicitly zero, and reachable
foreign or indirect callees are rejected, including calls through Lim helper
functions. Explicit FFI outside worker call graphs remains available. Unsafe
worker assembly must obey the same no-foreign-runtime and stack contracts;
it must not terminate the thread early or change its clear-child-TID address.
Installing custom signal handlers is also an unsafe responsibility: block
their signals before spawning, arrange a worker-owned alternate signal stack,
then unblock them. The computed Lim stack bound does not cover arbitrary
signal-handler frames. The backend provides no pthread cancellation or TLS
destructor behavior.

`examples/kernel_threads.lim` exercises concurrent parent/worker progress,
shared PID/distinct TIDs, the worker TLS boundary, repeated joining, and
stdout. `tests/kernel_threads.rs` checks static ELF linkage, argument/result
layouts, nested workers, large stack frames, and an actual guard-page fault.
Its opt-in ptrace tests also verify kernel calls and inject spawn/join failures.

For inspection, `(#generate #thread-spawn (: task TaskType : worker worker))` materializes in `.lim/` as a
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

```lisp syntax
(#borrow value (#u64::add-wrap value 2))
```

and a mutable borrow as:

```lisp syntax
(#borrow-mut value (#block (#set value 42) value))
```

The three-expression form borrows the owner for the duration of the body.
The two-expression form produces a reference:

```lisp library
(#fn first ((value (#ref #u64))) (#ref #u64)
  (#return value))
```

Multiple shared borrows may overlap, but a mutable borrow cannot overlap any
other borrow, and a shared borrow cannot overlap a mutation. References to
locals cannot escape their function; incoming reference referents and
globals may be returned. A by-value parameter's own storage is local too:
returning `(#borrow parameter)` is invalid even if the parameter itself
contains references. Loading one of those incoming references preserves
its external referent instead. `#deref` reads through a reference, and `#deref-set`
writes through a mutable reference when the target fits the native value
registers. The known target type is used for aggregate RHS values, including
one-word structs. Writing a zero-sized aggregate evaluates both operands but
writes no bytes. A field reference can
be derived from a named reference to a struct with `(#borrow (#get reference
field))` or `#borrow-mut` for an exclusive field reference. The derived
reference retains the original referent's borrow: it cannot escape when that
referent is local, and a mutable parent reference is suspended while its
derived field reference remains live. Tuple and array projections use `#get`
and `#index`; enum payload fields use `(#get-payload reference Variant index)`. Each
variant has zero or one payload. Use a named struct as the payload when a
variant needs multiple fields.
Projections may also start at an owned local, without borrowing the entire
aggregate first: `(#borrow (#get owner field))`. Nested struct, tuple, array,
and enum-payload projections address the original storage; a dynamic index
is evaluated once before the borrow's body. Mutable borrowing requires a
mutable local or an exclusive reference root. The same rules apply to
`#pin-borrow` and `#pin-borrow-mut`, and reborrowing through a pinned reference
preserves pinning. A projection cannot borrow a computed aggregate temporary.
When crossing a reference-valued field, bind that reference first so the
next borrow has an explicit reference root. See `examples/owned_field_borrow.lim`.

Reference-valued fields may be projected through nested aggregates; their
original source borrow remains active for as long as the containing aggregate
is live.

```lisp run=42
(#struct Point () ((x #u64) (y #u64)))
(#fn main () #u64
  (#let-mut point Point (#struct-literal Point ((x 1) (y 2))))
  (#let point-ref (#ref-mut Point) (#borrow-mut point))
  (#let y-ref (#ref-mut #u64) (#borrow-mut (#get point-ref y)))
  (#deref-set y-ref 42)
  (#return (#deref y-ref)))
```

## Raw pointers and unsafe blocks

Raw pointers are explicit and distinct from references. `(#ptr T)` is an
immutable raw pointer and `(#ptr-mut T)` is a mutable raw pointer. Taking an
address and reading or writing through a raw pointer must occur inside an
`#unsafe` block:

```lisp run=42
(#fn main () #u64
  (#let-mut value #u64 40)
  (#return
    (#unsafe
      (#block
        (#let pointer (#ptr-mut #u64) (#addr-of-mut value))
        (#ptr-write pointer 42)
        (#ptr-read pointer)))))
```

Functions with caller safety obligations use `#unsafe-fn` instead of `#fn`.
Their signatures otherwise have the same shape. Every call uses `#unsafe-call`
inside `#unsafe`, including calls from another unsafe function. `#call` rejects
unsafe functions even inside `#unsafe`, and `#unsafe-call` rejects safe
functions. The declaration does not make its body implicitly unsafe: raw
operations and unsafe calls still need an explicit block.

```lisp run=42
(#unsafe-fn read-byte ((pointer (#ptr #u8))) #u8
  (#return (#unsafe (#ptr-read pointer))))
(#fn main () #u64
  (#let value #u8 42u8)
  (#return (#as (#unsafe
    (#unsafe-call read-byte (: pointer (#addr-of value)))) #u64)))
```

Imports and generated declarations preserve the calling requirement. Implicit
entry points (`main`, aggregate clone hooks, and thread workers) must be safe;
use a safe wrapper that explicitly discharges the unsafe function's obligations.
Generator capability contracts currently describe safe operations, so an unsafe
operation does not satisfy one. The Linux library uses this contract for all
raw-pointer wrappers and integer-only APIs with hidden memory or execution-state
obligations. Reference-bounded byte/time helpers remain safe. See the
[syscall caller contracts](syscall-coverage.md#caller-safety-contracts).

The operations are `#addr-of`, `#addr-of-mut`, `#ptr-read`, `#ptr-write`, and
`(#ptr-offset pointer element-index)`. `(#ptr-null (#ptr-mut T))` or
`(#ptr-null (#ptr T))` constructs a typed null pointer; constructing one is
safe, but dereferencing it is not. `(#ptr-is-null pointer)` safely tests
whether a raw pointer is null without consuming it. `(#ptr-address pointer)`
returns the machine address as `#usize` without dereferencing it; it can check
Linux error-pointer returns before any access. The offset consumes a raw
pointer and returns a pointer with the same mutability and pointee type; its
index must be `#usize`. Offsets use the pointee's byte width (for example,
`*mut u8` advances one byte). Byte-offset multiplication and address addition
are checked for overflow and trap on overflow. Reads and writes access only
the pointee's width. Writing requires `(#ptr-mut T)`. Reads and writes do not
check allocation bounds, and raw-pointer operations are rejected
outside `#unsafe`; callers must uphold pointer validity and bounds themselves.
`#ptr-borrow` and `#ptr-borrow-mut` also require `#unsafe`; their first
argument is a reference used as the inferred lifetime anchor, and the second
is the pointer to the referenced value. The `#pin-ptr-borrow` variants require
a pinned-reference anchor and preserve the pinned-reference type/provenance.
The caller must ensure the pointer is valid, stable, and uniquely accessible
as required for the full anchor lifetime. These forms do not make allocation
or pointer validity safe by themselves.

Pinning is exposed through generated opaque objects rather than a special
binding statement. Import `library/pin.lim` and declare a concrete API:

```lisp syntax
(#generate #pin (: type Frame : name PinnedFrame : fields (: value #u64)))
(#generate #pin-scope (: type Frame : pin PinnedFrame : name with-pinned-frame
  : run drive-frame : destroy destroy-frame : result #u64))
```

`#generate #pin` emits opaque `PinnedFrame` and `PinnedFrame::Shared` handles, unsafe
constructors, and `PinnedFrame::Read::value` / `PinnedFrame::Write::value` free
functions (plus the shared reader). Field types are literal generator inputs;
ordinary checking verifies them and rejects moving linear fields or replacing
fields that do not satisfy the pinned-field restrictions. Optional `copy true`
emits whole-value readers and a writer only after checking a structural Copy
proof. All implementation functions are inspectable in the generated cache.
For linear fields, `projections (: child PinnedChild)` generates
`PinnedFrame::Project::child` and `PinnedFrame::ProjectMut::child`, returning
the existing concrete child pin handles without moving the field. Shared
handles also get a shared projection. Projection consumes the parent handle;
it does not leave a second mutable handle to the same storage. Derived handles
retain their source's borrow and cannot outlive it. Unsafe
`PinnedFrame::into-view` consumes a handle and exposes its low-level pinned
reference for trusted implementations; it does not unpin or move the referent.

The same declarations also generate `PinnedFrame::BorrowMut::child`, taking
`(: pin (#ref-mut PinnedFrame))`, and `PinnedFrame::Borrow::child`, taking
`(: pin (#ref PinnedFrame))`. Shared wrappers have their own shared `::borrow`
function. These reborrow the child without consuming the parent handle.
Disjoint mutable child fields can coexist, as can overlapping shared views;
overlapping exclusive access is rejected at the offending call argument.
Callee footprints follow the wrapper's actual pinned pointer slot, including
helper calls and transferred child arguments, not just its stack address.
Forgetting a wrapper does not unpin or destroy its referent: child views still
retain that referent, and prevent scope escape or heap release. See
`examples/pin_projection_borrows.lim` for two independently writable children.

`with-pinned-frame` takes `value Frame`, initializes private stack storage,
and calls `drive-frame` with `pin PinnedFrame`. It then calls `destroy-frame`
with a fresh pin handle before retiring that storage in place. The run function
returns the specified result type; the destruction function returns unit.
Both functions must consume their handles explicitly. The original storage
is inaccessible to callbacks, even if they forget their handles. Returned
borrows cannot escape the scope, and cancellation/resource cleanup must be
implemented in the destruction callback. No function pointers, lambdas,
`#let-pin`, or `#pin-end` are needed. See `examples/stationary_pin.lim`.

For an initialized local, `(#pin local)` creates an exclusive `(#pin-ref-mut T)`
and requires a `#let-mut` binding. `(#pin-shared local)` creates a shared
`(#pin-ref T)` and also accepts immutable locals. Neither accepts a temporary,
projection, reference variable, top-level constant, or static: use
`#pin-borrow`/`#pin-borrow-mut` for
projection reborrows. Both local operations permanently freeze the original
storage, including Copy locals. Forgetting the reference ends its loan, but
does not allow moving or assigning the original local again. A branch that
may pin a local also freezes it after the branch joins.
Copy values can still be read or copied from frozen storage when normal loan
rules permit: copying a Copy value does not move the storage itself. Whole-local
assignment remains forbidden. Each new loop iteration initializes fresh local
storage; explicitly end the previous iteration's local after its views end.

```lisp run=42
(#struct LocalJob (#linear) (: state #u64))

(#fn main () #u64
  (#let-mut job LocalJob (#struct-literal LocalJob (: state 0u64)))
  (#let view (#pin-ref-mut LocalJob) (#pin job))
  (#pin-set-field view state 42u64)
  (#let answer #u64 (#get view state))
  (#forget view)
  (#forget job)
  (#return answer))
```

Ordinary named functions can take pinned references, so multiple local pins
can be selected and polled in branches without callbacks or generated wrappers.
An ordinary reference does not satisfy a pinned-reference parameter. Local
pins cannot escape their storage scope, and overlapping mutable loans are
rejected. After all references end, explicit `#forget owner` ends the local
in place; it is not a destructor and performs no resource cleanup. Perform
any required in-place cleanup first. Local pinning does not change `#pin-own`:
that heap owner remains movable because its allocation stays stationary.

Low-level pinned-reference operations remain compiler primitives for generated
code and unsafe implementations. Ordinary `#pin-borrow` permanently prevents
moving a linear local after its first pin, even after its last view is forgotten;
explicit `#forget`/`#drop` ends that local's lifetime. Plain Copy referents retain
short-lived borrow rules. Nonmoving Copy field operations on pinned linear
locals remain allowed, subject to the existing field-loan checks.

`(#pin-own T)` is a linear, movable owner of stationary heap storage. Unsafe
`#pin-own-of pointer value` initializes uniquely owned writable allocation
storage using Lim's native value layout and adopts it; safe
`#pin-own-borrow` and `#pin-own-borrow-mut` borrow the allocation identity, not
the handle's address. Views remain valid across handle moves, aggregate moves,
and function returns. An optional allocator-reference argument keeps the
allocator borrowed for the entire view lifetime. Forgetting an owner leaks
the allocation rather than moving, freeing, or unpinning its contents.
In-place cleanup precedes unsafe `#pin-release`, which returns the pointer for
deallocation. Retained views block release, including release in called helpers.
Calls that obtain conflicting pointee access also reject retained views; a
pure owner-forwarding function does not. The opaque owner generated by
`#generate #pin-box` exposes native pinned references; its destruction callback accepts
`pin` with type `(#pin-ref-mut T)` for in-place cleanup.
Transferring an owning allocation to a thread requires retirement of its
existing pointee views.
The caller still guarantees validity, alignment, unique raw ownership, and
retirement of untracked raw pointers. Reference-bearing and nested owning-pin
pointees retain their contents' loans through owner moves, return summaries,
and field projections. Allocating storage does not extend a referent's lifetime.
Heap writes, including helper-call writes, update retained loans in the owning
allocation. A definite write to one concrete field retires that field's old
loan and records its replacement; uncertain writes and control-flow joins keep
all possible referents. A reference already loaded from the old field remains
an independent live loan. `library/pin_box.lim` defines the `#generate #pin-box`
generator, which takes exactly the named options `type`, `allocator`, `name`,
and `destroy`. `allocator` is a literal bundle root exposing `::State`,
`::Error`, byte-pointer `::Allocation`, safe `::allocate`, and unsafe
`::deallocate`. Its private typed adapter converts the byte pointers.
It generates an opaque named linear heap-owner type and create, shared-borrow,
mutable-borrow, and destroy functions. Its borrow functions return native
`#pin-ref` and `#pin-ref-mut` values. `examples/pin_box.lim` demonstrates
moving a handle while a view stays live. For an owner `Box`, generated symbols
include `Box::CreateResult`, `Box::created`, `Box::allocation-failed`, and
`Box::create` / `Box::borrow` / `Box::borrow-mut` / `Box::destroy`.

`library/pin_rc.lim` defines `#generate #pin-rc` with the same named options and
allocator bundle convention, and generates named linear reference-counted owners
with create, clone, shared-borrow, mutable-borrow, and destroy functions. This Rc
is single-threaded and is neither `Send` nor `Sync`; it has no weak-reference
handles. Mutable borrowing is available only while the handle is the unique
strong owner. Destroy every borrowed view before destroying a handle, because
the final handle destruction runs the pointee destructor in place and releases
the allocation. For an owner `Shared`, generated symbols include
`Shared::Allocation`, `Shared::CreateResult`, `Shared::MutResult`, and
`Shared::create` / `Shared::clone` / `Shared::borrow` / `Shared::borrow-mut` /
`Shared::destroy`; enum cases include `Shared::unique` and `Shared::Shared`.

For an owner named `PinnedFrameRc`, a private adapter converts the bundle's
`(#ptr-mut #u8)` success payload to a pointer to the generated
`PinnedFrameRc::Allocation` control block. The generated functions pass that
block's size and alignment to the allocator and deallocator. Both Box and Rc
request only allocate and deallocate adapters; their bundles may omit grow.
Destruction hooks are explicit safe functions taking
`(: allocator (#ref Root::State) : pin (#pin-ref-mut Element))` and must
perform explicit in-place cleanup. `examples/pinned_box_async.lim` and
`examples/pinned_rc_async.lim` poll generated futures through these native
pinned references, including after moving the owning handle.

An async function can initialize an owner containing an external reference
after an await and retain it across later suspension. Its source remains
borrowed through Pending; Ready or explicit state-specific cancellation must
consume the owner before the source can be modified. Structural reference
tracking includes references inside nested owning pins, not just inline
fields. `examples/async_heap_reference.lim` demonstrates this case. It is not
a frame-local self-reference: general delayed frame-owner initialization and
named pinned poll-handle recycling remain separate checked-analysis work.

`#pin-read` and `#pin-write` are lower-level unsafe operations for compiler-
generated pinned state machines. They access aggregate referents at their
existing storage address. A read can duplicate a linear value, and a write can
invalidate references derived from the pinned value; callers must prove
exclusive access, preserve any displaced ownership they need, and ensure no
derived references remain. Ordinary code should use safe field operations
instead; safe code cannot replace a pinned referent.

For a pinned handle proven to address one whole owned local value, the
compiler tracks a linear `#pin-read` as a move: the original value's cleanup
obligation is satisfied, and repeated loads, alias reads, and reborrows of
that uninitialized storage are rejected. A matching `#pin-write` requires
prior consumption before replacing a linear value and restores its cleanup
obligation. The loaded value keeps its own retained reference slots, not the
container address. Moving a reference-bearing holder transfers its loans;
copying one retains both sets until the corresponding values are released.
See `examples/pinned_local_move.lim` for local move/restoration and returning
a loaded reference-bearing value from a branch-local holder.

For `#deref-set` and unsafe `#pin-write`, a destination proven to be one whole
owned local value retains the RHS's reference fields and their original
referent loans. Replacing a holder releases its previous stored loans; moving
an exclusive-reference holder transfers its loans and keeps derived-reference
parents suspended until the restored holder is consumed. Shared copies keep
their respective loans. A local reference cannot be stored in external storage
or survive its referent's scope, even when the write is indirect. See
`examples/borrowed_variant.lim` and `examples/pinned_holder_restore.lim`.
This whole-local registration rule does not enable projected, ambiguous,
parameter, global, or lifetime-only destinations.

Whole ordinary `#deref` loads from borrowed parameters preserve the retained
reference fields of the loaded value. Each field remains tied to its original
input slot through function returns and caller substitution, rather than to
the address of the container. A shared container cannot grant exclusive
access through a stored mutable reference. See `examples/borrowed_whole_load.lim`.
Parameter `#pin-read` loads preserve those retained value slots as well;
see `examples/pinned_parameter_load.lim`. This provenance rule does not
supply a complete parameter move/restore contract or prove variant-conditioned
async frame accesses. The operation remains unsafe.

This local rule does not establish complete contracts for parameter-loaded
frames, projected/ambiguous storage, or lifetime-anchored raw pointers. Those
unsafe protocols still require the caller's guarantees; full referent and
variant-conditioned async ownership analysis remains under development.

`#pin-set-field` is the checked field-wise operation for scalar/fieldless-enum
and shared-reference struct fields. It writes only that field, so a state tag
can change independently and an immutable reference can be established after
the struct is pinned without moving the referent. The borrow checker
tracks the stored reference as part of the owner: it rejects overlapping field
replacement and keeps the owner pinned and borrowed until the reference field
is cleared. This operation is not a way to make a movable async frame
self-referential; generated frames still need stable storage slots and
cancellation-aware internal-loan handling.

Ordinary calls also check statically resolved internal owner loans against
the callee's writes and destructive accesses, including nested calls and
paths that trap instead of returning. A disjoint field update is allowed;
overwriting the internally borrowed field reports `E4100` at the caller's
argument and labels the callee access. Checked enum tests and assertions
retain entry-tag constraints for conditional initialization, rather than
treating a tag written by the initializer as an incoming constructor.
See `examples/pinned_self_reference.lim` for an ordinary-call example.
This additional rejection check is not permission to reborrow a whole
parent while its children remain live. Context-sensitive exclusive loans
in conditional enum payloads still require incoming/fresh-family correlation
and remain subject to the existing conservative borrow checks.

`#asm` embeds target assembler at an expression site. Its form is
`(#asm ResultType ((register value) ...) "instructions")`: each value is
evaluated and loaded into its named 64-bit general-purpose register, and the
result is read from `rax` (or discarded for `()`). The current backend uses
GNU Intel-syntax x86-64 assembly. `#asm` is unsafe and must be inside `#unsafe`.
The assembly must leave `rsp` and `rbp` unchanged, must not return or jump out
of the surrounding function, and must obey the platform ABI for any registers
it changes; the compiler preserves callee-saved GPRs but cannot verify raw
instructions. Syscall numbers and register conventions are OS/architecture
specific, so select implementations with `#cfg` rather than assuming one
assembly sequence is portable.

For Linux x86-64 kernel entry without hand-written register shuffling, unsafe
`#linux-syscall` takes an explicit result type, syscall number, and up to six
arguments. It emits the `syscall` instruction directly; no libc wrapper is
called. Integer arguments are passed as machine words, raw pointers as-is, and
Lim references have their internal low-bit tag removed before being passed as
addresses. Raw syscall failures are returned as negative errno values. The
primitive is deliberately unsafe because the kernel interprets syscall
numbers, flags, descriptors, and pointer/length pairs according to Linux ABI
contracts.

```lisp library
(#fn process-id () #i64
  (#return (#unsafe (#linux-syscall #i64 39usize ()))))
```

`library/linux_x86_64.lim` builds byte input/output, process helpers, and
file-descriptor operations (`openat`, positional and sequential IO, metadata,
directory queries, resource limits and usage, advice, locking, allocation,
descriptor duplication, anonymous files, wall-clock/process-time queries, and
private futex operations) on this primitive. The low-level
pointer wrappers do not validate kernel buffer ranges; callers must uphold
pointer validity and length preconditions. These wrappers are `#unsafe-fn`:
the compiler requires `#unsafe-call` inside `#unsafe`, even for null pointers
or zero-length buffers. Safe reference-bounded helpers use `#call`. For example,
this unsafe forwarding function passes its caller's buffer contract through
to the low-level read wrapper:

```lisp library
(#alias linux-read = ../library/linux_x86_64.lim::linux-read)
(#unsafe-fn read-buffer ((fd #i64) (destination (#ptr-mut #u8)) (count #usize)) #i64
  (#return (#unsafe
    (#unsafe-call linux-read (: fd fd : destination destination : count count)))))
```

The raw syscall operation remains available for the rest
of the Linux syscall table. `examples/linux_syscalls.lim` and
`examples/linux_sockets.lim` exercise direct socket syscalls, while
`examples/linux_socket_listener.lim` binds an automatically named abstract
UNIX socket, listens, connects, and exchanges bytes through both `accept` and
`accept4`. It checks returned peer addresses, nonblocking and close-on-exec
flags, empty accept queues, invalid arguments, and exact stdout;
`examples/linux_socket_messages.lim` transfers datagrams with `sendmsg`,
`recvmsg`, `sendmmsg`, and `recvmmsg`, checks each batched message length,
and verifies nonblocking empty-queue errors and exact received output;
`examples/linux_select.lim` checks `select` and raw `pselect6` readiness
before and after draining an `eventfd`, validates the kernel signal-mask
argument size, and exercises legacy epoll/inotify descriptor creation;
`examples/linux_shared_memory.lim` creates a private System V segment with
`shmget`, checks shared bytes through writable and read-only `shmat`
attachments, marks it for removal with `shmctl`, and verifies destruction
after the last `shmdt`;
`examples/linux_message_queue.lim` creates a private queue with `msgget`,
sends typed messages with `msgsnd`, verifies `msgrcv` type selection and
buffer-size/empty-queue errors, removes the queue with `msgctl`, and checks
the received payloads through exact stdout;
`examples/linux_semaphores.lim` creates and removes a private semaphore set
with `semget`/`semctl`, verifies atomic `semop` failure without partial
changes, and exercises successful and expired `semtimedop` calls;
`examples/linux_posix_mq.lim` exercises `mq_open`, `mq_unlink`,
`mq_timedsend`, `mq_timedreceive`, `mq_getsetattr`, and `mq_notify`.
It immediately unlinks its unique queue, verifies priority ordering,
oversized-message rejection, queue counts, expired deadlines, nonblocking
mode changes, and exclusive `SIGEV_NONE` notification registration. It also
blocks SIGUSR1 and verifies actual `SIGEV_SIGNAL` delivery, the `SI_MESGQ`
code, sender PID/UID, and notification payload, then checks one-shot delivery,
rearming, cancellation, and restoration of the original signal mask. Exact
stdout checks both the received messages and the notification payload; see
[mq_notify(3)](https://man7.org/linux/man-pages/man3/mq_notify.3.html).
Raw queue names omit the leading
slash required by libc, deadlines are absolute CLOCK_REALTIME values, and
descriptors close with `linux-close`; see
[mq_open(3)](https://man7.org/linux/man-pages/man3/mq_open.3.html).
`examples/linux_robust_futex.lim` registers and queries a robust-futex list,
restores the original thread registration, and checks invalid sizes, missing
threads, and invalid output pointers. A child then exits while owning a
futex in shared memory; the parent verifies that Linux clears its owner ID
and sets `FUTEX_OWNER_DIED`. A second owner is held behind a pipe while a
waiter blocks directly on its robust futex. A second run blocks on a staging
word and moves that waiter to the robust futex with `FUTEX_CMP_REQUEUE` before
the owner exits. The controller checks each child's `/proc/PID/wchan` for a
futex wait before releasing the owner, rather than guessing readiness with a
sleep. This test requires readable procfs wait
symbols; see [proc_pid_wchan(5)](https://man7.org/linux/man-pages/man5/proc_pid_wchan.5.html).
The waiter requires a successful wake and verifies both owner-death
and waiters bits before printing `W`; the parent reaps both children and
prints `R`. The requeue wrapper uses an explicit `#u32` count in the fourth
syscall argument, rather than pretending it is a timeout pointer. The example
tests an empty requeue, an expected-value mismatch, and successful blocked
requeue cleanup on the supported host. See
[FUTEX_CMP_REQUEUE(2)](https://man7.org/linux/man-pages/man2/FUTEX_CMP_REQUEUE.2const.html).
These raw registrations require
the caller to keep the list storage valid until replacement or thread exit;
see [get_robust_list(2)](https://man7.org/linux/man-pages/man2/get_robust_list.2.html).
`examples/linux_process_vectors.lim` transfers bytes within its own address
space using `process_vm_readv` and `process_vm_writev`, then through a pipe
using `vmsplice`, checking byte counts, error paths, and exact payload output;
`examples/linux_mseal.lim` exercises `linux-mseal`, whose flags are `#usize`
(Linux `unsigned long`). It verifies invalid inputs, page rounding,
idempotence, and rejected permission changes, discard, and unmapping while
preserving the payload. Sealed mappings cannot be unsealed; this example's
page is released only when its process exits. See the
[kernel mseal documentation](https://docs.kernel.org/userspace-api/mseal.html).
`examples/linux_secret_memory.lim` exercises `linux-memfd-secret` with `#u32`
flags. It verifies `O_CLOEXEC` (524288, not `MFD_CLOEXEC`), initial sizing,
rejected resizing, shared mappings, and rejected `process_vm_readv` access.
Mappings remain usable after descriptor close. The example deliberately
copies its synthetic test bytes into ordinary memory for stdout, then unmaps
all storage. Kernel secret-memory support and sufficient locked-memory
allowance are required; unsupported hosts do not count as passing. See
[memfd_secret(2)](https://man7.org/linux/man-pages/man2/memfd_secret.2.html).
`examples/linux_io_uring.lim` uses `linux-io-uring-setup`,
`linux-io-uring-enter`, and `linux-io-uring-register` without liburing.
The wrappers expose raw kernel layouts and results: callers must keep rings,
registered resources, and request buffers valid until operations finish.
The example follows kernel-provided offsets, exercises single/separate ring
mappings, and uses explicit x86-64 fences when publishing or consuming entries.
It repeatedly writes and reads a registered anonymous file after closing its
ordinary descriptor, checks completion cookies/results/flags and reused slots,
and verifies invalid setup flags, enter flags, opcodes, and file indices.
All resources are released after completion. Exact stdout comes from read
buffers. Kernel io_uring support and permission are required; no skip is counted
as success. See [io_uring_setup(2)](https://man7.org/linux/man-pages/man2/io_uring_setup.2.html)
and the [kernel ABI header](https://github.com/torvalds/linux/blob/master/include/uapi/linux/io_uring.h).
`examples/linux_aio.lim` exercises native `io_setup`, `io_submit`,
`io_getevents`, `io_pgetevents`, `io_cancel`, and `io_destroy` without libaio.
It writes and reads a memfd, checks completion cookies, the request pointer,
byte counts, empty-queue behavior, and invalid requests, then prints the read
payload. It also cancels a pending eventfd poll, drains its completion,
rejects a second cancellation, and checks the packed signal-mask argument
to `io_pgetevents`, including mask restoration and invalid sizes.
Modern Linux returns `-EINPROGRESS` when cancellation is accepted and posts
the completion to the queue; the legacy `io_cancel` output pointer is unused.
An accepted cancellation does not itself permit freeing request storage;
drain its completion first. This follows the
[kernel AIO implementation](https://github.com/torvalds/linux/blob/master/fs/aio.c).
These raw APIs require a
zero-initialized context output for setup and native iocb/io_event layouts;
request and data storage must remain valid until completion. See
[io_submit(2)](https://man7.org/linux/man-pages/man2/io_submit.2.html).
`examples/linux_process_control.lim` exercises `prctl` thread-name changes
and restoration, `arch_prctl` FS/GS queries, and `capget`/`capset` capability
version negotiation and unchanged-set round trips, with exact name output;
`examples/linux_identity.lim` exercises `setuid`, `setgid`, `setreuid`,
`setregid`, `setresuid`, `setresgid`, `setfsuid`, and `setfsgid` by reapplying
current IDs or using unchanged-ID sentinels. It compares all real, effective,
saved, and filesystem IDs, checks invalid-ID errors, and prints `U` only after
the checks pass. Run this example as an ordinary, non-setuid executable.
These direct credential syscalls affect the calling kernel thread, unlike
libc's process-wide credential synchronization. Filesystem-ID setters return
the previous ID on both success and failure, so callers must query again to
verify the result; see [setresuid(2)](https://man7.org/linux/man-pages/man2/setresuid.2.html)
and [setfsuid(2)](https://man7.org/linux/man-pages/man2/setfsuid.2.html).
`examples/linux_fifo.lim` exercises `mknod`/`mknodat` FIFO creation and
`fchmodat2` path and `AT_EMPTY_PATH` permission updates, verifies metadata
and errors, unlinks both FIFOs, and checks bytes through an open FIFO;
`examples/linux_ioctl.lim` checks pipe unread-byte counts with `FIONREAD`,
sets nonblocking mode with `FIONBIO`, verifies errors, and prints the exact
transferred bytes. `linux-ioctl` takes a `#u32` request and a `#usize` argument
word, which may encode a pointer; callers must supply the request-specific
buffer layout and lifetime. Request encodings are architecture-specific;
see [ioctl(2)](https://man7.org/linux/man-pages/man2/ioctl.2.html).
`examples/linux_zero_copy.lim` checks `sendfile`, `tee`, and `splice` payloads
and offsets; `examples/linux_directory.lim` checks both `getdents64` and
legacy `getdents`, including record boundaries, name termination, file/link
names, supported type tags (allowing `DT_UNKNOWN`), EOF, and errors. It prints
`D` after the legacy enumeration checks and also exercises cwd queries.
Legacy x86-64 records put the name at byte 18 and the type in their final
byte, unlike `getdents64`; see
[getdents(2)](https://man7.org/linux/man-pages/man2/getdents.2.html).
`examples/linux_resources.lim` checks usage, limits, and umask restoration;
`examples/linux_signals.lim` checks signal action and mask querying,
installation, and restoration without delivering a signal;
`examples/linux_signal_stack.lim` installs, queries, and restores a 64-KiB
alternate signal stack, checks invalid flags and undersized-stack errors,
arms and cancels an alarm, and tests `tkill` with signal zero and an invalid
signal. It prints `S` after these checks; it does not test execution of a
handler on the alternate stack. Stack storage must remain mapped while
registered; see [sigaltstack(2)](https://man7.org/linux/man-pages/man2/sigaltstack.2.html).
`examples/linux_pkeys.lim` requires Linux x86-64 PKU/OSPKE support. It tests
`pkey_alloc`, `pkey_mprotect`, and `pkey_free`, checks PKRU rights, and verifies
that a child's forbidden write produces SIGSEGV with core dumps disabled.
The parent restores key zero before freeing the allocated key, checks
invalid flags and stale-key errors, and prints `K` from the restored mapping.
On machines without protection-key support allocation can return `-ENOSPC`;
this hardware-specific test requires successful allocation rather than
silently counting an unsupported path as coverage. See
[pkey_alloc(2)](https://man7.org/linux/man-pages/man2/pkey_alloc.2.html).
`examples/linux_program_break.lim` queries and reapplies the current
personality, grows the program break by two pages, checks memory access,
rejects impossible growth, and restores the original break. It prints `H`
from the allocated region before releasing it. `linux-brk` returns a `#usize`
address: the new break on success or unchanged break on failure, not a
negative errno or libc's zero/-1 result. Its unsupported-target fallback is
zero. Program-break ownership must be coordinated across allocators/threads;
this example is standalone and single-threaded. See
[brk(2)](https://man7.org/linux/man-pages/man2/brk.2.html).
`examples/linux_signal_receive.lim` blocks SIGUSR1, sends it to itself,
consumes it with `signalfd`, `signalfd4`, and `rt_sigtimedwait`, checks
signal records and empty-queue errors, and restores the original mask.
It also sends to itself with `rt_sigqueueinfo` and `rt_tgsigqueueinfo`,
verifies SI_QUEUE, sender fields, and full 64-bit payloads, and checks invalid
signals and null input records. Raw `siginfo_t` records are 128 bytes on the
supported target; sender PID/UID fields are supplied by the caller, not
authenticated credentials. See
[rt_sigqueueinfo(2)](https://man7.org/linux/man-pages/man2/rt_sigqueueinfo.2.html).
`examples/linux_timers.lim` checks POSIX timer creation, arming, querying,
deletion, zero overruns on a newly created timer, and invalid-handle behavior
without signal delivery;
`examples/linux_interval_timers.lim` checks arming, querying, and restoring
the process's legacy interval timer state;
`examples/linux_inotify.lim` checks create/delete event records and watch
cleanup using a private working directory;
`examples/linux_wait4.lim` forks and reaps a child and validates the kernel's
encoded exit status. The paired `tests/fixtures/exec_driver.lim` and
`exec_target.lim` programs exercise `execve`, relative `execveat`, and
`execveat` with `AT_EMPTY_PATH`. Their Rust harness compiles the target into
a private working directory, checks exact output from all three replacement
images, and verifies child exit statuses and failed-execution errors.
Both wrappers take explicit null-terminated arrays of string pointers for
arguments and environment, and NUL-terminated path strings. Successful calls
replace the process image and never return; failures return raw negative
errno values. Descriptor-based execution follows the Linux-specific
[execveat rules](https://man7.org/linux/man-pages/man2/execveat.2.html).
`examples/linux_waitid.lim` checks `setsid` and `setpgid`
in isolated children, exits them through `exit`/`exit_group`, observes their
exit records with `WNOWAIT`, and reaps them with `waitid`;
`examples/linux_affinity.lim` round-trips the process's
allowed-CPU mask and checks the affinity state is unchanged;
`examples/linux_copy_file_range.lim` validates explicit-offset copying between
anonymous files, including the copied bytes and updated offsets;
`examples/linux_scheduler_queries.lim` checks scheduler parameters, policy
priority bounds, invalid-policy behavior, and the current nice value;
`examples/linux_scheduler_updates.lim` reapplies the current scheduling
parameters, policy, attributes, nice value, and I/O priority through
`sched_setparam`, `sched_setscheduler`, `sched_setattr`, `setpriority`, and
`ioprio_set`, then verifies queried state and invalid-argument errors;
`examples/linux_renameat2.lim` checks no-replace collision errors, successful
renaming, and old/new path visibility in a scratch working directory;
`examples/linux_statx.lim` checks anonymous-file metadata through
`AT_EMPTY_PATH`, including the returned size mask and exact file size;
`examples/linux_openat2.lim` exercises `RESOLVE_BENEATH`, missing-path errors,
and rejection of unknown resolution flags in a scratch cwd;
`examples/linux_xattrs.lim` exercises descriptor-based extended-attribute
creation, listing, retrieval, removal, and the missing-attribute error on a
fresh memfd.
`tests/io_examples.rs` checks exact program exit/output behavior,
syscall argument counts zero through six, piped IO, local socket payloads, and
kernel error results.

## Building and running

For the standard library's measured syscall breadth, test commands, and
remaining safety/coverage gaps, see [syscall coverage](syscall-coverage.md).

The repository contains a Nix flake with the Rust toolchain:

```sh
nix develop
nix develop --command cargo test --all-targets
nix develop --command cargo doc --no-deps --open
```

Compile Lim source directly to a native executable from the Nix development
shell. The backend emits inspectable assembly; its x86-64 encoder and ELF
writer produce the executable without external build tools.
By default, the output is placed beside the input and uses
the input filename without its extension. `-o` selects a different path:

```sh
nix develop --command cargo run -- examples/fibonacci.lim
nix develop --command cargo run -- examples/fibonacci.lim -o /tmp/fibonacci
/tmp/fibonacci
echo $? # 55 for the Fibonacci example
nix develop --command cargo run -- --check-examples examples
nix develop --command cargo run -- examples/fibonacci.lim --target x86_64-sysv
nix develop --command cargo run -- --format examples/fibonacci.lim
nix develop --command cargo run -- fmt examples/modules/main.lim
```

`--format` retains comments in their surrounding syntax, including nested
forms and generator templates. Formatting is idempotent.

The formatter keeps binding names beside their explicit types and callees
beside `#call` or `#unsafe-call`. Long colon argument lists put each named
group on its own line; empty argument lists use `()`. Short unsafe expressions
and single-expression cases stay compact, while multi-expression case bodies
are indented as sequences. Function and generator declarations are separated
with blank lines.

Formatting uses Lisp-style headers and two-space body indentation. Function
signatures stay together, short nested expressions stay inline, and closing
parentheses follow the final expression. A `#for` keeps initialization,
comparison, and mutation together, followed by its indented body:

```lisp syntax
(#for (#let-mut i #u64 0) (#u64::lt (#clone i) 10) (#set i (#u64::add-wrap (#clone i) 1))
  (#assert (#u64::lt (#clone i) 10)))
```

Ordinary expressions exceeding a target width of 100 columns wrap between
arguments. Form headers may exceed that width. Comments and parser shorthand
retain their source spelling.

`lim fmt INPUT` formats the file and its transitive explicit file dependencies
within the same library boundary. Dependencies across a boundary are skipped. The read-only `--format`
form remains available to print one formatted file or write it to a separate
output path.

Native compilation carries an explicit target description. The supported
target/ABI matrix currently has one entry:

| Target spellings | OS/object format | CPU ABI | Backend/linker |
| --- | --- | --- | --- |
| `x86_64-sysv`, `x86_64-unknown-linux-gnu` | Linux ELF | x86-64 System V | native x86-64 assembly, internal instruction encoder and ELF linker |

The linker reads ELF object symbol tables directly. When all objects have
no unresolved symbols and no libraries were explicitly requested, it links
statically without libc, pthread, or a dynamic interpreter. This includes
programs importing the direct-syscall Linux library. Unused external
declarations alone do not require a runtime. Inline assembly's foreign
references are detected from encoded relocations. References between supplied
objects are resolved before considering shared libraries. If unresolved
references remain, or libraries were explicitly requested, the compiler
writes the interpreter, dynamic symbol/string tables, GOT relocations, and
shared-library dependencies itself. Supplied ELF64 objects may contain code,
read-only data, writable data, and BSS. Source constants and object-file
read-only sections occupy a separate readable, non-executable ELF segment;
code is read-execute and mutable data is read-write. Unsupported `#asm` forms
or ELF relocations are diagnosed rather than passed to an external tool. All 318
current examples build with external build tools absent from `PATH`.
The object linker currently accepts x86-64 `R_X86_64_64`, `PC32`, `PLT32`,
`32`, `32S`, `GOTPCREL`, `GOTPCRELX`, and `REX_GOTPCRELX` relocations. Direct
unresolved `PC32` references to sized data symbols in shared libraries use
`R_X86_64_COPY` relocations. TLS data and unsupported relocation forms are
rejected with a linker diagnostic.
Absolute shared-library symbol addresses stored in writable object sections
use dynamic `R_X86_64_64` relocations. PC-relative GOT and COPY references
may also originate in writable sections. An undefined weak object symbol with
no linked object definition resolves to zero; it does not force a shared
library dependency. ELF forms outside this supported subset are rejected.
The dynamic loader path is
read from the compiler's own ELF interpreter when available, with
`LIM_DYNAMIC_LINKER` as an absolute-path override and the conventional Linux
x86-64 loader path as a fallback. Shared libraries are located using the
loader's directory, target library search paths, and standard Linux paths;
their directories are recorded as an ELF runpath.
After `main` returns, the entry stub calls Linux `exit_group` with its result,
not thread-only `exit`, so outstanding kernel workers cannot change the
process's final status. Explicit `linux-exit` remains thread-only. See
[exit_group(2)](https://man7.org/linux/man-pages/man2/exit_group.2.html).

All other target names (including other operating systems using the System V
calling convention) are rejected. Host selection requires both Linux and
x86-64. The Rust API exposes
`TargetDescription` and `generate_assembly_for_target`; the existing
`generate_assembly` API selects the supported host target.

`--check-examples` recursively parses, type-checks, borrow-checks, and lowers
every `.lim` file under the selected directory. It reports each source file
individually and returns failure if any example fails.

`--emit-asm INPUT OUTPUT` remains available to inspect backend output.
`--stack-usage INPUT` compiles the project through code generation, then
reports generated-code stack bounds without invoking the native linker. It
accepts `--target`, `--cfg`, and `--module-path` options just like compilation.
Every generated `#generate` expansion is materialized as a readable, content-addressed
`.lim` entry under `.lim/generated/`, regardless of whether it uses a built-in or a
user-defined generator. The digest is derived from the normalized invocation,
compiler version, target, complete loaded import forms, and compiler cfg
values. A neighboring key file verifies the full key before a cache hit, so a
digest collision cannot return unrelated generated source. A checksum over the
key and generated bytes detects edited or damaged entries; invalid entries are
regenerated. Checksums detect accidental changes and are not an authenticity
mechanism against someone who can edit both data and metadata. User-generator
evaluation also keeps its lower-level syntax cache in the same directory with
an integrity checksum. Cache records are staged under unique names and
published atomically; the inspectable-source checksum is published last as a
consistency marker. An interrupted or concurrent write is treated as a cache
miss and regenerated. Staging files older than one hour are removed when the
cache is next read; newer temporary files may belong to active compiler
processes and are left alone.
There are no numbered generated-source files; deleting `.lim/` only causes
generators to run and materialized entries to be recreated.

## Compile-time configuration

`#cfg-if` includes only the selected top-level forms. Its condition is built
from `#cfg-is`, `#cfg-not`, `#cfg-and`, and `#cfg-or`; branches contain forms
directly, with an optional final `#cfg-else` branch:

```lisp library
(#cfg-if (#cfg-and (#cfg-is #platform linux) (#cfg-is #feature fast))
  (#fn selected () #u64 (#return 1u64))
  (#cfg-else
    (#fn selected () #u64 (#return 0u64))))
```

`#platform` and `#os` are populated automatically from the compiler host OS
(`linux`, `macos`, or `windows`, where applicable); `#arch` is the target
architecture (such as `x86_64`), and `#target` is its canonical target triple
(currently `x86_64-unknown-linux-gnu` for the supported backend). Other keys
must be passed with `--cfg KEY=VALUE`; for example, `--cfg feature=fast`.
Command-line settings override automatic values. Configured values are literal
symbols or strings in `#cfg-is`. Excluded forms are removed before imports,
generators, name checks, and type checking are processed.

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

### Literal syntax bundles

Use `#syntax` to declare an immutable list of literal syntax, and explicitly
splice its elements into another list with `#syntax-splice`. Neither form
evaluates values or infers types. An await protocol can be named once:

```lisp syntax
(#syntax StepAwait (#u64 Step StepPoll.StepPending StepPoll.StepReady step-poll))
(#await StepAwait step)
```

The second form expands to `(#await #u64 Step StepPending StepReady step-poll
step)` before async lowering. It is only valid inside an async function.
The longer `(#await (#syntax-splice StepAwait) step)` spelling is equivalent.
Both async function generators export a bundle automatically. Supply one
explicit protocol name instead of listing all five generated names:

```lisp syntax
(#generate #async-fn (: protocol WorkAwait : waker LocalWaker
  : function (#fn work (: offset #u64) #u64
    (#return (#await StepAwait (Waiting offset))))))
; In another async function:
(#await WorkAwait (#call work (($ offset))))
```

For `work`, the generated names are `Work::Task`, `Work::Poll`,
`Work::Pending`, `Work::Ready`, and `Work::poll`. The exported declaration is
`(#syntax WorkAwait (#u64 Work::Task Work::Pending Work::Ready Work::poll))`.
`#generate #async-fn-pinned` instead generates `Work::Frame` and exports
`(#syntax WorkAwait (#u64 (#pin-ref-mut Work::Frame) Work::Pending Work::Ready Work::poll))`.
Callers must pin a frame explicitly before awaiting that protocol.
Both generated task and frame structs are `#opaque`: callers use their
constructor, poll and cleanup functions, not their internal fields. This
protects the initialization invariants used by generated unsafe accesses.
Pinning alone guarantees address stability, not initialization or alias safety.
Generated task, result, variant, and poll names come from the source function
name. Supply `: protocol` to select the exported bundle name.
Protocols are collected after imports, generators and cfg selection, before
await expansion, so functions can refer forward to one another's protocols.
Duplicate bundles and declaration collisions are rejected. The bundle appears
in the same inspectable, hash-cached generated file as the function's code.
This shorthand supplies types explicitly; it adds neither type inference nor
implicit pinning, allocation or cancellation.

On the graph route, pinned functions can request post-terminal access to
reference-free Copy parameters with `: access (: amount AmountAccess)`.
This emits `AmountAccess::read` and `AmountAccess::replace` ordinary functions
with pinned frame receivers; the latter also takes a named `value` argument.
They assert completion/cancellation and cleared loans before accessing the
same stationary storage. They do not restart the future, infer lifetimes, or
allow moving its frame. Without an access request no accessor bodies are
generated. See [parameter access](async-graph-production.md#post-terminal-parameter-access).

The default graph route can also be selected with `--cfg async-lowering=graph`.
It uses the same await protocol names, independently checked ordinary generated code, and
a source-named cleanup record instead of the legacy per-state cancellation
interface. Warm hash hits skip emission. Unsupported graph cases fail closed;
there is no publicly selectable legacy route or fallback. See
[graph async lowering](async-graph-production.md) for the
cleanup contract, supported guards/scoped borrows, and current limitations.

Bundles can also supply function parameters or named call arguments. Definitions
are top-level, may refer forward to other bundles, and may contain nested
splices. Names must be unique across declarations; cycles, unknown names,
malformed definitions, and splices outside a surrounding list are errors.
File dependencies and cfg selection happen first; aliases resolve bundle names
and referenced identifiers to their defining files. Quoted syntax and generator templates stay
literal until emitted. Generated bundle declarations are supported, and ordinary
type, borrow, and linearity checking still applies to their expanded code.

### Generator declarations

Generators are compile-time syntax functions. Their parameters receive the
invocation arguments literally; generator values are immutable syntax nodes:
symbols, literals, or lists. A generator returns a list of top-level forms,
which are expanded before ordinary Lim parsing and type checking.

Language and standard-library generator names are reserved and start with
`#`: for example, `(#generate #optional (: type #u64 : name MaybeU64))`, `#generate #cell`,
and `#generate #utf8-view`. User generators use ordinary names, such as `#generate make-record`.
The `#generate` keyword invokes generation/import; a generator name's `#`
identifies a reserved name, not a different execution or caching mechanism. Standard-library generators
remain ordinary immutable Lim declarations and must be imported before use.
Their shipped declarations cannot be redefined. All `#`-prefixed names are
unavailable for user declarations, including declarations emitted by generators.
There are no compatibility aliases for the old unprefixed builtin spellings;
unprefixed names belong to users, including names such as `optional` or `cell`.

Capabilities are explicit declarations for generator requirements. A concrete
type opts in with `#capability`, and a generator parameter can require one:

```lisp library
(#fn u64-less ((left (#ref #u64)) (right (#ref #u64))) #bool
  (#return (#u64::lt (#deref left) (#deref right))))
(#capability sortable #u64
  ((u64-less ((#ref #u64) (#ref #u64)) #bool)))
(#gn make-sortable ((element sortable))
  `((#type Sortable ,element)))
(#generate make-sortable #u64)
```

The list after a generator's name is its parameter declaration list, not a
pattern match. A bare symbol such as `name` declares an ordinary literal-syntax
parameter. A pair such as `(element sortable)` declares one parameter that
requires a capability; it does not destructure the invocation argument.
All invocation arguments are literal syntax; there is no implicit registry
lookup or distributed syntax expansion.
This mirrors function signatures, where each nested pair declares one named
parameter and its type.

```text
parameters := (parameter ...)
parameter  := name | (name capability-name ...)
```

For example, `(#gn alias (name target) ...)` has two literal-syntax
parameters. `(#gn sortable ((element sortable)) ...)` has one parameter
named `element` requiring the `sortable` capability. Likewise, `((left right))`
declares one parameter named `left` with a capability annotation `right`; it
never binds two names. Nested lists in the name or annotation position are
rejected as malformed declarations. No implicit destructuring takes place; use
`#gn-first`, `#gn-rest`, or `#gn-for-each` inside the generator body to inspect
literal list arguments.

Each capability declaration lists concrete free-standing operations and their
full argument/return types. Before any generator runs, the compiler verifies
that every named function exists and exactly matches its declared signature.
A missing capability reports the parameter, capability, and concrete type;
there are no implicit structural or interface requirements hidden inside a
generator. Capability definitions are part of the generated-code cache key, so
changing an operation contract cannot reuse expansions made under an older
contract.

```lisp library
(#gn aliases (pairs)
  (#gn-for-each pair pairs
    (#gn-list
      (#gn-symbol "#type")
      (#gn-first pair)
      (#gn-first (#gn-rest pair)))))

(#generate aliases ((Byte #u8) (Word #u16)))
```

Generator helpers can be declared with `#gn-fn` and called with `#gn-call`.
They take and return only syntax values (symbols, literals, or lists), so
predicate booleans remain internal to conditionals. Helpers may call other
helpers, but direct or indirect recursive calls are rejected. For example:

```lisp library
(#gn-fn make-alias (name target)
  `(#type ,name ,target))

(#gn aliases (pairs)
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

`#gn-gensym` evaluates its string hint and returns a fresh syntax symbol. The
hint must parse as exactly one non-keyword ordinary identifier. Generated
symbols remain ordinary syntax-symbol values, so they can be reused in the
generated declaration and its references; they do not introduce a new syntax
datatype. Each evaluation is fresh within its deterministic invocation scope.
Use a `#gn-fn` helper to pass one generated symbol through all places that need
to refer to the same binding. Identical generator invocations still deduplicate,
and cold or warm cache runs produce the same output.

Names beginning with the compiler-owned `lim.gensym.` prefix are reserved.
Source code cannot name them, and `#gn-symbol` and `#gn-symbol-append` cannot
forge or alter them. This facility does not automatically make ordinary
generated symbols hygienic: public API names passed to a generator remain
literal names, and ordinary generated identifiers still undergo the usual
duplicate-name, parsing, type, and borrow checks. Source no-shadowing rules are
unchanged, and generated output is validated as well. See `examples/gensym.lim`
for a helper that reuses one fresh local name in a generated function.

The generator builtins are `#gn-gensym`, `#gn-if`, `#gn-equal`, `#gn-symbol?`,
`#gn-list?`, `#gn-symbol`, `#gn-list`, `#gn-length`, `#gn-first`, `#gn-rest`,
`#gn-get`, `#gn-symbol-append`, `#gn-variant`, `#gn-for-each`, `#gn-call`, and `#gn-error`.
`#gn-get` looks up a literal key in a named syntax list without introducing a
new dictionary type. `#gn-symbol-append` constructs concrete API identifiers by
joining the base and suffix with `::`, for example `Frame` and `"read"` become
`Frame::read`. Nested calls produce names such as `Frame::State::Value`.
`#gn-variant` joins an enum type and uppercase variant suffix with `.`, for
example `(#gn-variant State "Ready")` produces `State.Ready`.
These are ordinary identifiers, not namespaces or proof of generator provenance.
`#gn-for-each` is the only iteration construct; there are no general loops or
mutable generator values. `#gn-error`
fails expansion with the supplied message. Generators cannot perform IO or
call runtime functions. Recursive expansion is rejected. Repeating an
invocation with the same generator name and structurally identical literal
syntax arguments emits its output only once. Each compilation allows at most
200,000 generator evaluation steps, 128 nested expansions, and 1,000,000
generated syntax nodes; exceeding a limit is a compile-time error. A
`#gn-for-each` binding cannot shadow a generator parameter or an enclosing
iteration binding; sibling iteration forms have independent scopes. Unknown
`#gn-*` operations are reported as generator errors with invocation and
definition locations.

Ordinary generated identifiers are not hygienic. Pass intended public
declaration names as literal arguments; use `#gn-gensym` only for fresh
compiler-reserved local names, and explicitly pass each generated symbol to
every generated reference that must resolve to it. Different invocations can
use distinct public names while their internal generated locals remain fresh.

### Generator-to-generator contracts

Generators can require that public inputs were emitted by a particular
generator, without reading its output during expansion:

```lisp syntax
(#require-generated Work::Frame #async-fn-pinned
  (Work::Poll Work::Poll.Pending Work::Poll.Ready Work::poll))
```

The first identifier and optional companion identifiers must share one
invocation of the named generator. Requirements are checked after expansion,
so they may appear before the producer invocation. They neither schedule
generators nor inspect unfinished distributed enums. Ordinary typechecking
still checks every generated declaration and call.

The compiler records actual generation ancestry. Handwritten lookalikes or
unrelated generators cannot claim that origin. Wrappers retain both their own
origin and the nested producer's origin, including deduplicated invocations.
Cached output is recorded under the actual invocation just like fresh output;
source comments and generated properties do not grant provenance.

## Imports

Distributed enums collect variants from active imports and generator outputs.
Declare `(#distributed-enum Error ())` once, and add individual variants with
`(#enum-contribute Error (Failure #u32))`. After expansion, the compiler merges
identical variants by name, rejects conflicts, and compiles one ordinary enum.
See [collections and tasks](collections-and-tasks.md) for the full rules and
cooperative async generators. General distributed syntax is not supported.

Struct and enum declarations require a property list between the name and their
fields or variants. Use `()` when no properties are needed. The supported
properties are `#linear` and `#repr-c`:

```lisp syntax
(#struct FileHandle (#linear) ((descriptor #u64)))
(#enum Maybe (#repr-c) ((Maybe.Some #u64) Maybe.None))
(#struct NativeOwner (#linear #repr-c) ((handle (#ptr #u8))))
```

Aggregates become linear transitively when they own a linear field or, for an
enum, any linear payload in any variant. References do not make their
containing aggregate linear because they do not own their referents. Explicit
`#linear` forces a struct or enum to be linear even when all fields or
payloads are plain data. It does not change layout or Send/Sync. Generated
task state types use this property.

File references identify declarations directly, without copying source or
prepending prefixes. Aliases give those declarations explicit local spellings:

```lisp syntax
(#alias read = ./shared.lim::read)
(#alias Widget = //compat/lib.lim::Widget)
```

`./` paths resolve relative to the source containing the reference. `//` paths
resolve from the nearest `lim.project` ancestor of the principal source; when
there is no manifest, its directory is the project root. All dependencies use
that same root. `/` retains filesystem-absolute meaning. Rooted paths cannot
contain `..`; direct references do not search module-path lists. Files are loaded
once by canonical identity, and alias cycles and runtime recursion are rejected.

A directory containing `lib.lim` establishes a library permission boundary.
Each source belongs to its nearest boundary, including a separately compiled
white-box test. References within that library may name implementation files;
references from outside must target `lib.lim` and select an exported declaration.
Nested library directories establish independent boundaries. Canonical paths
prevent symlink and `..` privacy bypasses. `#unstable` explicitly bypasses the
entry-point/export restrictions for a selected declaration, not its struct fields.

Only `lib.lim` may contain `(#export Type function ...)`, listing the declarations
available outside the library. Other declarations remain library-internal.
Exporting a struct type does not export its representation: external code cannot
construct, read, write, borrow, or project its fields. Exporting an enum exposes
every variant for construction and matching; individual variants cannot appear
in `#export`. Every payload type must also be publicly accessible, including in
unused variants. Adding a variant changes the exhaustive matching contract.
An unexported enum remains private. To hide its representation, store it inside
an exported opaque struct and expose functions that operate on that struct;
see `examples/opaque_handle.lim` and `examples/opaque_handle/lib.lim`.
Exported function signatures and aliases cannot expose private types. All
implementation declarations remain visible to whole-program borrow checking
and optimization.

Generated declarations belong to their invocation's library, not the physical
`.lim` cache directory. Each generated file has access to its producer's
definition library and its invocation library, including private functions,
types, and representations. A nested generator gets its own definition library
and the original invocation library; it does not accumulate its ancestors'
definition-library privileges. A canonical file has one declaration identity, regardless of which alias
reaches it. Separate source paths can carry different library versions.

Write `@name` to resolve a name before generator execution. Inside a generator
definition it uses that definition's file scope; in supplied arguments it
uses the invocation source's file scope. Qualification produces the actual flat
file-qualified identifier (for example, `/project/library/helper.lim::Helper`),
not a hidden binding or a runtime expression. Forwarding and substitution never
qualify it again. Literal strings, generator parameters, and unmarked local
bindings are not interpreted by this operation. Handwritten forward declarations
are collected before qualification. Exported generated targets can be qualified
using their library's literal export contract; other unknown names cannot be
qualified. In particular, `@local` cannot silently become a local reference after
splicing a literal function. Pass new declaration names as literal symbols.

Invocation references are checked using caller permissions before interpreting
the generator, including explicitly qualified references inside quoted syntax.
A caller cannot pass `@lib@secret` when that declaration is private to `lib`.
Literal strings and selectors remain data: a generator may deliberately turn
them into references using `#gn-symbol`, `#gn-symbol-append`, or `#gn-variant`.
The resulting code uses its generated file's permissions. Thus generators are
privileged library APIs: their authors must validate data and executable syntax
they incorporate into their output. Qualification checks are not a sandbox for
an arbitrary code-splicing generator. `#unsafe` obligations remain unchanged.

Inspectable generated files record permissions as reader syntax, for example:

```lisp syntax
(#generated-context
  ((producer "lib@make")
   (definition-module "/project/library/lib.lim")
   (definition-file "lib")
   (invocation-module "/project/app/lib.lim")
   (invocation-file "")))
```

This compiler-owned header is checked against the current generator and
invocation on cache reuse. It contains no serialized source IDs or per-symbol
permission comments. Copying a header into source, supplying one to a generator,
or manufacturing one with generator operations is rejected. A generator cannot
manufacture late `@` qualification either: qualification is a source operation.
Files outside a `lib.lim` boundary share the `<global>` module; physical invocation
locations remain in the existing generated-file origin comments and do not
prevent equivalent expansions in that module from sharing a cache artifact.

For example, an exported `counter-reader` generator can emit a call to a private
`counter-value` helper. The consumer still cannot invoke that helper directly:

```lisp syntax
(#alias counter-reader = ./encapsulation/lib.lim::counter-reader)
(#generate counter-reader read-generated-counter)
```

See `examples/generator_private_helpers.lim` for a complete executable example.

An expansion instance includes the invoking file's identity, generator, and
literal arguments. Identical calls in one file can reuse a generated declaration;
calls in different files retain separate declaration identities. Cache keys also
include resolved references, dependency contents, and validated definition/caller
contexts. Multiple aliases to one source share that source; separate dependency
versions occupy different source paths.

An exported generator may invoke its library-private generator helpers,
including nested generators. Syntax equality and argument deduplication compare
values, not the way symbols were constructed. Builtin expansions also distinguish
producing definition contexts. Cache keys include definition/invocation context
headers as well as generator/dependency identities, and digests cover the complete
generated file. Cached authority is reconstructed from the current expansion,
not accepted from a file's self-asserted claims.
`#std` remains one compiler-provided prelude. Its facade explicitly lists its
declarations; parameter labels retain their original source spelling.
See `examples/library_boundary.lim` and `examples/encapsulation/test.lim`.

To bound compiler resource use, a project is limited to 128 simultaneously
nested source files, 4096 unique source dependencies, and 64 MiB of cumulative
source text (including the root file). Dependency-limit errors identify the reference
that crosses the limit; an oversized root file is rejected before import
traversal.

The compiler resolves each file reference exactly: `./` is relative to its
source file, `//` is relative to the compilation's project root, and `/` is an
absolute filesystem path. There is no fallback search through module directories.

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

Manifest paths are relative to the manifest. The nearest manifest above the
principal source defines the `//` root, including for dependencies outside that
directory. Without a manifest, the principal source's directory defines it.
The CLI defaults binary output into the output directory and applies the
manifest target unless `--target` overrides it.
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
- `#generate` as the generated-code keyword; `#generate` stays inside identifiers;
- symbols;
- signed and unsigned integer literals;
- floating-point literals;
- strings and character literals.

`.` is an ordinary character in a symbol, not a namespace or member-access
operator.  `-` is also an ordinary symbol character.  Thus these are single
identifiers:

```lisp syntax
math.add.one
my-value
Maybe?::unwrap-or
```

Builtin forms are distinguished by their `#` prefix:

```lisp run=42
(#fn main () #u64
  (#return 42u64))
```

The character literal syntax is `#\a`, `#\space`, `#\newline`, and so on.
Unicode escapes use `#\u{03bb}`.  Strings support `\n`, `\r`, `\t`, `\\`,
`\"`, and `\u{...}` escapes.

Integer literals may use binary, octal, hexadecimal, and underscores:

```lisp syntax
42u32  -1i8  0b1010u16  0o77u8  0xffffu128
```

Floating-point literals carry an explicit width when used in canonical code:
`1.5f32` and `0.25f64`.

## Types

The builtin scalar types are:

| Category | Types |
| --- | --- |
| unsigned integers | `#u8`, `#u16`, `#u32`, `#u64`, `#u128`, `#usize` |
| signed integers | `#i8`, `#i16`, `#i32`, `#i64`, `#i128`, `#isize` |
| floating point | `#f32`, `#f64` |
| other scalars | `#bool`, `#char` |
| zero-sized | `()` |
| diverging | `!` |

Fixed aggregates are written explicitly:

```lisp syntax
(#tuple #u64 #bool #char)
(#array #u32 4)
```

Construct a fixed-size array value with `#array-of`, keeping it visually
distinct from the `#array` type form:

```lisp fragment=array
(#let values (#array #u32 3)
  (#array-of (#array #u32 3) 10u32 20u32 30u32))
```

An immutable slice type is written `(#slice T)`. Borrow an array directly with
`(#borrow-slice array)`, or select `[start, end)` with
`(#borrow-slice array start end)`. These operations explicitly borrow storage;
they neither move the array nor allocate. Both bounds must be `#usize`.
`(#slice-of array-reference)` instead converts an existing immutable array
reference into a slice without extending its backing storage's lifetime. Use
`(#slice-len view)` for its runtime length and
`(#slice-idx view index)` to get a shared reference to an element. Indexing
checks the index against the slice length and traps if it is out of bounds.
Use `(#slice-range view start end)` to create an immutable half-open subrange
`[start, end)`. Both bounds are `#usize`; the operation traps if `start > end`
or `end > (#slice-len view)`. Empty and end-boundary ranges are valid. A
subslice retains the original borrow provenance, including across function
returns; it does not extend the referent's lifetime. Slices remain immutable.

User-defined names refer to concrete structs, enums, and aliases.  Generic
declarations and angle-bracket applications are not part of Lim.  Generators
create concrete specializations explicitly, such as `(#generate #vec (: element #u64 : allocator Alloc : name VecU64))`.
Allocator-backed collections add their concrete operations explicitly with
`(#generate #vec-alloc (: element #u64 : allocator Root : vector VecU64 : destroy destroy))`;
`Root::State` must denote `Alloc`, the state type passed to `#generate #vec`.
The root provides a byte-pointer allocation enum, safe `::allocate`, and unsafe
`::grow` / `::deallocate`; grow takes `:old-layout` and the requested `:layout`.
Handwritten and generated bundles follow the same ordinary naming convention,
without a producer requirement. `#std` provides `SystemAllocator::Allocator`,
whose empty state is constructed with `(#struct-literal SystemAllocator ())`.
Providers promise fresh, unique, aligned, non-null successful allocations,
preservation of the old allocation on growth failure, and matching deallocation.
Names and type checking cannot prove these semantic promises.
The generated API includes `VecU64::new`, `::reserve`, `::push`, `::get`,
`::get-mut`, `::set`, `::pop`, and `::free`. `(#generate #vec-sort (: element #u64 : vector VecU64 : comparator compare-u64))`
adds `VecU64::sort`; its named comparator accepts two immutable element
references and returns `#bool`. Allocation failure and capacity
overflow are returned in generated result types. See [the allocator ABI](allocator.md)
for the allocator and destruction function signatures.

`()` is the unit value and `!` is the never type.  A function returning `!`
must not reach a normal return.  A void function returns explicitly with
`(#return ())`.

### Heap-owned UTF-8 strings

Import `library/string.lim` for the concrete, opaque, linear `String` type.
String literals remain fixed character arrays; conversion is explicit. The
native Lim process allocator owns the bytes. It pools small allocations and
uses Linux memory-mapping syscalls for backing storage, without libc or FFI.
This is an ordinary library, not a new builtin or an implicit allocation.

```lisp run=42
(#std)
(#fn main () #u64
  (#let text (#array #char 3) "Aé🙂")
  (#return
    (#match (#call String::from-chars (: text (#borrow-slice text)))
      (#case (StringCreateResult.StringCreated owned)
        (#block
          (#let length #usize (#call String::len (: string (#borrow owned))))
          (#call String::free (: string owned))
          (#if (#usize::eq length 7usize) 42u64 1u64)))
      (#case (StringCreateResult.StringCreateFailed error) 2u64))))
```

`String::new` creates an empty string without allocating. `String::with-capacity`,
`String::from-chars`, `String::from-utf8`, and `String::try-clone` return
`StringCreateResult`: `StringCreated` contains an owned string;
`StringCreateFailed` contains a `StringError`. Cloning is an explicit, fallible
deep copy, never a shallow `#clone` of the allocation handle.

`String::len` and `String::capacity` take `(: string (#ref String))` and count
**bytes**, not characters. `String::is-empty` uses the same shared argument.
`String::reserve` takes `(: string (#ref-mut String) : additional #usize)`;
additional capacity is relative to the current length. `String::push-char`,
`String::push-chars`, and `String::push-utf8` take a mutable string and,
respectively, `: value #char`, `: text (#slice #char)`, or `: bytes (#slice #u8)`.
These operations return `StringStatus`: `StringOk` or `(StringErr error)`.
Validation, overflow, and allocation failures leave the original string
unchanged. Errors are `StringOutOfMemory`, `StringCapacityOverflow`,
`StringInvalidUtf8`, and `StringInvalidChar`.
`String::push-string (: string (#ref-mut String) : text (#ref String))`
appends the borrowed source string and returns the same `StringStatus`. It
does not consume either string; the source remains available after the call.

With `#std`, the embedded String module can be used without an explicit
import. This example builds a string from fixed character arrays, appends a
second owned string by shared borrow, and releases both owners:

```lisp library
(#std)
(#fn main () #u64
  (#let greeting (#array #char 5) "Hello")
  (#let suffix (#array #char 9) ", world 🙂")
  (#let-mut message String
    (#match (#call String::from-chars (: text (#borrow-slice greeting)))
      (#case (StringCreateResult.StringCreated created-message) created-message)
      (#case (StringCreateResult.StringCreateFailed error) (#panic))))
  (#let tail String
    (#match (#call String::from-chars (: text (#borrow-slice suffix)))
      (#case (StringCreateResult.StringCreated created-tail) created-tail)
      (#case (StringCreateResult.StringCreateFailed error) (#panic))))
  (#assert (#match (#call String::push-string (: string (#borrow-mut message) : text (#borrow tail)))
    (#case StringStatus.StringOk true) (#case _ false)))
  (#assert (#match (#call String::push-char (: string (#borrow-mut message) : value #\!))
    (#case StringStatus.StringOk true) (#case _ false)))
  (#assert (#i64::eq (#println (#borrow message)) 0i64))
  (#call String::free (: string tail))
  (#call String::free (: string message))
  (#return 42u64))
```

`String::byte-at` takes a shared string and `: index #usize`. It returns
`(StringByte byte)` with a copied `#u8`, or `StringByteOutOfBounds`.
`String::bytes (: string (#ref String))` returns an opaque `StringBytes` view
that retains the owner borrow, preventing mutation, moving, or freeing its
owner while the view is live. `StringBytes-len (: bytes view)` and
`StringBytes-byte-at (: bytes view : index #usize)` inspect that view without
allocating; indexing also returns a copied byte. No mutable byte access is
exposed: safe operations preserve valid UTF-8.
`String::data-pointer (: string (#ref String))` is an unsafe raw-I/O escape
returning `(#ptr-mut #u8)`. The pointer does not retain the owner borrow. The
caller must keep a shared borrow alive, read only initialized bytes, and never
write, grow, move, or free the string while using it. Safe stdout functions
uphold these obligations internally; printing does not require `#unsafe`.

### Borrowed UTF-8 views

`(#std)` also provides `StringView` and `Utf8Slice`: opaque, allocation-free
UTF-8 views that retain a shared borrow of their source. `String-view
(: string (#ref String))` borrows the complete String in constant time, since
safe String operations already guarantee valid UTF-8. `Utf8Slice::from-owner
(: owner (#slice #u8))` validates the complete byte slice and returns
`(Utf8Slice::Result.Valid view)` or `Utf8Slice::Result.InvalidUtf8`, without allocating or
copying the bytes. Empty input and embedded NUL are valid.

Both APIs come from an ordinary library generator. To declare another concrete
view, choose its public name and source layout explicitly:

```lisp library
(#std)
(#generate #utf8-view (: name BorrowedText : owner (#slice #u8)))
(#fn main () #u64
  (#let bytes (#array #u8 2) (#array-of (#array #u8 2) 195u8 169u8))
  (#let view BorrowedText
    (#match (#call BorrowedText::from-owner (: owner (#borrow-slice bytes)))
      (#case (BorrowedText::Result.Valid accepted) accepted)
      (#case _ (#panic))))
  (#let-mut iterator BorrowedText::Chars (#call BorrowedText::chars (: view view)))
  (#assert (#match (#call BorrowedText::Chars::next (: iterator (#borrow-mut iterator)))
    (#case (BorrowedText::CharResult.Char value) (#char::eq value #\é))
    (#case _ false)))
  (#forget iterator)
  (#return 42u64))
```

For a generated name `V`, the public operations are:

| Function | Arguments | Result |
| --- | --- | --- |
| `V::from-owner` | `: owner` with the declared source type | `V::Result`: `(V::Result.Valid view)` or `V::Result.InvalidUtf8`; validates in O(bytes). |
| `V::len` | `: view (#ref V)` | `#usize` byte length, not character count. |
| `V::is-empty` | `: view (#ref V)` | `#bool`. |
| `V::byte-at` | `: view (#ref V) : index #usize` | `(Utf8Byte copied-byte)` or `Utf8ByteOutOfBounds`. |
| `V::boundary` | `: view (#ref V) : index #usize` | Whether the offset is a scalar boundary; zero and length are boundaries, out-of-range is false. |
| `V::subview` | `: view (#ref V) : start #usize : end #usize` | `V::Result` for half-open byte range `[start,end)`: `(V::Result.Valid subview)`, `V::Result.InvalidRange`, or `V::Result.InvalidBoundary`. |
| `V::clone` | `: view (#ref V)` | A new borrowed view; copies only borrow metadata, not the source or allocation. |
| `V::chars` | `: view V` | `V::Chars`, consuming the view and retaining its source borrow. |
| `V::Chars::next` | `: iterator (#ref-mut V::Chars)` | `(V::CharResult.Char scalar)` or `V::CharResult.End`; repeated end reads remain at end. |

Subview bounds are checked before additions or byte access, including maximal
`#usize` offsets. Splitting a multibyte scalar is an error, including an empty
range at a non-boundary offset. Nested subviews use offsets relative to their
parent and retain the original source borrow, not the temporary parent view.
Views can be returned through helpers or stored in aggregates. Forgetting a
parent does not release a child's or iterator's source loan. Mutation, growth,
moving, and destruction of that source are rejected while such loans remain
live. Explicitly `#forget` unused views and iterators; no destructor or allocator
operation runs. See `examples/string_view.lim` for an owned String example.

Iteration decodes Unicode scalar values, not grapheme clusters or normalized
text. It requires no dynamic dispatch, function pointers, heap allocation,
or compiler-specific view primitive. Generated ordinary Lim is inspectable in
`.lim/generated/` and uses the same content-addressed cache as other generators.
The supporting `V-byte`, `V-valid`, and `V-decode` functions perform checked byte
access, validation, and decoding; `V-decode` asserts an in-range scalar boundary
and returns `(#tuple #char #usize)` containing the scalar and its byte width.
`V-assume-valid` is an **unsafe** constructor that skips validation. Its caller
must prove the complete source is valid UTF-8 and preserve the source's shared
borrow. The safe `String-view` wrapper upholds this contract internally.

The generator accepts only `(#ref String)` and `(#slice #u8)` sources. Arbitrary
reader callbacks could change interior-mutable storage after validation and are
not accepted. Packed String bytes and Lim word-backed byte slices use separate
accessors: no raw pointer is reinterpreted as a word-layout slice or reference.

Raw-backed scalar references preserve exact byte addresses and access the
native width of the scalar, including at odd `#u8` addresses. References keep
internal high-bit storage metadata, which is removed before syscall and
assembly pointer operands. Lim aggregates and arrays still use Lim's word
layout; raw borrowing does not turn them into packed C aggregates. Unsafe
pointer-to-reference conversion still requires valid storage, alignment,
lifetime, and exclusive-access proofs from its caller.
`String-pop-char` takes a mutable string and returns
`(StringPopped character)` or `StringEmpty`. `String-clear` takes a mutable
string, empties it, and retains its capacity. Strings need not be
NUL-terminated and may contain embedded NUL bytes.

`String-free (: string owned)` consumes the owner and releases its allocation.
Every owned string must be consumed, returned, or explicitly forgotten before
returning; references do not implicitly destroy it. See
[the system allocator contract](allocator.md#standard-system-allocator-and-string)
and [the runnable printing example](../examples/heap_string.lim).

## Top-level declarations

### Compile-time proofs

`(#theorem name proposition)` declares a procedural compile-time obligation over the checked,
expanded program. The name follows value-identifier rules. Validation rejects a
false or unproved obligation; a procedural proof emits no runtime assertion and
supplies no unchecked assumptions to other program obligations. Ordinary type,
ownership, and unsafe checks still apply to the program. See the
[program verification checklist](program-verification.md) for supported checks,
bounds, and planned coverage.

`(#proof-using (name ...) proposition)` lets a proposition
depend on explicitly named `#theorem` declarations. Every dependency is
resolved and verified; aliases and imported file definitions refer to their
canonical declarations. The dependency list adds no assumptions or bindings,
and the proposition body retains its existing scope. Reuse supports reference
results and references inside owned aggregates using checked caller-storage
origins. Reference-bearing writable targets use checked final store origins,
validated against symbolic provider execution. Possible writes retain old and
replacement alternatives; all replacement sources are read at call entry.
Mutable argument targets define the writable frame; postconditions state their
new contents and any unchanged parts that callers need. Implicit global access,
unsafe operations and external effects are unsupported. Failed
preconditions and insufficient postconditions remain unproved. No assumption
is made when a dependency fails, is unsupported, or cannot be established.

```lisp library
(#fn identity ((value #u8)) #u8 (#return value))

(#theorem identity-law
  (#proof-for-all ((x #u8)) (#proof-eq (#call identity (: value x)) x)))

(#theorem identity-effects
  (#proof-no-effects identity (#proof-allocation #proof-io #proof-mutation)))
```

This is bounded symbolic universal bitvector solving, not testing selected
inputs. `#proof-for-all` creates symbolic values for every supported value of
each declared type. The engine symbolically evaluates modeled branches and
asks its SAT solver whether a guarded counterexample exists. An unsatisfiable
counterexample formula establishes the claim within the implemented model;
a satisfying assignment makes the claim false and supplies counterexample inputs
if the enclosing proof fails.
Unsupported semantics, missing implementations, and exhausted resources produce
an error, usually marked `unproved`. They never establish a theorem. A false
precondition can make an implication or contract vacuous; these forms do not
separately prove that their precondition is satisfiable.

`#proof-for-all`, `#proof-contract`, and execution-trace claims discharge their
own symbolic inputs and return a closed Boolean result to an enclosing logical
combination. Their local bindings and path guards do not escape into sibling
claims. Negating a closed universal claim negates the whole quantified result,
not its predicate separately for each input. Nested `#proof-for-all` and
`#proof-contract` claims are unsupported, including combinations of the two;
combine universal bindings in a single `#proof-for-all` list instead. Trace
claims quantify their own entry-function inputs and must also be outside these
quantifiers. Independent closed claims can be combined with `#proof-and`,
`#proof-or`, and the other logical forms.

`#proof-and` and `#proof-or` combine one or more propositions; `#proof-not`
negates one, and `#proof-implies` checks a consequence under its antecedent.
These logical combinations do not suppress unsupported-operation errors in
other operands. `#proof-eq` compares modeled scalar or aggregate values
structurally. Reference identity equality is unsupported: compare explicit
referent values with `#deref`. Integer operations use finite-width bitvectors,
including signedness and the operation's wrap or saturate mode. Modeled traps,
failed assertions, and invalid array indices must be unreachable under the
current guard. `#proof-no-overflow` checks whether integer add, subtract, or
multiply fits its type, even when the named operation wraps or saturates.
Its operation identifier must name an existing native integer builtin with a
valid mode, such as `#u8::add-wrap`, `#u8::sub-wrap`, or `#u8::mul-wrap` (or
the corresponding supported `-saturate` form). Mode-free identifiers such as
`#u8::add` are not native builtins and are rejected. Floating-point arithmetic
is unsupported.

`(#proof-contract function precondition postcondition)` universally quantifies
the function's declared parameters using their parameter names, restricts the
execution to the precondition, executes the checked implementation, and checks
the postcondition, then returns the closed result. A contract creates its own
parameter bindings; nested contracts and nesting with `#proof-for-all` are
unsupported. `(#proof-result)` denotes the returned value in a
postcondition. `(#proof-old expression)` evaluates against the saved contract
entry state, including entry referent contents, rather than the post-call state.
It is available only within a contract.

```lisp library
(#fn identity ((value #u8)) #u8 (#return value))

(#theorem identity-contract
  (#proof-contract identity true (#proof-eq (#proof-result) (#proof-old value))))

(#theorem identity-caller
  (#proof-using (identity-contract)
    (#proof-contract identity true (#proof-eq (#proof-result) (#proof-old value)))))
```

The second theorem explicitly reuses the verified direct contract. Its dependency
list creates no proposition binding; names in the body keep their ordinary
proof scope.

Calls in specifications evaluate actual checked function bodies, including
nested calls and applicable clone hooks, unless `#proof-using` selects a verified
contract for that call. Calls inside the selected contract's own pre/postconditions
still execute their bodies. Function names resolve to actual declarations.
A specification call's transitive checked graph must have no
`global-write`, `io`, `allocation`, `external`, or `asm` effects. The engine also
checks that the call preserves observable storage that existed before it;
the graph restriction and the storage check both apply. Specification syntax
accepts modeled expressions and qualifying function calls, but rejects statement
blocks. This restriction does not forbid statements inside a qualifying checked
function body. Calls executed as the subject of a contract or trace claim may
mutate modeled storage. This is not a general IO, FFI, pointer-validity, or concurrency
model. External functions have no executable symbolic implementation; assembly,
syscalls, and other unmodeled operations fail when symbolic evaluation reaches
them. Proof-side representation inspection respects opaque and library-private
boundaries. Fresh reference inputs have separately allocated symbolic referents;
this does not quantify every possible alias relationship between inputs.

`#proof-sorted` takes a fixed array or modeled slice and a named, safe,
two-argument Boolean comparator with a checked implementation.
It checks that the comparator is false for each adjacent pair in reverse order
`(later, earlier)`. It does not prove comparator transitivity, totality, or sort
stability. `#proof-permutation` compares equal-length arrays or modeled slices by element
multiplicities using modeled equality; an array and slice may be compared.
`#proof-unique` checks that no two selected elements compare equal. These
properties observe only a slice's selected range, including symbolic ranges,
and read its current backing storage. Use `#proof-old` around the entire
predicate to check an old-state property. For old/new permutation comparisons,
read an owned array inside `#proof-old`; saving an old slice handle alone does
not snapshot its referent. An empty range is sorted and
unique. None of these forms implicitly runs a sorting algorithm.
All reject backing arrays longer than 64 elements, including
directly constructed literal arrays, not just quantified inputs. This keeps
permutation multiplicities within the implementation's eight-bit counters.
Permutation operands must have matching element types. Sortedness requires
both comparator parameter types to match the collection element type and its return
type to be Boolean. These type checks apply even to empty arrays; emptiness
does not excuse an incompatible element type or comparator signature.
Comparator execution retains ordinary checked-call, trap and budget rules;
unsupported comparator execution remains unproved, including under negation.
Unsafe and external comparator declarations are rejected even for empty ranges.
Comparator specifications reject active call cycles and allow at most four
simultaneously active comparator calls. Sequential comparisons reuse that
allowance; recursive or deeper specifications report a resource-limit error,
including under negation. Ordinary call, evaluation and solver limits also apply.
Uniqueness and permutation require modeled equality for each comparison.

Modeled guarded matches accept only supported pure builtin guard expressions.
Guard expressions cannot call functions, contain blocks, or access globals
(including global constants). A guard that produces multiple symbolic branches
is unsupported, even if its operations are otherwise pure. Guard-expression
nesting is limited to 64. These are symbolic-engine restrictions on proofs and
on code evaluated by proofs, not additional runtime language rules.

Structural graph claims use the checked call graph, including clone-hook edges
and conservative generated thread spawn/join-to-worker edges.
`#proof-calls-directly` requires one call edge;
`#proof-calls-transitively` requires a nonempty path of one or more edges.
Naming the same function at both ends does not establish a call by itself; it
would require recursion, which checked runtime calls disallow. These are structural reachability claims: a positive path
need not be a feasible execution. Unknown function names are errors. A missing
path cannot establish call absence if reachable assembly, external code, or
other opaque execution could hide additional calls; that query is unproved.
`#proof-no-effects` requires an explicit nonempty list of effect tags and checks
transitive absence of each effect. Tags are `#proof-allocation`, `#proof-io`,
`#proof-global-write`, `#proof-unsafe`, `#proof-external`, `#proof-asm`, and
`#proof-mutation`. Mutation includes externally observable reference, field,
array, and global writes conservatively; local scalar reassignment is ignored.
External calls, assembly, and hidden thread runtime execution carry conservative
unknown effects, so a negative effect claim cannot silently treat them as safe.
Effect predicates describe this conservative structural summary. Negating an
absence claim establishes that the summary contains a classified effect; it
never proves that a runtime effect actually occurs on a feasible execution.

`(#proof-only-unsafe entry (allowed...))` inspects transitive unsafe primitives
outside the listed function boundaries or allowed builtin spellings. Listing a
function trusts that boundary and stops inspection beneath it. A known
function's unsafe-call flag alone is not an unsafe primitive: its internals are
inspected unless it is allowed. External functions and assembly require explicit
allowance; they are not silently safe. This form does not discharge ordinary
`#unsafe` requirements or establish memory safety.

Execution-trace claims differ from graph claims. In
`(#proof-calls-before entry required action)`, every modeled entry into `action`
must follow a completed call to `required` on that execution. It does not require
that either function be called, or a fresh required call before every action.
In `(#proof-calls-when entry observed expected action)`, `observed` must return
`#bool` and `expected` must be `true` or `false`. The claim forbids an `action`
call and an observed result equal to `expected` from occurring in the same
execution, in either order. It is not an obligation to call the action.
The engine executes the observed function's checked body, including modeled
nested calls and storage changes, and records its actual symbolic Boolean
return value when it completes. It does not replace that body with an arbitrary
result or an abstract validation boundary. Unmodeled operations still fail
closed. Nested trace claims are unsupported, and trace claims require complete
bounded loop exploration.

The explicit selectors in
`(#proof-requires-validation entry (#parameter-of validate user) (#parameter-of perform user))`
check a storage-specific validation protocol. Each descriptor must have the form
`(#parameter-of FUNCTION PARAMETER-NAME)`: it references an existing parameter
of that function, not a call expression or an argument expression. The selector
introduces no theorem binding. It is accepted only in a validation descriptor
position; old bare function/parameter pairs are rejected without compatibility.
In contrast, `(#parameter name TYPE)` declares a new mathematical theorem
parameter. The two selected validation parameters must be
ordinary or pinned references with the same resolved referent type; the
validator must return `#bool`. The descriptor names select parameter positions,
so they need not have the same spelling in the two functions.

The checker universally quantifies the explicit entry function's inputs and
follows every reachable action entry, including calls through helpers. Before
each action entry, a validator call must have completed with `true` for the same
storage location as the action's selected argument. Equal data in a different
object is insufficient. A missing validator call, a call that completes later,
or a completed `false` result supplies no valid evidence. A later validator
call returning `false` for the same object also revokes any earlier success.

Validation is invalidated by writes overlapping the object or its transitive
referenced dependencies. This includes writes through aliases and dependencies
whose contents may affect validation, even if the outer object is unchanged.
Primitive reference dependencies are tracked transitively as well.
Fresh successful validation can restore evidence after a write or false result. The claim
tracks storage and freshness, not just matching scalar values or function names.
Only an enum's active payload contributes referenced dependencies. Merely
checking a referenced child does not invalidate an unchanged parent's evidence.
It checks the actual validator body's Boolean result; it does not establish
that the body implements the intended business criterion.

```lisp library
(#struct User () ((age #u8)))

(#fn validate ((user (#ref User))) #bool
  (#return (#u8::ge (#get user age) 18u8)))

(#fn perform ((user (#ref User))) ()
  (#drop (#get user age))
  (#return ()))

(#fn dispatch ((user (#ref User))) ()
  (#call perform (: user user))
  (#return ()))

(#fn process ((user (#ref User))) ()
  (#if (#call validate (: user user))
    (#block
      (#call dispatch (: user user))
      ())
    ())
  (#return ()))

(#theorem safe
  (#proof-requires-validation process (#parameter-of validate user) (#parameter-of perform user)))

(#fn main () ()
  (#let user User (#struct-literal User ((age 21u8))))
  (#call process (: user (#borrow user)))
  (#forget user)
  (#return ()))
```

Here the `process` claim covers all supported `User` inputs and sees the action
inside `dispatch`. The `perform` body is a small modeled action for the example;
replace it with other supported code when applying the protocol. Calling the
validator for one local `User` and performing the action on a distinct local
with the same fields would fail. Mutating the validated object or a referenced
dependency before `perform` requires a new completed successful validation.

Claims begin at the specified root. Choosing `main` covers its synchronous call
tree; other roots need separate claims. Every branch and complete bounded loop
execution is considered. Unsupported semantics, unavailable or external
implementations, and exhausted budgets are unproved rather than assumed safe.
The theorem emits no runtime proof code and adds no runtime validation call.
Unlike this claim, `#proof-calls-before` does not require a `true` result or track
an object, and `#proof-calls-when` does not establish same-object freshness.
Their existing call-order and observation semantics are unchanged.

Validation tracking allows at most 64 facts, 128 dependencies per fact, and
256 dependencies total per symbolic state, with reference-dependency traversal
depth limited to 32. The existing 100,000-step symbolic execution budget also
applies. Exhausting these limits makes the obligation unproved.

`(#proof-stack-at-most function "x86_64-sysv" bytes)` checks a literal byte bound
against generated assembly for that explicit target. The current certificate
supports only `x86_64-sysv`. It includes reachable generated callees and their
call-stack costs, measured from the entry's incoming stack pointer. Unknown
external or indirect callees, recursion, and unsupported stack behavior prevent
a certificate. This is a generated-code stack bound, not a bound on process
memory, kernel use, or a thread worker's separate stack merely because its spawn
helper is called.

Loops default to 32 symbolic iterations. `(#proof-loop-limit limit proposition)`
scopes a literal limit in `1..=1024`; reaching a feasible continuation beyond it
is unproved, rather than an assumption that the loop terminates. Alternatively,
`(#proof-with-invariants ((function loop-label predicate unsigned-rank)...) proposition)`
attaches induction obligations to labeled loops. Each function/label pair must
identify exactly one checked loop; misspelled or ambiguous labels are errors. The engine checks entry and
preservation of the predicate, and strict decrease of a same-width unsigned
rank on continuing iterations. Invariants are checked obligations, not axioms.
Induction supports modeled owned-variable updates and borrowed write frames
whose reference graph remains stable. Numeric contents are abstracted while
stored handles keep their original locations. Loop-local mutable borrows
contribute their source roots to the frame. Every continuing step and forwarded
exit must preserve existing reference identities and reference-bearing enum tags.
Slice handles retain their backing location, start and length. Mutable views
over bounded arrays contribute guarded element regions, preserving storage
outside their ranges; references inside selected elements retain their actual
locations. Empty end-boundary ranges permit no writes. Bounds obligations still
apply to every access, including those used in invariants and ranks. Direct
unbounded symbolic slice inputs remain unsupported; construct a bounded view in
the proved wrapper or quantified call.
Global write destinations and arbitrary allocation remain unsupported.
Bounded changing reference graphs, slice geometry and execution-trace monitors
have additional coverage and closure checks described in the
[program verification model](program-verification.md). A valid invariant/rank
can avoid fully unrolling a supported loop; it does not enable arbitrary hidden execution.
Loop-body and for-step calls may use direct contracts explicitly selected by
`#proof-using`, including contracts over borrowed state. The selected contracts
retain their effect restrictions, and every helper precondition must follow
from the loop-head invariant and current path guard. Call-argument writes
contribute to the modified-variable set. Invariants, ranks and loop conditions
remain pure; general user-call expressions, statement blocks and lazy global
reads remain forbidden. Invariants can use `#proof-unique`,
`#proof-permutation` and `#proof-sorted` over bounded arrays and slice views.
Read-only range construction and explicit `#array-of` values are permitted;
range/index bounds must hold wherever those expressions are evaluated.
The named sortedness comparator uses ordinary specification-call checks,
including observable-storage preservation, effect restrictions and resource
limits. Its calls evaluate the specification and do not contribute program
events to call-order or validation traces. Selecting a contract does not
permit hidden global/environment access or unchecked changes to reference identity.
Checked return and store summaries retain provider-derived origin and
reference-bearing constructor conditions, including correlations across stored
and returned slots and branches that leave an entry reference unchanged. Conditions
bind to caller entry data before write-frame abstraction; numeric result fields
still follow the selected postcondition. Mutating parents with possible typed
in-place overlap against input referents and exclusive pinned inputs retain
conservative origins. Unknown choices within a dynamic subobject origin remain
conservative; symbolic-index writes of reference-bearing array elements require
additional path splitting. See the [verification model](program-verification.md)
for the template, condition and retained-memory limits.

Other current bounds include 100,000 symbolic evaluation steps, 4,096 paths at
path-budget checks, 4,096 symbolic storage slots, call depth 128, combined
expression/proposition evaluation nesting 32, and symbolic
type nesting depth 32. Fresh fixed-array inputs are limited to 64 elements;
`#proof-sorted`, `#proof-permutation` and `#proof-unique` also enforce that limit
on directly constructed arrays and modeled slice backing arrays.
The solver also has a 100,000-node circuit limit, a 2,000,000-work per-query
SAT search budget and a cumulative 64,000,000-work budget for search and query preparation;
solver errors and exhaustion remain errors on later queries. These are resource
limits, not a statement that every program below them is modeled. Supported
inputs include unit, Boolean and integer values, characters restricted to
Unicode scalar values, tuples, small fixed arrays, modeled records and enums,
and ordinary or pinned references. Raw pointers can be represented as address
bitvectors, but raw memory operations are not thereby supported. Use explicitly
typed literals and `#array-of`; context-dependent `#array-repeat`, arbitrary slice inputs,
arbitrary ownership/runtime facilities, and unsupported operations are not
made provable by increasing the loop limit.

The former dependent mathematical proof subsystem is no longer part of Lim.
Program-level symbolic obligations are described in the
[program verification checklist](program-verification.md).

### Functions

Functions are always free-standing; Lim has no methods or `impl` blocks.
The canonical form is:

```lisp library
(#fn add ((left #u32) (right #u32)) #u32
  (#let total #u32 (#u32::add-wrap left right))
  (#return total))
```

The parameter list is a list of `(name Type)` pairs. A colon-prefixed list
is equivalent and avoids repeating parentheses around each pair:

```lisp run=42
(#fn add (: left #u32 : right #u32) #u32
  (#return (#u32::add-wrap left right)))
(#fn main () #u64
  (#return (#as (#call add (: right 2u32 : left 40u32)) #u64)))
```

At one list depth, `(: left #u32 : right #u32)` expands to
`((left #u32) (right #u32))`. A colon must be the first token after `(` at
that depth; `(left : #u32)` is invalid. Nested lists have their own depth, so
their colons do not affect the enclosing list. Empty or adjacent groups and
a trailing colon are rejected; `(:)` is an empty list. Only a standalone `:`
token groups elements: embedded colons belong to the identifier, so
`Pipeline::Pending`, `left:right`, and `:label` are flat names, not namespace
lookups. This syntax works in other lists of groups too. Parameters may be
marked mutable:

```lisp library
(#fn increment ((#mut value #u64)) #u64
  (#set value (#u64::add-wrap value 1u64))
  (#return value))
```

Function calls also name every argument explicitly. Use `#call` for safe
functions or `#unsafe-call` for unsafe and external functions, with a
list of `(name value)` pairs or a colon-prefixed argument list;
each argument label must match a parameter in
the declaration:

```lisp syntax
(#call add (: left 20u32 : right 22u32))
```

When a variable has the same name as its parameter, `($ name)` expands to
`(name name)`:

```lisp run=42
(#fn add (: left #u32 : right #u32) #u32
  (#return (#u32::add-wrap left right)))
(#fn main () #u64
  (#let left #u32 20u32)
  (#let right #u32 22u32)
  (#return (#as (#call add (($ left) ($ right))) #u64)))
```

This is general parser sugar, so it also works in struct field lists and
quoted generator syntax. It accepts one identifier or an explicit unary borrow
of one identifier: `($ (#borrow owner))` expands to
`(owner (#borrow owner))`. The same form supports `#borrow-mut`, `#pin-borrow`,
and `#pin-borrow-mut`; arbitrary expressions and implicit borrowing are not
supported. It preserves that
identifier's source location for diagnostics, and does not change evaluation
order or borrowing rules. The formatter preserves the shorthand spelling.
Do not add a colon around an already grouped `($ name)` pair: `(: ($ name))`
would introduce an extra list, just like `(: (name name))`.

Positional call forms are rejected. Calls with no arguments use
`(#call function ())` for safe functions, or
`(#unsafe (#unsafe-call function ()))` for unsafe and external functions.
The equivalent empty colon group `(:)` formats as `()`.
`#call` rejects unsafe and external callees even inside `#unsafe`;
`#unsafe-call` requires an enclosing `#unsafe` block and rejects safe callees.
Both forms accept `($ name)` shorthand and apply the same argument checks.

`(#call-graph)` returns a `(#slice #char)` containing the actual caller chain:
`main:21 -> second:17 -> third:13`. Every number is the executing line **inside
that function**: the call to the next function, or the final `#call-graph`
expression. Repeated calls on different lines are distinguishable. No file
paths are included; function names remain directly greppable.

The trace uses bounded stack storage, without implicit heap allocation or
global mutable state. Its view cannot outlive the current function. Copy it
explicitly with `String::from-chars` when an owned result is needed; see
[`examples/call_graph.lim`](../examples/call_graph.lim) for printing and freeing
that string. Only functions that can reach a trace carry caller context;
thread spawning transfers its own owned context into the worker.

Named argument expressions are evaluated in the function's parameter
declaration order, regardless of the order of labels at the call site. `#struct-literal`
field expressions are evaluated in the struct's field declaration order,
regardless of their written order. The compiler checks and lowers expressions
in these same orders; labels select destinations and do not control effects.

Generic function declarations and angle-bracket calls are rejected.  Use a
generator to emit a concrete function for each required type combination.

There are no implicit returns.  Every reachable function path must use
`#return`; a unit return must use `(#return ())`.

Native functions declare their calling convention explicitly. `#abi-c` selects
the target's C ABI; external signatures currently accept scalar values and raw
pointers only. By-value aggregate FFI signatures remain rejected. Calls are
unsafe FFI boundaries and must use `#unsafe-call` inside `#unsafe`:

```lisp run=42
(#extern-fn #abi-c abs ((value #i32)) #i32)
(#fn main () #u64
  (#return (#as (#unsafe (#unsafe-call abs (: value -42i32))) #u64)))
```

Binary compilation links statically without libc or pthread when the assembled
objects have no unresolved symbols and no libraries were explicitly requested.
Foreign references still require the runtime linking path; generated threads
do not. Additional native link inputs can be supplied repeatedly
with `--link-lib NAME` and `--link-object PATH`. The internal linker reads
object definitions and relocations, resolves requested shared libraries, and
reports missing libraries or symbols before publishing output. These options
apply to binary output, not `--emit-asm`.

`(#std)` is an explicit top-level opt-in to Lim's bundled standard modules,
including `String` and standard output. Their immutable source is embedded in
the compiler, so this works outside a source checkout. Without `#std`, these
names are not added to the program. `(#println (#borrow string))` writes the
UTF-8 bytes of a borrowed `String`, then a newline, and returns `#i64`: zero on
success or a negative errno on failure. It neither converts string literals
implicitly nor consumes the string. Output can be partial on failure, and the
newline is skipped when writing the string bytes fails. See
`examples/string_println.lim` for building and printing a string.

`std-read-line (: string (#ref-mut String))` explicitly appends a UTF-8 line
from stdin to an existing String. `StdLineRead usize` reports appended bytes
(excluding the consumed LF); `StdEndOfInput` reports EOF before any new text.
`StdReadFailed StdReadError` distinguishes `StdIoError i64` (negative errno)
from `StdTextError StringError` (invalid UTF-8 or allocation failure). Existing
text and successfully appended complete characters remain intact on failure.
EOF after a partial line returns that line normally; interrupted reads retry.
This API is included in `#std`. See [the input contract](stdin.md) and
`examples/string_stdin.lim` for an echo loop with explicit cleanup.

`examples/echo_input.lim` shows byte-at-a-time input and output using Linux
x86-64 `read` and `write` syscalls inside unsafe `#asm` blocks;
`tests/io_examples.rs` runs it with piped input and checks that stdout matches.
To try it yourself:

```sh
printf 'hello from Lim\n' | ./target/debug/lim examples/echo_input.lim -o /tmp/lim-echo
printf 'hello from Lim\n' | /tmp/lim-echo
```

The program writes every byte it reads back to standard output, stopping at
end-of-file. The example is target-specific and uses `#cfg` when the standard
library has multiple platform implementations. `library/linux_x86_64.lim`
also wraps process identity/group queries, descriptor operations, memory
mapping, clocks, sleeping, and random-byte generation. These wrappers expose
the kernel's raw result convention: successful values are returned directly,
and errors are negative errno values. The integration test exercises both
successful calls and deterministic invalid-descriptor errors. Other syscalls
can be issued explicitly with `#linux-syscall` inside `#unsafe`. Importing
`library/linux_x86_64.lim` also imports the complete native x86-64 syscall
number catalog in `library/linux_x86_64_syscall_numbers.lim`; it names the
Linux `common` and native `64` ABI entries while excluding x32.

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

```lisp library
(#type UserId #u64)
(#type Pair (#tuple #u64 #bool))
(#type Matrix (#array #f32 4))
```

Aliases are concrete.  Recursive aliases are rejected.

### Structs

Structs are value types with named fields:

```lisp run=9
(#struct Point () ((x #u64) (y #u64)))

(#fn main () #u64
  (#let point Point (#struct-literal Point ((x 7u64) (y 9u64))))
  (#return (#get point y)))
```

Use a generator to emit concrete struct declarations when a family of
structs is needed.

### Enums

Variants may be fieldless or carry one payload. Use a named struct when a
variant needs multiple fields:

```lisp library
(#struct MovePayload () (: x #i32 : y #i32))
(#enum Message ()
  (Message.Quit
   (Message.Move MovePayload)
   (Message.Write (#array #char 8))))
```

Discriminants are assigned from zero, or can be explicitly supplied using a
numeric value after the variant name.  Variant names are global within a
program and must be unique.

Native `#match` dispatch uses a bounds-checked jump table for enums with
4–4096 contiguous discriminants when at least four distinct arms are initial
targets. Explicit nonzero and full-width tags are supported; declaration and
arm order need not follow tag order. Entries are signed 32-bit offsets in
read-only storage, resolved by Lim's own linker. Invalid tags trap before
indexing the table. Guards and refutable payload patterns retain their ordered
fallback checks. Small or sparse enums, matches with few destinations, and
or-patterns keep direct comparison chains. This changes no language semantics,
and whole-program stack analysis follows every table target.
See `examples/enum_dispatch.lim` for a runnable payload-dispatch example.

To inspect an enum without extracting its owner or payload, use
`(#variant-is reference Variant)`. It works through ordinary and pinned,
shared and exclusive references. The reference is evaluated once; only the
discriminant is read. The test grants no permission to move a payload or ignore
a live loan. Later payload projections still check the active variant at
runtime. See `examples/variant_is.lim` for inspection of a linear owner followed
by explicit consumption.

### Globals and statics

Top-level `#const`/`#let` values are immutable compile-time values. `#static`
creates immutable storage and is useful for aggregate data. Ordinary statics
are placed in read-only memory; statics containing atomic fields use writable
memory so their explicit interior-mutability operations can run. Every
read of a static must occur inside `#unsafe`, including reads used to create a
reference to it:

```lisp library
(#const answer #u64 42u64)
(#static values (#array #u64 3)
  (#array (#array #u64 3) 10u64 20u64 30u64))

(#fn first-value () #u64
  (#return (#unsafe (#index values 0u64))))
```

Initializers must be compile-time values.  Constant references, arithmetic,
casts, conditionals, tuples, arrays, structs, enums, and floating-point
values are supported.  Cyclic constant references are rejected.

Atomic initializers may also be constant, including inside structs, tuples,
arrays and enum payloads. They do not execute runtime initialization functions:

```lisp library
(#static counter (#atomic #u64) (#atomic-init #u64 0u64))
(#fn increment-counter () #u64
  (#return (#unsafe
    (#atomic-fetch-add (#borrow counter) 1u64 #memory-relaxed))))
```

This does not permit an ordinary mutable borrow of a static, even inside
`#unsafe`; updates go through the atomic API. A future may receive a reference
to static or heap storage through an explicit parameter and select it against
a local reference. Direct pinned static field/tuple borrows inside a future
also preserve their global storage identity. General direct local/static
ordinary-reference selection still requires a checked boundary parameter;
unsupported combinations fail closed rather than receiving fabricated anchors.

## Variables and mutation

Local bindings always state their type:

```lisp fragment=bindings
(#let count #u32 0u32)
(#let-mut total #u64 0u64)
```

`#let` creates an immutable binding; use `#let-mut` for a mutable binding.
Bindings may not shadow a visible parameter, local, or global; choose a distinct
name instead. Names may be reused in separate sibling scopes when neither
binding is visible from the other. `#set` assigns a mutable scalar or
aggregate local:

```lisp syntax
(#set total (#u64::add-wrap total 1u64))
```

A whole reference-bearing local may also be assigned from another typed
binding or a fieldless enum variant, for example `(#set view next)` or
`(#set view Empty)`. The replacement installs that
binding's reference origins and releases the old binding's loans. Shared
references remain Copy; exclusive references transfer without duplication.
An outstanding borrow of the destination still prevents replacement, and a
linear old value must already have been consumed. Arbitrary reference-bearing
RHS expressions and member replacement retain their existing restrictions.
`examples/reference_assignment.lim` releases the old owner, reads the new
owner, then drops both shared handles before mutating the new owner.

Binding an exclusive reference, or storing it in an aggregate, transfers its
handle: subsequent use of the source handle is rejected. Extracting an exclusive
reference from an owned aggregate likewise transfers its selected slot, not the
pointee or the other fields. Forgetting the remaining container does not end the
transferred borrow; explicitly release the destination handle before mutating
its owner. See `examples/exclusive_reference_move.lim`. References need no
mandatory destruction at function exit, and passing a reference directly to a
function is a call-duration reborrow rather than a handle transfer.

A derived field reference also suspends overlapping parent access through
function calls. Moving the child into another aggregate, or moving and restoring
its holder through pinned storage, does not erase that restriction. Calls may
use the child's own reference; explicitly release the child holder before
lending the parent again. `examples/reference_parent_call.lim` demonstrates
that order, and `tests/ui/call-suspended-parent.lim` shows a rejected parent call.

The same access restriction applies when a function returns the child reference,
directly or inside an aggregate. A returned call reborrow retains the referent's
loan even if its temporary parent handle is released; it does not require that
handle's storage to stay alive. See `examples/returned_reference_parent.lim` for
a returned reference carried out of a labeled loop and used after parent-handle
cleanup. `tests/ui/call-returned-parent.lim` rejects lending the parent again
while its returned child is live.

Struct types are not constructors. Create a value with `#struct-literal`, or
write a named free-standing constructor function that returns one. Every field
must be supplied exactly once; fields may appear in any order, and omitted
fields are not defaulted:

```lisp library
(#struct Point () ((x #u64) (y #u64)))
(#let point Point
  (#struct-literal Point
    ((y 22u64) (x 20u64))))
```

Unknown, duplicate, or missing fields are compile-time errors. A type name in
call position, such as `(Point 20u64 22u64)`, is rejected; give constructor
functions distinct names such as `make-point`. The UI suite covers this
rejection in `tests/ui/type-as-constructor.lim`; it also pins the diagnostic
spans for positional calls, generic function declarations, and
angle-bracket generic call syntax in `tests/ui/positional-call.lim`,
`tests/ui/generic-function.lim`, and `tests/ui/generic-angle-call.lim`.

Aggregate projections can be updated with `#set-index`, `#set-field`, and
`#set-payload`:

```lisp syntax
(#set-index values 0u64 10u64)
(#set-field point x 11u64)
(#set-field pair 1 12u64)
(#set-payload choice Move 0 5i32)
```

Mutable slices use a separate type and constructors: `(#slice-mut #u64)`,
`#borrow-slice-mut array` to borrow a full mutable array, or
`#borrow-slice-mut array start end` to select a half-open range.
`#slice-mut-of` converts an existing mutable array reference, `#slice-mut-idx` provides exclusive
element access, and `#slice-mut-split view at` to consume a view and produce
two disjoint halves. The split point is a checked `#usize` index; an index
greater than the length traps, and the halves cover `[0, at)` and `[at, len)`.
Views are linear: splitting consumes the parent, and overlapping mutable loans
or access through the original array are rejected while a view is live. Each
half must itself be consumed (for example, passed to a function or explicitly
`#forget`-ted). Mutable slices can be returned when their inferred provenance
comes from a function argument; a view of a local array cannot escape.

`(#borrow (#deref reference))` and `(#borrow-mut (#deref reference))`
explicitly reborrow the existing referent without loading or moving it.
Exclusive reborrowing requires an exclusive parent. A pinned parent produces
a pinned reborrow; this syntax cannot remove the pin guarantee. Scoped borrow
forms accept the same dereferenced places.

Pinning a mutable slice **holder** does not pin its backing elements. An
exclusive reference to that holder, including `(#pin-ref-mut (#slice-mut T))`,
can reborrow a range through `(#slice-mut-range (#deref holder) start end)`
without extracting or moving the holder. A shared holder reference cannot
grant this exclusive access. The resulting range still borrows the original
backing storage and must end before conflicting access to that storage.

`(#slice-mut-range parent start end)` reborrows an existing mutable slice
handle: a named handle or an exclusive, variable-rooted aggregate field/tuple
slot such as `(#get holder view)`. Owned aggregate projections require a
mutable owner; projections through a shared reference and temporary receiver
expressions are rejected. It does not consume the parent. Parent access,
transfer and destruction are suspended until the child is released. Nested views
retain the original backing storage's lifetime and physical offsets. Unrelated
aggregate slots remain usable while a field's child is live. All range
constructors check `start <= end <= length` and trap on failure; empty ranges are
valid. Constant disjoint regions permit independent exclusive borrows (or an
exclusive and a shared borrow). Dynamic bounds are conservatively overlapping;
use `#slice-mut-split` for two runtime-disjoint mutable regions. Direct array
borrowing accepts owned array places and array fields through ordinary references;
it does not silently convert an array reference or erase a pinned reference.

```lisp fragment=slices
(#let-mut values (#array #u64 4) (#array (#array #u64 4) 1u64 2u64 3u64 4u64))
(#let whole (#slice-mut #u64) (#borrow-slice-mut values))
(#let (#tuple left right)
  (#tuple (#slice-mut #u64) (#slice-mut #u64))
  (#slice-mut-split whole 2usize))
(#deref-set (#slice-mut-idx left 0usize) 17u64)
(#deref-set (#slice-mut-idx right 0usize) 25u64)
(#forget left)
(#forget right)
```

### Explicit enum construction

`#enum-literal` marks value construction, just as `#struct-literal` does for
structs. The variant declaration determines the concrete enum and payload
type; this does not introduce type inference. A payload expression is evaluated
once. A fieldless variant has no payload argument, while a variant carrying
unit explicitly receives `()`.

```lisp run=42
(#enum Answer () ((Answer.Value #u64) Answer.Empty))
(#fn main () #u64
  (#let answer Answer (#enum-literal Answer.Value 42u64))
  (#return (#match answer
    (#case (Answer.Value value) value)
    (#case Answer.Empty 0u64))))
```

Patterns do not use the construction keyword: `(Answer::Value value)` binds
the payload, and `Answer::Empty` tests the fieldless variant.

Local destructuring and `#let-else` support tuples, arrays, structs, and enum
patterns.  The `else` body must diverge, for example with `#return`,
`#break`, or `#panic`.

For a named enum variant, omit the redundant enum annotation and explicitly
delimit the failure body with `#else`:

```lisp run=42
(#enum Outcome () ((Outcome.Success #u64) Outcome.Failure))
(#fn main () #u64
  (#let-else (Outcome.Success answer) (Outcome.Success 42u64)
    (#else
      (#return 0u64)))
  (#return answer))
```

The named variant determines its declared owning enum; the value must have
that type. This is declaration lookup, not inference from the value. The value
is evaluated exactly once; use `#block` for a multi-statement computation.
Success bindings become available only after the statement, never inside
`#else`. Every failure path must return, break/continue an enclosing loop, or
otherwise diverge. Exiting a loop created inside `#else` is not sufficient:
it must be impossible to reach the following statement on failure.

`(#std)` provides `#generate #enum-project`, a generator rather than a runtime projection
keyword. It accepts
`(: enum Enum : variant Variant : payload Payload : mode ReferenceMode : name Name)`
and emits `Name::Some`/`Name::None` plus exactly one function, `Name::project`.
The required mode is `#ref`, `#ref-mut`, `#pin-ref`, or `#pin-ref-mut`. Both the
function's `source` parameter and its optional payload use that reference mode,
around `Enum` and `Payload` respectively. Its ordinary safe `#match` body uses
`#case-ref`, `#case-ref-mut`, `#case-pin`, or `#case-pin-mut` and returns `None`
on a different variant. No allocation, payload move, unchecked projection, or
asserting getter is involved. The optional reference retains its owner's loan
through ordinary `#let-else`:

```lisp run=42
(#std)
(#enum Task () ((Task.Work #u64) Task.Idle))
(#generate #enum-project (: enum Task : variant Task.Work : payload #u64 : mode #pin-ref-mut : name WorkProjection))
(#fn main () #u64
  (#let-mut task Task (Task.Work 42u64))
  (#let-else (WorkProjection.Some frame)
    (#call WorkProjection::project (: source (#pin-borrow-mut task)))
    (#else
      (#forget task)
      (#return 0u64)))
  (#let answer #u64 (#unsafe (#pin-read frame)))
  (#forget frame)
  (#forget task)
  (#return answer))
```
Destructuring consumes the aggregate and transfers each reference field's
borrow provenance to its corresponding binding. Nested struct, tuple, array,
and enum payload bindings retain their source loans; mutable fields cannot
alias an already active mutable loan. Returning a destructured reference is
allowed only when its origin outlives the function.

For borrowed fieldless tests, ignored payloads, or multiple borrowed failure
patterns, use ordinary borrowed `#match` cases directly. Projection helpers
require a payload-bearing variant with a referenceable payload type (not unit
or `#never`). Named exclusive input handles must be explicitly reborrowed if they
will be reused: `(#pin-borrow-mut (#deref parent))` or
`(#borrow-mut (#deref parent))`. There is no implicit reborrow in `#let-else`.
On a projection mismatch the optional contains no reference, allowing cleanup
of the owner in the failure branch. Another projection can be called there
to inspect a different variant. Unsafe unchecked payload projections remain
available only when the caller separately proves the active variant and
initialization; there is no asserting pinned-payload getter.

### Linear values and explicit cloning

Local values and function parameters are linear unless their type is plain-old
data or a reference. Built-in scalar values, raw pointers, and structs, enums,
tuples, or arrays whose fields/elements are all copyable are structurally
`Copy`; they can be used without consuming the binding. Resource-bearing
aggregates remain linear and must be consumed exactly once. A moved value
cannot be read or cloned again. Use `#clone` at the point where an additional
value is intended:

```lisp fragment=bindings
(#let count #u64 40u64)
(#let total #u64 (#u64::add-wrap (#clone count) count))
```

Assignments reinitialize mutable bindings only after the previous linear value
has been consumed. This also applies to linear struct fields, tuple slots,
enum payloads, and array elements: consume the old member before replacing it.
Replacing an aggregate member requires consuming all its linear leaves.
Copy members can be overwritten directly, even inside a linear owner. An
unknown array index cannot establish that a previously consumed element is
the element being replaced; use a constant index for checked linear updates.
`examples/linear_field_replacement.lim` demonstrates explicit consumption and
replacement of a resource-bearing field and returns 42.
A common update pattern moves the old value into the update
and installs the replacement:

```lisp fragment=bindings
(#let-mut count #u64 0u64)
(#set count (#u64::add-wrap count 1u64))
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

```lisp syntax
(#struct Buffer () ((allocation Allocation)))
(#fn Buffer::destroy ((buffer Buffer)) ()
  (Allocation::release (#get buffer allocation))
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

```lisp syntax
(#u64::add-wrap left right)
(#i32::sub-saturate left right)
(#u128::mul-wrap left right)
(#u128::div-wrap dividend divisor)
(#u128::rem-wrap dividend divisor)
```

The available integer arithmetic operations are `add`, `sub`, `mul`, `div`, and `rem`.
The modes are:

- `-wrap`: modular two's-complement or unsigned wrapping behavior;
- `-saturate`: clamp to the representable bounds.

There is no plain integer arithmetic spelling.  `#u64::add` and `#u128::div` are
rejected because they omit the overflow mode.

Floating-point arithmetic uses the type-qualified operator without an
overflow mode:

```lisp syntax
(#f64::add left right)
(#f32::div numerator denominator)
(#f64::rem left right)
```

The remaining type-qualified operator families are bitwise operations
(`&`, `|`, `^`, `!`, `<<`, `>>`), comparisons (`<`, `<=`, `>`, `>=`, `==`,
`!=`), and boolean short-circuit operations (`#bool::and`, `#bool::or`).  The
operand type must match the qualifier.  Shifts are checked against the width
of the left operand when the count is statically known; invalid dynamic
counts trap at runtime.

Unary negation is written, for example, as `#i128::sub-wrap value`.

All conversions are explicit with `#as`:

```lisp syntax
(#as value #u64)
```

Conversions cover integer, character, boolean, and floating-point scalar
representations subject to the type checker’s range rules.

## Expressions and builtin forms

Builtin forms are ordinary Lisp lists whose first symbol begins with `#`.
The table below is a quick, categorized overview. The alphabetic reference
that follows documents each reserved `#` form, its shape, a use in the
appropriate context, and its effect.

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

### Complete `#` builtin reference (alphabetical)

This is the crate's builtin index: each row gives the accepted shape, a small
example with its context, and its behavior. `Type`, `value`, and similar names
are placeholders; `...` means repetition and square brackets mean optional
syntax, not literal brackets. Fragment examples assume the named variables,
types, and functions are declared in their enclosing program. Runtime
statements belong inside a `#fn`, which must end with an explicit `#return`.
Generator expressions belong inside a `#gn` or `#gn-fn`, not a runtime
function. Operand markers and automatic cfg keys are included in the same
sorted list as forms. Typed operators are listed by family immediately below.

For example, a runtime binding, reference operation, and typed operator fit
inside a function like this. The parameter is mutable explicitly, the reference
is explicitly released before accessing its source, and the function returns
explicitly:

```lisp run=42
(#fn increment ((#mut value #u64)) #u64
  (#let reference (#ref-mut #u64) (#borrow-mut value))
  (#deref-set reference (#u64::add-wrap (#deref reference) 1u64))
  (#drop reference)
  (#return value))

(#fn main () #u64
  (#return (#call increment (: value 41u64))))
```

Generator expressions instead run at compile time. Here a helper checks its
syntax input, reports an error for a non-symbol, and emits a concrete type
alias. Quasiquote and unquote are syntax punctuation, not `#` builtins:

```lisp run=42
(#gn-fn alias-declaration (name)
  (#gn-if (#gn-symbol? name)
    `(#type ,name #u64)
    (#gn-error "alias name must be a symbol")))

(#gn make-alias (name)
  (#gn-list (#gn-call alias-declaration name)))

(#generate make-alias Answer)

(#fn main () Answer
  (#return 42u64))
```

| Builtin | Syntax | Example (context) | Meaning |
| --- | --- | --- | --- |
| `#abi-c` | `#abi-c` in `#extern-fn` | `(#extern-fn #abi-c abs ((value #i32)) #i32)` (declaration) | Selects the C calling convention; foreign calls use `#unsafe-call` inside `#unsafe`. |
| `#addr-of` | `(#addr-of local)` | `(#unsafe (#addr-of value))` (expression) | Takes a shared raw address of a scalar local; unsafe because later access is not checked. |
| `#addr-of-mut` | `(#addr-of-mut mutable-local)` | `(#unsafe (#addr-of-mut value))` (expression) | Takes a mutable raw address of a mutable scalar local. |
| `#alias` | `(#alias local-name = path.lim::declaration)` | `(#alias read = ./library/lib.lim::read)` (top level) | Binds a file-local spelling to an exact declaration identity. Preserves types, parameter labels, visibility, and ownership rules; the target may be wrapped in `#unstable`. |
| `#align-of` | `(#align-of Type)` | `(#align-of Point)` (expression) | Compile-time alignment in bytes for the Lim representation, or C layout of a `#repr-c` type. |
| `#arch` | `(#cfg-is #arch literal)` | `(#cfg-if (#cfg-is #arch x86_64) (#type Word #u64))` (top level) | Automatically populated target architecture cfg key; overridable with `--cfg arch=VALUE`. |
| `#array` | `(#array ElementType Length)` as a type; `(#array pattern...)` as a pattern | `(#let xs (#array #u8 2) (#array-of (#array #u8 2) 4u8 5u8))` (binding) | Names a fixed-length array type or destructures an array in a pattern; values are constructed with `#array-of`. |
| `#array-of` | `(#array-of ArrayType value...)` | `(#array-of (#array #u8 2) 4u8 5u8)` (expression) | Explicitly constructs a fixed array with its full type stated. |
| `#array-repeat` | `(#array-repeat value)` with an expected array type | `(#let xs (#array #u8 3) (#array-repeat 0u8))` (binding) | Fills every array slot with the given Copy value. |
| `#as` | `(#as value TargetType)` | `(#let n #u64 (#as byte #u64))` (expression) | Explicit scalar/enum conversion; narrowing integers truncate, and float-to-integer conversions trap when out of range. |
| `#asm` | `(#asm ResultType ((register value)...) "instructions")` | `(#unsafe (#asm #i64 ((rax 39usize)) "syscall"))` (expression) | Emits target assembly; unsafe, target-specific, and subject to the documented register/stack rules. |
| `#assert` | `(#assert condition)` | `(#assert (#u64::eq count 3u64))` (statement) | Traps if the condition is false. |
| `#atomic` | `(#atomic ScalarType)` | `(#let-mut counter (#atomic #u64) (#atomic-init #u64 0u64))` (type/binding) | Declares a supported atomic scalar wrapper type. |
| `#atomic-compare-exchange` | `(#atomic-compare-exchange reference expected desired success-order failure-order)` | `(#atomic-compare-exchange (#borrow counter) 0u64 1u64 #memory-acq-rel #memory-acquire)` (expression) | Strong compare-exchange; returns `(success, observed-value)`. |
| `#atomic-compare-exchange-weak` | `(#atomic-compare-exchange-weak reference expected desired success-order failure-order)` | `(#atomic-compare-exchange-weak (#borrow counter) 0u64 1u64 #memory-release #memory-relaxed)` (expression) | Weak compare-exchange; may fail spuriously and returns `(success, observed-value)`. |
| `#atomic-exchange` | `(#atomic-exchange reference desired order)` | `(#atomic-exchange (#borrow counter) 2u64 #memory-seq-cst)` (expression) | Atomically replaces the value and returns the previous value. |
| `#atomic-fetch-add` | `(#atomic-fetch-add reference addend order)` | `(#atomic-fetch-add (#borrow counter) 1u64 #memory-acq-rel)` (expression) | Atomically adds and returns the previous value. |
| `#atomic-init` | `(#atomic-init ScalarType initial-value)` | `(#atomic-init #u64 0u64)` (initializer) | Creates an atomic value; allowed scalar widths are documented in the atomics section. |
| `#atomic-load` | `(#atomic-load reference order)` | `(#atomic-load (#borrow counter) #memory-acquire)` (expression) | Atomically reads a value using an allowed load ordering. |
| `#atomic-store` | `(#atomic-store reference value order)` | `(#atomic-store (#borrow counter) 4u64 #memory-release)` (statement) | Atomically stores a value using an allowed store ordering. |
| `#await` | `(#await Protocol child-expression)`; explicit expanded forms can list the result/task types, variants and poll function | `(#let value #u64 (#await StepAwait child))` (inside `#generate #async-fn`, with a declared `StepAwait` bundle) | Marks a sequential suspension point for `#generate #async-fn` or `#generate #async-fn-pinned`; the protocol supplies concrete types and poll operations. Live captures are inferred from the continuation, and the form is not valid in an ordinary function. |
| `#block` | `(#block statement... final-expression)` | `(#block (#let x #u64 2u64) (#u64::add-wrap x 1u64))` (expression) | Evaluates statements in order and yields the final expression, or unit for a side-effect-only block. |
| `#bool` | `#bool` | `(#fn identity ((value #bool)) #bool (#return value))` (function signature) | Boolean scalar type; values are `true` and `false`. |
| `#borrow` | `(#borrow place)` or `(#borrow place body)` | `(#let r (#ref #u64) (#borrow value))` (binding) | Creates a shared reference, or scopes a shared borrow around a body. |
| `#borrow-mut` | `(#borrow-mut place)` or `(#borrow-mut place body)` | `(#let r (#ref-mut #u64) (#borrow-mut value))` (binding) | Creates an exclusive mutable reference, or scopes a mutable borrow around a body. |
| `#borrow-slice` | `(#borrow-slice array-place)` or `(#borrow-slice array-place start end)` | `(#let view (#slice #u64) (#borrow-slice values 1usize 3usize))` (binding) | Explicitly borrows a full array or checked half-open range as an immutable slice; retains the owner's lifetime without allocation. Bounds are #usize. |
| `#borrow-slice-mut` | `(#borrow-slice-mut mutable-array-place)` or `(#borrow-slice-mut mutable-array-place start end)` | `(#let view (#slice-mut #u64) (#borrow-slice-mut values 1usize 3usize))` (binding) | Exclusively borrows a full array or checked half-open range. Constant disjoint ranges can coexist; dynamic bounds conservatively overlap. |
| `#break` | `(#break)` or `(#break value)` | `(#loop (#break 42u64))` (expression in a function) | Exits the innermost loop, optionally supplying its expression value. |
| `#break-to` | `(#break-to label)` or `(#break-to label value)` | `(#break-to outer 42u64)` (labeled loop body) | Exits a named enclosing loop, optionally with a loop value. |
| `#call` | `(#call function (: name value : ...))` | `(#call add (: left 20u64 : right 22u64))` (expression) | Calls only a statically named safe function, even inside `#unsafe`; every argument is named and checked against its signature, with expressions evaluated in parameter declaration order. |
| `#call-graph` | `(#call-graph)` | `(#let trace (#slice #char) (#call-graph))` (function body) | Returns a borrowed character slice describing the actual caller chain, such as `main:8 -> work:5 -> report:2`. Each number is the executing line in that function, not its declaration or the parent's call line. Uses bounded, checked stack storage; the slice cannot escape its function. |
| `#capability` | `(#capability name Type ((operation (Args...) Result)...))` | `(#capability ordered #u64 ((less ((#ref #u64) (#ref #u64)) #bool)))` (declaration) | Declares a generator-time signature contract that a concrete type may satisfy. |
| `#case` | `(#case pattern body)` or `(#case pattern (#when guard) body)` | `(#case (Some x) x)` (inside `#match`) | Introduces one explicit match arm. |
| `#case-pin` | `(#case-pin Variant body)` or `(#case-pin (Variant binder) body)`, optionally with `(#when guard)` | `(#case-pin (Full payload) (#get payload value))` (inside a pinned `#match`) | Binds a shared `#pin-ref Payload` to an enum payload without moving it. Supports one payload binding or `_`; fieldless variants use their name, such as `(#case-pin Empty body)`. Works on shared or mutable pinned input. |
| `#case-pin-mut` | `(#case-pin-mut Variant body)` or `(#case-pin-mut (Variant binder) body)`, optionally with `(#when guard)` | `(#case-pin-mut (Full payload) (#pin-set-field payload value 42u64))` (inside a pinned `#match`) | Binds an exclusive `#pin-ref-mut Payload`; the match input must be exclusively pinned. Supports one payload binding or `_`; fieldless variants use their name, such as `(#case-pin-mut Other body)`. |
| `#case-ref` | `(#case-ref Variant body)` or `(#case-ref (Variant binder) body)`, optionally guarded | `(#case-ref (Full payload) (#get payload value))` (inside shared-reference `#match`) | Binds a shared `#ref Payload` without moving it; fieldless variants use their name. |
| `#case-ref-mut` | `(#case-ref-mut Variant body)` or `(#case-ref-mut (Variant binder) body)`, optionally guarded | `(#case-ref-mut (Full payload) (#get payload value))` (inside exclusive-reference `#match`) | Binds an exclusive `#ref-mut Payload`; requires mutable input and follows ordinary aliasing rules. |
| `#cfg-and` | `(#cfg-and condition...)` | `(#cfg-and (#cfg-is #os linux) (#cfg-is #arch x86_64))` (cfg condition) | Combines conditions with logical AND; requires at least one condition. |
| `#cfg-else` | `(#cfg-else form...)` | `(#cfg-else (#fn fallback () () (#return ())))` (last `#cfg-if` branch) | Supplies forms when the preceding `#cfg-if` condition is false. |
| `#cfg-if` | `(#cfg-if condition form... [(#cfg-else form...)])` | `(#cfg-if (#cfg-is #os linux) (#fn os-call () () (#return ())))` (top level) | Includes only the selected top-level forms before imports and semantic checks. |
| `#cfg-is` | `(#cfg-is #key literal)` | `(#cfg-is #feature fast)` (cfg condition) | Compares a configured key to a symbol, string, or integer literal. |
| `#cfg-not` | `(#cfg-not condition)` | `(#cfg-not (#cfg-is #debug enabled))` (cfg condition) | Negates one cfg condition. |
| `#cfg-or` | `(#cfg-or condition...)` | `(#cfg-or (#cfg-is #os linux) (#cfg-is #os macos))` (cfg condition) | Combines conditions with logical OR; requires at least one condition. |
| `#char` | `#char` | `(#fn identity ((value #char)) #char (#return value))` (function signature) | Unicode scalar value type, distinct from UTF-8 byte type `#u8`. |
| `#clone` | `(#clone value)` | `(#let second Buffer (#clone first))` (statement/expression) | Explicitly duplicates a Copy value or invokes the concrete type's `Type-clone` function. |
| `#const` | `(#const name Type value)` | `(#const LIMIT #u64 16u64)` (top level) | Declares an immutable compile-time constant with an explicit type. |
| `#continue` | `(#continue)` | `(#while false (#continue))` (function body) | Starts the next iteration of the innermost loop. |
| `#continue-to` | `(#continue-to label)` | `(#continue-to outer)` (labeled loop body) | Starts the next iteration of a named enclosing loop. |
| `#debug-assert` | `(#debug-assert condition)` | `(#debug-assert (#u64::lt length capacity))` (statement) | Currently identical to `#assert`: evaluates its condition and traps on false, regardless of cfg settings. |
| `#deref` | `(#deref reference)` | `(#return (#deref r))` (expression) | Reads through a Lim reference. |
| `#deref-set` | `(#deref-set mutable-reference value)` | `(#deref-set r 7u64)` (statement) | Writes through a mutable Lim reference. |
| `#distributed-enum` | `(#distributed-enum Name (properties...))` | `(#distributed-enum Error ())` (top level) | Declares an enum whose variants are collected after generator expansion; the central declaration owns its properties. |
| `#drop` | `(#drop value)` | `(#drop resource)` (statement) | Explicitly discards a value without calling user destruction code. Dropping a reference-bearing place ends its loan and makes that place unusable; plain Copy scalars remain reusable. |
| `#enum` | `(#enum Name (properties...) ((Variant [discriminant] [PayloadType])...))` | `(#enum Maybe (#repr-c) ((Some #u64) None))` (top level) | Declares a concrete enum; each variant has zero or one payload, and properties may include `#linear` and `#repr-c`. Use a named struct for multiple fields. |
| `#enum-contribute` | `(#enum-contribute EnumName (Variant [PayloadType]))` | `(#enum-contribute Error (ReadFailure #u32))` (top level) | Adds one variant to a distributed enum. Identical variants deduplicate; conflicting definitions fail with source locations. |
| `#enum-literal` | `(#enum-literal Variant [payload])` | `(#let result Maybe (#enum-literal Some 42u64))` (function body, with `Some` declared as a `Maybe` variant carrying `#u64`) | Constructs a concrete enum value. Payload variants require exactly one correctly typed expression; fieldless variants omit it. Patterns retain `(Variant binding)` or the fieldless variant name, without this keyword. |
| `#export` | `(#export name...)` | `(#export Counter counter-new counter-destroy)` (in `lib.lim`) | Exposes declarations outside the nearest directory library. Struct representation remains private; exporting an enum exposes all variants and requires publicly accessible payload types. Individual variant exports are rejected. |
| `#extern-fn` | `(#extern-fn #abi-c name (: arg Type : ...) ReturnType)`; the parameter list may also use nested pairs | `(#extern-fn #abi-c c_abs (: value #i32) #i32)` (top level) | Declares a C-ABI external function. Calling foreign functions uses the platform linker and is outside the direct-syscall-only standard library. |
| `#f32` | `#f32` | `(#fn identity ((value #f32)) #f32 (#return value))` (function signature) | 32-bit IEEE 754 floating-point scalar type. |
| `#f64` | `#f64` | `(#fn identity ((value #f64)) #f64 (#return value))` (function signature) | 64-bit IEEE 754 floating-point scalar type. |
| `#fn` | `(#fn name (: arg Type : ...) ReturnType body...)`; the parameter list may also use nested pairs | `(#fn add (: a #u64 : b #u64) #u64 (#return (#u64::add-wrap a b)))` (top level) | Declares a monomorphic function with explicit parameter/return types and body. |
| `#for` | `(#for init condition step body...)` | `(#for (#let-mut i #u64 0u64) (#u64::lt i 4u64) (#set i (#u64::add-wrap i 1u64)) (#set sum (#u64::add-wrap sum i)))` (statement) | Runs an explicitly structured init/condition/step loop. |
| `#for-range` | `(#for-range (name Type) start end body...)` | `(#for-range (i #u64) 0u64 4u64 (#set sum (#u64::add-wrap sum i)))` (statement) | Evaluates start, then end, once and iterates the typed, half-open range `[start, end)`. |
| `#forget` | `(#forget value)` | `(#forget raw-pointer)` (statement) | Discards a value without cleanup; use after explicit resource release. Forgetting a reference-bearing place ends its loan and makes that place unusable; plain Copy scalars remain reusable. Lim never inserts destructors. Task handles/results cannot be forgotten. |
| `#generate` | `(#generate generator arguments...)` | `(#generate #optional (: type #u64 : name Number))` (top level) | Expands a generator into inspectable, cached Lim declarations. Arguments are literal syntax, with named lists for builtin generators. |
| `#generated-context` | `(#generated-context ((producer "name") (definition-module "path") (definition-file "path") (invocation-module "path") (invocation-file "path")))` | `(#generated-context ((producer "/lib/lib.lim::make") (definition-module "/lib/lib.lim") (definition-file "/lib/lib.lim") (invocation-module "<global>") (invocation-file "/app/main.lim")))` (compiler-generated file header) | Records definition and invocation file identities and permission boundaries for generated-file private access. Validated against the expansion/cache key; forbidden in handwritten source and generator-produced forms. |
| `#get` | `(#get aggregate field-or-index)` | `(#get point x)` or `(#get pair 0)` (expression) | Projects a struct field or tuple element. |
| `#get-payload` | `(#get-payload enum variant index)` | `(#get-payload result Error 0)` (expression) | Projects a statically selected enum payload field. |
| `#gn` | `(#gn name (name-or-(name capability...)...) body)` | ``(#gn make-alias (name) `((#type ,name #u64)))`` (top level) | Declares an interpreted compile-time syntax generator. Each declaration binds one syntax parameter, not a destructuring pattern; arguments are literals/syntax, not runtime values. |
| `#gn-call` | `(#gn-call function syntax-arg...)` | `(#gn-call make-alias name target)` (generator body) | Calls a `#gn-fn` helper during generator interpretation. |
| `#gn-equal` | `(#gn-equal syntax-a syntax-b)` | `(#gn-equal item expected)` (generator expression) | Tests structural equality of immutable generator syntax values. |
| `#gn-error` | `(#gn-error message)` where `message` evaluates to string syntax | `(#gn-error "unsupported element type")` (generator expression) | Stops generation with a source-associated explanatory diagnostic; non-string syntax is rejected. |
| `#gn-first` | `(#gn-first list)` | `(#gn-first members)` (generator expression) | Returns the first element of a non-empty syntax list. |
| `#gn-fn` | `(#gn-fn name (parameter...) body)` | `(#gn-fn identity (value) value)` (top level) | Declares a reusable generator-time function with one syntax-producing body. |
| `#gn-for-each` | `(#gn-for-each name syntax-list body)` | `(#gn-for-each field fields (#gn-list (#gn-symbol "#type") field #u64))` (generator body) | Maps one syntax-producing body over a syntax list; returns a list of results and is the bounded iteration primitive. |
| `#gn-gensym` | `(#gn-gensym string-hint)` | `(#gn-gensym "task")` (generator expression) | Evaluates a string hint and returns a fresh syntax symbol. The hint must be one non-keyword ordinary identifier; generated names use the reserved `lim.gensym.` prefix and cannot be forged or changed by source, `#gn-symbol`, or `#gn-symbol-append`. |
| `#gn-get` | `(#gn-get named-syntax key [fallback])` | `(#gn-get (: type #u64 : name PinnedU64) type)` (generator expression) | Returns a literal value from a list of key/value syntax pairs. Rejects malformed pairs and duplicate keys; a missing key errors unless a lazily evaluated fallback is supplied. |
| `#gn-if` | `(#gn-if condition then-value else-value)` | `(#gn-if (#gn-equal kind sortable) yes no)` (generator expression) | Selects a syntax value based on a generator boolean. |
| `#gn-length` | `(#gn-length syntax-list)` | `(#gn-length fields)` (generator expression) | Returns the number of elements in a syntax list. |
| `#gn-list` | `(#gn-list syntax...)` | `(#gn-list a b)` (generator expression) | Constructs an immutable syntax list. |
| `#gn-list?` | `(#gn-list? syntax)` | `(#gn-list? value)` (generator expression) | Tests whether a syntax value is a list. |
| `#gn-rest` | `(#gn-rest list)` | `(#gn-rest fields)` (generator expression) | Returns a list containing all but the first element. |
| `#gn-symbol` | `(#gn-symbol string-literal)` | `(#gn-symbol "#type")` (generator expression) | Constructs one symbol syntax value from a string literal, including builtin names; rejects malformed text and compiler-reserved gensym names. |
| `#gn-symbol-append` | `(#gn-symbol-append symbol string-or-symbol)` | `(#gn-symbol-append PinnedFrame "read")` (generator expression) | Joins the base and literal suffix with `::`, producing `PinnedFrame::read`, and checks that the result parses as exactly one symbol. Used for concrete generated type and function names. |
| `#gn-symbol?` | `(#gn-symbol? syntax)` | `(#gn-symbol? value)` (generator expression) | Tests whether a syntax value is a symbol. |
| `#gn-variant` | `(#gn-variant enum-type string-or-symbol)` | `(#gn-variant Result "Ok")` (generator expression) | Constructs the variant identifier `Result.Ok`, requiring an uppercase enum type and uppercase variant suffix. The emitted enum declaration still verifies the owner and payload type. |
| `#i128` | `#i128` | `(#fn identity ((value #i128)) #i128 (#return value))` (function signature) | Signed 128-bit integer scalar type. |
| `#i16` | `#i16` | `(#fn identity ((value #i16)) #i16 (#return value))` (function signature) | Signed 16-bit integer scalar type. |
| `#i32` | `#i32` | `(#fn identity ((value #i32)) #i32 (#return value))` (function signature) | Signed 32-bit integer scalar type. |
| `#i64` | `#i64` | `(#fn identity ((value #i64)) #i64 (#return value))` (function signature) | Signed 64-bit integer scalar type. |
| `#i8` | `#i8` | `(#fn identity ((value #i8)) #i8 (#return value))` (function signature) | Signed 8-bit integer scalar type. |
| `#if` | `(#if condition then [else])` | `(#return (#if ready 1u64 0u64))` (expression) | Selects an expression by a boolean; without `else`, the then branch must be unit. |
| `#if-let` | `(#if-let pattern Type value then [else])` | `(#if-let (Some x) Maybe maybe x 0u64)` (expression) | Tests a typed pattern and scopes its bindings to the successful branch. |
| `#index` | `(#index array usize-index)` | `(#index values 1usize)` (expression) | Reads an array element with a checked index. |
| `#isize` | `#isize` | `(#fn identity ((value #isize)) #isize (#return value))` (function signature) | Signed integer scalar type with the target's native pointer width. |
| `#label` | `(#label name loop)` | `(#label outer (#while condition (#continue-to outer)))` (statement) | Names an enclosing `#while`, `#loop`, or `#for` for targeted control flow. |
| `#let` | `(#let pattern-or-name Type value)` | `(#let count #u32 0u32)` (function body) | Declares an immutable local with an explicit type. |
| `#let-else` | `(#let-else variant-pattern value (#else statements...))`; typed aggregate/failure-pattern form: `(#let-else pattern Type value fallback...)` | `(#let-else (Some x) maybe (#else (#return 0u64)))` (function body) | Destructures on success. A named variant fixes its owning enum without a repeated type annotation. Every else path must exit before subsequent success code. |
| `#let-mut` | `(#let-mut name-or-pattern Type value)` | `(#let-mut count #u32 0u32)` (function body) | Declares a mutable local with an explicit type. |
| `#linear` | Property in `(#struct Name (#linear) fields)` or `(#enum Name (#linear) variants)` | `(#struct FileHandle (#linear) ((descriptor #u64)))` (top level) | Forces the declared struct or enum to be linear; also inherited by aggregates that own linear fields or payloads. |
| `#linux-syscall` | `(#linux-syscall ResultType number (arg...))` | `(#unsafe (#linux-syscall #i64 39usize ()))` (expression) | Emits a raw Linux x86-64 syscall instruction with up to six machine-word arguments and unmodified negative-errno results. |
| `#literal` | `(#literal NumericType literal)` | `(#let n #u16 (#literal #u16 42))` (expression) | Gives an integer/float literal an explicit numeric type. |
| `#loop` | `(#loop body...)` | `(#return (#loop (#break 42u64)))` (function returning `#u64`) | Repeats indefinitely until broken; a break value makes it value-producing. |
| `#match` | `(#match value arms...)` | `(#match maybe (#case (Some x) x) (#case None 0u64))` (expression) | Performs an exhaustive match. Borrowed and pinned enum references use their corresponding `#case-ref`, `#case-ref-mut`, `#case-pin`, or `#case-pin-mut` arms; ordinary `#case` is allowed only as `(#case _ body)` fallback. |
| `#memory-acq-rel` | `#memory-acq-rel` | `(#atomic-fetch-add r 1u64 #memory-acq-rel)` (ordering operand) | Selects acquire-release ordering for read-modify-write atomics. |
| `#memory-acquire` | `#memory-acquire` | `(#atomic-load r #memory-acquire)` (ordering operand) | Selects acquire ordering where permitted. |
| `#memory-relaxed` | `#memory-relaxed` | `(#atomic-load r #memory-relaxed)` (ordering operand) | Selects relaxed ordering with no synchronization ordering. |
| `#memory-release` | `#memory-release` | `(#atomic-store r 1u64 #memory-release)` (ordering operand) | Selects release ordering where permitted. |
| `#memory-seq-cst` | `#memory-seq-cst` | `(#atomic-load r #memory-seq-cst)` (ordering operand) | Selects sequentially consistent ordering. |
| `#mut` | `(#mut parameter Type)` | `(#fn advance ((#mut count #u64)) #u64 (#set count 1u64) (#return count))` (parameter list) | Marks a function parameter mutable; local mutable bindings use `#let-mut`. |
| `#offset-of` | `(#offset-of ReprCType field)` | `(#offset-of Header payload)` (expression) | Computes a field's offset in the declared C layout; requires a `#repr-c` struct. |
| `#opaque` | `(#opaque StructName)` | `(#struct Token () ((slot #u64))) (#opaque Token)` (top level) | Restricts construction, field access, and cloning of a linear struct to its defining source module; external code can use its public functions. The annotation must appear in the same source module as the concrete struct. |
| `#or` | `(#or pattern pattern...)` | `(#case (#or Red Blue) 1u64)` (pattern) | Matches any listed alternative; alternatives must bind consistently. |
| `#os` | `(#cfg-is #os literal)` | `(#cfg-if (#cfg-is #os linux) (#type Fd #i32))` (top level) | Automatically populated OS cfg key; overridable with `--cfg os=VALUE`. |
| `#panic` | `(#panic)` | `(#if failed (#panic) ())` (expression) | Traps and never returns. |
| `#parameter-of` | `(#parameter-of FUNCTION PARAMETER-NAME)` inside #proof-requires-validation | `(#theorem safe (#proof-requires-validation entry (#parameter-of validate user) (#parameter-of perform user)))` (procedural theorem declaration) | Selects an existing parameter of the named function; introduces no theorem binding. Accepted only as a validation descriptor; old bare pairs are rejected. Unlike #parameter, this is a reference rather than a binder. |
| `#pin` | `(#pin initialized-local)` | `(#let view (#pin-ref-mut Node) (#pin node))` (expression) | Exclusively pins an initialized `#let-mut` local. Permanently prevents moving or assigning that local, even after forgetting the reference; explicit cleanup and then `#forget` end its lifetime in place. Rejects temporaries, projections, and reference variables. |
| `#pin-borrow` | `(#pin-borrow place)` | `(#let pinned (#pin-ref Node) (#pin-borrow node))` (expression) | Creates a shared pinned reference to a local or projected field place. Pinning a linear local permanently prevents moving it, even after derived views end; Copy referents retain ordinary loan-duration restrictions. |
| `#pin-borrow-mut` | `(#pin-borrow-mut place)` | `(#let pinned (#pin-ref-mut Node) (#pin-borrow-mut node))` (expression) | Creates an exclusive pinned reference; whole-referent replacement is forbidden, and normal exclusive-borrow rules apply. |
| `#pin-get-payload-unchecked` | `(#pin-get-payload-unchecked pinned-enum-reference variant)` | `(#let payload (#pin-ref #u64) (#unsafe (#pin-get-payload-unchecked slot Full)))` (expression) | Unsafe shared pinned payload projection without a runtime variant-tag check. The caller proves the variant is active and the payload initialized; loan origins, lifetimes and native layout are retained. |
| `#pin-get-payload-unchecked-mut` | `(#pin-get-payload-unchecked-mut mutable-pinned-enum-reference variant)` | `(#let payload (#pin-ref-mut #u64) (#unsafe (#pin-get-payload-unchecked-mut slot Full)))` (expression) | Unsafe exclusive pinned payload projection without a runtime variant-tag check. Requires a mutable pinned reference and the same active-variant/initialization proof as the shared form; it does not waive aliasing or pinning rules. |
| `#pin-own` | `(#pin-own TargetType)` | `(#let owner (#pin-own #u64) (#unsafe (#pin-own-of pointer 42u64)))` (type) | Linear pointer-sized owner of stationary heap storage. Moving the owner does not move the pointee or invalidate its views. It cannot be cloned; forgetting it leaks the allocation. |
| `#pin-own-borrow` | `(#pin-own-borrow owner-or-reference [allocator-reference])` | `(#let view (#pin-ref #u64) (#pin-own-borrow owner allocator))` (expression) | Borrows the allocation, independently of the owner's stack address. An optional allocator anchor remains borrowed for the view's lifetime, even after moving or forgetting the owner. |
| `#pin-own-borrow-mut` | `(#pin-own-borrow-mut mutable-owner-or-reference [allocator-reference])` | `(#let view (#pin-ref-mut #u64) (#pin-own-borrow-mut owner))` (expression) | Exclusively borrows stationary heap storage. Requires a mutable owner binding or reference; rejects overlapping retained views. |
| `#pin-own-of` | `(#pin-own-of mutable-pointer initializer)` | `(#let owner (#pin-own #u64) (#unsafe (#pin-own-of pointer 42u64)))` (expression) | Consumes an initializer into aligned, uniquely owned writable storage using Lim's native layout, then adopts it as stationary. The caller ensures sufficient space, validity until release, and no raw-pointer aliases that move or free it. Stored references and nested owning pins retain their lifetime provenance; allocation does not extend those lifetimes. |
| `#pin-ptr-borrow` | `(#pin-ptr-borrow pinned-anchor pointer)` | `(#unsafe (#pin-ptr-borrow pinned pointer))` (expression) | Unsafe shared pointer borrow tied to a pinned-reference anchor; returns a pinned reference and preserves anchor provenance. The caller proves pointer validity and address stability for the anchor lifetime. |
| `#pin-ptr-borrow-mut` | `(#pin-ptr-borrow-mut pinned-mut-anchor mutable-pointer)` | `(#unsafe (#pin-ptr-borrow-mut pinned pointer))` (expression) | Unsafe exclusive pointer borrow tied to a mutable pinned-reference anchor; returns a mutable pinned reference. The caller proves validity, stability, and unique access. |
| `#pin-read` | `(#pin-read pinned-reference)` | `(#unsafe (#pin-read pinned))` (expression) | Reads a pinned referent by value. Unsafe because the caller must prevent aliasing and must not duplicate ownership of linear data. |
| `#pin-ref` | `(#pin-ref TargetType)` | `(#let pinned (#pin-ref Node) (#pin-shared node))` (type) | Shared reference to stationary storage, distinct from an ordinary reference. Forgetting a local pin reference does not unpin the original local. |
| `#pin-ref-mut` | `(#pin-ref-mut TargetType)` | `(#let pinned (#pin-ref-mut Node) (#pin-borrow-mut node))` (type) | Exclusive pinned-reference type; it cannot be used to replace the complete referent. |
| `#pin-release` | `(#pin-release owner)` | `(#let pointer (#ptr-mut #u64) (#unsafe (#pin-release owner)))` (expression) | Consumes the owning heap pin after in-place cleanup, returning its pointer for deallocation. Retained pointee views block release, including through helper calls. Unsafe: untracked pointers and address-sensitive cleanup remain the caller's responsibility. |
| `#pin-set-field` | `(#pin-set-field pinned-reference field copy-or-shared-reference-value)` | `(#pin-set-field pinned state 2u32)` (statement) | Replaces one scalar/fieldless-enum or shared-reference struct field through a mutable pinned reference. The field loan is checked independently; it does not move or replace the pinned struct. |
| `#pin-share` | `(#pin-share unique-owner)` | `(#let shared (#pin-shared-own Node) (#pin-share owner))` (expression) | Converts uniquely owning pinned storage to shared reference-counted pinned ownership. Consumes the unique owner; no additional unsafe block is required. |
| `#pin-share-clone` | `(#pin-share-clone reference-to-shared-owner)` | `(#let clone (#pin-shared-own Node) (#unsafe (#pin-share-clone (#borrow shared))))` (expression) | Clones a shared pinned owner. Unsafe: the caller must uphold the strong-count invariants; Lim's Rc wrapper checks the count before incrementing it. |
| `#pin-shared` | `(#pin-shared initialized-local)` | `(#let view (#pin-ref Node) (#pin-shared node))` (expression) | Shared-pins an initialized mutable or immutable local. Permanently prevents moving or assigning that local, including Copy locals and after forgetting the reference. Rejects temporaries, projections, and reference variables. |
| `#pin-shared-borrow` | `(#pin-shared-borrow shared-owner-or-reference [allocator-anchor])` | `(#let view (#pin-ref Node) (#pin-shared-borrow shared))` (expression) | Creates a shared pinned view of the allocation. An optional allocator anchor is retained for the view's lifetime. |
| `#pin-shared-borrow-mut` | `(#pin-shared-borrow-mut mutable-shared-owner-or-reference [allocator-anchor])` | `(#let view (#pin-ref-mut Node) (#unsafe (#pin-shared-borrow-mut shared allocator)))` (expression) | Creates an exclusive pinned view and requires a mutable owner binding or mutable reference. The optional anchor keeps that mutable owner borrow active, preventing clones while exclusivity is relied on. Unsafe: the caller must establish unique strong ownership and no conflicting views. |
| `#pin-shared-own` | `(#pin-shared-own TargetType)` | `(#let shared (#pin-shared-own Node) (#pin-share owner))` (type) | Linear, movable strong-owner handle for stationary pinned storage. It is single-threaded, cannot be cloned with ordinary `#clone`, and has no weak-owner counterpart. |
| `#pin-shared-release` | `(#pin-shared-release shared-owner)` | `(#let pointer (#ptr-mut Node) (#unsafe (#pin-shared-release shared)))` (expression) | Consumes a shared owner and returns its allocation pointer; it does not check the strong count. Unsafe: the caller must prove this is the final owner, destroy all views, run final in-place cleanup, and deallocate only afterward. |
| `#pin-write` | `(#pin-write mutable-pinned-reference value)` | `(#unsafe (#pin-write pinned replacement))` (expression) | Replaces a pinned referent in place. Unsafe: the caller must prove no live derived references are invalidated and preserve ownership of the replaced value. |
| `#platform` | `(#cfg-is #platform literal)` | `(#cfg-if (#cfg-is #platform linux) (#type Fd #i32))` (top level) | Automatically populated platform cfg key, initially the host OS; overridable with `--cfg platform=VALUE`. |
| `#println` | `(#println (#borrow string))` | `(#assert (#i64::eq (#println (#borrow message)) 0i64))` (expression) | Writes a borrowed `String`'s UTF-8 bytes and a newline; returns zero on success or negative errno on failure. It does not consume the string; a failed text write may be partial and skips the newline. Available after top-level `(#std)`. |
| `#proof-allocation` | `#proof-allocation in an effect list` | `(#proof-no-effects helper (#proof-allocation))` (proof proposition) | Conservative allocation effect; a tag for #proof-no-effects, not a standalone proposition. |
| `#proof-and` | `(#proof-and proposition...)` | `(#proof-and true (#proof-eq 1u8 1u8))` (proof proposition) | Conjunction of one or more propositions; unsupported operands still fail. |
| `#proof-asm` | `#proof-asm in an effect list` | `(#proof-no-effects helper (#proof-asm))` (proof proposition) | Inline assembly or conservatively unknown assembly effects; a tag for #proof-no-effects, not a standalone proposition. |
| `#proof-calls-before` | `(#proof-calls-before entry required action)` | `(#proof-calls-before main validate commit)` (proof proposition) | Every modeled action entry must follow a completed required call on the same execution; does not require a call to occur. |
| `#proof-calls-directly` | `(#proof-calls-directly caller callee)` | `(#proof-calls-directly main helper)` (proof proposition) | Checks one structural edge between actual function identities, independent of execution feasibility. |
| `#proof-calls-transitively` | `(#proof-calls-transitively caller callee)` | `(#proof-calls-transitively main helper)` (proof proposition) | Checks a nonempty structural path of one or more call edges; equal endpoints require an actual cycle, and reachability does not establish execution feasibility. |
| `#proof-calls-when` | `(#proof-calls-when entry observed expected action)` | `(#proof-calls-when main validate false commit)` (proof proposition) | Forbids an action call and the selected Boolean observation from co-occurring in either order; executes the observed function's checked body and uses its actual symbolic result. |
| `#proof-contract` | `(#proof-contract function precondition postcondition)` | `(#proof-contract identity true (#proof-eq (#proof-result) value))` (proof proposition) | Quantifies declared parameters, runs the checked implementation under the precondition, checks the postcondition, and returns a closed Boolean; nested contracts or universal claims are unsupported. |
| `#proof-eq` | `(#proof-eq left right)` | `(#proof-eq 1u8 1u8)` (proof proposition) | Modeled structural value equality; reference identity comparison is unsupported. |
| `#proof-external` | `#proof-external in an effect list` | `(#proof-no-effects helper (#proof-external))` (proof proposition) | External or conservatively unknown execution effects; a tag for #proof-no-effects, not a standalone proposition. |
| `#proof-for-all` | `(#proof-for-all ((name Type)...) proposition)` | `(#proof-for-all ((x #u8)) (#proof-eq x x))` (proof proposition) | Universally quantifies supported symbolic values without sampling and discharges them to a closed Boolean; nested universal or contract claims are unsupported. |
| `#proof-global-write` | `#proof-global-write in an effect list` | `(#proof-no-effects helper (#proof-global-write))` (proof proposition) | Direct or possible indirect writes to global storage; a tag for #proof-no-effects, not a standalone proposition. |
| `#proof-implies` | `(#proof-implies antecedent consequence)` | `(#proof-implies (#u8::lt x 255u8) (#proof-no-overflow #u8::add-wrap x 1u8))` (quantified proof proposition) | Checks the consequence under the antecedent; does not separately establish satisfiability of the antecedent. |
| `#proof-io` | `#proof-io in an effect list` | `(#proof-no-effects helper (#proof-io))` (proof proposition) | IO or conservatively unknown IO effects; a tag for #proof-no-effects, not a standalone proposition. |
| `#proof-loop-limit` | `(#proof-loop-limit literal-limit proposition)` | `(#proof-loop-limit 64 (#proof-contract count true true))` (proof proposition) | Scopes the symbolic loop bound to 1 through 1024; feasible execution beyond the limit fails closed. |
| `#proof-mutation` | `#proof-mutation in an effect list` | `(#proof-no-effects helper (#proof-mutation))` (proof proposition) | Observable reference, aggregate, array, or global writes; local scalar reassignment is ignored; a tag for #proof-no-effects, not a standalone proposition. |
| `#proof-no-effects` | `(#proof-no-effects function (effect-tag...))` | `(#proof-no-effects helper (#proof-io #proof-mutation))` (proof proposition) | Requires a nonempty effect-tag list and transitive conservative absence of each effect. |
| `#proof-no-overflow` | `(#proof-no-overflow integer-builtin left right)` | `(#proof-no-overflow #u8::add-wrap 1u8 2u8)` (proof proposition) | Requires an existing native integer add/subtract/multiply builtin with a valid wrap or saturate mode; checks representability independently of that mode. |
| `#proof-not` | `(#proof-not proposition)` | `(#proof-not false)` (proof proposition) | Logical negation; an unsupported or unproved operand remains an error. |
| `#proof-old` | `(#proof-old expression)` | `(#proof-old (#deref value))` (contract expression) | Evaluates using the saved contract entry state, including entry referent contents; requires a contract. |
| `#proof-only-unsafe` | `(#proof-only-unsafe entry (allowed...))` | `(#proof-only-unsafe main (trusted-helper #ptr-read))` (proof proposition) | Inspects unsafe primitives outside explicitly allowed function boundaries or builtin spellings; does not establish memory safety. |
| `#proof-or` | `(#proof-or proposition...)` | `(#proof-or false true)` (proof proposition) | Disjunction of one or more propositions; unsupported operands still fail. |
| `#proof-permutation` | `(#proof-permutation left right)` | `(#proof-permutation before after)` (proof proposition) | Checks equal length and selected element multiplicities of fixed arrays or modeled slices, including mixed array/slice operands. Backing arrays are limited to 64 elements; matching element types are required even for empty ranges, and equality must be modeled. |
| `#proof-requires-validation` | `(#proof-requires-validation entry (#parameter-of validator parameter) (#parameter-of action parameter))` | `(#theorem safe (#proof-requires-validation process (#parameter-of validate user) (#parameter-of perform user)))` (top-level procedural theorem) | Universally checks that every reachable action entry from the explicit root has an earlier completed true validation for the same referenced storage; overlapping object or transitive dependency writes invalidate it. Explicit #parameter-of selectors reference existing function parameters with matching resolved referent types and introduce no binding; unsupported execution and exhausted budgets are unproved. |
| `#proof-result` | `(#proof-result)` | `(#proof-eq (#proof-result) value)` (contract postcondition) | Denotes the returned value of the contract subject; valid only in its postcondition. |
| `#proof-sorted` | `(#proof-sorted collection comparator)` | `(#proof-sorted values less)` (proof proposition) | Accepts fixed arrays or modeled slices over backing arrays of at most 64 elements; requires a named, safe checked Boolean comparator with two parameters matching the element type even for empty ranges, and checks it is false on selected reversed adjacent pairs. Ordinary call, trap and budget checks still apply. Does not establish comparator laws or stability. |
| `#proof-stack-at-most` | `(#proof-stack-at-most function target-string literal-bytes)` | `(#proof-stack-at-most main "x86_64-sysv" 4096)` (proof proposition) | Bounds reachable generated-code stack use for an explicit target; currently only x86_64-sysv, with unknown stack behavior rejected. |
| `#proof-unique` | `(#proof-unique collection)` | `(#theorem distinct (#proof-unique (#array-of (#array #u8 2) 1u8 2u8)))` (top-level theorem) | Checks pairwise inequality of selected fixed-array or modeled-slice elements using modeled equality. Empty and singleton ranges are unique. Backing arrays are limited to 64 elements; this is proof-only and does not mutate or deduplicate the collection. |
| `#proof-unsafe` | `#proof-unsafe in an effect list` | `(#proof-no-effects helper (#proof-unsafe))` (proof proposition) | Unsafe primitives or unknown unsafe execution; a known function unsafe-call flag alone is not a primitive; a tag for #proof-no-effects, not a standalone proposition. |
| `#proof-using` | `(#proof-using (theorem-name...) proposition)` | `(#proof-using (identity-contract) (#proof-contract identity true (#proof-eq (#proof-result) (#proof-old value))))` (proof proposition) | Adds explicit verified direct contract theorem dependencies; names resolve to theorem declarations, the list introduces no bindings, and an empty list selects no dependencies. |
| `#proof-validated` | `(#proof-validated (#parameter-of validator parameter) object)` inside a loop invariant predicate | `(#theorem safe (#proof-with-invariants ((process again (#proof-implies checked (#proof-validated (#parameter-of validate user) user)) remaining)) (#proof-requires-validation process (#parameter-of validate user) (#parameter-of perform user))))` (validation claim loop invariant) | Positively asserts lower-bound validation evidence for the current same-storage object. Accepted only in a positive loop-invariant predicate of `#proof-with-invariants` inside a `#proof-requires-validation` claim, and only for that claim's exact validator descriptor. Evidence must hold at loop entry and be preserved; writes to the object or its dependencies and a failing revalidation revoke it. This is proof-only metadata and has no runtime behavior. |
| `#proof-with-invariants` | `(#proof-with-invariants ((function label predicate unsigned-rank)...) proposition)` | `(#proof-with-invariants ((count loop-body (#u8::le i n) (#u8::sub-wrap n i))) (#proof-contract count true true))` (proof proposition) | Checks labeled-loop invariant entry, preservation, and strictly decreasing unsigned rank under restricted induction semantics. |
| `#ptr` | `(#ptr PointeeType)` | `(#let p (#ptr #u8) (#ptr-null (#ptr #u8)))` (type) | Immutable raw-pointer type; dereference and address operations require unsafe context. |
| `#ptr-address` | `(#ptr-address pointer)` | `(#ptr-address (#ptr-null (#ptr #u8)))` (expression) | Converts a raw pointer to its machine address as `#usize` without dereferencing it; useful for checking syscall error-pointer results before access. |
| `#ptr-borrow` | `(#ptr-borrow reference-anchor pointer)` | `(#unsafe (#ptr-borrow owner pointer))` (expression) | Creates a shared reference tied to an existing reference's inferred borrow lifetime; caller must uphold pointer validity. |
| `#ptr-borrow-mut` | `(#ptr-borrow-mut mutable-reference-anchor mutable-pointer)` | `(#unsafe (#ptr-borrow-mut owner pointer))` (expression) | Creates an exclusive reference tied to an anchor; caller must prove unique valid access. |
| `#ptr-is-null` | `(#ptr-is-null pointer)` | `(#if (#ptr-is-null p) 0u64 1u64)` (expression) | Safely tests a raw pointer for null. |
| `#ptr-mut` | `(#ptr-mut PointeeType)` | `(#let p (#ptr-mut #u8) (#ptr-null (#ptr-mut #u8)))` (type) | Mutable raw-pointer type. |
| `#ptr-null` | `(#ptr-null PointerType)` | `(#ptr-null (#ptr #u8))` (expression) | Constructs a typed null raw pointer. |
| `#ptr-offset` | `(#ptr-offset pointer usize-index)` | `(#unsafe (#ptr-offset p 2usize))` (expression) | Advances by pointee elements with checked address arithmetic; requires unsafe context and does not check allocation bounds. |
| `#ptr-read` | `(#ptr-read pointer)` | `(#unsafe (#ptr-read p))` (expression) | Reads the pointee value without bounds/validity checks. |
| `#ptr-write` | `(#ptr-write mutable-pointer value)` | `(#unsafe (#ptr-write p 7u8))` (statement) | Writes the pointee without bounds/validity checks. |
| `#range` | `(#range lower upper)` | `(#case (#range 1u32 4u32) 1u64)` (pattern) | Matches integer/character values in an inclusive interval: both endpoints match. |
| `#ref` | `(#ref TargetType)` | `(#let r (#ref #u64) (#borrow value))` (type/binding) | Shared-reference type. |
| `#ref-mut` | `(#ref-mut TargetType)` | `(#let r (#ref-mut #u64) (#borrow-mut value))` (type/binding) | Mutable-reference type. |
| `#ref-ptr` | `(#ref-ptr reference)` | `(#let p (#ptr-mut Node) (#ref-ptr pinned))` (expression) | Safely extracts a thin ordinary or pinned reference's raw pointer with the same pointee and mutability. Lends the input handle without moving or duplicating it; the pointer retains no loan and does not extend the pointee lifetime or pinning guarantee. Slices are rejected. Raw memory access and pointer-to-reference borrowing still require unsafe context and valid lifetime/aliasing proofs. Raw pointers do not automatically implement Send or Sync. |
| `#repr-c` | Property in `(#struct Name (#repr-c) fields)` or `(#enum Name (#repr-c) variants)` | `(#struct Header (#repr-c) ((tag #u8) (length #u32)))` (top level) | Requests C layout metadata for layout queries; does not make arbitrary Lim values FFI-safe. |
| `#require-generated` | `(#require-generated Name GeneratorName (CompanionName...))`; companions may be omitted | `(#require-generated Work::Frame #async-fn-pinned (Work::Poll Work::poll))` (top level) | Requires one actual invocation of the named generator to have produced all listed identifiers; checked after expansion with compiler-recorded ancestry. |
| `#return` | `(#return value)` | `(#return ())` (function body) | Exits a function with its explicitly typed result; void functions must return `()`. |
| `#send` | `(#unsafe-impl #send Type)` | `(#struct Handle () ((raw (#ptr #u8)))) (#unsafe-impl #send Handle)` (top level) | Unsafe promise that ownership of the type may be transferred between threads. Without an override, Send is derived structurally. |
| `#set` | `(#set name value)` | `(#set count (#u32::add-wrap count 1u32))` (statement) | Reassigns a mutable local. |
| `#set-field` | `(#set-field aggregate field-or-index value)` | `(#set-field point x 4u64)` (statement) | Mutates a struct field or tuple slot; a linear member must first be consumed. |
| `#set-index` | `(#set-index array index value)` | `(#set-index values 0usize 9u8)` (statement) | Mutates an array element after a bounds check; a linear element needs proven prior consumption at a constant index. |
| `#set-payload` | `(#set-payload enum variant index value)` | `(#set-payload choice Data 0 9u64)` (statement) | Replaces one payload field of a mutable enum value; a linear payload must first be consumed. |
| `#size-of` | `(#size-of Type)` | `(#return (#size-of Point))` (expression) | Returns the compile-time size in bytes for the Lim or selected C layout. |
| `#slice` | `(#slice ElementType)` | `(#let view (#slice #u8) (#slice-of (#borrow bytes)))` (type) | Immutable dynamically sized view over an array borrow. |
| `#slice-idx` | `(#slice-idx slice usize-index)` | `(#deref (#slice-idx view 0usize))` (expression) | Bounds-checks and returns a shared reference to an element. |
| `#slice-len` | `(#slice-len slice)` | `(#slice-len view)` (expression) | Returns the immutable slice length as `#usize`. |
| `#slice-mut` | `(#slice-mut ElementType)` | `(#let view (#slice-mut #u8) (#slice-mut-of (#borrow-mut bytes)))` (type) | Mutable dynamically sized view retaining an exclusive array borrow. |
| `#slice-mut-idx` | `(#slice-mut-idx slice usize-index)` | `(#deref-set (#slice-mut-idx view 0usize) 9u8)` (expression) | Bounds-checks and returns a mutable reference to an element. |
| `#slice-mut-len` | `(#slice-mut-len slice)` | `(#slice-mut-len view)` (expression) | Returns the mutable slice length as `#usize`. |
| `#slice-mut-of` | `(#slice-mut-of mutable-array-reference)` | `(#slice-mut-of (#borrow-mut bytes))` (expression) | Creates a mutable slice over an array while retaining its exclusive borrow. |
| `#slice-mut-range` | `(#slice-mut-range mutable-slice-place start end)` | `(#let child (#slice-mut #u8) (#slice-mut-range parent 1usize 3usize))` (binding) | Reborrows a checked half-open mutable subrange of a named handle or exclusive aggregate slot without consuming the parent; parent access and release are suspended while the child is live. Bounds are #usize. |
| `#slice-mut-split` | `(#slice-mut-split slice usize-index)` | `(#let pair (#tuple (#slice-mut #u8) (#slice-mut #u8)) (#slice-mut-split view 2usize))` (expression) | Consumes a mutable slice and returns two disjoint mutable slices. |
| `#slice-of` | `(#slice-of shared-array-reference)` | `(#slice-of (#borrow bytes))` (expression) | Creates a full immutable slice while retaining the source borrow. |
| `#slice-range` | `(#slice-range slice start end)` | `(#slice-range view 1usize 3usize)` (expression) | Creates a checked half-open immutable subslice `[start,end)`. |
| `#static` | `(#static name Type value)` | `(#static answer #u64 42u64)` (top level) | Declares storage with static lifetime; accesses must be inside `#unsafe`. |
| `#std` | `(#std)` | `(#std)` (top level) | Loads the embedded standard String and stdout modules into the program. This is explicit opt-in and works without a source checkout. |
| `#struct` | `(#struct Name (properties...) ((field Type)...))` | `(#struct Point () ((x #u64) (y #u64)))` (top level) | Declares a concrete struct; properties may include `#linear` and `#repr-c`. |
| `#struct-literal` | `(#struct-literal Type ((field value)...))` | `(#struct-literal Point ((x 1u64) (y 2u64)))` (expression) | Constructs a struct by explicitly naming every field; no defaults are applied. |
| `#sync` | `(#unsafe-impl #sync Type)` | `(#struct Handle () ((raw (#ptr #u8)))) (#unsafe-impl #sync Handle)` (top level) | Unsafe promise that sharing references to this type across threads is sound. Without an override, Sync is derived structurally. |
| `#syntax` | `(#syntax Name (syntax ...))` | `(#syntax StepAwait (#u64 Step StepPending StepReady step-poll))` (top level) | Declares an immutable literal syntax bundle with a unique identifier; no values are evaluated and no types are inferred. |
| `#syntax-splice` | `(#syntax-splice Name)` | `(#await (#syntax-splice StepAwait) step)` (inside an async function) | Inserts a named bundle's elements into the surrounding list before ordinary checking and async lowering; unknown names and cycles are errors. |
| `#target` | `(#cfg-is #target literal)` | `(#cfg-if (#cfg-is #target x86_64-unknown-linux-gnu) (#type Word #u64))` (top level) | Automatically populated canonical target triple cfg key; overridable with `--cfg target=VALUE`. |
| `#theorem` | `(#theorem name proposition)` | `(#theorem add-zero (#proof-for-all ((value #u8)) (#proof-eq (#u8::add-wrap value 0u8) value)))` (top level) | Checks a symbolic program proposition after expansion and ordinary safety validation. Quantified claims cover every modeled input and feasible path; unsupported semantics and exhausted verification budgets fail. Emits no runtime code. |
| `#thread-task` | `(#thread-task TaskType worker [spawn-signature join-signature])` | `(#thread-task ReadTask read-value)` (generated declaration) | Declares a concrete task type and its named worker; generated builtins are compiler-managed. |
| `#thread-task-join` | `(#thread-task-join FunctionName ((arg Type)...) ReturnType)` | `(#thread-task-join ReadTask::join ((task ReadTask)) ReadTask::JoinResult)` (generated signature) | Internal generated function signature for joining a task and retrieving its result. |
| `#thread-task-spawn` | `(#thread-task-spawn FunctionName ((arg Type)...) ReturnType)` | `(#thread-task-spawn ReadTask::spawn ((input #u64)) ReadTask::SpawnResult)` (generated signature) | Internal generated function signature for creating a worker task. |
| `#tuple` | `(#tuple Type...)` as a type; `(#tuple TupleType value...)` as a value; `(#tuple pattern...)` as a pattern | `(#let pair (#tuple #u64 #bool) (#tuple (#tuple #u64 #bool) 3u64 true))` (binding) | Declares, constructs, or destructures a fixed tuple. |
| `#type` | `(#type Name Type)` | `(#type UserId #u64)` (top level) | Declares a transparent alias; uses remain strongly and statically typed. |
| `#u128` | `#u128` | `(#fn identity ((value #u128)) #u128 (#return value))` (function signature) | Unsigned 128-bit integer scalar type. |
| `#u16` | `#u16` | `(#fn identity ((value #u16)) #u16 (#return value))` (function signature) | Unsigned 16-bit integer scalar type. |
| `#u32` | `#u32` | `(#fn identity ((value #u32)) #u32 (#return value))` (function signature) | Unsigned 32-bit integer scalar type. |
| `#u64` | `#u64` | `(#fn identity ((value #u64)) #u64 (#return value))` (function signature) | Unsigned 64-bit integer scalar type. |
| `#u8` | `#u8` | `(#fn identity ((value #u8)) #u8 (#return value))` (function signature) | Unsigned 8-bit integer scalar type. |
| `#unreachable` | `(#unreachable)` | `(#case impossible (#unreachable))` (expression) | Marks a path that must never execute; execution traps. |
| `#unsafe` | `(#unsafe expression)` | `(#unsafe (#ptr-read p))` (expression) | Marks a region allowed to contain raw memory, static access, assembly, raw syscalls, and `#unsafe-call`; does not permit unsafe callees through `#call`. |
| `#unsafe-call` | `(#unsafe-call function (: name value : ...))` | `(#unsafe (#unsafe-call read-byte (: pointer p)))` (expression) | Calls only a statically named unsafe or external function and requires an enclosing `#unsafe` block. Uses the same named arguments, parameter declaration evaluation order, signature checks, and ownership rules as `#call`; rejects safe callees. |
| `#unsafe-fn` | `(#unsafe-fn name ((arg Type)...) ReturnType body...)` | `(#unsafe-fn read-byte ((p (#ptr #u8))) #u8 (#return (#unsafe (#ptr-read p))))` (top level) | Declares caller safety obligations: calls use `#unsafe-call` inside `#unsafe`, and raw operations in the body still need explicit unsafe blocks. |
| `#unsafe-impl` | `(#unsafe-impl property Type)` | `(#unsafe-impl #send NativeHandle)` (top level) | Unsafely overrides a type's structural thread-safety property; this is an author promise. |
| `#unstable` | `(#unstable path.lim::declaration)` | `(#alias inspect = (#unstable ./library/private.lim::inspect))` (alias target) | Explicitly bypasses entry-point/export restrictions for the selected declaration. Does not grant struct field access or waive ordinary safety checking. |
| `#usize` | `#usize` | `(#fn identity ((value #usize)) #usize (#return value))` (function signature) | Unsigned integer scalar type with the target's native pointer width. |
| `#variant-is` | `(#variant-is enum-reference Variant)` | `(#let is-some #bool (#variant-is value Some))` (expression) | Tests an enum reference's active variant without consuming the reference or enum; accepts ordinary or pinned shared/exclusive references. It does not statically refine later payload projections, which retain their runtime active-variant check. |
| `#when` | `(#when boolean-expression)` | `(#case (Some x) (#when (#u64::gt x 0u64)) x)` (inside `#case`) | Adds a guard to a match arm; guarded arms do not alone establish exhaustiveness. |
| `#while` | `(#while condition body...)` | `(#while (#u64::lt i 4u64) (#set i (#u64::add-wrap i 1u64)))` (statement) | Repeats while its boolean condition is true. |
| `#while-let` | `(#while-let pattern value body...)` | `(#while-let (Some x) next (#set total x))` (statement) | Evaluates the value once per iteration, matches that same value, and runs the body while the pattern succeeds. A mismatch exits without running the body. Inside async functions, the scrutinee may remain synchronous while the body suspends. |
| `#word-forget` | `(#word-forget LayoutType mutable-word-slice)` | `(#unsafe (#word-forget Pair words))` (statement) | Explicitly retires reference provenance in the flat words occupied by `LayoutType` without loading a typed value or reading, zeroing, or freeing its backing bytes. The numeric buffer stays initialized; a typed write is needed before recovering forgotten reference slots. Requires unsafe, sufficient capacity, and unique mutable access. The caller must have destroyed or deliberately forgotten any owned contents; separate escaped and neighboring loans remain checked. |
| `#word-read` | `(#word-read ValueType word-slice)` | `(#let value Pair (#unsafe (#word-read Pair words)))` (expression) | Unsafe owned read from a slice of `#u64` in flat Lim value-word layout, not packed native bytes. The caller proves sufficient capacity, a valid initialized representation, and no duplicated linear ownership. No initialization tags are added or checked. |
| `#word-take` | `(#word-take ValueType mutable-word-slice)` | `(#let value Pair (#unsafe (#word-take Pair words)))` (expression) | Unsafe ownership transfer from flat `#u64` word storage. Requires a mutable slice and retires the selected backing words' reference provenance while preserving it in the returned value. Bytes are loaded without zeroing or runtime initialization flags. The caller proves capacity, valid initialized representation and unique ownership, as for `#word-read`; reference-bearing rereads require a new typed write. |
| `#word-view` | `(#word-view ReferenceType word-slice)` or `(#word-view (#slice[-mut] #u64) reference)` | `(#let view (#ref Pair) (#unsafe (#word-view (#ref Pair) words)))`; `(#let words (#slice #u64) (#unsafe (#word-view (#slice #u64) view)))` (expressions) | Unsafe reinterpretation between flat value words and ordinary or pinned references. Exclusive results require exclusive sources. A reference-to-words view has exactly the referent's flat word count and requires flat-word backing, not packed native bytes. The caller proves capacity, initialized representation and, for a pinned view, permanent address stability. Source lifetime and alias anchors remain checked, but arbitrary numeric words do not establish provenance for stored references. |
| `#word-write` | `(#word-write ValueType mutable-word-slice value)` | `(#unsafe (#word-write Pair words pair))` (statement) | Consumes a value into flat `#u64` word storage without initialization flags. The caller proves capacity and unique writable access and consumes any previously owned contents before overwriting them. Source slice borrowing is still checked. |

#### Typed operator families (alphabetical)

The qualifier is part of the identifier, not a namespace. In this table,
`I` expands to each of `#i8`, `#i16`, `#i32`, `#i64`, `#i128`, `#isize`,
`#u8`, `#u16`, `#u32`, `#u64`, `#u128`, and `#usize`; `F` expands to
`#f32` or `#f64`. Both operands must match the qualifier. Examples are
expressions in a function body; the operator determines their result type.
Pipe characters in the table are escaped only for Markdown rendering.

| Family | Syntax | Example (context) | Meaning |
| --- | --- | --- | --- |
| `#F::add` | `(#F::add a b)` | `(#f64::add 2.0f64 3.0f64)` (expression) | Floating-point addition. |
| `#F::div` | `(#F::div a b)` | `(#f64::div 6.0f64 2.0f64)` (expression) | Floating-point division. |
| `#F::mul` | `(#F::mul a b)` | `(#f32::mul 2.0f32 3.0f32)` (expression) | Floating-point multiplication. |
| `#F::rem` | `(#F::rem a b)` | `(#f64::rem 5.0f64 2.0f64)` (expression) | Floating-point remainder. |
| `#F::sub` | `(#F::sub a b)` or `(#F::sub a)` | `(#f32::sub 2.0f32)` (expression) | Floating-point subtraction or unary negation. |
| `#I::add-saturate` | `(#I::add-saturate a b)` | `(#u8::add-saturate 255u8 1u8)` (expression) | Addition clamped to the integer bounds. |
| `#I::add-wrap` | `(#I::add-wrap a b)` | `(#u8::add-wrap 255u8 1u8)` (expression) | Modular addition. |
| `#I::bit-and` | `(#I::bit-and a b)` | `(#u8::bit-and 3u8 1u8)` (expression) | Bitwise AND. |
| `#I::bit-or` | `(#I::bit-or a b)` | `(#u8::bit-or 2u8 1u8)` (expression) | Bitwise OR. |
| `#I::bit-xor` | `(#I::bit-xor a b)` | `(#u8::bit-xor 3u8 1u8)` (expression) | Bitwise XOR. |
| `#I::div-saturate` | `(#I::div-saturate a b)` | `(#i8::div-saturate -128i8 -1i8)` (expression) | Integer division; signed overflow clamps to the maximum. Zero divisor traps. |
| `#I::div-wrap` | `(#I::div-wrap a b)` | `(#i8::div-wrap -128i8 -1i8)` (expression) | Integer division; signed overflow wraps to the minimum. Zero divisor traps. |
| `#I::mul-saturate` | `(#I::mul-saturate a b)` | `(#u8::mul-saturate 200u8 2u8)` (expression) | Multiplication clamped to the integer bounds. |
| `#I::mul-wrap` | `(#I::mul-wrap a b)` | `(#u8::mul-wrap 200u8 2u8)` (expression) | Modular multiplication. |
| `#I::not` | `(#I::not value)` | `(#u8::not 0u8)` (expression) | Bitwise complement. |
| `#I::rem-saturate` | `(#I::rem-saturate a b)` | `(#i8::rem-saturate -128i8 -1i8)` (expression) | Remainder with explicit saturation mode; zero divisor traps. |
| `#I::rem-wrap` | `(#I::rem-wrap a b)` | `(#u64::rem-wrap 7u64 3u64)` (expression) | Remainder with explicit wrapping mode; zero divisor traps. |
| `#I::shl` | `(#I::shl value count)` | `(#u32::shl 1u32 3u32)` (expression) | Left shift; an out-of-width count is rejected or traps. |
| `#I::shr` | `(#I::shr value count)` | `(#i32::shr -8i32 1i32)` (expression) | Arithmetic right shift for signed types, logical for unsigned; count is checked. |
| `#I::sub-saturate` | `(#I::sub-saturate a b)` or `(#I::sub-saturate a)` | `(#u8::sub-saturate 0u8 1u8)` (expression) | Subtraction or negation clamped to the integer bounds. |
| `#I::sub-wrap` | `(#I::sub-wrap a b)` or `(#I::sub-wrap a)` | `(#i8::sub-wrap -128i8)` (expression) | Modular subtraction or negation. |
| `#T::eq` | `(#T::eq a b)` | `(#bool::eq true false)` (expression) | Equality returning bool; T is I, F, bool, or char. |
| `#T::ge` | `(#T::ge a b)` | `(#i32::ge 2i32 1i32)` (expression) | Greater than or equal, returning bool; T is I, F, bool, or char. |
| `#T::gt` | `(#T::gt a b)` | `(#char::gt #\b #\a)` (expression) | Greater than, returning bool; T is I, F, bool, or char. |
| `#T::le` | `(#T::le a b)` | `(#f32::le 1.0f32 2.0f32)` (expression) | Less than or equal, returning bool; T is I, F, bool, or char. |
| `#T::lt` | `(#T::lt a b)` | `(#u64::lt 1u64 2u64)` (expression) | Less than, returning bool; T is I, F, bool, or char. |
| `#T::ne` | `(#T::ne a b)` | `(#char::ne #\a #\b)` (expression) | Inequality returning bool; T is I, F, bool, or char. |
| `#bool::and` | `(#bool::and a b)` | `(#bool::and true false)` (expression) | Short-circuit AND; evaluates b only when a is true. |
| `#bool::bit-and` | `(#bool::bit-and a b)` | `(#bool::bit-and true false)` (expression) | Boolean AND that evaluates both operands. |
| `#bool::bit-or` | `(#bool::bit-or a b)` | `(#bool::bit-or true false)` (expression) | Boolean OR that evaluates both operands. |
| `#bool::bit-xor` | `(#bool::bit-xor a b)` | `(#bool::bit-xor true false)` (expression) | Boolean exclusive OR that evaluates both operands. |
| `#bool::not` | `(#bool::not value)` | `(#bool::not false)` (expression) | Logical negation. |
| `#bool::or` | `(#bool::or a b)` | `(#bool::or true false)` (expression) | Short-circuit OR; evaluates b only when a is false. |

Plain integer arithmetic such as `#u64::add` is rejected. There is no generic
`#T.op` builtin: expand the documented family to a concrete identifier.
User-defined cfg keys such as `#feature`, `#debug`, or `#backend` are not
additional builtins and are not automatically populated; set them with
`--cfg KEY=VALUE`. The `#generate` generators and quote/backtick reader syntax are
documented separately; they are not `#` builtins.

### Conditionals and blocks

An `#if` without an else branch must have unit type.  Value-producing
conditionals require both branches:

```lisp syntax
(#return (#if (#u64::gt value 0u64)
              value
              0u64))
```

`#block` permits statements in an expression position.  Its final expression
is its value; a block used only for side effects has unit type.

### Loops

Statement loops use `#break` without a value:

```lisp syntax
(#while (#u64::lt i 10u64)
  (#set i (#u64::add-wrap i 1u64)))
```

A loop expression has a value only when a reachable break supplies one:

```lisp run=42
(#fn main () #u64
  (#let result #u64 (#loop (#break 42u64)))
  (#return result))
```

An async `#while-let` may evaluate a synchronous scrutinee and suspend only
inside its matched body. The scrutinee is evaluated once per iteration; a
failed pattern does not start the body task. Payload values and references
needed after suspension are carried by the generated frame and retain normal
borrow checks. `examples/async_while_let_body.lim` demonstrates two Pending
iterations followed by Ready(42), without allocating a dynamic task.

The explicit `#for` form is:

```lisp syntax
(#for (#let-mut i #u64 0u64)
      (#u64::lt i 10u64)
      (#set i (#u64::add-wrap i 1u64))
  (#set total (#u64::add-wrap total i)))
```

Inside `#generate #async-fn`, a unit-returning await can be the step itself:

```lisp syntax
(#for () keep-going
      (#await () StepTask StepPoll.StepPending StepPoll.StepReady step-poll step-task)
  (#set keep-going false))
```

The step starts after the body and after `#continue`, but is skipped by
`#break` and a false condition. A Pending step resumes before the next
condition check. Direct body declarations remain in scope through the step,
including across a Pending step. That iteration's scope ends after the step,
or on a break/return; it does not extend through the next condition. Linear
body values still require explicit consumption, and references cannot escape
their referents' iteration scope. The condition may itself await. The explicit
`()` result type makes this an effect-only step; no user-maintained dummy binding is
required. Generated code contains an ordinary unit assignment, and still
undergoes normal type, ownership, and borrow checking.
See `examples/async_for_unit_step.lim` for a runnable Pending/Ready example
that exits with status 42.

An awaited condition can also be combined with a computed step, such as
arithmetic around an awaited value. Step operands are evaluated in source
order and are not reevaluated when a child reports Pending. Changes to
captured mutable values, including writes through explicitly borrowed places,
are returned by the generated iteration task. Terminal `#continue` runs the
step; terminal `#break` and `#return` skip it. See
`examples/async_for_computed_step.lim` for a runnable example.

A synchronous condition can also use an effect-only computed step, including
a `#call` with an awaited argument. For example:

```lisp syntax
(#for () (#u64::lt index 2u64)
  (#call advance
    (: next (#await #u64 StepTask StepPoll.StepPending StepPoll.StepReady step-poll step-task)
     : counter (#borrow-mut index)))
  ())
```

Operands before the await execute once, including their side effects. An
exclusive reference captured by the iteration is transferred into its child,
not duplicated in the parent's Pending state. The source owner remains
borrowed until Ready or explicit cancellation consumes the task. Conditional
and matched `#continue` execute the step; `#break` and `#return` skip it.
`examples/async_for_effect_step.lim` demonstrates Pending, Ready, an initially
false condition, and a break. These forms do not yet imply support for
arbitrary control transfers in async bodies.

Conditional early `#continue`, `#break`, and `#return` can precede later awaits
inside an iteration. The compiler keeps the remaining statements only on
fall-through paths, so skipped work is not evaluated or polled. Scoped branch
locals and match payloads remain unavailable after the branch; shadowing and
explicit consumption checks still apply. An early `#continue` in `#for` runs
the step before reevaluating the condition. `examples/async_early_continue.lim`
shows a first iteration skipping its body await and a later iteration resuming
that await before returning.

An awaited `#while` condition may itself await a task-producing dependency.
The dependency and condition run in order on each iteration, including the
final false condition. Child construction finishes before live captures are
saved, and Pending retries do not repeat construction side effects.
Conditional helpers return mutable updates with their logical result;
linear updated owners belong to the child until Ready restores them. See
`examples/async_condition_dependencies.lim`, which exits 43: three condition
constructions add one each, the first body is skipped by `#continue`, and
the second body adds 40 after suspension.

Likewise, a `#while-let` scrutinee can await a factory and then poll the task
that factory returns. Both awaits remain inside the iteration. A successful
pattern makes its explicitly typed payload available to the body, including
body helpers that suspend again; a mismatch skips every body await. Shared
references in those payloads retain their source loans while the frame is
Pending. Consuming the cancelled frame releases those loans. The native
`examples/async_while_let_dependencies.lim` exercises repeated conditions,
two body suspension points, and construction side effects (exit 40).

Tuple and array patterns, including aliases and nested aggregate patterns,
also obtain their captured field types from the declared layout. A suspended
match body may retain a shared-reference field without losing its source loan.
Ready helpers destructure mutable outputs into typed bindings before assigning
them back. See `examples/async_pattern_payloads.lim` for a tuple-payload match
whose bias is retained across a child await (exit 42).

`#for-range` is shorthand with a typed binding, start, and end.  Its bounds
are explicit and the range is half-open. Start is evaluated first, then end;
both are evaluated exactly once before iteration, including when either bound
awaits a child. Changing a variable used by a bound inside the body does not
change the captured endpoint. `#continue` and `#continue-to` do not evaluate
the bounds again. By contrast, `#for` evaluates its condition on each iteration.
See `examples/range_bounds_once.lim` and
`examples/async_range_bounds_once.lim` for side effects and suspended bounds:

```lisp syntax
(#for-range (i #u64) 0u64 10u64
  (#set total (#u64::add-wrap total i)))
```

Labels wrap statement loops with `#label`, and value-loop breaks can target an
outer value loop:

```lisp run=42
(#fn main () #u64
  (#return
    (#label outer
      (#loop (#break-to outer 42u64)))))
```

Recursive calls are rejected.  Mutual recursion is rejected as well.

## Patterns and matching

`#match` requires exhaustive coverage. Enums require every variant; scalar
booleans require both values. Integer literals and inclusive `#range` patterns
are combined to check coverage of the complete scrutinee type, including
`#u128` and `#i128`. Patterns may overlap or appear in any order; the first
matching arm wins. `_` supplies a wildcard. Character matches still require
a wildcard. Guarded arms do not contribute unconditional coverage.
Every arm must be explicitly introduced with `#case`. Enum payloads are
written as constructor patterns:

```lisp syntax
(#match value
  (#case (Some payload) payload)
  (#case None 0u64))
```

Tuple, struct, array, scalar, range, typed-literal, and `#or` patterns are
supported. Guards are placed between the pattern and body, using `#when`:

```lisp syntax
(#match value
  (#case (Some payload) (#when (#u64::gt payload 40u64)) payload)
  (#case (Some _) 0u64)
  (#case None 0u64))
```

No wildcard is needed when integer patterns cover the entire domain. This
example tests the inclusive boundary between two ranges:

```lim run=42
(#fn classify (: value #u8) #u64
  (#return (#match value
    (#case (#range 0u8 127u8) 0u64)
    (#case (#range 128u8 255u8) 42u64))))
(#fn main () #u64
  (#assert (#u64::eq (#call classify (: value 127u8)) 0u64))
  (#return (#call classify (: value 128u8))))
```

Destructuring uses the same aggregate pattern shapes:

```lisp syntax
(#let (#tuple left right) (#tuple #u64 #u64) pair)
```

The pattern syntax is checked against the explicitly declared type; bindings
are not inferred. When the matched value is a pinned enum reference, ordinary
`#case` is reserved for the wildcard fallback `(#case _ body)`. Every named
variant uses `#case-pin` or `#case-pin-mut`, including fieldless variants such
as `(#case-pin Empty body)`. The shared form binds a `#pin-ref` payload,
including when the input itself is mutable; the mutable form binds a
`#pin-ref-mut` and therefore requires exclusive input. Payload arms accept
only one binder or `_`. Guards, wildcard defaults, exhaustiveness, and
duplicate checks follow the usual match rules. The payload stays in its
original stack or heap slot, and returned payload references retain the
matched owner’s lifetime. Existing unsafe `#pin-write` and checked
`#pin-set-field` rules still apply inside an exclusive arm.

Ordinary references use `#case-ref` and `#case-ref-mut` to borrow enum
payloads without pinning the owner. The shared form binds `#ref Payload`; the
exclusive form binds `#ref-mut Payload` and requires mutable input. Each named
variant, including fieldless variants, uses the matching form. `#case _` is
the fallback, and borrowed and pinned forms cannot be mixed in one match.
Payload patterns accept one binder or `_`, without nested destructuring.
`examples/borrowed_cases.lim` is a runnable example.

All five case forms accept a sequence of body expressions, after the optional
`(#when condition)` guard. Multiple expressions lower to one `#block` in the
arm's scope; the last expression supplies its value. This does not introduce
implicit function returns or automatic destruction. For example:

```lisp syntax
(#case (Work::Poll.Pending pending)
  (#forget pending)
  0u64)
```

This is equivalent to `(#case (Work::Pending pending)
(#block (#forget pending) 0u64))`. A body is required even after a guard.

Async lowering can still conservatively reject an exclusive match receiver
returned by another function: its frame retains a conflicting parent reference
handle. This is a generator limitation, not a restriction on ordinary functions;
`async_generator_matches_reference_returned_by_call` records the pending case.

```lim run=42
(#enum Choice () ((Choice.Full #u64) Choice.Empty Choice.Other))
(#fn main () #u64
  (#let-mut choice Choice (Choice.Full 41u64))
  (#let observed #u64 (#match (#borrow choice)
    (#case-ref (Choice.Full payload) (#deref payload))
    (#case-ref Choice.Empty 0u64)
    (#case _ 0u64)))
  (#let updated #u64 (#match (#borrow-mut choice)
    (#case-ref-mut (Choice.Full payload) (#block (#deref-set payload 42u64) (#deref payload)))
    (#case-ref-mut Choice.Empty 0u64)
    (#case _ 0u64)))
  (#assert (#u64::eq observed 41u64))
  (#return updated))
```

```lim run=42
(#struct Payload () (: value #u64))
(#enum Choice () ((Choice.Full Payload) Choice.Empty))
(#fn main () #u64
  (#let-mut choice Choice (Choice.Full (#struct-literal Payload (: value 41u64))))
  (#let pin (#pin-ref-mut Choice) (#pin choice))
  (#let answer #u64 (#match pin
    (#case-pin-mut (Choice.Full payload)
      (#block
        (#pin-set-field payload value 42u64)
        (#get payload value)))
    (#case-pin-mut Choice.Empty 0u64)))
  (#forget pin)
  (#forget choice)
  (#return answer))
```

## Generated declarations

`#generate` marks a generated declaration. Compiler-provided generators take one
colon-prefixed list of named literal arguments. Keys may be written in any
order, but every required key must appear exactly once. User-defined `#gn`
generators retain their own positional literal interface. For example:

```lisp library
(#generate #optional (: type #u64 : name Maybe?))
(#generate #result (: ok #u64 : error #u32 : name Result))
```

`(#generate #optional (: type T : name Name))` always creates an enum with `Name-some`
and `Name-none`, plus the free-standing `Name-construct` constructor. When the
enum and its payload are Copy, it also creates:

- `Name-is-some`
- `Name-unwrap-or`

`(#generate #result (: ok Ok : error Err : name Name))` always creates an enum with
`Name-ok-value` and `Name-err-value`, plus the `Name-ok` and `Name-err`
constructors. When the enum and both payloads are Copy, it also creates:

- `Name-is-ok`;
- `Name-unwrap-or` and `Name-unwrap-err-or`.

The by-value predicate and fallback unwrap helpers discard values on some
paths, so they are omitted for linear payloads, exclusive references, and
explicitly linear generated enums. No implicit `#forget` is inserted. Use
explicit matching or [`#let-else` error propagation](error-propagation.md)
instead. AST expansion and inspectable generated sources use the same Copy
policy, whose declaration context is included in the generated-source cache.

Expansion is part of program parsing. Readable generated Lim sources for both
built-in and user-defined `#generate` invocations are stored as hash-named `.lim` files
under `.lim/generated/`. Serialized expansions and integrity metadata remain
in `.lim/cache/`, so `rg 'pattern' .lim/generated` searches only Lim code.
Their keys include the invocation, compiler version,
supported target, loaded imports, cfg values, and a deterministic fingerprint
of compiler Rust sources and build logic. User-generator execution also caches
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

## Direct file references and aliases

An explicit file reference has the spelling `./path/file.lim::declaration`.
The `.lim::` delimiter separates the path from the complete declaration name,
which may itself contain `::` or an enum variant's dot. Paths resolve relative
to the source file containing the reference. Canonical file identity and the
declaration name identify the target; two files may declare the same name.
No library source is copied or rewritten to add prefixes.

Bind a file-local spelling with `#alias`:

```text
(#alias allocate = ./allocator/lib.lim::allocate)
(#alias Value = ./values.lim::Value)
```

Calls may use an alias or a direct reference. Named argument labels keep the
callee's declared spelling. Aliases preserve type and function identity and
cannot shadow declarations, other aliases, or local bindings. Unused aliases
are checked too. Cyclic aliases and conflicting imported spellings are errors.
There are no wildcard or prefixing import forms. Every dependency is an explicit
file reference or alias; `#std` selects the compiler-provided standard prelude.

Files in the same nearest `lib.lim` boundary may refer to implementation files.
Cross-library references must target `lib.lim` and select an exported name.
The entry point can export aliases to declarations in its implementation files.
Exporting a struct alias keeps the representation opaque; exporting an enum
alias exposes its variants under the aliased type name.

For an intentional dependency on an implementation detail, wrap the target:

```text
(#alias inspect = (#unstable ./library/internal.lim::inspect))
```

`#unstable` bypasses the entry-point and export restrictions for that exact
declaration. It does not expose other declarations or struct representations.
Selecting an enum type includes that enum's variants, as for an enum export.
It does not remove type, borrow, linearity, or unsafe-call checks. Private
functions may rely on library invariants, so this escape hatch is a deliberate
dependency on an internal contract, not a promise that arbitrary calls are safe.

Generator definitions resolve their own references in their definition file.
Explicit `@name` inputs resolve in the caller's file before interpretation;
unmarked generator arguments remain literal syntax. Generated aliases contain
resolved file references and retain the validated definition/invocation context.
A generator may deliberately expose a declaration it can access by emitting an
alias; this grants access to that declaration, never to its struct fields or
unrelated private helpers. Forward generated targets are checked after expansion.
Generator cache identities include resolved references and loaded dependencies.
Fresh declarations belong to their source file. A resolved reference cannot be
used to declare a symbol in another file; generators should receive a separate
fresh local name for their outputs.
See `examples/file_access.lim` for two same-named functions in different files.

## Value representation and native backend

The established backend emits Intel-syntax x86-64 assembly and follows the explicit
`x86_64-sysv` target description. Scalar integer and pointer-sized ABI words use general
purpose registers; `#f32` and `#f64` values use SSE registers.  `#i128` and
`#u128` use two machine words.

An experimental `aarch64-linux` target (`aarch64-unknown-linux-gnu`) lowers
checked bodies directly through a separate A64 instruction encoder and writes
static Linux ELF internally. Its inspectable `.inst` listing contains resolved
instruction words and descriptions; no external assembler or linker is used.
Scalar integer arguments use AAPCS64 registers and aligned stack arguments.
Aggregates use Lim's internal indirect convention, not a foreign aggregate ABI.
The target deliberately rejects operations it does not yet implement; it is
not equivalent in coverage to x86-64. See [AArch64 testing](aarch64-testing.md)
for the supported subset, emulator execution and remaining acceptance matrix.
`--target` selects builtin cfg defaults independently of the host; explicit
`--cfg` values override those defaults regardless of argument order.

Tuples, arrays, structs, and enums remain value types.  Small aggregates can
be flattened through the native argument and result registers.  Larger
aggregates use compiler-generated caller storage at the ABI boundary and are
copied as value data. Aggregate operations do not implicitly expose their
storage addresses or permit layout reinterpretation; raw pointers remain
explicit values handled by the unsafe pointer operations described above.
Large struct-field and enum-payload projections copy directly into aggregate
storage, so the source value does not need to fit in the native value
registers. Enum payload reads check the active discriminant before copying.
References to local enums retain the stack-layout tag used to distinguish
their downward-growing storage from upward-growing static storage.

Zero-sized values such as `()` and empty structs/arrays occupy no value words.
The compiler computes each function’s maximum call depth after type checking.
Use `lim --stack-usage INPUT` to inspect a static upper bound for generated
code from `main` and each thread entry point, including frames, stack
temporaries, outgoing arguments, alignment, generated helpers, and the
limiting internal call chain. The analysis follows emitted control flow and
reports positive stack-growth loops as unbounded. Any reachable external or
indirect callee makes the total unknown; the report shows the known generated
portion and the unresolved callees. Runtime startup and external-library stack
use are excluded, so finite Lim call depth alone is not a guarantee against
stack overflow.

The report recognizes local assembly labels and follows both edges of each
conditional branch, including early returns and generated thread error paths.
It tracks frame-pointer save/restore operations and includes return-address
space for external calls in the known portion. Unsupported stack-pointer
updates or inconsistent frame-pointer states produce an analysis error instead
of a numeric bound. This analysis describes the emitted assembly; it does not
measure the operating system's available stack.

Division by zero, invalid dynamic shifts, failed assertions, `#panic`, and
`#unreachable` lower to runtime traps.  Intentional trap examples are kept
separate by the repository’s native sweep.

## Compiler pipeline

The library exposes these stages:

1. `lex` converts source into tokens with byte and line/column spans.
2. `parse` builds untyped S-expressions and preserves `#generate` as `Expr::Generate`.
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
When `#if` branches have different types, the incompatible branch value is
selected without confusing a similarly typed condition expression.
For `#match` result mismatches, span selection only considers arm values, not
the scrutinee or patterns.
Named-call argument type errors include the parameter name internally, allowing
the diagnostic to underline the responsible named value rather than the call.
Struct-literal field type errors similarly underline the named field value,
even when an earlier field has the same actual type.
Enum constructor payload type errors identify the failing payload position and
underline that argument.
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
Unknown worker parameter types are resolved to the worker signature even when
an unrelated earlier local has the same name.
Call safety errors for `#call` and `#unsafe-call` underline the callee; raw-pointer
operation errors underline the offending builtin name.
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
An explicit `#return` whose value does not match the function return type
underlines the returned expression.
Tuple and array constructor element type errors underline the specific
incompatible element, even when another element has the same actual type.
Aggregate constructor arity errors underline an extra value or the constructor
head when an element is missing; nested tuple mismatch coverage confirms the
inner expression does not steal the outer diagnostic span.
Borrow conflict spans select the accessed binding rather than a same-named
field selector, call callee, or named-argument label in the same expression.

The CLI renders errors with an available span or line/column as a source hunk
with an underline. The parsed source tree retains recursive spans, and the
type, ownership, borrow, unsafe, generator, and code-generation phases use
them where their checks identify a source expression. Statement-level checks
prefer their value expression over the enclosing statement when a more
precise token or projection is not available. In that case the diagnostic
uses the smallest retained expression or declaration span. The UI suite
requires each diagnostic fixture to assert an exact source fragment and
underline width, or a custom exact-alignment check, so future diagnostics keep
this source-location contract.
Diagnostic source hunks expand tabs at four-column stops before aligning the
underline, and account for common wide and combining Unicode characters, so
the displayed code and caret use the same columns. Lexer column positions count
Unicode scalar values rather than UTF-8 bytes.
Extremely long source lines are rendered as a bounded excerpt with ellipses;
the underline stays aligned to the original source column.
When a global constant expression contains a function call, its codegen
diagnostic highlights the nested `#call` form rather than the whole initializer.
Imported-source parsing retains lexer and parser spans directly, including
quoted tokens with internal whitespace and escaped quotes, instead of
reconstructing a one-character range from line and column.
UI regression tests verify exact caret columns for unknown identifiers,
recursive calls, and code-generation failures, including highlighted widths, as
well as checking their lines.
The UI rejection fixtures also pin type-as-constructor, positional-call,
generic declaration/call, missing-`#case`, and aggregate-layout-overflow
diagnostics (`tests/ui/{type-as-constructor,positional-call,generic-function,
generic-angle-call,match-missing-case,aggregate-layout-overflow}.lim`). The
aggregate overflow diagnostic covers the declaration and caps its underline
at the renderer's documented 80-column limit. Complete positive examples in
this reference are compiled through native assembly generation by
`tests/language_docs.rs`; stack-bound examples are additionally checked by the
stack-usage report tests, including the external-callee unknown-bound case.
Repeated moves of linear fields and array elements identify their repeated
`#get` or `#index` projections.
The UI tests also verify full unterminated-string spans and zero-width EOF
locations for incomplete lists. Each UI fixture must provide an exact
highlighted fragment or an explicit custom caret-alignment assertion.

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
atom          = symbol | integer | float | character | string | "#generate" ;
symbol        = identifier ;
identifier    = { letter | digit | "_" | "-" | "." | ":" | "@" | "?" | "!" | "+" | "*" | "/" | "<" | ">" | "=" | "&" | "|" | "^" } ;
```

Whitespace and semicolon-to-end-of-line comments may occur between tokens.
Builtin declaration and statement forms are the `#`-prefixed forms described
in the tables and sections above; arithmetic and comparison forms include
their type and overflow mode in the identifier. `#let`, `#let-mut`, `#borrow`,
`#borrow-mut`, `#return`, `#unsafe`, `#drop`, `#forget`, and `#clone` define ownership and
borrow behavior; `#cfg-*` is compile-time only; `#gn-*` is generator-time only;
and `#generate` declarations expand before ordinary parsing, type checking, and borrow
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
# Generated thread calls

Spawn and join are ordinary named calls, including when the compiler derives
their signatures from a short `#thread-task` declaration. Spawn uses the
worker's parameter names; join uses `task`. For example, write
`(#call Task::join (: task handle))`. Generated enum variants in
`#case` patterns retain their constructor syntax. There is no positional-call
exception for generated thread functions.
# Floating-point global evaluation

Float constants and static aggregate fields retain their declared f32/f64
bit representation. Each arithmetic operation rounds at its operand width,
including intermediate f32 results; it is not an integer conversion or a
single rounding at the end of an expression. Literal tokens must be finite,
but pure arithmetic can produce infinities and NaNs, as at runtime. Signed
zero is preserved. NaN payload bits are not a portable equality contract.
Pure float arithmetic, named constants, and supported constant conditionals
may initialize globals; calls and runtime effects remain forbidden, and
constant dependency cycles are errors. Reading or writing statics still
requires `#unsafe`.

### Typed word-memory loan inputs

A direct `#word-view` passed to a checked function has
physical layout geometry for owned field, tuple, array-index and enum-payload
projections. Consuming and restoring those values maps to the selected backing
word range rather than an opaque lifetime anchor. This does not establish
stored-reference provenance or permit a dereference through an untracked
reference. Unknown runtime coordinates, insufficient known slice extents and
opaque pointer anchors still cannot supply a physical consumption contract.

Writes by a checked helper through a direct mutable word view also map to the
actual backing offsets. They replace reference-slot metadata only with real
incoming loans and publish constructor facts from actual typed writes. Mutation
footprints use the projected word range, so neighboring cells retain their
facts. A projection through a stored reference addresses its external referent,
not the numeric word holding the pointer; it uses ordinary reference checking
instead of this owned-layout mapping. Unresolved coordinates, opaque anchors,
known-short slices and zero-width ownership identities are not strong writes.

`#word-write` records a value's actual contained-reference loans at their flat
word offsets. Reference-bearing `#word-read` and `#word-view` recover those
loans; numeric bytes and layout types alone never establish reference provenance.
Numeric overwrites retire the metadata at the overwritten offsets. These facts
exist only during compilation, without runtime occupancy flags.

Typed writes also establish enum constructor facts at the actual backing word
offsets. A subsequent read, take or view need not recover reference slots in an
inactive variant. Nested payload tags require a known enclosing constructor;
facts belong to the specific cell and enum declaration, not merely a numeric
discriminant. Zero-filled memory, a numeric tag write, or a layout type alone
does not establish a constructor fact. Unknown branches and opaque addresses
remain conservative, and raw mutations invalidate known tags.

`#word-forget` retires loans but leaves bytes and constructor facts unchanged.
An occupied cell still needs real reference provenance after retirement; a new
typed empty-constructor write can establish an empty cell instead. These rules
do not add runtime occupancy bits or branches.

Checked helper summaries keep byte writes separate from loan retirement. A
helper may publish an empty constructor, retire that cell's metadata, and
forward the unchanged constructor fact to its caller. Metadata-only forwarding
does not recreate an occupied cell's references. Later numeric, raw or unknown
writes invalidate the constructor promise; branch joins retain only facts true
on every returning path. The distinction is preserved in semantic caches.

An ordinary helper can require loans in a borrowed word slice. The compiler
infers those entry requirements and checks the actual stored origins at every
call, including through forwarding helpers and cached imports. Returning only
a scalar does not hide a reference read. All reaching loans must meet the
required shared/exclusive, pinned and owning permissions.

Reference slots in enum payloads have conditional entry requirements. A caller
may omit such a loan only when an actual constructor fact proves the payload
inactive at every reaching address. Unknown tags still require the loan. The
same condition applies to the callee's pointee-access effects; it does not
fabricate a reference or suppress unrelated effects. Checked forwarding helpers
preserve exact physical tag conditions, including static slice offsets.

A tag condition can describe entry storage only if the callee has not changed
that tag before reading the cell. Known disjoint writes preserve the condition;
tag writes, raw mutations, unknown effects and ambiguous substitutions discard
it conservatively. No runtime flags or conditional checks are added by these
compile-time contracts.

A checked helper's owned enum result may also contain an optional reference
loaded from numeric storage. If every source for that result payload is a
concrete local `#u64` array cell with no stored loan, the payload cannot be
inhabited by that invocation. This is a result-provenance proof, not a
constructor fact about the buffer or permission to read it. The call's reader
requirements are still checked independently. Unknown addresses, globals,
borrowed-reference boundaries and bodyless callees do not establish absence;
live source loans continue to restrict the caller after the result is returned.
The same proof applies to an optional owning allocation pointer. Proven absent
payloads are excluded from unchanged owned-result match paths, so an impossible
owning-pin arm does not require a fabricated allocation identity. Occupied or
unknown input slots still require their real loans; this does not authorize
access to a live pointer's pointee or retire any of its nested references.

Checked forwarding functions propagate a word reader's owning-pointer
requirement as an entry obligation. Inferring that obligation does not turn
abstract numeric input storage into an allocation. Each actual caller must
still supply a primary, non-lifetime owning loan with the required mutability
and pinning; ordinary call and return substitution rejects non-owning slots.

Restoring an owning pointer also retains the loans stored in its allocation.
These are pointee metadata, not extra words in the backing array. A checked
reader exports requirements for both the owning pointer and its retained
reference fields, including through forwarding calls. Concrete restoration
requires existing pointee loans; neither a layout nor an owner of a different
reference-free pointee fabricates them. Mutation of a retained field's referent
and release with a live owning-pin view remain borrow errors.

Moving an input owner preserves pointee loans supplied by its checked entry
contract, even when those loans are not adjacent slots in the moved value.
Allocation contents are initialized from that existing provenance only on
first registration. A later clear or replacement remains authoritative and
does not re-import stale entry loans. Typed word writes likewise register the
actual owner and pointee loans they store; raw bytes alone do not register them.

```lisp run=42
(#struct RefValue () (: value (#ref #u64)))
(#fn read-value (: words (#slice #u64)) #u64
  (#let restored RefValue (#unsafe (#word-read RefValue words)))
  (#let answer #u64 (#deref (#get restored value)))
  (#forget restored)
  (#return answer))

(#fn main () #u64
  (#let seed #u64 42u64)
  (#let-mut words (#array #u64 1) (#array-repeat 0u64))
  (#unsafe (#word-write RefValue (#borrow-slice-mut words)
    (#struct-literal RefValue (: value (#borrow seed)))))
  (#let answer #u64 (#call read-value (: words (#borrow-slice words))))
  (#forget words)
  (#return answer))
```

Removing the typed write, or overwriting its reference word with a number before
the call, fails compilation. Inferred inputs are not permission to fabricate a
reference. The unsafe implementation still proves capacity, representation
validity and ownership conservation. The same input contracts apply to numeric
arrays passed by value, including arrays inside structs and tuples. Moving the
backing into another local or extracting its array field preserves the required
slot's relationship to the caller's real loan. Shared inputs cannot satisfy an
exclusive read. A thread capturing such backing retains its input loans until
join; checking only the spawn call would not protect the caller while it runs.

Numeric parameter slots are symbolic candidates during contract inference,
not evidence that a reference was initialized. Array candidates use one
symbolic index rather than enumerating every element. A typed read specializes
the requirement to its selected offset; every ordinary call must then supply
the actual loan recorded by a typed write. Raw numeric snapshots are not a
general mechanism for transporting concealed reference ownership.
