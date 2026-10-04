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

This document describes the language implemented by this crate.  The
canonical spelling uses `#` before every builtin form. Unprefixed builtin
forms are rejected.

User function names retain their identity when called with `#call`, even
when a name also spells a builtin. For example, `(#call panic (: value
reference))` calls the declared user function named `panic`; `(#panic)` remains
the builtin trap. `#call` requires named arguments, evaluates their expressions
in parameter declaration order, and applies the declared function signature
and ordinary eager-call ownership rules. The public syntax is unchanged.

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

`@cell` is a user-defined generator in `library/cell.lim`, not a builtin
type. Each invocation explicitly names the concrete type and three
free-standing functions. It currently accepts the integer widths supported
by `#atomic` (`i8/i16/i32/i64`, `u8/u16/u32/u64`, and `usize`); it does not
support floats, pointers, or enums. The generated get/set functions take a
shared reference to the concrete cell and never return a reference to its
contents:

```lisp library
(#import "../library/cell.lim")
(@cell u64 CellU64 CellU64-create CellU64-get CellU64-set)
(#struct Arena ((cursor CellU64)))
(#fn advance ((cursor (#ref CellU64))) u64
  (#let next u64 (#u64.+.wrap
    (#call CellU64-get (: cell (#clone cursor))) 1u64))
  (#call CellU64-set (: cell (#clone cursor) : value next))
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
The atomic API supports `i8/i16/i32/i64`, `u8/u16/u32/u64`, and
`usize`. Each operation uses the width's naturally aligned x86 memory access;
Lim's current local and aggregate storage is at least eight-byte aligned:

```lisp fragment=atomics
(#let-mut counter (#atomic u64) (#atomic-init u64 0u64))
(#atomic-fetch-add (#borrow counter) 1u64 #memory-acq-rel)
(#let observed u64 (#atomic-load (#borrow counter) #memory-acquire))
(#atomic-store (#borrow counter) observed #memory-release)
```

`(#atomic-exchange reference desired #memory-order)` replaces the value and
returns the old scalar. Compare-exchange has these explicit forms:

```lisp syntax
(#atomic-compare-exchange reference expected desired #memory-acq-rel #memory-acquire)
(#atomic-compare-exchange-weak reference expected desired #memory-release #memory-relaxed)
```

Both return `(#tuple bool ScalarType)`: success followed by the observed
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
available for `i128` or `u128`. Unsafe `#send`/`#sync` overrides remain the
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
- Generated `@cell` types use relaxed atomic storage and are `Send + Sync` for
  their supported integer widths.
- `(#atomic T)` is both `Send` and `Sync` only for the supported atomic integer
  widths listed below.
- `(#ref T)` is `Send` when `T` is `Sync`, and is `Sync` when `T` is `Sync`.
- `(#ref-mut T)` is `Send` when `T` is `Send`, and `Sync` when `T` is `Sync`.
- An aggregate has a property only when all of its stored fields/payloads
  have that property.

Unsafe native or opaque types may opt in explicitly:

```lisp library
(#struct NativeResource ((handle (#ptr u8))))
(#unsafe-impl #send NativeResource)
(#unsafe-impl #sync NativeResource)
```

These declarations are promises by the author and override the structural
result for that property. They must only be used when the type's invariants
make cross-thread transfer or shared access sound. Generic-type overrides are
currently rejected; duplicate or undeclared targets are errors. The
`@thread-spawn` with `(: task TaskType : worker worker-function)` validates a monomorphic
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

For inspection, `(@thread-spawn (: task TaskType : worker worker))` materializes in `.lim/` as a
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
(#borrow value (#u64.+.wrap value 2))
```

and a mutable borrow as:

```lisp syntax
(#borrow-mut value (#block (#set value 42) value))
```

The three-expression form borrows the owner for the duration of the body.
The two-expression form produces a reference:

```lisp library
(#fn first ((value (#ref u64))) (#ref u64)
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
and `#index`; enum payloads use
`(#get-payload reference Variant index)`.
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

```lisp run=42
(#fn main () u64
  (#let-mut value u64 40)
  (#return
    (#unsafe
      (#block
        (#let pointer (#ptr-mut u64) (#addr-of-mut value))
        (#ptr-write pointer 42)
        (#ptr-read pointer)))))
```

Functions with caller safety obligations use `#unsafe-fn` instead of `#fn`.
Their signatures otherwise have the same shape. Every call must be enclosed
in `#unsafe`, including calls from another unsafe function. The declaration
does not make its body implicitly unsafe: raw operations still need a block.

```lisp run=42
(#unsafe-fn read-byte ((pointer (#ptr u8))) u8
  (#return (#unsafe (#ptr-read pointer))))
(#fn main () u64
  (#let value u8 42u8)
  (#return (#as (#unsafe
    (#call read-byte (: pointer (#addr-of value)))) u64)))
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
returns the machine address as `usize` without dereferencing it; it can check
Linux error-pointer returns before any access. The offset consumes a raw
pointer and returns a pointer with the same mutability and pointee type; its
index must be `usize`. Offsets use the pointee's byte width (for example,
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
(@pin (: type Frame : name PinnedFrame : fields (: value u64)))
(@pin-scope (: type Frame : pin PinnedFrame : name with-pinned-frame
  : run drive-frame : destroy destroy-frame : result u64))
```

`@pin` emits opaque `PinnedFrame` and `PinnedFrame-shared` handles, unsafe
constructors, and `PinnedFrame-value-read` / `PinnedFrame-value-write` free
functions (plus the shared reader). Field types are literal generator inputs;
ordinary checking verifies them and rejects moving linear fields or replacing
fields that do not satisfy the pinned-field restrictions. Optional `copy true`
emits whole-value readers and a writer only after checking a structural Copy
proof. All implementation functions are inspectable in the generated cache.
For linear fields, `projections (: child PinnedChild)` generates
`PinnedFrame-child-project` and `PinnedFrame-child-project-mut`, returning
the existing concrete child pin handles without moving the field. Shared
handles also get a shared projection. Projection consumes the parent handle;
it does not leave a second mutable handle to the same storage. Derived handles
retain their source's borrow and cannot outlive it. Unsafe
`PinnedFrame-into-view` consumes a handle and exposes its low-level pinned
reference for trusted implementations; it does not unpin or move the referent.

The same declarations also generate `PinnedFrame-child-borrow-mut`, taking
`(: pin (#ref-mut PinnedFrame))`, and `PinnedFrame-child-borrow`, taking
`(: pin (#ref PinnedFrame))`. Shared wrappers have their own shared `-borrow`
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
pure owner-forwarding function does not. The opaque `@pin-box` API returns
the named handles generated by `@pin`; its destruction callback consumes a
`pin` handle rather than accepting a public pinned-reference type.
Transferring an owning allocation to a thread requires retirement of its
existing pointee views.
The caller still guarantees validity, alignment, unique raw ownership, and
retirement of untracked raw pointers. Reference-bearing and nested owning-pin
pointees retain their contents' loans through owner moves, return summaries,
and field projections. Allocating storage does not extend a referent's lifetime.
Heap writes, including helper-call writes, add retained loans to the owning
allocation. Replacement conservatively retains old possible loans until the
owner is consumed; this may reject early reuse of a replaced source, but never
silently discards a borrow. `library/pin_box.lim` generates this owning protocol;
`examples/pin_box.lim` demonstrates moving a handle while a view stays live.

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
(#fn process-id () i64
  (#return (#unsafe (#linux-syscall i64 39usize ()))))
```

`library/linux_x86_64.lim` builds byte input/output, process helpers, and
file-descriptor operations (`openat`, positional and sequential IO, metadata,
directory queries, resource limits and usage, advice, locking, allocation,
descriptor duplication, anonymous files, wall-clock/process-time queries, and
private futex operations) on this primitive. The low-level
pointer wrappers do not validate kernel buffer ranges; callers must uphold
pointer validity and length preconditions, and callers should mark those calls
with `#unsafe`. Lim does not yet enforce unsafe function contracts on wrapper
calls, so this annotation is presently a caller convention rather than a
checked requirement. The raw syscall operation remains available for the rest
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
prints `R`. The requeue wrapper uses an explicit `u32` count in the fourth
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
`examples/linux_mseal.lim` exercises `linux-mseal`, whose flags are `usize`
(Linux `unsigned long`). It verifies invalid inputs, page rounding,
idempotence, and rejected permission changes, discard, and unmapping while
preserving the payload. Sealed mappings cannot be unsealed; this example's
page is released only when its process exits. See the
[kernel mseal documentation](https://docs.kernel.org/userspace-api/mseal.html).
`examples/linux_secret_memory.lim` exercises `linux-memfd-secret` with `u32`
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
transferred bytes. `linux-ioctl` takes a `u32` request and a `usize` argument
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
from the allocated region before releasing it. `linux-brk` returns a `usize`
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

`lim fmt INPUT` formats the file in place and follows internal `#import`s
transitively. `#import-external` files are skipped. The read-only `--format`
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
Every generated `@` expansion is materialized as a readable, content-addressed
`.lim` entry under `.lim/cache/`, regardless of whether it uses a built-in or a
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
  (#fn selected () u64 (#return 1u64))
  (#cfg-else
    (#fn selected () u64 (#return 0u64))))
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
(#syntax StepAwait (u64 Step StepPending StepReady step-poll))
(#await (#syntax-splice StepAwait) step)
```

The second form expands to `(#await u64 Step StepPending StepReady step-poll
step)` before async lowering. It is only valid inside an async function.
Bundles can also supply function parameters or named call arguments. Definitions
are top-level, may refer forward to other bundles, and may contain nested
splices. Names must be unique across declarations; cycles, unknown names,
malformed definitions, and splices outside a surrounding list are errors.
Imports and cfg selection happen first; external imports prefix bundle names
and referenced identifiers normally. Quoted syntax and generator templates stay
literal until emitted. Generated bundle declarations are supported, and ordinary
type, borrow, and linearity checking still applies to their expanded code.

### Generator declarations

Generators are compile-time syntax functions. Their parameters receive the
invocation arguments literally; generator values are immutable syntax nodes:
symbols, literals, or lists. A generator returns a list of top-level forms,
which are expanded before ordinary Lim parsing and type checking.

Capabilities are explicit declarations for generator requirements. A concrete
type opts in with `#capability`, and a generator parameter can require one:

```lisp library
(#fn u64-less ((left (#ref u64)) (right (#ref u64))) bool
  (#return (#u64.< (#deref left) (#deref right))))
(#capability sortable u64
  ((u64-less ((#ref u64) (#ref u64)) bool)))
(#gn make-sortable ((element sortable))
  `((#type Sortable ,element)))
(@make-sortable u64)
```

The list after a generator's name is its parameter declaration list, not a
pattern match. A bare symbol such as `name` declares an ordinary literal-syntax
parameter. A pair such as `(element sortable)` declares one parameter that
requires a capability; it does not destructure the invocation argument. A
frozen syntax collection is requested explicitly at the call site with
`(#syntax-distribute Collection)`, leaving the generator parameter ordinary.
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

(@aliases ((Byte u8) (Word u16)))
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
`#gn-get`, `#gn-symbol-append`, `#gn-for-each`, `#gn-call`, and `#gn-error`.
`#gn-get` looks up a literal key in a named syntax list without introducing a
new dictionary type. `#gn-symbol-append` constructs concrete API identifiers.
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

## Imports

Compile-time collections (`#syntax-collection`, `#syntax-contribute`) are
frozen after active imports and before generators. A direct invocation argument
`(#syntax-distribute Collection)` receives its deterministic snapshot. See
[collections and tasks](collections-and-tasks.md) for the user-defined
distributed-slice, error-enum, and cooperative async generators.

`(#linear Type)` makes a concrete struct or enum non-Copy even when every
field is plain data. Generated task state types use this annotation; Send/Sync
and layout are unaffected.

Imports load Lim source relative to the importing file. Internal imports keep
identifiers unchanged. External imports prefix user identifiers from the
imported source (including types, functions, fields, variants, and local
bindings); builtin forms and primitive types are unchanged:

```lisp syntax
(#import "shared.lim")
(#import-external "compat.lim" compat-)
```

The external prefix is a symbol prefix, conventionally ending in `-`. Imports
are expanded before generator expansion and ordinary type checking. Repeated
imports of the same canonical path with the same mode and prefix are
deduplicated; cycles are rejected. Imported declarations participate in the
same compilation and duplicate-name checks as declarations in the root file.
See `examples/imports.lim`.
To bound compiler resource use, a project is limited to 128 simultaneously
nested source files, 4096 non-deduplicated imports, and 64 MiB of cumulative
source text (including the root file). Import-limit errors identify the import
that crosses the limit; an oversized root file is rejected before import
traversal.

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

```lisp syntax
math.add.one
my-value
Maybe?-unwrap-or
```

Builtin forms are distinguished by their `#` prefix:

```lisp run=42
(#fn main () u64
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
| unsigned integers | `u8`, `u16`, `u32`, `u64`, `u128`, `usize` |
| signed integers | `i8`, `i16`, `i32`, `i64`, `i128`, `isize` |
| floating point | `f32`, `f64` |
| other scalars | `bool`, `char` |
| zero-sized | `()` |
| diverging | `!` |

Fixed aggregates are written explicitly:

```lisp syntax
(#tuple u64 bool char)
(#array u32 4)
```

Construct a fixed-size array value with `#array-of`, keeping it visually
distinct from the `#array` type form:

```lisp fragment=array
(#let values (#array u32 3)
  (#array-of (#array u32 3) 10u32 20u32 30u32))
```

An immutable slice type is written `(#slice T)`. Create a full-array view with
`(#slice-of (#borrow array))`; the array's borrow is retained by the slice. Use
`(#slice-len view)` for its runtime length and
`(#slice-idx view index)` to get a shared reference to an element. Indexing
checks the index against the slice length and traps if it is out of bounds.
Use `(#slice-range view start end)` to create an immutable half-open subrange
`[start, end)`. Both bounds are `usize`; the operation traps if `start > end`
or `end > (#slice-len view)`. Empty and end-boundary ranges are valid. A
subslice retains the original borrow provenance, including across function
returns; it does not extend the referent's lifetime. Slices remain immutable.

User-defined names refer to concrete structs, enums, and aliases.  Generic
declarations and angle-bracket applications are not part of Lim.  Generators
create concrete specializations explicitly, such as `(@vec (: element u64 : allocator Alloc : name VecU64))`.
Allocator-backed collections add their concrete operations explicitly with
`(@vec-alloc (: element u64 : allocator Alloc : vector VecU64 : alloc-result AllocResult : alloc-error AllocError : alloc alloc : grow grow : dealloc dealloc : destroy destroy))`;
the generated API includes `VecU64-new`, `-reserve`, `-push`, `-get`,
`-get-mut`, `-set`, `-pop`, and `-free`. `(@vec-sort (: element u64 : vector VecU64 : comparator compare-u64))`
adds `VecU64-sort`; its named comparator accepts two immutable element
references and returns `bool`. Allocation failure and capacity
overflow are returned in generated result types. See [the allocator ABI](allocator.md)
for the allocator and destruction function signatures.

`()` is the unit value and `!` is the never type.  A function returning `!`
must not reach a normal return.  A void function returns explicitly with
`(#return ())`.

### Heap-owned UTF-8 strings

Import `library/string.lim` for the concrete, opaque, linear `String` type.
String literals remain fixed character arrays; conversion is explicit. The
standard process allocator (`malloc`, `realloc`, `free`) owns the bytes. This
is an ordinary library, not a new builtin or an implicit allocation.

```lisp run=42
(#import "../library/string.lim")
(#fn main () u64
  (#let text (#array char 3) "Aé🙂")
  (#return
    (#match (#call String-from-chars (: text (#slice-of (#borrow text))))
      (#case (StringCreated owned)
        (#block
          (#let length usize (#call String-len (: string (#borrow owned))))
          (#call String-free (: string owned))
          (#if (#usize.== length 7usize) 42u64 1u64)))
      (#case (StringCreateFailed error) 2u64))))
```

`String-new` creates an empty string without allocating. `String-with-capacity`,
`String-from-chars`, `String-from-utf8`, and `String-try-clone` return
`StringCreateResult`: `StringCreated` contains an owned string;
`StringCreateFailed` contains a `StringError`. Cloning is an explicit, fallible
deep copy, never a shallow `#clone` of the allocation handle.

`String-len` and `String-capacity` take `(: string (#ref String))` and count
**bytes**, not characters. `String-is-empty` uses the same shared argument.
`String-reserve` takes `(: string (#ref-mut String) : additional usize)`;
additional capacity is relative to the current length. `String-push-char`,
`String-push-chars`, and `String-push-utf8` take a mutable string and,
respectively, `: value char`, `: text (#slice char)`, or `: bytes (#slice u8)`.
These operations return `StringStatus`: `StringOk` or `(StringErr error)`.
Validation, overflow, and allocation failures leave the original string
unchanged. Errors are `StringOutOfMemory`, `StringCapacityOverflow`,
`StringInvalidUtf8`, and `StringInvalidChar`.
`String-push-string (: string (#ref-mut String) : text (#ref String))`
appends the borrowed source string and returns the same `StringStatus`. It
does not consume either string; the source remains available after the call.

With `#std`, the embedded String module can be used without an explicit
import. This example builds a string from fixed character arrays, appends a
second owned string by shared borrow, and releases both owners:

```lisp library
(#std)
(#fn main () u64
  (#let greeting (#array char 5) "Hello")
  (#let suffix (#array char 9) ", world 🙂")
  (#let-mut message String
    (#match (#call String-from-chars (: text (#slice-of (#borrow greeting))))
      (#case (StringCreated created-message) created-message)
      (#case (StringCreateFailed error) (#panic))))
  (#let tail String
    (#match (#call String-from-chars (: text (#slice-of (#borrow suffix))))
      (#case (StringCreated created-tail) created-tail)
      (#case (StringCreateFailed error) (#panic))))
  (#assert (#match (#call String-push-string (: string (#borrow-mut message) : text (#borrow tail)))
    (#case StringOk true) (#case _ false)))
  (#assert (#match (#call String-push-char (: string (#borrow-mut message) : value #\!))
    (#case StringOk true) (#case _ false)))
  (#assert (#i64.== (#println (#borrow message)) 0i64))
  (#call String-free (: string tail))
  (#call String-free (: string message))
  (#return 42u64))
```

`String-byte-at` takes a shared string and `: index usize`. It returns
`(StringByte byte)` with a copied `u8`, or `StringByteOutOfBounds`.
`String-bytes (: string (#ref String))` returns an opaque `StringBytes` view
that retains the owner borrow, preventing mutation, moving, or freeing its
owner while the view is live. `StringBytes-len (: bytes view)` and
`StringBytes-byte-at (: bytes view : index usize)` inspect that view without
allocating; indexing also returns a copied byte. No mutable byte access is
exposed: safe operations preserve valid UTF-8.
`String-data-pointer (: string (#ref String))` is an unsafe raw-I/O escape
returning `(#ptr-mut u8)`. The pointer does not retain the owner borrow. The
caller must keep a shared borrow alive, read only initialized bytes, and never
write, grow, move, or free the string while using it. Safe stdout functions
uphold these obligations internally; printing does not require `#unsafe`.

Raw-backed scalar references preserve exact byte addresses and access the
native width of the scalar, including at odd `u8` addresses. References keep
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

### Functions

Functions are always free-standing; Lim has no methods or `impl` blocks.
The canonical form is:

```lisp library
(#fn add ((left u32) (right u32)) u32
  (#let total u32 (#u32.+.wrap left right))
  (#return total))
```

The parameter list is a list of `(name Type)` pairs. A colon-prefixed list
is equivalent and avoids repeating parentheses around each pair:

```lisp run=42
(#fn add (: left u32 : right u32) u32
  (#return (#u32.+.wrap left right)))
(#fn main () u64
  (#return (#as (#call add (: right 2u32 : left 40u32)) u64)))
```

At one list depth, `(: left u32 : right u32)` expands to
`((left u32) (right u32))`. A colon must be the first token after `(` at
that depth; `(left : u32)` is invalid. Nested lists have their own depth, so
their colons do not affect the enclosing list. Empty or adjacent groups and
a trailing colon are rejected; `(:)` is an empty list. This syntax works in
other lists of groups too. Parameters may be
marked mutable:

```lisp library
(#fn increment ((#mut value u64)) u64
  (#set value (#u64.+.wrap value 1u64))
  (#return value))
```

Function calls also name every argument explicitly. Use `#call` with a
colon-prefixed argument list; each argument label must match a parameter in
the declaration:

```lisp syntax
(#call add (: left 20u32 : right 22u32))
```

Positional call forms are rejected. Calls with no arguments use
`(#call function (:))`.
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
pointers only. By-value aggregate FFI signatures remain rejected. Calls are unsafe FFI boundaries and must be enclosed in
`#unsafe`:

```lisp run=42
(#extern-fn #abi-c abs ((value i32)) i32)
(#fn main () u64
  (#return (#as (#unsafe (#call abs (: value -42i32))) u64)))
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
UTF-8 bytes of a borrowed `String`, then a newline, and returns `i64`: zero on
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
(#type UserId u64)
(#type Pair (#tuple u64 bool))
(#type Matrix (#array f32 4))
```

Aliases are concrete.  Recursive aliases are rejected.

### Structs

Structs are value types with named fields:

```lisp run=9
(#struct Point ((x u64) (y u64)))

(#fn main () u64
  (#let point Point (#struct-literal Point ((x 7u64) (y 9u64))))
  (#return (#get point y)))
```

Use a generator to emit concrete struct declarations when a family of
structs is needed.

### Enums

Variants may be fieldless or carry one or more values:

```lisp library
(#enum Message
  (Quit
   (Move i32 i32)
   (Write (#array char 8))))
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
creates immutable read-only storage and is useful for aggregate data. Every
read of a static must occur inside `#unsafe`, including reads used to create a
reference to it:

```lisp library
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

```lisp fragment=bindings
(#let count u32 0u32)
(#let-mut total u64 0u64)
```

`#let` creates an immutable binding; use `#let-mut` for a mutable binding.
Bindings may not shadow a visible parameter, local, or global; choose a distinct
name instead. Names may be reused in separate sibling scopes when neither
binding is visible from the other. `#set` assigns a mutable scalar or
aggregate local:

```lisp syntax
(#set total (#u64.+.wrap total 1u64))
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
(#struct Point ((x u64) (y u64)))
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

Mutable slices use a separate type and constructors: `(#slice-mut u64)`,
`#slice-mut-of` from a mutable array reference, `#slice-mut-idx` for exclusive
element access, and `#slice-mut-split view at` to consume a view and produce
two disjoint halves. The split point is a checked `usize` index; an index
greater than the length traps, and the halves cover `[0, at)` and `[at, len)`.
Views are linear: splitting consumes the parent, and overlapping mutable loans
or access through the original array are rejected while a view is live. Each
half must itself be consumed (for example, passed to a function or explicitly
`#forget`-ted). Mutable slices can be returned when their inferred provenance
comes from a function argument; a view of a local array cannot escape.

```lisp fragment=slices
(#let-mut values (#array u64 4) (#array (#array u64 4) 1u64 2u64 3u64 4u64))
(#let whole (#slice-mut u64) (#slice-mut-of (#borrow-mut values)))
(#let (#tuple left right)
  (#tuple (#slice-mut u64) (#slice-mut u64))
  (#slice-mut-split whole 2usize))
(#deref-set (#slice-mut-idx left 0usize) 17u64)
(#deref-set (#slice-mut-idx right 0usize) 25u64)
(#forget left)
(#forget right)
```

Local destructuring and `#let-else` support tuples, arrays, structs, and enum
patterns.  The `else` body must diverge, for example with `#return`,
`#break`, or `#panic`.
Destructuring consumes the aggregate and transfers each reference field's
borrow provenance to its corresponding binding. Nested struct, tuple, array,
and enum payload bindings retain their source loans; mutable fields cannot
alias an already active mutable loan. Returning a destructured reference is
allowed only when its origin outlives the function.

### Linear values and explicit cloning

Local values and function parameters are linear unless their type is plain-old
data or a reference. Built-in scalar values, raw pointers, and structs, enums,
tuples, or arrays whose fields/elements are all copyable are structurally
`Copy`; they can be used without consuming the binding. Resource-bearing
aggregates remain linear and must be consumed exactly once. A moved value
cannot be read or cloned again. Use `#clone` at the point where an additional
value is intended:

```lisp fragment=bindings
(#let count u64 40u64)
(#let total u64 (#u64.+.wrap (#clone count) count))
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

```lisp syntax
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

```lisp syntax
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

```lisp syntax
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

```lisp syntax
(#as value u64)
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
| `#index`, `#get`, `#get-payload`, `#pin-get-payload`, `#pin-get-payload-mut` | aggregate and enum projection |
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
(#fn increment ((#mut value u64)) u64
  (#let reference (#ref-mut u64) (#borrow-mut value))
  (#deref-set reference (#u64.+.wrap (#deref reference) 1u64))
  (#drop reference)
  (#return value))

(#fn main () u64
  (#return (#call increment (: value 41u64))))
```

Generator expressions instead run at compile time. Here a helper checks its
syntax input, reports an error for a non-symbol, and emits a concrete type
alias. Quasiquote and unquote are syntax punctuation, not `#` builtins:

```lisp run=42
(#gn-fn alias-declaration (name)
  (#gn-if (#gn-symbol? name)
    `(#type ,name u64)
    (#gn-error "alias name must be a symbol")))

(#gn make-alias (name)
  (#gn-list (#gn-call alias-declaration name)))

(@make-alias Answer)

(#fn main () Answer
  (#return 42u64))
```

| Builtin | Syntax | Example (context) | Meaning |
| --- | --- | --- | --- |
| `#abi-c` | `#abi-c` in `#extern-fn` | `(#extern-fn #abi-c abs ((value i32)) i32)` (declaration) | Selects the C calling convention; foreign calls require `#unsafe`. |
| `#addr-of` | `(#addr-of local)` | `(#unsafe (#addr-of value))` (expression) | Takes a shared raw address of a scalar local; unsafe because later access is not checked. |
| `#addr-of-mut` | `(#addr-of-mut mutable-local)` | `(#unsafe (#addr-of-mut value))` (expression) | Takes a mutable raw address of a mutable scalar local. |
| `#align-of` | `(#align-of Type)` | `(#align-of Point)` (expression) | Compile-time alignment in bytes for the Lim representation, or C layout of a `#repr-c` type. |
| `#arch` | `(#cfg-is #arch literal)` | `(#cfg-if (#cfg-is #arch x86_64) (#type Word u64))` (top level) | Automatically populated target architecture cfg key; overridable with `--cfg arch=VALUE`. |
| `#array` | `(#array ElementType Length)` as a type; `(#array pattern...)` as a pattern | `(#let xs (#array u8 2) (#array-of (#array u8 2) 4u8 5u8))` (binding) | Names a fixed-length array type or destructures an array in a pattern; values are constructed with `#array-of`. |
| `#array-of` | `(#array-of ArrayType value...)` | `(#array-of (#array u8 2) 4u8 5u8)` (expression) | Explicitly constructs a fixed array with its full type stated. |
| `#array-repeat` | `(#array-repeat value)` with an expected array type | `(#let xs (#array u8 3) (#array-repeat 0u8))` (binding) | Fills every array slot with the given Copy value. |
| `#as` | `(#as value TargetType)` | `(#let n u64 (#as byte u64))` (expression) | Explicit scalar/enum conversion; narrowing integers truncate, and float-to-integer conversions trap when out of range. |
| `#asm` | `(#asm ResultType ((register value)...) "instructions")` | `(#unsafe (#asm i64 ((rax 39usize)) "syscall"))` (expression) | Emits target assembly; unsafe, target-specific, and subject to the documented register/stack rules. |
| `#assert` | `(#assert condition)` | `(#assert (#u64.== count 3u64))` (statement) | Traps if the condition is false. |
| `#atomic` | `(#atomic ScalarType)` | `(#let-mut counter (#atomic u64) (#atomic-init u64 0u64))` (type/binding) | Declares a supported atomic scalar wrapper type. |
| `#atomic-compare-exchange` | `(#atomic-compare-exchange reference expected desired success-order failure-order)` | `(#atomic-compare-exchange (#borrow counter) 0u64 1u64 #memory-acq-rel #memory-acquire)` (expression) | Strong compare-exchange; returns `(success, observed-value)`. |
| `#atomic-compare-exchange-weak` | `(#atomic-compare-exchange-weak reference expected desired success-order failure-order)` | `(#atomic-compare-exchange-weak (#borrow counter) 0u64 1u64 #memory-release #memory-relaxed)` (expression) | Weak compare-exchange; may fail spuriously and returns `(success, observed-value)`. |
| `#atomic-exchange` | `(#atomic-exchange reference desired order)` | `(#atomic-exchange (#borrow counter) 2u64 #memory-seq-cst)` (expression) | Atomically replaces the value and returns the previous value. |
| `#atomic-fetch-add` | `(#atomic-fetch-add reference addend order)` | `(#atomic-fetch-add (#borrow counter) 1u64 #memory-acq-rel)` (expression) | Atomically adds and returns the previous value. |
| `#atomic-init` | `(#atomic-init ScalarType initial-value)` | `(#atomic-init u64 0u64)` (initializer) | Creates an atomic value; allowed scalar widths are documented in the atomics section. |
| `#atomic-load` | `(#atomic-load reference order)` | `(#atomic-load (#borrow counter) #memory-acquire)` (expression) | Atomically reads a value using an allowed load ordering. |
| `#atomic-store` | `(#atomic-store reference value order)` | `(#atomic-store (#borrow counter) 4u64 #memory-release)` (statement) | Atomically stores a value using an allowed store ordering. |
| `#await` | `(#await ChildTask PendingVariant ReadyVariant poll-function child-expression)`; nested value forms add the result type after `#await` | `(#let value u64 (#await Step StepPending StepReady step-poll child))` (inside `@async-fn`) | Marks a sequential suspension point for `@async-fn` or `@async-fn-pinned`; live captures are inferred from the continuation, and the form is not valid in an ordinary function. |
| `#block` | `(#block statement... final-expression)` | `(#block (#let x u64 2u64) (#u64.+.wrap x 1u64))` (expression) | Evaluates statements in order and yields the final expression, or unit for a side-effect-only block. |
| `#borrow` | `(#borrow place)` or `(#borrow place body)` | `(#let r (#ref u64) (#borrow value))` (binding) | Creates a shared reference, or scopes a shared borrow around a body. |
| `#borrow-mut` | `(#borrow-mut place)` or `(#borrow-mut place body)` | `(#let r (#ref-mut u64) (#borrow-mut value))` (binding) | Creates an exclusive mutable reference, or scopes a mutable borrow around a body. |
| `#break` | `(#break)` or `(#break value)` | `(#loop (#break 42u64))` (expression in a function) | Exits the innermost loop, optionally supplying its expression value. |
| `#break-to` | `(#break-to label)` or `(#break-to label value)` | `(#break-to outer 42u64)` (labeled loop body) | Exits a named enclosing loop, optionally with a loop value. |
| `#call` | `(#call function (: name value : ...))` | `(#call add (: left 20u64 : right 22u64))` (expression) | Calls a statically named function; every argument is named and checked against its signature. |
| `#capability` | `(#capability name Type ((operation (Args...) Result)...))` | `(#capability ordered u64 ((less ((#ref u64) (#ref u64)) bool)))` (declaration) | Declares a generator-time signature contract that a concrete type may satisfy. |
| `#case` | `(#case pattern body)` or `(#case pattern (#when guard) body)` | `(#case (Some x) x)` (inside `#match`) | Introduces one explicit match arm. |
| `#cfg-and` | `(#cfg-and condition...)` | `(#cfg-and (#cfg-is #os linux) (#cfg-is #arch x86_64))` (cfg condition) | Combines conditions with logical AND; requires at least one condition. |
| `#cfg-else` | `(#cfg-else form...)` | `(#cfg-else (#fn fallback () () (#return ())))` (last `#cfg-if` branch) | Supplies forms when the preceding `#cfg-if` condition is false. |
| `#cfg-if` | `(#cfg-if condition form... [(#cfg-else form...)])` | `(#cfg-if (#cfg-is #os linux) (#fn os-call () () (#return ())))` (top level) | Includes only the selected top-level forms before imports and semantic checks. |
| `#cfg-is` | `(#cfg-is #key literal)` | `(#cfg-is #feature fast)` (cfg condition) | Compares a configured key to a symbol, string, or integer literal. |
| `#cfg-not` | `(#cfg-not condition)` | `(#cfg-not (#cfg-is #debug enabled))` (cfg condition) | Negates one cfg condition. |
| `#cfg-or` | `(#cfg-or condition...)` | `(#cfg-or (#cfg-is #os linux) (#cfg-is #os macos))` (cfg condition) | Combines conditions with logical OR; requires at least one condition. |
| `#clone` | `(#clone value)` | `(#let second Buffer (#clone first))` (statement/expression) | Explicitly duplicates a Copy value or invokes the concrete type's `Type-clone` function. |
| `#const` | `(#const name Type value)` | `(#const LIMIT u64 16u64)` (top level) | Declares an immutable compile-time constant with an explicit type. |
| `#continue` | `(#continue)` | `(#while false (#continue))` (function body) | Starts the next iteration of the innermost loop. |
| `#continue-to` | `(#continue-to label)` | `(#continue-to outer)` (labeled loop body) | Starts the next iteration of a named enclosing loop. |
| `#debug-assert` | `(#debug-assert condition)` | `(#debug-assert (#u64.< length capacity))` (statement) | Currently identical to `#assert`: evaluates its condition and traps on false, regardless of cfg settings. |
| `#deref` | `(#deref reference)` | `(#return (#deref r))` (expression) | Reads through a Lim reference. |
| `#deref-set` | `(#deref-set mutable-reference value)` | `(#deref-set r 7u64)` (statement) | Writes through a mutable Lim reference. |
| `#drop` | `(#drop value)` | `(#drop resource)` (statement) | Explicitly discards a value without calling user destruction code. Dropping a reference-bearing place ends its loan and makes that place unusable; plain Copy scalars remain reusable. |
| `#enum` | `(#enum Name [#repr-c] ((Variant [discriminant] PayloadType...)...))` | `(#enum Maybe ((Some u64) None))` (top level) | Declares a concrete enum; variants can carry typed payloads and explicit discriminants. |
| `#extern-fn` | `(#extern-fn #abi-c name (: arg Type : ...) ReturnType)`; the parameter list may also use nested pairs | `(#extern-fn #abi-c c_abs (: value i32) i32)` (top level) | Declares a C-ABI external function. Calling foreign functions uses the platform linker and is outside the direct-syscall-only standard library. |
| `#fn` | `(#fn name (: arg Type : ...) ReturnType body...)`; the parameter list may also use nested pairs | `(#fn add (: a u64 : b u64) u64 (#return (#u64.+.wrap a b)))` (top level) | Declares a monomorphic function with explicit parameter/return types and body. |
| `#for` | `(#for init condition step body...)` | `(#for (#let-mut i u64 0u64) (#u64.< i 4u64) (#set i (#u64.+.wrap i 1u64)) (#set sum (#u64.+.wrap sum i)))` (statement) | Runs an explicitly structured init/condition/step loop. |
| `#for-range` | `(#for-range (name Type) start end body...)` | `(#for-range (i u64) 0u64 4u64 (#set sum (#u64.+.wrap sum i)))` (statement) | Iterates a typed, half-open range `[start, end)`. |
| `#forget` | `(#forget value)` | `(#forget raw-pointer)` (statement) | Discards a value without cleanup; use after explicit resource release. Forgetting a reference-bearing place ends its loan and makes that place unusable; plain Copy scalars remain reusable. Lim never inserts destructors. Task handles/results cannot be forgotten. |
| `#get` | `(#get aggregate field-or-index)` | `(#get point x)` or `(#get pair 0)` (expression) | Projects a struct field or tuple element. |
| `#get-payload` | `(#get-payload enum variant index)` | `(#get-payload result Error 0)` (expression) | Projects a statically selected enum payload field. |
| `#gn` | `(#gn name (name-or-(name capability...)...) body)` | ``(#gn make-alias (name) `((#type ,name u64)))`` (top level) | Declares an interpreted compile-time syntax generator. Each declaration binds one syntax parameter, not a destructuring pattern; arguments are literals/syntax, not runtime values. |
| `#gn-call` | `(#gn-call function syntax-arg...)` | `(#gn-call make-alias name target)` (generator body) | Calls a `#gn-fn` helper during generator interpretation. |
| `#gn-equal` | `(#gn-equal syntax-a syntax-b)` | `(#gn-equal item expected)` (generator expression) | Tests structural equality of immutable generator syntax values. |
| `#gn-error` | `(#gn-error message)` where `message` evaluates to string syntax | `(#gn-error "unsupported element type")` (generator expression) | Stops generation with a source-associated explanatory diagnostic; non-string syntax is rejected. |
| `#gn-first` | `(#gn-first list)` | `(#gn-first members)` (generator expression) | Returns the first element of a non-empty syntax list. |
| `#gn-fn` | `(#gn-fn name (parameter...) body)` | `(#gn-fn identity (value) value)` (top level) | Declares a reusable generator-time function with one syntax-producing body. |
| `#gn-for-each` | `(#gn-for-each name syntax-list body)` | `(#gn-for-each field fields (#gn-list (#gn-symbol "#type") field u64))` (generator body) | Maps one syntax-producing body over a syntax list; returns a list of results and is the bounded iteration primitive. |
| `#gn-gensym` | `(#gn-gensym string-hint)` | `(#gn-gensym "task")` (generator expression) | Evaluates a string hint and returns a fresh syntax symbol. The hint must be one non-keyword ordinary identifier; generated names use the reserved `lim.gensym.` prefix and cannot be forged or changed by source, `#gn-symbol`, or `#gn-symbol-append`. |
| `#gn-get` | `(#gn-get named-syntax key [fallback])` | `(#gn-get (: type u64 : name PinnedU64) type)` (generator expression) | Returns a literal value from a list of key/value syntax pairs. Rejects malformed pairs and duplicate keys; a missing key errors unless a lazily evaluated fallback is supplied. |
| `#gn-if` | `(#gn-if condition then-value else-value)` | `(#gn-if (#gn-equal kind sortable) yes no)` (generator expression) | Selects a syntax value based on a generator boolean. |
| `#gn-length` | `(#gn-length syntax-list)` | `(#gn-length fields)` (generator expression) | Returns the number of elements in a syntax list. |
| `#gn-list` | `(#gn-list syntax...)` | `(#gn-list a b)` (generator expression) | Constructs an immutable syntax list. |
| `#gn-list?` | `(#gn-list? syntax)` | `(#gn-list? value)` (generator expression) | Tests whether a syntax value is a list. |
| `#gn-rest` | `(#gn-rest list)` | `(#gn-rest fields)` (generator expression) | Returns a list containing all but the first element. |
| `#gn-symbol` | `(#gn-symbol string-literal)` | `(#gn-symbol "#type")` (generator expression) | Constructs one symbol syntax value from a string literal, including builtin names; rejects malformed text and compiler-reserved gensym names. |
| `#gn-symbol-append` | `(#gn-symbol-append symbol string-or-symbol)` | `(#gn-symbol-append PinnedFrame "-read")` (generator expression) | Appends literal text to an identifier and checks that the result parses as exactly one symbol. Used for concrete generated type and function names. |
| `#gn-symbol?` | `(#gn-symbol? syntax)` | `(#gn-symbol? value)` (generator expression) | Tests whether a syntax value is a symbol. |
| `#if` | `(#if condition then [else])` | `(#return (#if ready 1u64 0u64))` (expression) | Selects an expression by a boolean; without `else`, the then branch must be unit. |
| `#if-let` | `(#if-let pattern Type value then [else])` | `(#if-let (Some x) Maybe maybe x 0u64)` (expression) | Tests a typed pattern and scopes its bindings to the successful branch. |
| `#import` | `(#import "relative/path.lim")` | `(#import "types.lim")` (top level) | Imports internal declarations without renaming their symbols. |
| `#import-external` | `(#import-external "path.lim" prefix)` | `(#import-external "math.lim" math-)` (top level) | Imports declarations while prefixing their symbols. |
| `#index` | `(#index array usize-index)` | `(#index values 1usize)` (expression) | Reads an array element with a checked index. |
| `#label` | `(#label name loop)` | `(#label outer (#while condition (#continue-to outer)))` (statement) | Names an enclosing `#while`, `#loop`, or `#for` for targeted control flow. |
| `#let` | `(#let pattern-or-name Type value)` | `(#let count u32 0u32)` (function body) | Declares an immutable local with an explicit type. |
| `#let-else` | `(#let-else pattern Type value else-statement...)` | `(#let-else (Some x) Maybe maybe (#return 0u64))` (function body) | Destructures on success; the else branch must diverge. |
| `#let-mut` | `(#let-mut name-or-pattern Type value)` | `(#let-mut count u32 0u32)` (function body) | Declares a mutable local with an explicit type. |
| `#linear` | `(#linear TypeName)` | `(#linear FileHandle)` (top level) | Disables structural Copy for the named struct/enum, making its values linear. |
| `#linux-syscall` | `(#linux-syscall ResultType number (arg...))` | `(#unsafe (#linux-syscall i64 39usize ()))` (expression) | Emits a raw Linux x86-64 syscall instruction with up to six machine-word arguments and unmodified negative-errno results. |
| `#literal` | `(#literal NumericType literal)` | `(#let n u16 (#literal u16 42))` (expression) | Gives an integer/float literal an explicit numeric type. |
| `#loop` | `(#loop body...)` | `(#return (#loop (#break 42u64)))` (function returning `u64`) | Repeats indefinitely until broken; a break value makes it value-producing. |
| `#match` | `(#match value (#case pattern body)...)` | `(#match maybe (#case (Some x) x) (#case None 0u64))` (expression) | Performs an exhaustive pattern match; every arm must use `#case`. |
| `#memory-acq-rel` | `#memory-acq-rel` | `(#atomic-fetch-add r 1u64 #memory-acq-rel)` (ordering operand) | Selects acquire-release ordering for read-modify-write atomics. |
| `#memory-acquire` | `#memory-acquire` | `(#atomic-load r #memory-acquire)` (ordering operand) | Selects acquire ordering where permitted. |
| `#memory-relaxed` | `#memory-relaxed` | `(#atomic-load r #memory-relaxed)` (ordering operand) | Selects relaxed ordering with no synchronization ordering. |
| `#memory-release` | `#memory-release` | `(#atomic-store r 1u64 #memory-release)` (ordering operand) | Selects release ordering where permitted. |
| `#memory-seq-cst` | `#memory-seq-cst` | `(#atomic-load r #memory-seq-cst)` (ordering operand) | Selects sequentially consistent ordering. |
| `#mut` | `(#mut parameter Type)` | `(#fn advance ((#mut count u64)) u64 (#set count 1u64) (#return count))` (parameter list) | Marks a function parameter mutable; local mutable bindings use `#let-mut`. |
| `#offset-of` | `(#offset-of ReprCType field)` | `(#offset-of Header payload)` (expression) | Computes a field's offset in the declared C layout; requires a `#repr-c` struct. |
| `#opaque` | `(#opaque StructName)` | `(#struct Token ((slot u64))) (#opaque Token)` (top level) | Restricts construction, field access, and cloning of a linear struct to its defining source module; external code can use its public functions. The annotation must appear in the same source module as the concrete struct. |
| `#or` | `(#or pattern pattern...)` | `(#case (#or Red Blue) 1u64)` (pattern) | Matches any listed alternative; alternatives must bind consistently. |
| `#os` | `(#cfg-is #os literal)` | `(#cfg-if (#cfg-is #os linux) (#type Fd i32))` (top level) | Automatically populated OS cfg key; overridable with `--cfg os=VALUE`. |
| `#panic` | `(#panic)` | `(#if failed (#panic) ())` (expression) | Traps and never returns. |
| `#pin-borrow` | `(#pin-borrow place)` | `(#let pinned (#pin-ref Node) (#pin-borrow node))` (expression) | Creates a shared pinned reference to a local or projected field place. While any derived pin is live, safe code cannot copy, move, replace, or destroy the referent. |
| `#pin-borrow-mut` | `(#pin-borrow-mut place)` | `(#let pinned (#pin-ref-mut Node) (#pin-borrow-mut node))` (expression) | Creates an exclusive pinned reference; whole-referent replacement is forbidden, and normal exclusive-borrow rules apply. |
| `#pin-get-payload` | `(#pin-get-payload pinned-enum-reference variant index)` | `(#let payload (#pin-ref u64) (#pin-get-payload slot Full 0))` (expression) | Borrows a selected enum payload in place as a shared pinned reference. Unlike `#get-payload`, it never extracts or moves the payload value. |
| `#pin-get-payload-mut` | `(#pin-get-payload-mut mutable-pinned-enum-reference variant index)` | `(#let payload (#pin-ref-mut u64) (#pin-get-payload-mut slot Full 0))` (expression) | Borrows a selected enum payload in place as an exclusive pinned reference; requires a mutable pinned reference to the enum. |
| `#pin-own` | `(#pin-own TargetType)` | `(#let owner (#pin-own u64) (#unsafe (#pin-own-of pointer 42u64)))` (type) | Linear pointer-sized owner of stationary heap storage. Moving the owner does not move the pointee or invalidate its views. It cannot be cloned; forgetting it leaks the allocation. |
| `#pin-own-borrow` | `(#pin-own-borrow owner-or-reference [allocator-reference])` | `(#let view (#pin-ref u64) (#pin-own-borrow owner allocator))` (expression) | Borrows the allocation, independently of the owner's stack address. An optional allocator anchor remains borrowed for the view's lifetime, even after moving or forgetting the owner. |
| `#pin-own-borrow-mut` | `(#pin-own-borrow-mut mutable-owner-or-reference [allocator-reference])` | `(#let view (#pin-ref-mut u64) (#pin-own-borrow-mut owner))` (expression) | Exclusively borrows stationary heap storage. Requires a mutable owner binding or reference; rejects overlapping retained views. |
| `#pin-own-of` | `(#pin-own-of mutable-pointer initializer)` | `(#let owner (#pin-own u64) (#unsafe (#pin-own-of pointer 42u64)))` (expression) | Consumes an initializer into aligned, uniquely owned writable storage using Lim's native layout, then adopts it as stationary. The caller ensures sufficient space, validity until release, and no raw-pointer aliases that move or free it. Stored references and nested owning pins retain their lifetime provenance; allocation does not extend those lifetimes. |
| `#pin-ptr-borrow` | `(#pin-ptr-borrow pinned-anchor pointer)` | `(#unsafe (#pin-ptr-borrow pinned pointer))` (expression) | Unsafe shared pointer borrow tied to a pinned-reference anchor; returns a pinned reference and preserves anchor provenance. The caller proves pointer validity and address stability for the anchor lifetime. |
| `#pin-ptr-borrow-mut` | `(#pin-ptr-borrow-mut pinned-mut-anchor mutable-pointer)` | `(#unsafe (#pin-ptr-borrow-mut pinned pointer))` (expression) | Unsafe exclusive pointer borrow tied to a mutable pinned-reference anchor; returns a mutable pinned reference. The caller proves validity, stability, and unique access. |
| `#pin-read` | `(#pin-read pinned-reference)` | `(#unsafe (#pin-read pinned))` (expression) | Reads a pinned referent by value. Unsafe because the caller must prevent aliasing and must not duplicate ownership of linear data. |
| `#pin-ref` | `(#pin-ref TargetType)` | `(#let pinned (#pin-ref Node) (#pin-borrow node))` (type) | Shared pinned-reference type. It is distinct from an ordinary reference and keeps its referent immovable while the loan is live. |
| `#pin-ref-mut` | `(#pin-ref-mut TargetType)` | `(#let pinned (#pin-ref-mut Node) (#pin-borrow-mut node))` (type) | Exclusive pinned-reference type; it cannot be used to replace the complete referent. |
| `#pin-release` | `(#pin-release owner)` | `(#let pointer (#ptr-mut u64) (#unsafe (#pin-release owner)))` (expression) | Consumes the owning heap pin after in-place cleanup, returning its pointer for deallocation. Retained pointee views block release, including through helper calls. Unsafe: untracked pointers and address-sensitive cleanup remain the caller's responsibility. |
| `#pin-set-field` | `(#pin-set-field pinned-reference field copy-or-shared-reference-value)` | `(#pin-set-field pinned state 2u32)` (statement) | Replaces one scalar/fieldless-enum or shared-reference struct field through a mutable pinned reference. The field loan is checked independently; it does not move or replace the pinned struct. |
| `#pin-write` | `(#pin-write mutable-pinned-reference value)` | `(#unsafe (#pin-write pinned replacement))` (expression) | Replaces a pinned referent in place. Unsafe: the caller must prove no live derived references are invalidated and preserve ownership of the replaced value. |
| `#platform` | `(#cfg-is #platform literal)` | `(#cfg-if (#cfg-is #platform linux) (#type Fd i32))` (top level) | Automatically populated platform cfg key, initially the host OS; overridable with `--cfg platform=VALUE`. |
| `#println` | `(#println (#borrow string))` | `(#assert (#i64.== (#println (#borrow message)) 0i64))` (expression) | Writes a borrowed `String`'s UTF-8 bytes and a newline; returns zero on success or negative errno on failure. It does not consume the string; a failed text write may be partial and skips the newline. Available after top-level `(#std)`. |
| `#ptr` | `(#ptr PointeeType)` | `(#let p (#ptr u8) (#ptr-null (#ptr u8)))` (type) | Immutable raw-pointer type; dereference and address operations require unsafe context. |
| `#ptr-address` | `(#ptr-address pointer)` | `(#ptr-address (#ptr-null (#ptr u8)))` (expression) | Converts a raw pointer to its machine address as `usize` without dereferencing it; useful for checking syscall error-pointer results before access. |
| `#ptr-borrow` | `(#ptr-borrow reference-anchor pointer)` | `(#unsafe (#ptr-borrow owner pointer))` (expression) | Creates a shared reference tied to an existing reference's inferred borrow lifetime; caller must uphold pointer validity. |
| `#ptr-borrow-mut` | `(#ptr-borrow-mut mutable-reference-anchor mutable-pointer)` | `(#unsafe (#ptr-borrow-mut owner pointer))` (expression) | Creates an exclusive reference tied to an anchor; caller must prove unique valid access. |
| `#ptr-is-null` | `(#ptr-is-null pointer)` | `(#if (#ptr-is-null p) 0u64 1u64)` (expression) | Safely tests a raw pointer for null. |
| `#ptr-mut` | `(#ptr-mut PointeeType)` | `(#let p (#ptr-mut u8) (#ptr-null (#ptr-mut u8)))` (type) | Mutable raw-pointer type. |
| `#ptr-null` | `(#ptr-null PointerType)` | `(#ptr-null (#ptr u8))` (expression) | Constructs a typed null raw pointer. |
| `#ptr-offset` | `(#ptr-offset pointer usize-index)` | `(#unsafe (#ptr-offset p 2usize))` (expression) | Advances by pointee elements with checked address arithmetic; requires unsafe context and does not check allocation bounds. |
| `#ptr-read` | `(#ptr-read pointer)` | `(#unsafe (#ptr-read p))` (expression) | Reads the pointee value without bounds/validity checks. |
| `#ptr-write` | `(#ptr-write mutable-pointer value)` | `(#unsafe (#ptr-write p 7u8))` (statement) | Writes the pointee without bounds/validity checks. |
| `#range` | `(#range lower upper)` | `(#case (#range 1u32 4u32) 1u64)` (pattern) | Matches integer/character values in a half-open interval. |
| `#range-inclusive` | `(#range-inclusive lower upper)` | `(#case (#range-inclusive 1u32 4u32) 1u64)` (pattern) | Matches both endpoints of an integer/character interval. |
| `#ref` | `(#ref TargetType)` | `(#let r (#ref u64) (#borrow value))` (type/binding) | Shared-reference type. |
| `#ref-mut` | `(#ref-mut TargetType)` | `(#let r (#ref-mut u64) (#borrow-mut value))` (type/binding) | Mutable-reference type. |
| `#repr-c` | `(#struct Name #repr-c fields)` or `(#enum Name #repr-c variants)` | `(#struct Header #repr-c ((tag u8) (length u32)))` (declaration) | Requests C layout metadata for layout queries; does not make arbitrary Lim values FFI-safe. |
| `#return` | `(#return value)` | `(#return ())` (function body) | Exits a function with its explicitly typed result; void functions must return `()`. |
| `#send` | `(#unsafe-impl #send Type)` | `(#struct Handle ((raw (#ptr u8)))) (#unsafe-impl #send Handle)` (top level) | Unsafe promise that ownership of the type may be transferred between threads. Without an override, Send is derived structurally. |
| `#set` | `(#set name value)` | `(#set count (#u32.+.wrap count 1u32))` (statement) | Reassigns a mutable local. |
| `#set-field` | `(#set-field aggregate field-or-index value)` | `(#set-field point x 4u64)` (statement) | Mutates a struct field or tuple slot; a linear member must first be consumed. |
| `#set-index` | `(#set-index array index value)` | `(#set-index values 0usize 9u8)` (statement) | Mutates an array element after a bounds check; a linear element needs proven prior consumption at a constant index. |
| `#set-payload` | `(#set-payload enum variant index value)` | `(#set-payload choice Data 0 9u64)` (statement) | Replaces one payload field of a mutable enum value; a linear payload must first be consumed. |
| `#size-of` | `(#size-of Type)` | `(#return (#size-of Point))` (expression) | Returns the compile-time size in bytes for the Lim or selected C layout. |
| `#slice` | `(#slice ElementType)` | `(#let view (#slice u8) (#slice-of (#borrow bytes)))` (type) | Immutable dynamically sized view over an array borrow. |
| `#slice-idx` | `(#slice-idx slice usize-index)` | `(#deref (#slice-idx view 0usize))` (expression) | Bounds-checks and returns a shared reference to an element. |
| `#slice-len` | `(#slice-len slice)` | `(#slice-len view)` (expression) | Returns the immutable slice length as `usize`. |
| `#slice-mut` | `(#slice-mut ElementType)` | `(#let view (#slice-mut u8) (#slice-mut-of (#borrow-mut bytes)))` (type) | Mutable dynamically sized view retaining an exclusive array borrow. |
| `#slice-mut-idx` | `(#slice-mut-idx slice usize-index)` | `(#deref-set (#slice-mut-idx view 0usize) 9u8)` (expression) | Bounds-checks and returns a mutable reference to an element. |
| `#slice-mut-len` | `(#slice-mut-len slice)` | `(#slice-mut-len view)` (expression) | Returns the mutable slice length as `usize`. |
| `#slice-mut-of` | `(#slice-mut-of mutable-array-reference)` | `(#slice-mut-of (#borrow-mut bytes))` (expression) | Creates a mutable slice over an array while retaining its exclusive borrow. |
| `#slice-mut-split` | `(#slice-mut-split slice usize-index)` | `(#let pair (#tuple (#slice-mut u8) (#slice-mut u8)) (#slice-mut-split view 2usize))` (expression) | Consumes a mutable slice and returns two disjoint mutable slices. |
| `#slice-of` | `(#slice-of shared-array-reference)` | `(#slice-of (#borrow bytes))` (expression) | Creates a full immutable slice while retaining the source borrow. |
| `#slice-range` | `(#slice-range slice start end)` | `(#slice-range view 1usize 3usize)` (expression) | Creates a checked half-open immutable subslice `[start,end)`. |
| `#static` | `(#static name Type value)` | `(#static answer u64 42u64)` (top level) | Declares storage with static lifetime; accesses must be inside `#unsafe`. |
| `#std` | `(#std)` | `(#std)` (top level) | Loads the embedded standard String and stdout modules into the program. This is explicit opt-in and works without a source checkout. |
| `#struct` | `(#struct Name [#repr-c] ((field Type)...))` | `(#struct Point ((x u64) (y u64)))` (top level) | Declares a concrete struct; optional `#repr-c` selects C layout for layout queries. |
| `#struct-literal` | `(#struct-literal Type ((field value)...))` | `(#struct-literal Point ((x 1u64) (y 2u64)))` (expression) | Constructs a struct by explicitly naming every field; no defaults are applied. |
| `#sync` | `(#unsafe-impl #sync Type)` | `(#struct Handle ((raw (#ptr u8)))) (#unsafe-impl #sync Handle)` (top level) | Unsafe promise that sharing references to this type across threads is sound. Without an override, Sync is derived structurally. |
| `#syntax` | `(#syntax Name (syntax ...))` | `(#syntax StepAwait (u64 Step StepPending StepReady step-poll))` (top level) | Declares an immutable literal syntax bundle with a unique identifier; no values are evaluated and no types are inferred. |
| `#syntax-collection` | `(#syntax-collection name)` | `(#syntax-collection handlers)` (top level) | Declares a deterministic compile-time syntax collection, frozen before generator expansion. |
| `#syntax-contribute` | `(#syntax-contribute collection key syntax)` | `(#syntax-contribute handlers Read (Read u64))` (top level) | Adds literal syntax under a key; duplicate keys must contribute identical syntax. |
| `#syntax-distribute` | `(#syntax-distribute Collection)` | `(@error-enum (#syntax-distribute Errors) Error)` (direct generator argument) | Replaces one explicit generator-call argument with the frozen, key-sorted syntax values of a collection. Unknown collections are errors. |
| `#syntax-splice` | `(#syntax-splice Name)` | `(#await (#syntax-splice StepAwait) step)` (inside an async function) | Inserts a named bundle's elements into the surrounding list before ordinary checking and async lowering; unknown names and cycles are errors. |
| `#target` | `(#cfg-is #target literal)` | `(#cfg-if (#cfg-is #target x86_64-unknown-linux-gnu) (#type Word u64))` (top level) | Automatically populated canonical target triple cfg key; overridable with `--cfg target=VALUE`. |
| `#thread-task` | `(#thread-task TaskType worker [spawn-signature join-signature])` | `(#thread-task ReadTask read-value)` (generated declaration) | Declares a concrete task type and its named worker; generated builtins are compiler-managed. |
| `#thread-task-join` | `(#thread-task-join FunctionName ((arg Type)...) ReturnType)` | `(#thread-task-join ReadTask-join ((task ReadTask)) ReadTask-join-result)` (generated signature) | Internal generated function signature for joining a task and retrieving its result. |
| `#thread-task-spawn` | `(#thread-task-spawn FunctionName ((arg Type)...) ReturnType)` | `(#thread-task-spawn ReadTask-spawn ((input u64)) ReadTask-spawn-result)` (generated signature) | Internal generated function signature for creating a worker task. |
| `#tuple` | `(#tuple Type...)` as a type; `(#tuple TupleType value...)` as a value; `(#tuple pattern...)` as a pattern | `(#let pair (#tuple u64 bool) (#tuple (#tuple u64 bool) 3u64 true))` (binding) | Declares, constructs, or destructures a fixed tuple. |
| `#type` | `(#type Name Type)` | `(#type UserId u64)` (top level) | Declares a transparent alias; uses remain strongly and statically typed. |
| `#unreachable` | `(#unreachable)` | `(#case impossible (#unreachable))` (expression) | Marks a path that must never execute; execution traps. |
| `#unsafe` | `(#unsafe expression)` | `(#unsafe (#ptr-read p))` (expression) | Marks a region allowed to contain raw memory, static access, assembly, and raw syscalls. |
| `#unsafe-fn` | `(#unsafe-fn name ((arg Type)...) ReturnType body...)` | `(#unsafe-fn read-byte ((p (#ptr u8))) u8 (#return (#unsafe (#ptr-read p))))` (top level) | Declares caller safety obligations: calls require `#unsafe`, and raw operations in the body still need explicit unsafe blocks. |
| `#unsafe-impl` | `(#unsafe-impl property Type)` | `(#unsafe-impl #send NativeHandle)` (top level) | Unsafely overrides a type's structural thread-safety property; this is an author promise. |
| `#variant-is` | `(#variant-is enum-reference Variant)` | `(#let is-some bool (#variant-is value Some))` (expression) | Tests an enum reference's active variant without consuming the reference or enum; accepts ordinary or pinned shared/exclusive references. It does not statically refine later payload projections, which retain their runtime active-variant check. |
| `#when` | `(#when boolean-expression)` | `(#case (Some x) (#when (#u64.> x 0u64)) x)` (inside `#case`) | Adds a guard to a match arm; guarded arms do not alone establish exhaustiveness. |
| `#while` | `(#while condition body...)` | `(#while (#u64.< i 4u64) (#set i (#u64.+.wrap i 1u64)))` (statement) | Repeats while its boolean condition is true. |
| `#while-let` | `(#while-let pattern value body...)` | `(#while-let (Some x) next (#set total x))` (statement) | Repeatedly matches a value and runs the body while the pattern succeeds. Inside async functions, the scrutinee may remain synchronous while the body suspends. |

#### Typed operator families (alphabetical)

The qualifier is part of the identifier, not a namespace. In this table,
`I` expands to each of `i8`, `i16`, `i32`, `i64`, `i128`, `isize`,
`u8`, `u16`, `u32`, `u64`, `u128`, and `usize`; `F` expands to
`f32` or `f64`. Both operands must match the qualifier. Examples are
expressions in a function body; the operator determines their result type.
Pipe characters in the table are escaped only for Markdown rendering.

| Family | Syntax | Example (context) | Meaning |
| --- | --- | --- | --- |
| `#F.%` | `(#F.% a b)` | `(#f64.% 5.0f64 2.0f64)` (expression) | Floating-point remainder. |
| `#F.*` | `(#F.* a b)` | `(#f32.* 2.0f32 3.0f32)` (expression) | Floating-point multiplication. |
| `#F.+` | `(#F.+ a b)` | `(#f64.+ 2.0f64 3.0f64)` (expression) | Floating-point addition. |
| `#F.-` | `(#F.- a b)` or `(#F.- a)` | `(#f32.- 2.0f32)` (expression) | Floating-point subtraction or unary negation. |
| `#F./` | `(#F./ a b)` | `(#f64./ 6.0f64 2.0f64)` (expression) | Floating-point division. |
| `#I.!` | `(#I.! value)` | `(#u8.! 0u8)` (expression) | Bitwise complement. |
| `#I.%.saturate` | `(#I.%.saturate a b)` | `(#i8.%.saturate -128i8 -1i8)` (expression) | Remainder with explicit saturation mode; zero divisor traps. |
| `#I.%.wrap` | `(#I.%.wrap a b)` | `(#u64.%.wrap 7u64 3u64)` (expression) | Remainder with explicit wrapping mode; zero divisor traps. |
| `#I.&` | `(#I.& a b)` | `(#u8.& 3u8 1u8)` (expression) | Bitwise AND. |
| `#I.*.saturate` | `(#I.*.saturate a b)` | `(#u8.*.saturate 200u8 2u8)` (expression) | Multiplication clamped to the integer bounds. |
| `#I.*.wrap` | `(#I.*.wrap a b)` | `(#u8.*.wrap 200u8 2u8)` (expression) | Modular multiplication. |
| `#I.+.saturate` | `(#I.+.saturate a b)` | `(#u8.+.saturate 255u8 1u8)` (expression) | Addition clamped to the integer bounds. |
| `#I.+.wrap` | `(#I.+.wrap a b)` | `(#u8.+.wrap 255u8 1u8)` (expression) | Modular addition. |
| `#I.-.saturate` | `(#I.-.saturate a b)` or `(#I.-.saturate a)` | `(#u8.-.saturate 0u8 1u8)` (expression) | Subtraction or negation clamped to the integer bounds. |
| `#I.-.wrap` | `(#I.-.wrap a b)` or `(#I.-.wrap a)` | `(#i8.-.wrap -128i8)` (expression) | Modular subtraction or negation. |
| `#I./.saturate` | `(#I./.saturate a b)` | `(#i8./.saturate -128i8 -1i8)` (expression) | Integer division; signed overflow clamps to the maximum. Zero divisor traps. |
| `#I./.wrap` | `(#I./.wrap a b)` | `(#i8./.wrap -128i8 -1i8)` (expression) | Integer division; signed overflow wraps to the minimum. Zero divisor traps. |
| `#I.<<` | `(#I.<< value count)` | `(#u32.<< 1u32 3u32)` (expression) | Left shift; an out-of-width count is rejected or traps. |
| `#I.>>` | `(#I.>> value count)` | `(#i32.>> -8i32 1i32)` (expression) | Arithmetic right shift for signed types, logical for unsigned; count is checked. |
| `#I.^` | `(#I.^ a b)` | `(#u8.^ 3u8 1u8)` (expression) | Bitwise XOR. |
| `#I.\|` | `(#I.\| a b)` | `(#u8.\| 2u8 1u8)` (expression) | Bitwise OR. |
| `#T.!=` | `(#T.!= a b)` | `(#char.!= #\a #\b)` (expression) | Inequality returning bool; T is I, F, bool, or char. |
| `#T.<` | `(#T.< a b)` | `(#u64.< 1u64 2u64)` (expression) | Less than, returning bool; T is I, F, bool, or char. |
| `#T.<=` | `(#T.<= a b)` | `(#f32.<= 1.0f32 2.0f32)` (expression) | Less than or equal, returning bool; T is I, F, bool, or char. |
| `#T.==` | `(#T.== a b)` | `(#bool.== true false)` (expression) | Equality returning bool; T is I, F, bool, or char. |
| `#T.>` | `(#T.> a b)` | `(#char.> #\b #\a)` (expression) | Greater than, returning bool; T is I, F, bool, or char. |
| `#T.>=` | `(#T.>= a b)` | `(#i32.>= 2i32 1i32)` (expression) | Greater than or equal, returning bool; T is I, F, bool, or char. |
| `#bool.!` | `(#bool.! value)` | `(#bool.! false)` (expression) | Logical negation. |
| `#bool.&` | `(#bool.& a b)` | `(#bool.& true false)` (expression) | Boolean AND that evaluates both operands. |
| `#bool.&&` | `(#bool.&& a b)` | `(#bool.&& true false)` (expression) | Short-circuit AND; evaluates b only when a is true. |
| `#bool.^` | `(#bool.^ a b)` | `(#bool.^ true false)` (expression) | Boolean exclusive OR that evaluates both operands. |
| `#bool.\|` | `(#bool.\| a b)` | `(#bool.\| true false)` (expression) | Boolean OR that evaluates both operands. |
| `#bool.\|\|` | `(#bool.\|\| a b)` | `(#bool.\|\| true false)` (expression) | Short-circuit OR; evaluates b only when a is false. |

Plain integer arithmetic such as `#u64.+` is rejected. There is no generic
`#T.op` builtin: expand the documented family to a concrete identifier.
User-defined cfg keys such as `#feature`, `#debug`, or `#backend` are not
additional builtins and are not automatically populated; set them with
`--cfg KEY=VALUE`. The `@` generators and quote/backtick reader syntax are
documented separately; they are not `#` builtins.

### Conditionals and blocks

An `#if` without an else branch must have unit type.  Value-producing
conditionals require both branches:

```lisp syntax
(#return (#if (#u64.> value 0u64)
              value
              0u64))
```

`#block` permits statements in an expression position.  Its final expression
is its value; a block used only for side effects has unit type.

### Loops

Statement loops use `#break` without a value:

```lisp syntax
(#while (#u64.< i 10u64)
  (#set i (#u64.+.wrap i 1u64)))
```

A loop expression has a value only when a reachable break supplies one:

```lisp run=42
(#fn main () u64
  (#let result u64 (#loop (#break 42u64)))
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
(#for (#let-mut i u64 0u64)
      (#u64.< i 10u64)
      (#set i (#u64.+.wrap i 1u64))
  (#set total (#u64.+.wrap total i)))
```

Inside `@async-fn`, a unit-returning await can be the step itself:

```lisp syntax
(#for () keep-going
      (#await () StepTask StepPending StepReady step-poll step-task)
  (#set keep-going false))
```

The step starts after the body and after `#continue`, but is skipped by
`#break` and a false condition. A Pending step resumes before the next
condition check. The condition may itself await. The explicit `()` result
type makes this an effect-only step; no user-maintained dummy binding is
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
(#for () (#u64.< index 2u64)
  (#call advance
    (: next (#await u64 StepTask StepPending StepReady step-poll step-task)
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
are explicit and the range is half-open:

```lisp syntax
(#for-range (i u64) 0u64 10u64
  (#set total (#u64.+.wrap total i)))
```

Labels wrap statement loops with `#label`, and value-loop breaks can target an
outer value loop:

```lisp run=42
(#fn main () u64
  (#return
    (#label outer
      (#loop (#break-to outer 42u64)))))
```

Recursive calls are rejected.  Mutual recursion is rejected as well.

## Patterns and matching

`#match` is exhaustive for enums and scalar booleans; `_` supplies a wildcard.
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
  (#case (Some payload) (#when (#u64.> payload 40u64)) payload)
  (#case (Some _) 0u64)
  (#case None 0u64))
```

Destructuring uses the same aggregate pattern shapes:

```lisp syntax
(#let (#tuple left right) (#tuple u64 u64) pair)
```

The pattern syntax is checked against the explicitly declared type; bindings
are not inferred.

## Generated declarations

`@` marks a generated declaration. Compiler-provided generators take one
colon-prefixed list of named literal arguments. Keys may be written in any
order, but every required key must appear exactly once. User-defined `#gn`
generators retain their own positional literal interface. For example:

```lisp library
(@optional (: type u64 : name Maybe?))
(@result (: ok u64 : error u32 : name Result))
```

`(@optional (: type T : name Name))` creates an enum with `Name-some` and `Name-none`, plus
free-standing helpers:

- `Name-construct`
- `Name-is-some`
- `Name-unwrap-or`

`(@result (: ok Ok : error Err : name Name))` creates `Name-ok-value` and `Name-err-value`, plus:

- `Name-ok` and `Name-err` constructors;
- `Name-is-ok`;
- `Name-unwrap-or` and `Name-unwrap-err-or`.

Expansion is part of program parsing. Readable generated Lim sources for both
built-in and user-defined `@` invocations are stored as hash-named `.lim` files
under `.lim/cache/`. Their keys include the invocation, compiler version,
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

## Value representation and native backend

The backend emits Intel-syntax x86-64 assembly and follows the explicit
`x86_64-sysv` target description. Scalar integer and pointer-sized ABI words use general
purpose registers; `f32` and `f64` values use SSE registers.  `i128` and
`u128` use two machine words.

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
Unsafe external calls in named `#call` syntax underline the callee; raw-pointer
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
# Generated thread calls

Spawn and join are ordinary named calls, including when the compiler derives
their signatures from a short `#thread-task` declaration. Spawn uses the
worker's parameter names; join uses `task`. For example, write
`(#call Task-join (: task handle))`. Generated enum variants in
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
