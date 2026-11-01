# Lim allocation ABI

This document specifies the first dynamic-memory ABI. It is deliberately
small enough for generated collections and does not introduce function
pointers, closures, methods, or implicit allocators.

## Standard system allocator and String

`library/system_allocator.lim` implements a native Lim process heap on Linux
x86-64. It uses raw `mmap`, `mremap`, and `munmap` syscalls, not libc, FFI,
external allocator code, or thread-local runtime state.
`system-allocate (: size #usize)`
returns `SystemAllocated` with a raw pointer, or `SystemAllocationFailed` with
`SystemAllocationOutOfMemory` or `SystemAllocationInvalidSize`. Zero-size
requests and sizes above `SYSTEM-ALLOCATION-MAX` (PTRDIFF_MAX) are rejected
before accessing the heap. Empty owners therefore keep a null pointer without
requesting a zero-size allocation.

`system-reallocate (: pointer (#ptr-mut #u8) : size #usize)` and
`system-deallocate (: pointer (#ptr-mut #u8))` are unsafe functions. The caller
must supply live storage from this allocator, ensure unique access, and stop
using the old pointer after successful reallocation or deallocation. Failed
reallocation leaves the original allocation valid. Reallocation never uses a
zero size. A null input to reallocation allocates fresh storage; null
deallocation is a no-op. Deallocation is explicit; there is no implicit destructor.

Call safe `system-allocate` with `#call`. Calls to `system-reallocate` and
`system-deallocate` require `#unsafe-call` inside `#unsafe`; `#call` rejects
them even within that block. Both call forms use the same named arguments.
For example, this allocates fresh storage through the documented null-input
reallocation path, then releases the successful allocation:

```lisp run=42
(#std)
(#fn main () #u64
  (#let allocation SystemAllocationResult
    (#unsafe (#unsafe-call system-reallocate
      (: pointer (#ptr-null (#ptr-mut #u8)) : size 16usize))))
  (#return (#match allocation
    (#case (SystemAllocationResult.SystemAllocated pointer)
      (#block
        (#unsafe (#unsafe-call system-deallocate (: pointer pointer)))
        42u64))
    (#case (SystemAllocationResult.SystemAllocationFailed error)
      (#block (#drop error) 0u64)))))
```

Allocations are aligned to `SYSTEM-ALLOCATION-ALIGNMENT` (16 bytes). Sizes
up to 4080 bytes use power-of-two block classes in 64 KiB slabs; a 16-byte
header precedes each payload. Partially occupied slabs maintain per-class
free lists under an acquire/release atomic lock. One empty slab per class
is cached (at most 512 KiB of mapped space); additional empty slabs are
unmapped. Large allocations use dedicated page-rounded mappings.

Reallocation within the existing capacity updates the requested size in
place. Growth out of a small class allocates, copies the old requested bytes,
and frees the old block only after success. Large growth uses `mremap` with
movement permitted; failure preserves the original mapping and bytes.
Successful reallocation invalidates the old pointer for further use, even
when its numeric address is unchanged. Never reallocate live pinned storage.

The heap supports concurrent calls, including generated raw kernel workers.
It is not async-signal-safe, and fork children must not use a lock inherited
while held by a different thread. It has no over-aligned allocation interface.
Invalid pointers, double frees, concurrent accesses to a freed/resized block,
and mixing this heap with a foreign `malloc`/`free` pair violate the unsafe
caller contract. Implementation entry points use `system-heap-*` names;
the library does not define or replace C `malloc`, `realloc`, or `free`.

`library/string.lim` builds an opaque, linear `String` from these functions.
Its length and capacity are UTF-8 byte counts. Constructors and deep cloning
are fallible; reserve uses checked geometric growth. Bulk appends validate
the entire input and reserve once before copying, so an error cannot leave a
partially appended string. UTF-8 validation rejects truncated sequences,
invalid continuation bytes, overlong encodings, surrogate code points, and
scalars above U+10FFFF. Interior NUL is permitted; no terminating NUL is added.
Borrowed `StringBytes` views retain an owner borrow; byte indexing copies a
`#u8` and no mutable byte access is public. `String-free` consumes the owner
and returns its allocation to the native heap exactly once. `String-clear` retains
allocated capacity; an empty
string with retained capacity still needs freeing.

`library/utf8_view.lim`, included by `#std`, generates validated borrowed text
views over String allocations or shared byte slices. `String-view` is a
constant-time borrow; `Utf8Slice::from-owner` validates without allocation.
Checked byte-boundary subviews, explicit view clones, and character iterators
retain the original source loan even after a parent view is forgotten.
They never copy or destroy the owner. Packed heap bytes and word-backed Lim
slices use distinct safe readers. See the borrowed UTF-8 view section in
`docs/language.md` for the complete generated API and unsafe-constructor contract.

The allocator is fixed by this concrete library type, not selected implicitly
by a call or borrowed from a temporary allocator instance. It is a
process-wide allocator with process lifetime. Collections using user-defined
allocators continue to retain the instance borrow described below.

This library adds no Rust crate dependencies, invokes no external linker
tools, and introduces no dynamic-library dependency. String-only programs
link as native static executables. Other explicitly imported FFI functions
can still require dynamic libraries. The String library does not override
structural Send/Sync checks: removing libc does not authorize transferring
an otherwise non-Send owner or reference between threads.

## Allocator bundles

An allocator bundle is a naming convention rooted at a literal symbol such as
`SystemAllocator::Allocator` or `Arena::Allocator`. It introduces no trait,
property, dynamic dispatch, or producer provenance requirement. Handwritten
declarations and generator-produced declarations satisfy the same convention.
Consumers resolve ordinary names and their generated calls are statically checked.

A root exposes `Root::State`, `Root::Error`, `Root::Allocation`,
`Root::Allocation.Allocated`, `Root::Allocation.AllocationFailed`, `Root::allocate`,
`Root::grow`, and `Root::deallocate`. State and Error may be aliases to
existing types. Allocation carries a raw byte pointer on success and Error on
failure. Pinned Box and Rc request only allocate and deallocate adapters, so
their bundles may omit grow. The shared adapter generator accepts an explicit
literal `:operations` list to select the operations it emits.

```lisp syntax
(#generate #allocator-for (: allocator Root : type T : name TypedAllocator
  : operations (allocate deallocate)))
```

This emits typed allocate and deallocate adapters without referencing
`Root::grow`. Request `:operations (allocate grow deallocate)` when all three
adapters are needed. Each listed operation must be `allocate`, `grow`, or
`deallocate`; consumers check the signatures of the selected operations.

`#std` includes the shared convention helpers and
`SystemAllocator::Allocator`, backed by the native process heap above.
Its State aliases the empty `SystemAllocator` struct; construct an instance
with `(#struct-literal SystemAllocator ())`. Its Error aliases
`SystemAllocationError`. Layouts are byte counts and alignments are byte
alignments; unsupported alignment or invalid sizes fail explicitly.

Pinned consumers use exactly these public options:

```lisp syntax
(#generate #pin-box (: type T : allocator Root : name Box : destroy destroy-value))
(#generate #pin-rc (: type T : allocator Root : name Rc : destroy destroy-value))
```

Each generates its own typed adapter for the bundle's byte-pointer ABI.
The safe destroy callback takes
`(: allocator (#ref Root::State) : pin (#pin-ref-mut T))` and performs
explicit in-place cleanup. A callback accepting the original State alias is
equivalent. Rc adapts pointers to its generated control block internally;
providers never depend on that control-block type.

## Allocator identity

An allocator is an ordinary user-defined value with a stable concrete type.
Collections store an immutable reference to that value:

```lisp library
(#alias cell-generator = ../library/cell.lim::#cell)
(#generate cell-generator #usize CellUsize CellUsize::create CellUsize::get CellUsize::set)
(#struct AllocatorU64 () ((cursor CellUsize)))
(#struct VecU64 () ((allocator (#ref AllocatorU64))
                 (pointer (#ptr-mut #u64))
                 (length #usize)
                 (capacity #usize)))
```

The reference is immutable at the type level. Allocator implementations use
explicit interior-mutable state such as the generated `#generate #cell` type to track
their allocation state. The allocator type is part of the
collection's concrete generated type. Each owner retains the particular
instance reference used at construction and passes it to every operation.

`#generate #vec` must therefore generate a distinct concrete type for each allocator
type and element type. A generated collection retains the allocator borrow for
its entire lifetime. Moving or returning the collection also moves that borrow;
the collection cannot outlive the allocator. Other collection generators must
obey the same ownership rule.

The concrete representation is declared first:

```lisp syntax
(#generate #vec (: element ElementType : allocator AllocatorType : name ConcreteVecType))
```

It emits `ConcreteVecType` with `allocator`, `pointer`, `length`, and
`capacity` fields, plus `ConcreteVecType-new-with-storage`, `-len`, and
`-capacity`. The allocator-backed API is then generated separately:

```lisp syntax
(#generate #vec-alloc (: element ElementType : allocator Root : vector ConcreteVecType : destroy destroy-name))
```

Here `Root::State` must denote the state type passed to `#generate #vec`.
The representation generator still accepts a state type, not a bundle root.
The consumer converts byte pointers to element pointers internally and calls
the root's operations directly. The explicit safe destruction function takes
`(: allocator (#ref Root::State) : value ElementType)`. This lets destruction
use allocator-local interior-mutable state without function pointers.

The generated API includes an empty `-new`, checked geometric `-reserve`,
`-push`, `-get`, `-get-mut`, `-set`, `-pop`, and explicit `-free`. Allocation
and capacity failures are returned in concrete generated result enums. On a
failed push, the error value retains ownership of the element; a failed
reserve leaves the vector's pointer and capacity unchanged. `-set` explicitly
destroys the replaced element, `-pop` transfers ownership to its caller, and
`-free` destroys each remaining element once before deallocating storage.
Zero-sized elements do not call the allocator or deallocator, but their
logical elements are still destroyed individually.

Sorting is generated separately and takes a comparator name as a literal
input:

```lisp syntax
(#generate #vec-sort (: element ElementType : vector ConcreteVecType : comparator comparator-name))
```

The comparator must have the concrete signature
`((left (#ref ElementType)) (right (#ref ElementType))) #bool`. The generated
`ConcreteVecType-sort` makes a direct call to that named function; no
function-pointer value or runtime dispatch is created. It uses iterative
insertion sort, so it does not add recursion to the program call graph. A
zero-sized element vector is left unchanged.

## Required operations

Bundle operations have these concrete signatures:

```lisp syntax
(#type Root::State Arena)
(#type Root::Error ArenaError)
(#enum Root::Allocation ()
  ((Root::Allocation.Allocated (#ptr-mut #u8))
   (Root::Allocation.AllocationFailed Root::Error)))

(#fn Root::allocate
  (: allocator (#ref Root::State) : layout #usize : alignment #usize)
  Root::Allocation)

(#unsafe-fn Root::grow
  (: allocator (#ref Root::State) : pointer (#ptr-mut #u8)
   : old-layout #usize : layout #usize : alignment #usize)
  Root::Allocation)

(#unsafe-fn Root::deallocate
  (: allocator (#ref Root::State) : pointer (#ptr-mut #u8)
   : layout #usize : alignment #usize)
  ())
```

`allocate` is safe and called with `#call`. `grow` and `deallocate`
are unsafe declarations, called with `#unsafe-call` inside `#unsafe`.
Using `#call` for an unsafe operation remains an error inside an unsafe block.
Growth's `layout` is the requested new byte size, and `old-layout` is the
previous byte size. Failed growth preserves the old allocation and all its
initialized bytes; successful growth transfers ownership to the returned
pointer. Do not grow live pinned storage.

These signatures are generator contracts rather than interfaces or dynamic
dispatch. The generated calls are statically checked like every other Lim
call. The element type is used through explicit `#size-of`/`#align-of`
expressions in generated code.

Raw pointer operations remain inside `#unsafe`. A collection generator is
responsible for establishing the safety invariant that a pointer is either
null with zero capacity or points to an allocation large enough for the
collection's initialized elements.

## Allocation failure and destruction

Allocation failure is an explicit `Root::Allocation.AllocationFailed Root::Error` result.
A successful allocation promises fresh, uniquely owned, non-null storage of
at least the requested byte size and alignment. Growth failure preserves the
old allocation and its initialized bytes; successful growth returns uniquely
owned storage and retires the old pointer. Deallocation must release the
matching allocation exactly once. These are semantic promises made by a
custom provider: names, types, and generated-call checking cannot prove them.
No allocator operation may return a null pointer as a successful allocation.
`deallocate` is called only
for a pointer previously returned by the same allocator instance, with the
same layout and alignment. A zero-sized element uses a non-dereferenceable
sentinel and has no allocation requirement.

Collections are responsible for deallocation when they are explicitly
destroyed or reach the language's future deterministic destruction point.
Until that destruction mechanism is implemented, generated collections must
provide an explicit `-free` function and the language reports leaked owned
allocations only as a runtime/debugging concern, not as undefined behavior.

The ABI passes allocator references, pointers, layouts, and results using the
normal Lim native calling convention. There is no hidden global allocator and
no implicit allocation in constructors, moves, clones, or function calls.
