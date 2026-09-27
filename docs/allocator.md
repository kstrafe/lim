# Lim allocation ABI

This document specifies the first dynamic-memory ABI. It is deliberately
small enough for generated collections and does not introduce function
pointers, closures, methods, or implicit allocators.

## Allocator identity

An allocator is an ordinary user-defined value with a stable concrete type.
Collections store an immutable reference to that value:

```lisp library
(#import "../library/cell.lim")
(@cell usize CellUsize CellUsize-create CellUsize-get CellUsize-set)
(#struct AllocatorU64 ((cursor CellUsize)))
(#struct VecU64 ((allocator (#ref AllocatorU64))
                 (pointer (#ptr-mut u64))
                 (length usize)
                 (capacity usize)))
```

The reference is immutable at the type level. Allocator implementations use
explicit interior-mutable state such as the generated `@cell` type to track
their allocation state. The allocator type is part of the
collection's concrete generated type, so two allocator instances cannot be
accidentally mixed.

`@vec` must therefore generate a distinct concrete type for each allocator
type and element type. A generated collection retains the allocator borrow for
its entire lifetime. Moving or returning the collection also moves that borrow;
the collection cannot outlive the allocator. `@vec-ref-alloc` and similar
generators may produce alternate concrete layouts, but they must obey the same
ownership rule.

The concrete representation is declared first:

```lisp syntax
(@vec ElementType AllocatorType ConcreteVecType)
```

It emits `ConcreteVecType` with `allocator`, `pointer`, `length`, and
`capacity` fields, plus `ConcreteVecType-new-with-storage`, `-len`, and
`-capacity`. The allocator-backed API is then generated separately:

```lisp syntax
(@vec-alloc ElementType AllocatorType ConcreteVecType
  AllocResult AllocError alloc-name grow-name dealloc-name destroy-name)
```

The allocation result must contain `(#ptr-mut ElementType)` on success and
`AllocError` on failure. The four function names are literal inputs; they
resolve to ordinary, statically checked functions. Allocation, growth, and
deallocation functions receive `(#ref AllocatorType)` followed by layout and
alignment values (growth also receives the old pointer and old layout). The
element destruction function receives the allocator reference and one owned
element. This lets destruction use allocator-local interior-mutable state
without function pointers or a hidden global context.

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
(@vec-sort ElementType ConcreteVecType comparator-name)
```

The comparator must have the concrete signature
`((left (#ref ElementType)) (right (#ref ElementType))) bool`. The generated
`ConcreteVecType-sort` makes a direct call to that named function; no
function-pointer value or runtime dispatch is created. It uses iterative
insertion sort, so it does not add recursion to the program call graph. A
zero-sized element vector is left unchanged.

## Required operations

The compiler recognizes the following allocator operation signatures when a
collection generator requests them. They are ordinary free-standing functions
whose names are supplied as literal generator arguments:

```lisp syntax
(#enum AllocError (OutOfMemory))
(@result (#ptr-mut u8) AllocError AllocResult)

(#fn allocator-alloc
  ((allocator (#ref AllocatorU64)) (layout usize) (alignment usize))
  AllocResult)

(#fn allocator-dealloc
  ((allocator (#ref AllocatorU64))
   (pointer (#ptr-mut u8))
   (layout usize)
   (alignment usize))
  ())

(#fn allocator-grow
  ((allocator (#ref AllocatorU64))
   (pointer (#ptr-mut u8))
   (old-layout usize)
   (new-layout usize)
   (alignment usize))
  AllocResult)
```

These signatures are generator contracts rather than interfaces or dynamic
dispatch. The generated calls are statically checked like every other Lim
call. The element type is used through explicit `#size-of`/`#align-of`
expressions in generated code.

Raw pointer operations remain inside `#unsafe`. A collection generator is
responsible for establishing the safety invariant that a pointer is either
null with zero capacity or points to an allocation large enough for the
collection's initialized elements.

## Allocation failure and destruction

Allocation failure is an explicit `AllocError` result. No allocator operation
may return a null pointer as a successful allocation. `dealloc` is called only
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
