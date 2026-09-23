# Lim allocation ABI

This document specifies the first dynamic-memory ABI. It is deliberately
small enough for generated collections and does not introduce function
pointers, closures, methods, or implicit allocators.

## Allocator identity

An allocator is an ordinary user-defined value with a stable concrete type.
Collections store an immutable reference to that value:

```lisp
(#struct VecU64 ((allocator (#ref AllocatorU64))
                 (pointer (#ptr-mut u64))
                 (length usize)
                 (capacity usize)))
```

The reference is immutable at the type level. Allocator implementations use
explicit interior-mutable state such as `#cell` or a user-defined generated
cell type to track their allocation state. The allocator type is part of the
collection's concrete generated type, so two allocator instances cannot be
accidentally mixed.

`@vec` must therefore generate a distinct concrete type for each allocator
type and element type. A generated collection retains the allocator borrow for
its entire lifetime. Moving or returning the collection also moves that borrow;
the collection cannot outlive the allocator. `@vec-ref-alloc` and similar
generators may produce alternate concrete layouts, but they must obey the same
ownership rule.

## Required operations

The compiler recognizes the following allocator operation signatures when a
collection generator requests them. They are ordinary free-standing functions
whose names are supplied as literal generator arguments:

```lisp
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
dispatch. A generator validates the literal function names and emitted calls
are statically checked like every other Lim call. The element type is used to
calculate `layout` and `alignment` at generation time or through explicit
`#size-of`/`#align-of` expressions in generated code.

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
