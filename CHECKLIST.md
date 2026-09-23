# Lim implementation checklist

This is the working roadmap for the language. Checked items are implemented
and covered by the current test suite. Keep this file uncommitted while using
it as the project checklist; cross items off as they are completed.

## Completed foundation

- [x] S-expression lexer and parser with comments, strings, characters, and
  numeric literals.
- [x] Nix development shell with the Rust toolchain.
- [x] Explicit `#`-prefixed builtin syntax; legacy unprefixed forms rejected.
- [x] Explicit typed bindings, free-standing functions, and explicit returns.
- [x] Builtin scalar types through 128-bit integers, floats, `bool`, `char`,
  unit, and never.
- [x] Explicitly qualified arithmetic, comparison, shift, cast, and overflow
  operations.
- [x] Structs, enums, tuples, arrays, aliases, destructuring, and keyed
  struct construction.
- [x] Linear/affine values with explicit `#clone` and structural `Copy`
  handling.
- [x] Recursion rejection and finite call-graph checking.
- [x] Native x86-64 assembly generation and default Clang linking to a binary.
- [x] Internal and external imports with cycle detection and deduplication.
- [x] `@` generated declarations, user generators, `#gn-*` operations,
  quasiquote/unquote, generator limits, and generator error reporting.
- [x] Generated-code caching keyed by generator code, dependencies, and
  literal invocation inputs.
- [x] Raw pointers, `#unsafe`, unsafe statics, and pointer access checks.
- [x] Structural `Send`/`Sync`, unsafe overrides, and generated thread
  spawn/join operations.
- [x] Compile-time `#cfg-*` forms, automatic platform keys, and
  `--collect-cfgs`.
- [x] Lexical borrow checking with reference provenance, control-flow joins,
  loop handling, mutable references in aggregates, field-sensitive struct
  places, derived-field suspension, and `#drop` loan release.

## Next implementation work

### Borrowing and references

- [x] Extend place-sensitive borrowing to nested tuple fields and array
  elements, including dynamic array indices that conservatively conflict with
  every element. Tuple and array projections now work through references.
- [x] Add borrowable enum-payload projections with explicit
  `#get-payload reference Variant index` syntax and place-sensitive conflict
  checking.
- [x] Define and implement reference projection rules for nested aggregates,
  including references stored inside tuple and struct aggregates and nested
  reference chains.
- [ ] Add borrow-checker diagnostics with source spans, the original borrow
  site, the conflicting access, and generator invocation context.
- [x] Add regression tests for the supported projection and control-flow
  combinations, including nested tuples, static/dynamic arrays, branch-local
  projections, and multiple derived field loans.
- [x] Remove stale comments that described references as not being first-class
  values.

### Values, memory, and aggregates

- [x] Specify the dynamic allocation ABI and allocator ownership model in
  `docs/allocator.md`.
- [x] Implement allocator-backed generated collections, beginning with the
  concrete `@vec` representation and explicit `@vec-sort` design.
- [x] Define allocation failure, deallocation, destruction, and current leak
  behavior in `docs/allocator.md`.
- [x] Add aggregate `#deref`/`#deref-set` support for aggregates that fit the
  native value registers; larger aggregate ABI support remains a separate item.
- [x] Remove backend restrictions on large aggregate returns, arguments, and
  reference projections by routing them through indirect aggregate storage.
- [x] Specify and implement field-wise destruction for reference-containing
  aggregates.

### Generators and monomorphization

- [x] Reject angle-bracket generic declarations and applications. Concrete
  specialization is generator-driven, and generic examples use concrete names.
- [x] Add generator dependency tracking for imported files and compiler
  configuration values, not only generator definitions and nested generators.
- [x] Make generated-file cache entries durable across compiler-version and
  target changes by including both values in the cache key namespace.
- [x] Improve generator diagnostics so failures identify the generator,
  invocation, argument position, and generated source location.
- [x] Add capability-aware generators without hidden typeclass/interface
  requirements; `#capability` declarations are checked against explicit
  generator parameter requirements before evaluation.

### Backend, platform, and interoperation

- [x] Add an explicit target description for the native x86-64 System V ABI;
  unsupported target names are rejected rather than silently treated as host.
- [x] Implement the native x86-64 assembler/linker path; normal compilation
  invokes `as` and `ld` directly, without requiring Clang.
- [x] Define constrained FFI declarations: `#extern-fn` uses the target C ABI,
  accepts directly passed scalar signatures only, and requires `#unsafe` at
  every call site.
- [x] Add failure-safe thread creation/join behavior: generated spawn returns a
  null task on allocation/creation failure, and join returns a zeroed result on
  a null task or join failure instead of unconditionally aborting.
- [x] Add compile-and-run coverage for the binary pipeline under the Nix
  development shell.

### Language completeness and tooling

- [x] Add public structured diagnostics with stable phase/category codes,
  optional source spans, and notes while retaining the existing string APIs.
- [x] Add a parser-backed formatter and syntax-aware pretty-printer, exposed
  through `format_source` and `--format INPUT [OUTPUT]`.
- [x] Add `--check-examples [DIRECTORY]`, which checks all `.lim` examples and
  reports failures by source file, including generated examples.
- [ ] Add package/project metadata and a stable module search path beyond
  relative imports.
- [ ] Document the complete grammar and specify the semantics of every
  builtin, especially ownership, `#unsafe`, thread, generator, and cfg forms.
- [x] Closures, function pointers, methods, traits, and user interfaces are
  documented as permanent non-goals; named free-standing functions and
  generators provide the explicit alternatives.
