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
- [ ] Add borrowable enum-payload projections. Enum payload mutation already
  participates in place conflict checking, but source-level payload projection
  is not yet exposed by `#get`.
- [ ] Define and implement complete reference projection rules for nested
  aggregates, including references stored inside references and aggregates.
- [ ] Add borrow-checker diagnostics with source spans, the original borrow
  site, the conflicting access, and generator invocation context.
- [ ] Add regression tests for every remaining projection and control-flow
  combination, including branch-local drops and multiple derived field loans.
- [ ] Remove or update stale comments that still describe references as not
  being first-class values.

### Values, memory, and aggregates

- [ ] Specify the dynamic allocation ABI and allocator ownership model.
- [ ] Implement allocator-backed generated collections, beginning with the
  concrete `@vec` and `@vec-sort` design.
- [ ] Define allocation failure, deallocation, destruction, and leak behavior.
- [ ] Add aggregate `#deref`/`#deref-set` support, or explicitly replace these
  scalar-only forms with projection operations for all aggregate types.
- [ ] Remove backend restrictions on large aggregate returns, arguments, and
  reference projections.
- [ ] Specify and implement field-wise destruction for reference-containing
  aggregates.

### Generators and monomorphization

- [ ] Decide whether the currently implemented angle-bracket generic syntax is
  retained. If generators are the sole specialization mechanism, remove or
  deprecate generic declarations and migrate the examples.
- [ ] Add generator dependency tracking for imported files and compiler
  configuration values, not only generator definitions and nested generators.
- [ ] Make generated-file cache entries durable across compiler-version and
  target changes.
- [ ] Improve generator diagnostics so failures identify the generator,
  invocation, argument position, and generated source location.
- [ ] Add capability-aware generators without hidden typeclass/interface
  requirements; capabilities must remain explicit in generator inputs.

### Backend, platform, and interoperation

- [ ] Add a target description instead of assuming host x86-64 System V ABI.
- [ ] Implement the planned native assembler/backend path so Clang is no
  longer required for normal compilation.
- [ ] Define FFI declarations, calling conventions, layout guarantees, and
  safety boundaries for external libraries.
- [ ] Add runtime support for thread creation/join failures instead of
  unconditionally aborting the process.
- [ ] Add compile-and-run coverage for the binary pipeline under the Nix
  development shell.

### Language completeness and tooling

- [ ] Add structured compiler diagnostics and stable error codes.
- [ ] Add a formatter and a syntax-aware pretty-printer for generated code.
- [ ] Add a command that checks all examples and reports failures by source
  file, including generated examples.
- [ ] Add package/project metadata and a stable module search path beyond
  relative imports.
- [ ] Document the complete grammar and specify the semantics of every
  builtin, especially ownership, `#unsafe`, thread, generator, and cfg forms.
- [ ] Decide whether closures, function pointers, methods, traits, and user
  interfaces remain permanent non-goals; document the decision explicitly.
