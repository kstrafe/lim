# Lim implementation checklist

This is the working roadmap for the language. Checked items are implemented
and covered by the current test suite. Cross items off as they are completed;
the checklist is committed alongside the implementation it tracks.

## Completed foundation

- [x] S-expression lexer and parser with comments, strings, characters, and
  numeric literals.
- [x] Nix development shell with the Rust toolchain.
- [x] Explicit `#`-prefixed builtin syntax; legacy unprefixed forms rejected.
- [x] Explicit typed bindings, free-standing functions, and explicit returns.
- [x] Require named function arguments using `#call` and `#fn-args`; reject
  positional calls and validate argument labels at compile time.
- [x] Builtin scalar types through 128-bit integers, floats, `bool`, `char`,
  unit, and never.
- [x] Explicitly qualified arithmetic, comparison, shift, cast, and overflow
  operations.
- [x] Structs, enums, tuples, arrays, aliases, destructuring, and keyed
  struct construction.
- [x] Linear values with structural plain-old-data `Copy`, explicit `#clone`,
  explicit `#forget`, and consume-before-scope/return checks.
- [x] Recursion rejection and finite call-graph checking.
- [x] Native x86-64 assembly generation and direct `as`/`ld` binary linking.
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
  places, derived-field suspension, and explicit `#drop`/`#forget` loan release.
- [x] Audit public documentation and checklist claims against implemented
  behavior; replace the obsolete README generic examples and update the build
  instructions to describe direct `as`/`ld` linking and concrete generators.

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
- [x] Add borrow-checker diagnostics with stable `E4100`, function/statement
  context, exact source underlines for borrow operators and conflicting
  borrow/read/write accesses, and preserved generator/source context where
  available.
- [x] Add regression tests for the supported projection and control-flow
  combinations, including nested tuples, static/dynamic arrays, branch-local
  projections, and multiple derived field loans.
- [x] Remove stale comments that described references as not being first-class
  values.
- [x] Add unsafe raw-pointer-to-reference operations whose explicit reference
  anchor feeds inferred lifetime provenance into the borrow checker.

### Values, memory, and aggregates

- [x] Specify the dynamic allocation ABI and allocator ownership model in
  `docs/allocator.md`.
- [x] Define the concrete allocator-borrowing `@vec` representation and the
  explicit `@vec-sort` invocation contract.
- [x] Implement usable allocator-backed vectors: construction, checked
  reserve/growth, push, indexed read/write, pop, and explicit destruction.
  Allocation and capacity failures must be represented with generated
  `Result` types, including zero-sized element behavior.
- [x] Implement `#ptr-offset` for raw pointers, with a `usize` element index,
  explicit `#unsafe` boundaries, zero-sized pointee handling, and checked
  byte-offset/address overflow.
- [x] Add typed `#ptr-null` construction so allocator-backed collections can
  represent an empty, zero-capacity storage state without an uninitialized
  pointer.
- [x] Add non-consuming `#ptr-is-null` so allocator wrappers can report
  allocation failure without losing the returned pointer value.
- [x] Implement `@vec-sort` using its literal comparator function name, with
  compile-time signature validation and no runtime function-pointer values.
- [x] Define allocation failure, deallocation, destruction, and current leak
  behavior in `docs/allocator.md`.
- [x] Add aggregate `#deref`/`#deref-set` support for aggregates that fit the
  native value registers; larger aggregate ABI support remains a separate item.
- [x] Remove backend restrictions on large aggregate returns, arguments, and
  reference projections by routing them through indirect aggregate storage.
- [x] Finish large aggregate lowering for nested multiword fields and payloads
  across returns, globals, reference projections, patterns, and native ABI
  boundaries; several backend branches still report scalar-field-only limits.
- [x] Specify and implement field-wise destruction for reference-containing
  aggregates.
- [x] Define and test deterministic explicit destruction for owned resources
  and generated collections: user/generated destroy functions consume values,
  including after moves/returns and field-wise aggregate destruction; no
  implicit destructor calls are inserted, and `-free` consumes a vector.

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
- [x] Add generated native thread creation/join behavior with structural
  `Send` checks, captured-borrow tracking, and explicit runtime failure paths.
- [x] Replace thread null/zero failure sentinels with explicit fallible
  spawn/join results. Preserve task ownership and borrow state on failed join,
  and make it possible to distinguish a valid zero result from runtime failure.
  Spawn reports allocation versus creation errors; join failure returns its
  still-owned handle and native error code. Runtime tests cover both direct and
  indirect result layouts and injected spawn/join failures.
- [x] Add compile-and-run coverage for the binary pipeline under the Nix
  development shell.

### Language completeness and tooling

- [x] Add public structured diagnostics with stable phase/category codes,
  optional source spans, and notes while retaining the existing string APIs.
- [x] Add a parser-backed formatter and syntax-aware pretty-printer, exposed
  through `format_source` and `--format INPUT [OUTPUT]`.
- [x] Preserve semicolon comments and source annotations in formatted output
  (commented files are currently preserved verbatim); keep parser-backed
  canonical formatting idempotent for generator templates and generated
  declarations.
- [x] Add `--check-examples [DIRECTORY]`, which checks all `.lim` examples and
  reports failures by source file, including generated examples.
- [x] Add dependency-free `lim.project` metadata with a project name and
  manifest-relative module paths; these are loaded by the binary CLI, alongside
  the explicit `CompileConfig::add_module_path` and `--module-path` APIs.
- [x] Extend project metadata with a versioned schema, explicit source root and
  output directory, target/link settings, and validation for duplicate or
  nonexistent module roots.
- [x] Document the core grammar and builtin semantics, including ownership,
  `#unsafe`, thread, generator, cfg, and explicit arithmetic forms.
- [x] Closures, function pointers, methods, traits, and user interfaces are
  documented as permanent non-goals; named free-standing functions and
  generators provide the explicit alternatives.

### Newly identified runtime and language gaps

- [x] Add end-to-end tests that compile and execute generated vector operations
  with a real allocator, covering growth, allocation failure, element
  destruction, and allocator-borrow lifetime enforcement.
- [x] Make FFI linking configurable for external libraries and object files;
  `#extern-fn` remains restricted to scalar signatures, while binary compilation
  accepts repeated `--link-lib` and `--link-object` arguments in deterministic
  object-before-library order after the built-in C and pthread libraries.
- [x] Specify reusable C layout metadata for external aggregates: explicit
  `#repr-c`, declaration-order fields, natural alignment/padding, tagged-union
  enum layout, `#size-of`/`#align-of`/`#offset-of`, and explicit `#abi-c` on
  external functions. By-value aggregate FFI remains rejected until Lim's
  runtime aggregate representation can match C's ABI.
- [x] Define a recoverable compilation/linking diagnostic API end to end.
  `compile_source_to_assembly`, generated-source materialization, and
  `link_native_binary` return structured diagnostics with stable phase codes;
  the CLI uses those APIs for normal binary and assembly builds while legacy
  string-returning APIs remain available.
- [x] Add Rust-style CLI diagnostic rendering with source excerpts and
  underlines for errors that carry or expose a source location.
- [ ] Carry exact spans from parsed expressions into every type, ownership,
  borrow, unsafe, generator, and codegen error. Source identities and contents
  are retained across imports, but some analysis fallbacks still underline a
  containing statement rather than the precise offending expression.
- [x] Specify generator capability contracts beyond name membership: bind each
  capability/type pair to concrete free-standing operation signatures, validate
  function existence and exact signatures before expansion, and include a
  deterministic capability-contract hash in generated-code cache keys.
- [x] Add a soundness-focused audit and adversarial regression suite for
  unsafe pointer operations, reference provenance through aggregate/control
  flow forms, `Send`/`Sync` overrides, and generated destruction paths;
  `docs/soundness-audit.md` maps each invariant to its regression evidence and
  records the limits of unsafe promises.

## Remaining hardening and platform work

These items close known gaps between the implementation, its safety claims,
and the documented behavior. They are not prerequisites for the current
single-target experimental compiler, but should be completed before treating
these areas as stable.

### Safety audit and ownership

- [x] Re-audit thread spawn/join failure paths, including task-handle
  ownership and captured borrows on every success and error branch. Reconcile
  the checklist claims, regression tests, and `docs/soundness-audit.md`; add
  adversarial tests for any uncovered paths.
- [x] Extend the soundness audit with explicit invariants and adversarial
  tests for unsafe `Send`/`Sync` overrides, raw-pointer-derived references,
  and unsafe destruction/allocator interactions. Clearly distinguish
  compiler-enforced guarantees from programmer promises.

### Diagnostics and generated source

- [x] Add CLI UI regression fixtures for lexical/parser errors, imports and
  cycles, cfg and type/named-call errors, struct literals, borrow, linearity,
  top-level type mismatches, unsafe, recursion, duplicate
  parameters, fields, local/cross-enum variants, types, and recursive aliases;
  thread ownership and thread-safety; generator invocation,
  capability-contract and #gn-fn recursion failures; and codegen failures.
  Assert diagnostic categories, source lines,
  underlines, and key token alignment, including imported files and nested
  expressions.
- [x] Ensure source-level compilation errors carry a source location and
  underline the responsible Lim statement, declaration, or expression across
  parsing, imports/cfg, generators, type/ownership/borrow/unsafe checking, and
  code generation. CLI UI coverage exercises representative failures in each
  phase. Some diagnostics use a containing statement/declaration span where
  the exact inner token is not retained; exact-span coverage remains tracked
  separately above.
- [x] Add diagnostic regression tests for nested expressions and imported
  generated source locations, asserting the exact highlighted source range.

### Native ABI and targets

- [x] Make `#repr-c` layout guarantees match actual Lim storage and the C ABI,
  or narrow the feature and its documentation so layout-query results cannot
  be mistaken for permission to pass or reinterpret Lim aggregates as C
  values.
- [ ] Implement and test by-value C aggregate arguments and returns, including
  structs and enums, or explicitly keep them unsupported until the internal
  representation and target ABI agree.
- [ ] Define the supported target policy and add a target/ABI test matrix.
  Unsupported targets must continue to fail explicitly; add a backend and
  linker path for each newly supported target.
