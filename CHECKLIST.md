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
- [x] Carry source spans from parsed expressions into type, ownership, borrow,
  unsafe, generator, and codegen errors. Type mismatches now select
  identifiable incompatible operands (including normalized typed literals)
  for local and top-level initializers, and borrow escapes identify the local
  referent. Each analysis maps a failure to the offending token or projection
  when identifiable, otherwise to the smallest retained value expression or
  declaration span. Unknown types in expressions and declarations, and
  representative borrow, linearity,
  unsafe, generator, and codegen diagnostics now have exact-range assertions.
  Named-call and struct-literal lowering also identifies unknown, duplicate,
  and omitted arguments/fields at their source forms. Duplicate declarations,
  unsafe-impl targets, and specialization-time validation now underline the
  relevant name where that name is available in the original form. C-enum
  discriminant, thread-task worker/result, and task-in-aggregate diagnostics
  now identify their invalid source token/type as well. Thread-task handles in
  function signatures and type aliases also underline the task type token.
  Missing-import and import-cycle failures underline the path string, while
  unknown cfg keys underline the referenced key token.
  `Send` failures on thread workers now underline the offending parameter type,
  not the unrelated worker return type, even when an earlier local has the
  same name as the unknown type. Unsafe external calls underline the callee
  in `#call` syntax, and raw-pointer safety errors underline their builtin.
  Diagnostic hunks expand tabs at
  four-column stops before positioning underlines; common wide and combining
  Unicode characters are included in display-column calculations, and lexer
  columns count Unicode scalars to match the renderer.
  Non-constant global initializers now highlight a nested `#call` that makes
  the initializer invalid instead of the larger enclosing constant expression.
  Imported and generated-source parser errors retain their original lexer or
  parser spans instead of reconstructing one-character spans from locations;
  this covers quoted tokens with whitespace and escaped quotes. UI
  diagnostics now also assert exact token alignment for unknown identifiers,
  recursion, and codegen errors, including underline widths. Repeated linear
  field moves underline the repeated `#get` projection, and repeated
  array-element moves underline the
  repeated `#index`, instead of the enclosing `#let` statement. CLI tests
  assert full unterminated-string spans and zero-width end-of-file parse spans.
  Every UI fixture is required to declare a precise fragment or a custom
  alignment assertion.
  Mismatched `#if` branch values underline the incompatible branch, excluding
  the condition expression from type-hint matching. Mismatched `#match` arms
  similarly exclude the scrutinee and patterns from arm-value selection.
  Named-call type mismatches carry the parameter name through type checking
  and underline that argument's value, even if an earlier argument has the
  same type. Struct-literal field mismatches identify the responsible named
  field value rather than a same-typed value from an earlier field. Enum
  constructor payload mismatches carry the payload index and underline the
  corresponding constructor argument.
  Explicit `#return` type mismatches also underline the incompatible returned
  expression, covered by a UI test. Tuple and array construction diagnostics
  retain the mismatching element index and underline that element rather than
  another value with the same inferred type; extra constructor values and
  missing-element constructor heads are also pinpointed, including nested
  tuple constructors. Borrow conflicts distinguish an
  accessed binding from a same-named struct field selector, call callee, or
  named-argument label.
  The UI diagnostic suite requires every fixture to assert a precise source
  fragment and underline width, or a custom exact-alignment check; new
  diagnostics must add coverage under the same rule.
  Unknown named types in local `#let` annotations underline the annotation,
  including when type checking represents the failure as an expected-type
  mismatch. Immutable assignments now underline the assigned binding instead
  of the entire assignment form. Named-type mismatches in destructuring lets
  underline the declared type rather than an identically named pattern
  constructor. Mutable-borrow-through-immutable-reference errors underline
  the owner argument. Invalid operands to `index`, `slice-of`, `slice-len`,
  `get`, `get-payload`, and `deref-set` also receive argument-level spans with
  UI coverage. Invalid conditions, array indices, and out-of-range shift counts
  also select their offending operand. Generator capability checks now pinpoint
  missing, mismatched, and duplicate operation names, including the later
  duplicate occurrence;
  duplicate capability/type pairs and generator declarations point at their
  repeated identifier. Generator-function recursion diagnostics underline the
  recursive `#gn-call` target, and duplicate generator parameters underline
  the repeated parameter. Builtin arity errors underline the operator
  identifier, including its full typed spelling; unresolved calls underline
  the function name. Non-exhaustive match diagnostics underline the `#match`
  head. Invalid array/struct assignment targets underline
  the named target instead of the full statement. Missing struct fields and
  enum payload variants underline the missing member name, and invalid enum
  match arms underline the variant pattern rather than treating it as an
  operator symbol. Unknown enum variants in `#let-else` patterns also underline
  the pattern token. Repeated boolean, enum, and wildcard match patterns
  underline the later duplicate. Out-of-range and repeated integer match
  patterns underline the corresponding literal token. Range-pattern errors
  underline the invalid range or its upper bound when the bounds are reversed;
  duplicate character patterns underline the later character literal. Enum
  match payload-arity errors underline the affected variant pattern.
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
- [x] Implement and test by-value C aggregate arguments and returns, including
  structs and enums, or explicitly keep them unsupported until the internal
  representation and target ABI agree.
- [x] Define the supported target policy and add a target/ABI test matrix.
  Unsupported targets must continue to fail explicitly; add a backend and
  linker path for each newly supported target.

## Next development priorities (September 2026 audit)

These are follow-ups beyond the completed baseline, not claims that every
limitation below is a soundness bug. Implementation must retain explicit
types, ownership and destruction, concrete generators, and free-standing
functions; no implicit dispatch, runtime recursion, or external Rust crates.
Each item requires documentation and regression coverage before being checked.

### Priority 1: semantic consistency and safety guarantees

- [x] Specify and enforce evaluation order for named calls and aggregate
  construction. `normalize_call_expr` in `src/lib.rs` currently rearranges
  argument expressions into parameter declaration order. Decide explicitly
  whether evaluation follows source order or declaration order; if source
  order, stage values before ABI argument placement. Apply the same documented
  rule to struct field initializers. Test reordered arguments/fields with
  observable side effects, traps, moves, and conflicting borrows; ensure
  borrow checking and native execution use the same order.
- [x] Support destructuring aggregates that retain references.
  `Statement::Destructure` and `Statement::LetElse` in `src/borrowcheck.rs`
  currently reject these values wholesale. Transfer field-specific origins,
  loans, and mutable-reference ownership to pattern bindings, including
  nested structs, tuples, and enum payloads. Accept returned wrappers whose
  referents remain alive; reject escaped locals, duplicated mutable loans,
  and parent access during a derived mutable borrow. Cover both let-else
  branches and explicit consumption of remaining linear fields.
- [x] Remove register-count limits from otherwise legal aggregate projections.
  `src/codegen.rs` still rejects large fields projected through references and
  large enum payload projections. Reuse indirect aggregate destinations rather
  than requiring every projected value to fit `VALUE_REGISTERS`. Test nested
  aggregates above the register threshold, zero-sized and mixed scalar fields,
  local/global referents, and inactive enum variants. Preserve the distinction
  between copying a Copy value and illegally moving a linear value out of a
  reference; these tests must execute natively, not only pass type checking.
- [x] Report a conservative stack bound in bytes, not only call depth.
  The backend documentation currently connects finite call depth to a static
  stack requirement. Account for frames, expression temporaries, outgoing
  arguments, indirect aggregate storage, alignment, and generated helpers
  along each call path. Add a stack-usage report with the limiting call chain
  for main and thread entry points. Mark external-call usage unknown unless
  an explicit trusted bound is supplied; do not claim no overflow merely
  because recursion is forbidden. Test nested large calls, repeated loops
  without stack growth, checked size arithmetic, and thread stack budgets.
  - [x] State accurately that finite call depth alone does not prove a byte
    bound or prevent stack overflow, especially across external calls.

### Priority 2: trustworthy generated artifacts and diagnostics

- [x] Detect syntactically valid modifications to cached generated source.
  `cached_generated_source` in `src/generator.rs` verifies the input key and
  parses the `.lim` file, but does not verify its original output contents.
  Store and validate an output digest/length for both inspectable source and
  cached expansions; define whether edits cause regeneration or a diagnostic.
  Test valid edited source, truncation, missing metadata, and stale artifacts.
  Preserve full-key collision checks. Document that checksums detect damage,
  not an attacker who can rewrite both the cache and its metadata.
- [x] Make cache publication robust across concurrent compilers and interrupted
  writes. Current inspectable artifacts publish source and key separately and
  use process-ID temporary filenames. Use unique per-write staging and a
  coherent validated publication protocol, including concurrent library calls
  in one process. Test simultaneous same-key and different-key invocations,
  interruption between publication steps, and cleanup of abandoned temporary
  files; readers must never accept a mismatched source/metadata pair.
- [x] Automatically fingerprint generator implementation changes in cache keys.
  Builtin materialization in `src/lib.rs` currently includes package version
  and a manually maintained `builtin-materializer` revision. Add a deterministic
  implementation/build fingerprint that changes when expansion semantics or
  reachable generator helpers change, even without a package version bump.
  Use the effective compilation target/configuration rather than assuming host
  settings. Test builtin and user-generator hits, helper-only changes, cfg
  changes, and identical reproducible builds without timestamps or local paths.
- [ ] Carry diagnostic identity and exact spans through semantic lowering.
  Replace message-text/name-based span recovery in `src/lib.rs` incrementally
  with node IDs, structured error variants, and retained source ranges.
  Preserve expansion provenance so errors can label both the generated code
  and invocation, plus a borrow origin where relevant. Add exact-range UI
  assertions for repeated identifiers, shadowing, reordered named arguments,
  nested `#case` patterns, imports, and cache hits; changing message wording
  must not change the highlighted token.
  - [x] Resolve duplicate named-call parameter spans from retained syntax
    structure instead of recovering the parameter name from diagnostic text.
  - [x] Verify semantic errors from generated declarations retain the
    invocation span identically on cold expansion and cache hit.
  - [x] Assert exact UI source ranges for a shadowed-name type error, a
    reordered named-argument mismatch, a nested enum `#case` pattern mismatch,
    imported-source errors, and a generated semantic error on a cache hit.
  - [ ] Replace `"source span …"` and `"conflicting span …"` string metadata
    with structured semantic errors carrying a stable diagnostic category,
    source ID, and byte range from type checking through CLI rendering.
  - [x] Carry function-body and top-level-initializer type-error ranges as
    `Span` data to the CLI diagnostic constructor; retain the string-returning
    checker API as a compatibility wrapper. Unit and UI tests assert exact
    source excerpts and verify these errors need no span text in the message.
  - [x] Carry unsafe-checker source locations as structured spans into the CLI
    diagnostic path; the unsafe-static UI case and semantic unit test pin the
    accessed static without serializing its range into the error message.
  - [x] Carry linear-checker source locations as structured spans into the CLI
    diagnostic path; the existing linearity diagnostic coverage pins the local
    ownership violation without serializing the range into its message.
  - [x] Preserve borrow conflicts and their origin as structured primary and
    secondary spans through CLI rendering; tests assert both exact source
    tokens and distinct rendered hunks without span-marker text.
  - [x] Carry a structured semantic diagnostic category into CLI construction;
    `analysis_diagnostic` consumes that category directly instead of
    classifying errors by searching message text.
  - [x] Stop decoding serialized span markers in `analysis_diagnostic`; the
    CLI now consumes checker-provided spans or retained syntax provenance.
    Imported-source and generated-code UI tests pin their rendered locations.
  - [x] Assign the borrow category at the `#borrow-mut` immutable-reference
    rejection site using an internal diagnostic identity tag; unit and UI tests
    verify the structured category and rendered E4100 without exposing the tag.
  - [x] Resolve duplicate-parameter diagnostics at parameter validation time
    from the retained function declaration tree, and remove the corresponding
    message-parsing branch from `unlocated_analysis_span`; the UI test asserts
    that the second duplicate name is underlined.
  - [x] Resolve duplicate struct-field and enum-variant spans while validating
    declarations, including variants duplicated across enums, and remove their
    diagnostic-message span-recovery branches. UI fixtures pin the second
    declaration occurrence.
  - [x] Carry the recursive call edge's source span from call-graph cycle
    detection, and remove cycle parsing/call-name span recovery from
    `unlocated_analysis_span`; the recursive-call UI assertion pins the callee.
  - [ ] Remove message-text/name-based fallback span selection from
    `analysis_diagnostic` and `unlocated_analysis_span`; retain syntax-node
    identity or explicit provenance for repeated identifiers and generated
    declarations.
  - [x] Preserve user-generator expansion source and invocation provenance;
    cold and cache-hit UI tests independently check both rendered ranges.
  - [x] Preserve builtin-generated declaration source and invocation
    provenance; UI tests assert exact ranges on cold and cached compilations.
  - [x] Select the generator invocation span structurally when generated
    function body syntax has no retained source nodes. The cached
    generated-error UI test asserts the invocation hunk on cold and warm
    compilations.

### Priority 3: collection ergonomics without implicit behavior

- [x] Add explicit ranged immutable subslices. `docs/language.md` currently
  documents immutable slices without ranged slicing. Choose a constructor
  distinct from the slice type, specify half-open bounds and failure behavior,
  and retain the original referent's lifetime through nested slices and
  function returns. Test empty and end-boundary ranges, reversed/out-of-bounds
  ranges, overflow, zero-sized elements, and attempted escape from a local.
- [x] Add mutable slices and an explicit disjoint-split operation. Specify
  exclusive reborrowing, parent suspension, and linear handling of mutable
  views before implementing syntax. A checked split must establish disjoint
  regions without callbacks, implicit copying, or lifetime annotations.
  Test writes through each half, prohibited overlapping views and parent
  access, nested reborrows, zero-sized elements, and return provenance.
  - [x] Fix the surface contract: `#slice-mut T` is the mutable-view type,
    `#slice-mut-of` creates one only from a mutable array reference,
    `#slice-mut-idx` yields an exclusive element reference, and
    `#slice-mut-split view at` consumes the view and returns a pair of
    disjoint mutable views. Bounds are checked at runtime; the parent view is
    unavailable after reborrow/split until the derived view is consumed.
- [x] Establish a safe synchronization foundation for shared allocators and
  other interior-mutable state. Send/Sync classification alone is not a
  synchronization operation. Specify a small explicit atomic API, supported
  scalar widths/alignment, memory-order arguments, and invalid-order errors;
  provide concrete generated wrappers if appropriate. Keep unsafe override
  obligations explicit. Test cross-thread publication and counter updates,
  reject invalid orderings, and document which target guarantees are relied
  upon; stress tests alone are not a memory-model proof.
  - [x] Fix the API contract: `(#atomic T)` wraps supported integer scalars;
    `#atomic-init` initializes one; `#atomic-load`, `#atomic-store`, and
    `#atomic-fetch-add` take an explicit shared reference plus an explicit
    `#memory-*` order. Load/store order restrictions follow Rust's rules;
    atomics are Send+Sync only when their scalar width is supported.
  - [x] Implement checked load/store/fetch-add operations with operation-specific
    memory-order validation and x86-64 lowering; exercise signed and unsigned
    widths and ensure oversized atomics are rejected.
  - [x] Run two native workers against one shared atomic counter, join both,
    and verify the combined update; test rejected load/store orderings in the
    compiler and document the supported x86-64 memory-model mapping.

### Priority 4: tooling and implementation quality

- [x] Format commented source instead of returning the entire file unchanged.
  `format_source` in `src/lib.rs` retains source spans for line comments and
  attaches them to surrounding syntax while formatting declarations, calls,
  `#case` arms, and
  generator quasiquotes without dropping or moving comments to the wrong
  form. Test leading/trailing comments, strings with semicolons, empty lists,
  and formatting idempotence; parsed semantics must remain unchanged.
  - [x] Distinguish actual line comments from semicolons inside string literals
    before deciding whether comment-preserving formatting is required.
- [x] Bound recursive parser nesting and return a source-spanned parse error
  before the Rust call stack can be exhausted. Test the nesting limit at and
  beyond its boundary with generated inputs.
- [x] Add a dependency-free compiler robustness suite with explicit resource
  budgets. Audit import traversal, generator expansion size, aggregate layout
  arithmetic, and diagnostic rendering beyond existing limits. Exercise seeded
  generated inputs and malformed/truncated files in bounded subprocesses.
  Require deterministic diagnostics instead of panics, hangs, or partially
  published outputs; keep minimal reproducers for every discovered failure.
  - [x] Reject aggregate storage/value word-count overflow instead of
    saturating or wrapping layout arithmetic; cover arrays and nested layouts.
  - [x] Bound recursive import depth, import count (including differently
    prefixed repeats), and cumulative source bytes; report the import site.
  - [x] Bound diagnostic excerpts and underline construction for very long
    source lines while preserving source-column alignment.
  - [x] Exercise seeded malformed/truncated inputs in timeout-bounded compiler
    subprocesses; require deterministic diagnostics and no partial assembly.
  - [x] Include failing generator invocations in the bounded subprocess seeds,
    and reject truncated, forged-length, and oversized cache artifacts without
    panicking or trusting partially published generated source.
- [x] Establish reproducible compile-time and generated-code performance
  baselines before optimizing the compiler. Measure lex/parse, import/cfg,
  generation (cold and warm cache), semantic checks, native emission, and
  linking separately on small and large generated projects. Record time,
  peak memory where available, and artifact sizes with toolchain/machine
  details. Include runtime collection and aggregate workloads with checked
  outputs; use results to prioritize work without flaky timing assertions in
  ordinary correctness tests.
- [x] Add a dependency-free regression test that parses every fenced Lim
  example in the language reference and fully compiles every complete example
  containing `main`. Fix stale examples found by the test and describe
  aggregate pointer exposure consistently with the explicit raw-pointer API.
- [x] Audit the remaining language reference against the compiler for canonical
  type-versus-constructor forms, named calls, `#case`, aggregate limits, stack
  bounds, and deliberate negative examples. Compile complete positive examples
  through the backend, and pair each documented rejection with a UI fixture
  asserting its intended diagnostic; document any example that is only a
  syntax fragment or depends on a stated backend limitation.
  - [x] Add exact-span UI rejection fixtures for type names in constructor
    position, positional calls, generic declarations, and angle-bracket calls.
  - [x] Compile every complete fenced positive program through assembly
    generation; the dependency-free `tests/language_docs.rs` harness does so.
  - [x] Pin the documented `#case`, aggregate-overflow, and stack-bound
    rejection/limitation behavior with UI or report tests and cross-reference
    those fixtures in the reference.
