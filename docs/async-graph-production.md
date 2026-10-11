# Graph async production route

The graph generator is available through the ordinary public compile, parse,
and generated-source APIs with `CompileConfig::set("async-lowering", "graph")`.
The CLI can use the same configuration key. An unknown value is an error.
The default remains `legacy`: this is an explicit migration route, not completion
of ASYNC-01, ASYNC-CFG-01, or ASYNC-PIN-LATE-01.

Graph selection applies to all async invocations in the prepared program,
including imported and generator-produced invocations. Unsupported lowering
fails; it does not retry the legacy rewriter. Original source witnesses and the
completed ordinary emitted program must both pass the existing checkers.
No async runtime operation or borrow-checker exception is introduced. Internal
thin references in a stationary frame can use generated unsafe raw-pointer
storage; their permission and escape checks still come from the original source.

Executable compilation and source publication use the same versioned graph
artifact cache. Keys include the implementation fingerprint, dependency/config
context without source locations, Copy types, and declaration environment.
Artifacts contain ordinary declarations and the public await protocol bundle. Cached
text is reparsed and checked before compilation. Warm hits skip source emission;
one complete ordinary/source-witness check validates the assembled program.
Fresh misses stay in memory until that check succeeds, before publication.
Corrupt or incomplete existing graph entries fail closed without regeneration.

## Source-named cleanup

For a task/frame named `Work-frame`, the public cleanup record is
`Work-frame-cleanup`. `work-poll-cleanup` drains the current obligations into this
record. A pinned frame remains stationary, with cleared cells and a terminal
program counter; a movable frame is consumed.

The record exposes possibly initialized *owning* slots at construction and
reachable Pending returns. Source locals use their declaration names; child
tasks use `await-0`, `await-1`, etc., in source await order. Other retained owning
operands use `source-expression-N`, a preorder ordinal within the original body.
Repeated names receive `.2`, `.3`, etc.
Public names do not depend on a private program counter or storage-cell number.
Adding a same-named declaration or changing the body's expression structure can
change its public cleanup name. Source file/line changes do not. Inspect the
generated declaration when defining a cleanup contract for computed operands.

Each field is an ordinary linear tagged cell. For example, `owner` has type
`Work-frame-cleanup-owner`, with variants `Work-frame-cleanup-owner-empty` and
`(Work-frame-cleanup-owner-full Source)`. Cleanup can inspect and explicitly
consume this record using ordinary Lim, independently of the generator.
Non-owning reference handles, including scoped tokens, are cleared before
owners are drained. Omitted owning temporaries have physical Empty proofs at
the cancellation boundaries and emitted tag assertions.

Graph cancellation configuration uses these source slots:

```lim
(@#async-fn-pinned (: protocol WorkAwait : waker Wake
  : cancel (work-cancel
    ((owner destroy-owner) (await-0 cancel-child)))
  : function (#fn work (...) #u64 ...)))
```

Each handler must safely consume exactly one value of the slot's declared type
and return `()`, except for stationary dependent children described below.
Every exposed owning slot requires a handler; duplicate,
missing, unknown, unsafe, or incorrectly typed handlers are rejected. The
dispatcher has the ordinary signature
`(#fn work-cancel (: task Work-frame-cleanup) () ...)`. Call it on the result of
`work-poll-cleanup`. Only Full cells invoke handlers. Repeated pinned cleanup
returns empty cells and does not repeat destruction. Movable cleanup consumes
the frame, so reusing that frame is rejected.

This contract intentionally differs from the legacy per-state cancellation
mapping. Selecting the graph route for legacy mappings requires migrating them
to source-slot handlers. The old private graph `work-poll-cancel` storage record
remains available for staged regression compatibility; its fields are not the
public cleanup interface.

## Current support and gates

Source-time delayed initialization stays at the original graph Bind. Factories
install only parameters; repeated Pending retries poll the existing child.
Static pinned owner projections and supported checked selected addresses use
stationary storage. Repeatable scalar and ordinary shared-reference guard
payloads can be previewed from a linear scrutinee while an awaiting guard
executes. Shared snapshots retain their ordinary pointee loans, not loans of
the containing cell. Rejection clears the preview and preserves the scrutinee
for later arms. Exclusive/move-only guard aliases, reference-bearing aggregate
previews and alternative-pattern previews still fail closed. Reading cleanup
handlers for shared-reference enum payloads work at entry, preview suspension
and fallback-arm suspension. Ordinary call analysis carries complete nested
enum alternatives and removes output payloads whose mandatory input references
are proved absent through one checked safe-reference boundary. Raw pointers,
unknown tags and repeated dereferences cannot establish that absence; supporting
a preview does not relax the ordinary checker boundary.

Scoped external borrows have explicit reference cells, tracked by the physical
state solver through Pending and cleared on scope exit/cancellation. Their
materialization preserves checked pinning and exclusivity. Source and ordinary
generated-code checking can still reject cases requiring unsupported parent
permissions. Ordinary local-owner references retain their ordinary reference
type at use sites; they are not silently converted to pinned references.

### Frame-local borrows across suspension

On the graph route, `@#async-fn-pinned` supports ordinary shared and exclusive
thin reference locals into stationary frame owners, including checked static
struct/tuple projections. Declare them with `#borrow`/`#borrow-mut` as in an
ordinary function. The factory initializes only arguments; owner construction
and pointer formation occur when polling the pinned frame reaches those source
statements, never before the caller pins it.

Generated Empty/Full cells hold `#ptr` or `#ptr-mut` for internal handles. The
generator obtains addresses with the general `#ref-ptr` builtin and reconstructs
a short-lived reference with unsafe `#ptr-borrow` when an operation needs it.
Each temporary uses its checked, initialized owner projection as the anchor,
preserving native reference layout. The checked original source and stationary
owner cells provide the across-suspension proof. Source checks still reject
conflicting loans, mutation or
consumption of borrowed owners, and returning a reference to a source local.
Cancellation clears these non-owning handles before extracting owning cells.
External references keep lifetime-bearing storage and caller contracts.
Thin handles may select internal storage or a reference supplied at the function
boundary. For mixed handles, the generator retains the real boundary reference
in a separate Empty/Full capture and reconstructs the source parameter from it;
erasing a selected address never erases the caller's borrow. Shared and exclusive
captures survive source-handle release and are cleared on completion or explicit
cancellation. Reference parameter roots are seeded during planning as type facts,
not as a replacement for either ownership check. Static field/tuple projections
preserve the selected referent's native layout, including stack-backed versus
frame-backed aggregates. Other mixed provenance needs a checked anchor recipe
and remains rejected rather than guessed.
Thin handles may select multiple internal referents with checked static
struct/tuple projections. Their
raw address preserves the source choice; reconstruction first checks each
candidate owner's Full tag, then compares its projected address. It never
accesses an Empty owner's payload. Shared and exclusive references can select
different owners across branches and loop iterations. Source loan checking
still protects all possible referents, and ordinary generated-code checking
remains mandatory.

Owning aggregates and child futures retaining frame-local borrows require a
configured cancellation handler. Cleanup first retires non-owning poll handles,
then invokes dependent handlers in dependency order while their referents remain
Full and stationary. Independent owners are extracted only afterward. A movable
dependent child can be consumed by its handler; a generated pinned child requires
a safe handler taking `(#pin-ref-mut ChildFrame)` and returning `()`. A pinned
graph task with cancellation configuration generates `work-poll-destroy` with
that signature, so a parent can use it directly as its child's handler. Both
public cleanup and private cancellation perform this phase. Dependent cleanup
record fields are Empty; they never export live pointers into the parent.
Repeated destruction is idempotent. Missing handlers and dependency cycles fail
closed. Movable `@#async-fn` frames cannot use internal raw-reference storage.

The default switch remains gated on legacy public task/state layout adapters,
the full existing async matrix, general guard aliases and retained child borrows,
broader selected-address/projection contracts, and named poll-handle recycling
with correct internal-loan permissions. A passing graph fixture does not close
these gates. No `src/lib.rs` patch is needed to select this explicit route;
changing `DEFAULT_ASYNC_ROUTE` before compatibility work would break existing
public cancellation-state patterns.

Focused public-API/native and standalone-artifact regressions are in
`tests/async_graph_production.rs`. Private graph emitter and frontend migration
regressions provide additional coverage, not proof of a complete default switch.
Thin local-reference and cleanup regressions are in `tests/async_self_borrows.rs`
and `tests/async_self_borrow_cleanup.rs`, including signed narrow writes and
descending aggregate projections after repeated Pending, warm-cache identity,
source-spanned loan violations, and unsafe dependent-child extraction rejection.
`tests/async_dependent_cancellation.rs` covers native dependent destruction before
owner extraction, entry/Ready/repeated cancellation, private cleanup, nested
generated pinned children, and cold/warm identity. This coverage does not close
the selected-target, guard/lending, or default-route migration gates.

Checkpoint verification (2026-10-10, through `nix develop -c`): the library
suite passed 1,295 tests; frontend migration/cache regressions passed 12 tests;
`async_graph_production` passed all 7 tests, including independently checked
ordinary artifacts and native execution. All-target checking, scoped Rust
formatting and diff checks passed. These counts do not certify default-route
migration or close the gates above.
After removing the misleading fixed-target metadata from the non-graph v6
inspectable key, all 12 frontend and 8 generated-source cache regressions passed
again; the selected target remains part of dependency/config identity.
