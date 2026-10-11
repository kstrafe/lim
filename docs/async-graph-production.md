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
stationary storage. Thin selected references can also project constant array
indices, including selections between frame arrays and caller-owned arrays with
different lengths and offsets. Source bounds checks still run at selection;
an impossible constant-index candidate is never probed when reconstructing a
different selected reference. The checked original borrow retains its ordinary
or pinned type and exclusivity; a pinned physical address is not permission to
upgrade a source loan to a pin. Native tests cover mutable writes, repeated
Pending, cancellation, caller alias conflicts and standalone emitted source.
Runtime array indices retain the address selected by the original bounds-checked
expression, not the index variable's later value. Pure generated address recipes
recover coordinates using sampled physical element stride and address direction;
they account for nested field offsets and zero-sized elements. Reconstruction
uses ordinary checked projection helpers, retaining source type and exclusivity.
Cold/warm native tests cover index mutation before suspension, shared/exclusive
scalar and nested field selections, two runtime coordinates, zero-sized arrays
and trailing empty fields. Dependent-child cancellation tests read the selected
element before destroying its array owner; caller alias violations still fail
with original source spans, and standalone generated source remains checked.
Allocation/static mixed-anchor recipes remain gates.
Repeatable scalar and ordinary shared-reference guard
payloads can be previewed from a linear scrutinee while an awaiting guard
executes. Shared snapshots retain their ordinary pointee loans, not loans of
the containing cell. Rejection clears the preview and preserves the scrutinee
for later arms. Copy reference-bearing struct and tuple previews preserve their
nested pointee origins, including after a rejected awaiting guard. Their checked
shared-reference field reads do not create loans of the containing cell.
Reference-bearing writes still require restoration storage. Direct exclusive
reference guard leaves now use ordinary checked identity reborrows of the retained
scrutinee, not copies of its unique handle. Nested patterns request exclusive
projections only along paths that need a lender; shared sibling leaves remain
shared. The commit edge retires every preview before moving the scrutinee, just
as rejection and cancellation retire aliases before destroying their owners.
Native regressions cover rejected and accepted suspended exclusive guards,
mutation after commitment, caller alias conflicts, and reading cleanup handlers
at entry, guard suspension and fallback suspension, including repeated cleanup.
Move-only non-reference guard bindings still require stationary storage aliases
and fail closed. Legal
enum `#or` guards have no pattern bindings and therefore perform no payload
preview; their tests still discriminate variants before any committed read.
The ordinary language continues to reject bindings in enum alternatives.
Reading cleanup handlers for shared-reference enum payloads work at entry,
preview suspension and fallback-arm suspension. Ordinary call analysis carries complete nested
enum alternatives and removes output payloads whose mandatory input references
are proved absent through one checked safe-reference boundary. Raw pointers,
unknown tags and repeated dereferences cannot establish that absence; supporting
a preview does not relax the ordinary checker boundary.

Cold/warm and standalone native tests cover Copy struct and tuple previews,
rejected guards followed by fallback-arm suspension, and both variants of a
binding-free alternative guard. A caller mutation during a suspended aggregate
guard is rejected at the original `#set` span before cache publication. A cleanup
handler reading the aggregate's nested reference works at entry, suspended
preview, and committed fallback; repeated cancellation then releases the caller's
loan so it can mutate the referent. These are copied nonexclusive snapshots, not
move-only or exclusive guard aliases.

Scoped external borrows have explicit reference cells, tracked by the physical
state solver through Pending and cleared on scope exit/cancellation. Their
materialization preserves checked pinning and exclusivity. Source and ordinary
generated-code checking can still reject cases requiring unsupported parent
permissions. Ordinary local-owner references retain their ordinary reference
type at use sites; they are not silently converted to pinned references.

### Frame-local borrows across suspension

For synchronous calls on movable frames, shared `#borrow-slice` of a Copy
local array (including static struct/tuple fields) projects the original storage
through an ordinary checked helper. Whole-array and ranged slices retain the
native layout and reference-element provenance. Range bounds use the already
evaluated graph operands; the generator does not replay their source expressions.
When a slice has one resolved synchronous call consumer in the same effect-free
block window, the generator materializes it only at that call. Neither the slice
nor its otherwise unused Copy array snapshot receives a resumable frame cell.
This avoids requiring Empty tag knowledge to move or resume the frame after an
unrelated syscall. Slice locals, control-edge transfers, multiple consumers and
intervening effects do not receive this certificate; ordinary borrow checking
still checks escapes, loan conflicts and any result retaining the input.
This is not across-suspension slice support: pinned, dynamically selected and
non-Copy array storage still require a nonmoving storage lease and fail closed.
No unsafe fat-reference reconstruction is used by this projection.

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

## Operation-local borrows

Operation-local owner borrows can now be passed directly to a resolved
synchronous call, including disjoint static struct/tuple fields. A graph
certificate requires one consumer in the same block, no control-edge escape,
and only pure address formation, literals, or other borrows for that same call
between the borrow and consumer. Such an argument has no reference cell in the
future; its frame is stationary only for the duration of the operation. The
ordinary source and emitted-program checks still authorize all accesses and
returned-reference lifetimes. Borrowing before an await, retaining a handle in
a local, and effectful intervening evaluation do not receive this certificate.

Cold/warm native tests and independent ordinary artifacts cover
`async_while_let_body.lim`, `async_for_effect_step.lim`, and two disjoint mutable
field arguments. An aliasing variant still fails with an original-source borrow
diagnostic. The heap-owner example now preserves nested reference-slot
provenance and passes native and standalone generated-source regressions.
A root-example check audit passes 38/42 examples with no timeouts; the
remaining four legacy frame/cancellation interface failures still prevent the
default-route switch.

## Compilation measurements

Graph emitters share one lazy declarative ownership classification per planning
arena. It is not an ownership proof, and cached generated output does not force
this classification to be built. Source and generated ordinary-code checks
remain mandatory.

Run the manual sampler with:

```sh
nix develop -c cargo test --release --test async_graph_compile_timing -- --ignored --nocapture
```

Seven-sample medians on the same host, with 128 unrelated record declarations:

| Async functions | Cache | Before sharing | After sharing |
| --- | --- | ---: | ---: |
| 1 | Cold | 37.563 ms | 36.987 ms |
| 1 | Warm | 32.897 ms | 32.098 ms |
| 8 | Cold | 250.460 ms | 248.198 ms |
| 8 | Warm | 211.035 ms | 209.228 ms |

These are in-process source-to-assembly measurements, excluding executable
encoding/linking and process startup. Each cold sample has a new cache; each
warm sample follows an unmeasured compilation into that cache. The small
changes do not establish a reliable end-to-end speedup. At that checkpoint,
semantic work dominated the larger fixture: expansion validated the generated
program and source witnesses, then compilation validated it again. Reusing that
checked result must preserve its association with immutable syntax and the
fail-closed publication boundary, not trust mutable public programs or cache
metadata.

The compiler now retains that proof in a private owned syntax/declarations pair.
Native emission borrows this exact immutable program; extracting a mutable
public `Program` discards the proof. Compilation and checking also materialize
the already-validated graph sources rather than expanding and validating again.
Semantic summaries are loaded and published at the initial graph validation,
using the caller's configuration and target. Cache publication still follows
successful source-witness and generated-code validation, including on cache hits.

Seven-sample medians after validation reuse, compared with the immediately
preceding shared-classification implementation above:

| Async functions | Cache | Before reuse | After reuse |
| --- | --- | ---: | ---: |
| 1 | Cold | 36.987 ms | 24.242 ms |
| 1 | Warm | 32.098 ms | 18.908 ms |
| 8 | Cold | 248.198 ms | 156.130 ms |
| 8 | Warm | 209.228 ms | 117.217 ms |

The eight-function fixture improves approximately 37% cold and 44% warm.
The remaining top-level `semantic_validate` stage is a proof-presence check,
measured below 0.001 ms; mandatory semantic checks remain inside expansion.
Expansion still dominates (135.534 ms cold / 96.948 ms warm); referent contracts
remain a substantial nested detail (~50 ms). Detailed events are inclusive and
must not be summed with the enclosing stages. These results do not certify
graph-default migration or complete reuse of source facts across all planners.

### Heap-owner extraction provenance

An exclusive whole-value load of borrowed storage now retains the loans inside
owning allocations in that value, not just the owning pointer itself. Traversal
uses current contents, follows only owning allocations, excludes lifetime-only
anchors, and does not turn a shared view into an ownership transfer. Ordinary
checking accepts pinned-cell extraction helper definitions and still rejects
returning an extracted owner whose stored reference targets a local variable.

Returning an owner selected from borrowed storage now selects the actual owned
slot before checking allocation identity. A borrowed container is not itself an
allocation handle, but it can contain one. Non-owning stored loans and
lifetime-only anchors still cannot supply an owning-pointer return summary.

Shared operation-local borrows in movable frames use ordinary storage
projections rather than raw-pointer reconstruction. Their actual pointee and
nested contents therefore remain available to ordinary call-contract checking.
Mutable access and pinned frames keep the existing guarded lowering. The
`async_heap_reference.lim` regression checks cold and warm compilation, native
execution, and independent ordinary checking of the emitted source.

### Scope-exit reference retirement

Scope exit clears reference handles before the local storage they borrow. It
uses captured borrow dependencies and anchor identities, with reverse lexical
order for otherwise independent bindings. A dependency cycle is rejected, not
treated as permission to destroy borrowed storage. Linear cell clearing still
requires the value to have been consumed; this does not add implicit destruction.

Graph-proved Empty reference-cell assertions are published before accesses to
Copy owners as well as linear owners. Copy does not permit mutation of borrowed
storage. This also excludes impossible incoming self-reference states when
initializing a local in an earlier dispatcher case. The local self-reference
example now passes repeated polling and native cold/warm regressions without
adding explicit reference drops to its source.

### Cancellation example migration

`async_fn_cancel_dispatch.lim` now configures handlers for `token` and `await-0`
and cancels the record returned by `work-poll-cleanup`, both at construction and
after Pending. `async_fn_pinned.lim` similarly drains `Work-frame-cleanup` rather
than matching a legacy frame-state enum. Their native outcomes remain 42 and 41.
Public-API regressions independently check their emitted ordinary declarations
and exercise cold/warm generation before executing them.

`async_single_poll.lim` uses the same public cleanup
contract after polling two children through a single poll entry point, while
its pin scope owns stationary storage until destruction completes. The native
and standalone generated-code regressions verify its result is still 42.

The native outcome manifest marks migrated examples as `graph-exit`, selecting
graph configuration for both native execution and the staged contract audit.
This is migration bookkeeping, not a second runtime API: the default route is
still legacy, and the selectors must be removed when the default switch lands.

The printing example now uses graph lowering with the same IO and cancellation
behavior. Its synchronous Copy array slices project ordinary storage and do not
inhabit the future frame. Printing between Pending and resume therefore needs
no remembered slice-cell tags; unknown syscall effects still invalidate tag
facts conservatively. Cold/warm and standalone native regressions compare the
full stdout fixture and exit code 42. Retained slices across suspension remain
a separate storage/provenance gate.

The public cache audit now uses this migrated graph example. All three user
generator invocations are expanded once across preparation, compilation and
source publication. A warm hit reuses graph text, but the semantic-pass counter
is still two on both cold and warm runs: generation planning resolution followed
by full validation of the assembled program, including source ownership witnesses
and ordinary emitted code. Planning is not an ownership proof. Reusing its checked
source typing/flow facts without skipping either ownership proof remains a
performance goal, not an optimization claimed by the slice-storage change. Corrupt graph
text is rejected without emission or repair; legacy capture-cache regeneration
is not the graph cache's policy.

### Reusing entry pin facts

Entry capture planning now reuses its same-body loan-origin solution for local
pin lookups instead of solving origins again inside consumption analysis.
The consumption mode remains local-only: sharing a lookup does not enable
referent/callee ownership effects or make these entry facts a body proof.
Differential tests compare every consumption field, including a type-correct
shared-reference move that ordinary ownership must still reject.

The ignored release test `typed_flow::tests::entry_pin_fact_reuse_timing` compares
the former independent solves with the reused path in one process. Eleven
alternating samples, ten constructions per sample, measured eight pin operations
at 0.274 -> 0.241ms (12.0%) and 32 at 3.258 -> 3.062ms (6.0%). Resolution and
native emission are excluded; these are entry-analysis improvements, not an
end-to-end async compilation claim. Full source and emitted ownership validation
still run; source-fact remapping across planning and assembled program arenas
remains unfinished.
