# Graph async production route

The graph generator is the default for the ordinary public compile, parse,
and generated-source APIs. `CompileConfig::set("async-lowering", "graph")`
explicitly selects the same route; the CLI supports the same configuration key.
`legacy` is no longer a selectable route, and its internal implementation has
been deleted. Earlier migration entries below
are historical verification records, not descriptions of the current default.
Switching the default alone does not complete the full async safety goal.

See [the requirement-by-requirement audit](async-goal-audit.md) for current
invariants, coverage, performance measurements, and verification results.

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

Cleanup uses source-slot handlers, not per-state cancellation mappings.
Graph is the only lowering implementation. No raw-state `poll-cancel` export or
fixed public `Frame-state` type is generated; temporary extraction storage uses
a fresh internal name. Both movable and pinned generators expose cleanup.

## Post-terminal parameter access

Pinned graph functions can explicitly request access to reference-free Copy
parameters after Ready or public cleanup:

```lim
(@#async-fn-pinned (: protocol WorkAwait : waker #u64
  : access (: amount amount-access)
  : function (#fn work (: amount #u64) #u64 (#return amount))))
```

This emits ordinary `amount-access-read` and `amount-access-replace` functions.
Read takes `(: task (#pin-ref Work-frame))` and returns `#u64`. Replace takes
`(: task (#pin-ref-mut Work-frame) : value #u64)` and returns `()`. Accessor
names are literal inputs, so external imports prefix them exactly once. No
access functions are emitted unless requested. Unit parameters and aliases
are supported; duplicate requests, unknown parameters, declaration collisions,
owning data and reference-bearing data are rejected before publication.

Both functions assert a terminal counter and Empty reference/owning cells.
Replacement reads and explicitly consumes the previous tagged cell before
writing its replacement; merely overwriting a Full cell is not a valid
initialization contract. Cleanup clears parameter cells too, so read requires
a Full cell, installed by replacement when necessary. Neither operation
restarts the future or moves its pinned frame. Access before the terminal
state traps even when the frame contains no internal reference.

Cold/warm generated artifacts run independently as ordinary Lim. A native
self-reference regression replaces the parameter in the **same** pinned frame
after Ready and after public cleanup, retaining the original result of 58.
An unguarded helper called while Pending is rejected by ordinary borrow
checking, which underlines its receiver and labels its offending write. There
is no ownership exemption for accessors and private cell names remain unstable.
`async_fn_self_reference.lim` now uses these source-named accessors for both
Ready and cancellation, and drains its child through public cleanup. It keeps
the same two frames and native result of 58. An additional source-body test
reads Copy owner data while its shared self-references are retained; this legal
read is supported by graph lowering, unlike the old shape-specific restriction.
Graph-default selection and legacy removal remain separate gates.

## Current support and gates

Range bounds now have the same semantics in ordinary code and both async
routes: evaluate start, then end, exactly once before entering the loop.
Suspending either bound resumes its computation without evaluating a completed
bound again. Labeled continue and break preserve the captured endpoints.
Native regressions cover side-effecting factories, immediate children,
suspending children, and an awaiting body. Classic `#for` conditions remain
per-iteration computations.

Conditional expression capture regressions use graph lowering explicitly,
without requiring legacy private field or helper names. Both typed parameters
and typed locals survive a Pending return and retry; an unselected branch does
not poll its child. Immediate completion and original explicit-type mismatch
spans are checked too. Nested call operands containing conditional and match
expressions run through their public poll interfaces.

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
and trailing empty fields. The two-coordinate regression retains an aliased
inner array type: native construction, argument and return layout checks resolve
the annotation instead of mistaking it for an element. Dependent-child
cancellation tests read the selected
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

Movable graph frames support reads and Copy, reference-free writes through
fixed-layout owned array paths. Struct/tuple prefixes and array aliases retain
their checked layout. Literal indices proved in bounds need no selection cell;
dynamic indices are saved as `#usize` values and bounds-checked at the original
selection point, before later index effects or RHS suspension. Nested selections
copy their already-selected parent indices rather than reloading source locals.
The emitter projects the resumed frame using this metadata, never a persistent
pointer into movable storage. Index cells follow the selected-place retirement
plan and ordinary frame cleanup.

This includes `#set-index` with a suspending RHS and an index expression that
itself awaits. Handle roots, payload-tag checks, non-Copy selected aggregates and
reference-bearing leaves remain on the capability/snapshot path. This does not
authorize moving an object with live user-visible self-references.
Native regressions cover aliased `#u128` storage, struct/tuple prefixes, index
mutation before Pending, a nested parent index retained across child-index
suspension, repeated selection in loops, and eager bounds traps. Public graph
tests also check cold/warm artifacts, standalone ordinary-code execution, and
cancellation of a movable frame holding selected index metadata.

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

Graph lowering also accepts an external mutable-slice parameter retained
across Pending. Its whole-binding lending read can feed one checked slice-index
selection directly, borrowing the stored holder rather than moving or copying
the slice into a second frame cell. Literal indices and effect-free numeric
binding reads preserve this window; calls and other effects do not. Indexing
uses the ordinary checked builtin at the original selection point. Alias types
retain their resolved element layout. Native regressions mutate an element,
release that element reference, await, and index again after resumption; the
emitted ordinary program runs independently too. Backing-array writes while
the task is Pending are still rejected at the original source span.

Derived thin element references can now survive Pending while their original
external slice holder remains the sole lifetime-bearing capture. The generator
stores selected element addresses, not a second retained reference loan. Each
poll reconstructs an ordinary checked element anchor from that holder before
using the saved address. Runtime selection is recovered using sampled leaf
addresses and actual stride/direction, not the later value of the source index.
Zero stride selects the canonical indistinguishable zero-sized element; empty
slices cannot supply an element anchor. Alias layouts are resolved before
projection. Source permissions and pin kinds are not upgraded, and both source
witnesses and emitted ordinary code remain checked.

Native regressions cover wide (`#u128`), shared, and zero-sized slice elements,
and references selecting either of two external slice holders across branches.
Both holders retain their source loans while Pending. Selected address cells
use a separate retirement plan; checked Empty assertions republish their exit
invariant before extracting a completed movable frame, even when intervening
calls have invalidated the ordinary checker's earlier stored tag facts.
Static struct/tuple/array suffixes preserve element layout during reconstruction.
A dormant constant out-of-bounds nested array projection is excluded from
candidate probing, while actually selecting it still traps at the original
bounds check. Native tests exercise both candidate orders, padded struct and
aliased tuple elements, and index mutation before suspension.

Nested runtime array coordinates inside external slice elements now reuse the
ordinary array geometry recipes. A coarse outer-element lookup is followed by
short-circuit nested bounds probes and an exact final leaf-address comparison;
it never treats matching an outer range as permission to access any inner leaf.
Each coordinate is recovered from the saved address, not the current index
binding. The real slice holder remains the lifetime-bearing capture. Native
tests cover shared and exclusive projections, padded and zero-sized elements,
multiple nested indices, one-element outer slices, varying dynamic/static targets, standalone
generated code, and owner mutation rejection while Pending.

References may also select an external slice element or a separate ordinary
reference parameter. The real slice holder and the real external reference
are each retained exactly once; the selected thin handle uses address storage.
Static external field projections use ordinary helper contracts, not an inline
copy of a mutable handle borrowed from the frame's capture cell. Whole-referent
`#borrow`/`#borrow-mut` through `#deref` now lowers through the same checked
projection interface and preserves the incoming pin kind.
Native tests exercise both branches for shared/exclusive, aliased, padded-field
and runtime-indexed external targets, plus whole pinned reborrows before and
after Pending. Source-owner mutation, overlapping input borrows, pin-kind
downgrades and locally sourced escaping frames remain rejected.

Pinned parents can retain mutable slices of local frame arrays across Pending
when the slice has an explicit cancellation handler. A child borrowing a
subslice retains both the backing array and its lending slice as dependencies.
Cancellation consumes the movable child before calling the lender's handler,
then extracts the remaining owners. Native tests verify that the child can
write its borrowed element during cancellation and that the lender observes
that write while the array remains alive; normal child completion is tested
as well. Conflicting parent access with a live child remains a source error.
Length and range operations read retained slice snapshots through pinned
holder parameters rather than moving exclusive handles into temporary values.
Only source-certified reborrow snapshots may be discarded at retirement;
the original slice binding remains linear. Cleanup results explicitly mark
already-canceled dependent cells Empty rather than exporting fictitious loans.

Non-owning reference-bearing bindings can themselves be child referents. For
example, a child may hold a reference to a parent's shared slice descriptor,
not merely to one of its elements. Cancellation now clears disposable handles
first, cancels dependent children, publishes their Empty tags, and only then
clears retained non-owning lenders. Public and private cancellation share this
sequence. A native regression reads the descriptor from the resumed child's
destructor before releasing the backing array.

Whole local shared references to reference-bearing values are reconstructed
from their checked owner rather than an opaque pointer anchor. An ordinary
helper performs `(#ptr-borrow anchor (#ref-ptr anchor))` with the same named
reference. General loan analysis recognizes this exact identity round trip
and preserves nested referent provenance. Different bindings and arbitrary
pointer expressions remain lifetime-only; no keyword or async-specific
borrow permission was added.

The descriptor destructor now reads through its borrowed header in both Start
and Resume arms. Native regressions cover polls retaining either constructor.
Call-result refinement preserves a guaranteed physical constructor write even
when substitution of alternate incoming loan sources is incomplete. This
proves the dormant arm inactive without pretending those missing loan sources
were supplied. Reference-contents replacement stays conservative; tag certainty
has a separate flag propagated through store summaries, joins, and thread
capture mapping. A non-async unit regression verifies that split, and another
checks that ambiguous destinations do not acquire strong tag facts. Semantic
cache records include the new flag and use a versioned format boundary.

Mixed pinned-reference selections now cover the same-kind local/external paths
described below. Effectful index windows and the other public-interface gates
remain unfinished. Poll-local mutable-slice projections are covered by the
retained-capability path described below.

### Local pin primitives and same-kind external selections

The executable graph lowers `#pin` and `#pin-shared` as checked address borrows,
not generic expressions whose local operand would be replaced by a value read.
They preserve the checked source pin type and shared/exclusive mode. Original
source validation still enforces permanent local immovability; this lowering
does not permit moving a source-pinned local after forgetting its view.
Pinning a local in a movable async frame reports the stationary-frame requirement
at the source pin expression, rather than a generated projection error.

Native regressions choose a shared or exclusive pinned reference to either a
parent local or a caller's pinned object, retain the selected reference across
Pending, and resume both branches. Indexed variants use local and external
arrays with different lengths and change the index variable before suspension;
the resumed read retains the originally selected element. Cancellation covers
both whole-object choices. A conflicting write to the caller's pinned object
while Pending remains live is rejected even inside `#unsafe`.

An ordinary slice reference and a pinned reference cannot be branch alternatives
of the same value: their types differ. These tests do not introduce an implicit
pin upgrade/downgrade or prove arbitrary allocation/static mixed anchors.

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
A fresh graph-default readiness audit compiles all 422 valid example cases,
including programs with transitively imported async invocations. This is
source-to-assembly evidence, not a claim that every graph-mode runtime outcome
has been checked. Run it with `cargo test --test async_graph_readiness --
--ignored --nocapture`; the broad test uses a 32 MiB thread stack like the staged
contract audit. Default-route runtime verification and legacy removal remain
required. Representation-specific legacy solver tests retain an explicitly
named temporary fixture rather than depending on the migrated public example.

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

The enum self-reference example no longer declares an unused function matching
legacy frame-state variants. Its unchanged native result (42) now runs via
`graph-exit`, with cold/warm and standalone ordinary-artifact checks. Additional
regressions exercise public cleanup at construction, Pending and Ready, repeated
cleanup, exactly-once child destruction, and a source-spanned rejection of
destroying a frame while its Pending handle is live. The direct owner-field
replacement in `async_fn_self_reference.lim` remains a separate migration gate;
this change does not remove that behavior or switch the default.

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

### Reusing graph cache-key context

Graph expansion and source publication each serialize their immutable shared
dependency, Copy-type, and declaration environment once per pass rather than
once per invocation. Per-invocation keys remain byte-identical to the previous
v3 format; this changes neither invalidation nor cache validation. A regression
checks exact identity and dependency/type changes. Source planning, original
ownership witnesses, and emitted ordinary-code validation still run.

The repeatable workload is `scripts/benchmark-compile.py --async-heavy
--cfg async-lowering=graph --baseline /path/to/previous/lim --repetitions 20`.
It compiles 64 async functions with separate warm caches for both compilers.
After concurrent test processes finished, the release median measured
1526.05 -> 1518.28ms (0.5%); sample ranges overlapped (1499.22..1564.40ms
versus 1499.15..1566.65ms). Executable bytes were identical. This is not a
convincing end-to-end speedup; repeated declaration sorting/serialization is
eliminated, but the larger semantic-analysis cost remains.

At this checkpoint, all 1,333 library tests, 213 async integration tests, and
32 graph-production tests pass. More loop, value-break, external-borrow, and
three-phase condition/body/step regressions now explicitly exercise graph
lowering instead of relying on legacy private helper names. These checks do
not complete the default switch, legacy removal, or source-fact remapping.

### Layout-independent pinned-storage solver tests

Two staged solver probes no longer require the legacy generator's private
state representation. Ordinary pinned frames now exercise direct and
helper-mediated writes: Ready definitely clears the retained reference, while
Pending definitely stores the external parameter's reference. The assertions
check the destination's pin/exclusivity and the stored parameter identity.

A separate ordinary frame probe loads direct and tuple-nested reference fields.
It verifies their real incoming provenance, then removes that incoming loan
without removing the indirect field schema. The contents contract rejects the
load with a source-spanned missing-provenance error, and the origin solver does
not fabricate loaded references. Public graph self-reference regressions remain
separate: their generated thin-pointer representation is not expected to have
the legacy frame's physical reference slots. Two legacy-layout solver probes
remain; removing these layout dependencies is progress toward legacy removal,
not the default switch.

### Graph-default integration audit

A temporary default selection of graph lowering ran the entire 213-test async
integration suite: 138 passed and 75 failed. The previous audit had 104 passes
and 109 failures. The default was restored to legacy after the run; these
numbers do not authorize a production switch. The run included a native-test
timeout and many assertions about legacy private helper names, so the failure
count is not a count of independent language defects.

There are still semantic gaps. The public pinned-child protocol composition
case rejects a parent poll as overlapping exclusive borrows. Tracing the call
analysis shows the same exclusive referent appearing at two different tagged
frame storage positions. Nested exclusive-reference aggregate captures trigger
similar errors. Resolving their storage/path provenance is required; removing
the overlap check or treating matching source spans as permission is not a fix.
Synchronous mutation of local values through borrowed places also fails graph
storage planning and needs coverage before switching the default.

Four regressions from this audit now select graph explicitly. Two obsolete
legacy restrictions on nested await result annotations were replaced with
native Ready and Pending/resume tests: the child's declared poll-result payload
supplies the result contract, including inside a let-else failure arm. Explicit
conflicting annotations still fail with a Type diagnostic underlining `#u32`,
including the annotation in the later conditional branch. Assignment
to an immutable captured local underlines the offending identifier. These
changes do not resolve the exclusive-storage failures above, and the complete
graph-default matrix has not been rerun after this four-test migration.

### Retiring dead exclusive source holders

The pinned-child composition failure above is now covered on the explicit
graph route. Its factory retained one input pin correctly, but a Pending poll
retained both that original source handle and the child's reborrow. The source
never read the original handle again. Value-cell retirement alone did not end
the binding cell's physical obligation, leaving an unnecessary overlapping
loan in the next poll's argument summary.

Binding liveness now includes both Ready successors and Pending retries,
branches, cyclic paths, and later place-recipe accesses. Pending explicitly
clears dead non-owning exclusive holders in place, after restoring the child.
Owning/linear aggregates are not candidates. Internal selected-address anchors
and retained dependency holders are excluded too: a derived address can still
need that storage without another lexical read.
The physical cell solver applies the same retirement for retry and cancellation
metadata, and the plan validator rejects a retirement inconsistent with source
liveness. This does not authorize
moving a referent, clearing a live holder, or ignoring overlapping loans.

Native regressions cover two Pending returns before Ready, parent cleanup
followed by reacquiring the child's pin, and rejection of destroying the child
frame while the parent retains its borrow. Alias-aware solver tests keep an
input handle live when it is read after Ready, in a selected branch, or on the
next loop iteration; removing or adding an incorrect retirement is rejected.
Original source witnesses and generated ordinary code still pass their full
ownership checks. Cases that genuinely need both ancestor and child handles
live, and the other graph-default failures, remain separate work.

Final verification for this change passed 1,334 library tests (one ignored),
213 async integration tests, all 32 graph-production tests, and 54 dedicated
self-borrow, cancellation, guard, immediate-borrow, and rejection tests.

### Typed constants in synchronous borrow windows

An operation-local mutable borrow followed by a typed constant argument now
uses the existing synchronous-window representation. Numeric constants lower
as checked `#literal` forms, so treating only Atom literals as effect-free
incorrectly required a retained frame reference for an ordinary call such as
`(#call put (: target (#borrow-mut total) : value 22u64))`.

Only an operand-free builtin literal preserves this window. Rendering still
rejects executable literal metadata, and intervening calls, stored handles,
control edges, or awaits remain outside the certificate. This is an emission
order check, not borrow permission; original and emitted checks still run.
Direct scalar and field-projection tests cover suffix and explicit literal
spellings. The mutation-branch regression now exercises graph lowering for
both selected branches, match alternatives, immediate/mixed suspension, local
borrowed writes, and linear-owner consumption failures. Longer-lived scoped
reference holders and the other default-switch gates remain unfinished.

### Removing the remaining legacy-layout solver fixtures

The two remaining legacy-layout solver probes have been replaced, and their
dedicated legacy self-reference fixture and parser helper removed. This does
not remove the legacy lowering implementation or switch the default route.

Ordinary pinned-storage tests now check that the union of poll exits retains
the possible Pending source even when Ready definitely clears it. Both direct
and helper-mediated writes are covered. At a call site, selecting Ready allows
mutation of the cleared external referent; an unselected result rejects the
same mutation with a Borrow diagnostic at the exact `#set` source location.

The three public graph self-reference examples now positively exercise staged
poll and cleanup contracts. Both functions must accept an exclusive pinned
frame reference, return normally, and have no unresolved accesses or reads.
Contents-aware contracts are also checked. Every generated function is audited
for ordinary scope escapes and direct-loan conflicts using final checked facts,
not intermediate union-only store snapshots. Independent ordinary frame tests
continue to require actual loaded-slot provenance and reject missing inputs.

Stored local references in movable polls and the other graph-default failures
remain separate implementation work; these solver migrations do not relax
their safety gates.

Verification passed all 1,335 library tests (one ignored), all 213 async
integration tests, formatting, and whitespace checks.

### Retired local references in movable polls

Thin references stored in locals can now be used across multiple synchronous
operations in a movable poll. References whose anchors are entirely local now
retain their actual checked capability instead of reconstructing a pointer from
the backing owner. Their anchor metadata still authorizes movement only when
every reachable Pending boundary proves all internal reference cells and dependent
owners physically Empty. Missing physical facts fail closed. An internal
reference retained across an await still requires a pinned async frame, with
the diagnostic pointing to its source address formation where available.

This includes sequential calls through stored exclusive references, reborrows
of struct fields, shared references, and references selecting different local
targets. Explicit release, scope exit, or proved dead exclusive-handle
retirement must clear their storage before returning Pending. Both original
source witnesses and all generated ordinary functions still undergo full
ownership validation; pointer erasure is not permission to alias or escape.

Regression coverage includes aliases retained after releasing the original,
references live in just one suspension branch, reference-bearing aggregate
holders, and missing boundary-fact rejection. Cold and warm generated-code
tests compile and execute the inspectable artifact as standalone Lim. The
existing loop-mutation regression now uses graph lowering for its scalar,
struct-reference, and mutable-slice variants. Scoped local borrows also use this
boundary proof:
ending the scope before suspension permits movement, but retaining the scope
across suspension still requires a pinned frame. Other default-switch
requirements remain open. Legacy lowering is still the default.

The array variant of
`async_loop_body_restores_values_mutated_through_borrowed_places` is a narrower
fat-slice gate than retention across suspension: it creates a mutable slice,
calls a synchronous helper on `#slice-mut-idx`, and explicitly forgets the slice
**before** awaiting. This now executes with graph lowering. Erasing the selected
element reference and reconstructing it from the backing array conflicted with
the slice's still-live exclusive loan. Keeping the selected reference preserves
the original lending capability through the synchronous call and its retirement.
The regression also stores the element reference in a named local, uses it for
two calls, and verifies that modifying the backing array while that reference is
live still fails with a Borrow diagnostic underlining `#set-index`. Pinned-frame
and external-anchor pointer storage remain unchanged. Both the slice holder and
its selected references must be physically Empty before the frame can move.

`examples/async_fn_poll_local_borrow.lim` demonstrates stored mutable field
reborrows and a scoped shared read, releases both before suspension, then moves
and resumes the pending task. Its native result is 42 with both lowering routes;
the graph cache/standalone regression also covers this exact example.

Final verification passed 1,337 library tests (one ignored), all 301 selected
async integration tests, formatting, and whitespace checks. The selected
integration suites cover general async behavior, immediate/poll-local borrows,
graph production, selected-reference rejection, dependent cancellation,
reference guards, self-borrow cleanup, and self-borrows.

### Reusing cancellation occupancy during emission

Private cancellation and public cleanup now share one lazily computed,
owner-inclusive occupied-slot set per emitter. The reference-only Pending-cell
plan is not substituted: it omits linear owners without references. The graph,
transfer plans, and slot mapping are immutable during emission; adding a slot
invalidates the cache. Original and generated ownership checking are unchanged.

A regression counts actual cancellation solves, checks owner coverage that the
reference-only plan lacks, verifies invalidation, and validates complete private
and public cleanup output. `--timings` reports the uncached solve as
`generator.async.cancellation_cells` when generation is required.

The manual debug microbenchmark compares three independent solves against one
solve plus two lookups, with equal occupied sets. For 20 emitter-equivalent
cycles per sample, the medians were 27,572 us and 9,344 us (66.1% less time).
This isolates repeated analysis; it is not a whole-compiler speedup.

Release end-to-end measurements used eight pinned functions, each with eight
owning locals and await sites, ten samples per compiler, and two warmups.
Fresh-generation samples use separate temporary source/cache directories;
snapshot setup and teardown are outside the timed compiler process. Normal
warm samples reuse generated Lim. Both comparisons produced identical 61,328
byte native executables.

| Generated cache | Before median | After median | Observed change |
| --- | ---: | ---: | ---: |
| Fresh each sample | 4,557.52 ms | 4,573.53 ms | 0.4% slower |
| Warm | 2,914.92 ms | 2,945.39 ms | 1.0% slower |

The sample ranges overlap (cold: 4,521–4,615 ms versus 4,526–4,889 ms;
warm: 2,896–3,019 ms versus 2,904–3,070 ms). No measurable end-to-end gain is
claimed: the eliminated work is small relative to remaining analysis, and warm
cache hits do not run this emission path. Reusing checked source facts across
arenas, reducing remaining checks, and the default-route migration remain open.

Reproduce with `scripts/benchmark-compile.py --async-pinned-heavy
--cold-generators --cfg async-lowering=graph --baseline BEFORE --repetitions 10`;
omit `--cold-generators` for the warm comparison. The existing synthetic
workloads also use the current prefixed builtin spellings now.

Verification passed 1,338 library tests (two ignored, including the manual
benchmark), 87 focused async integration tests, all six synthetic benchmark
workloads, formatting, and whitespace checks. The manual benchmark was run
separately and passed.

## Default-route audit after movable poll-local reference support

### October 11 re-audit and whole global reads

At commit `6bc2b2f`, temporarily selecting graph as the default and running
`cargo test --test async_fn -- --test-threads=4` completed with 167 passing and
62 failing tests (229 total, 88.53 seconds). Legacy was restored immediately
after the audit. The earlier 145/68 audit below used a smaller test suite;
these counts are not a like-for-like defect metric.

Failure kinds still require separate treatment:

- Legacy-private generated-name assertions: the first failed loop test runs
  both its scalar and linear-return native programs successfully, then expects
  `#linear Lim.async.work.choice`. Replace layout-specific assertions with the
  intended semantic/ownership invariant rather than recreating legacy stages.
- Explicit legacy-private type annotations in user test functions: generated
  declarations reference `Lim.async.work.choice-2-sequence-task` or
  `Lim.async.work.choice-0-body-frame`. Migrate these cancellation/interface
  probes to the public graph frame protocol and verify equivalent behavior.
- Diagnostic/phase expectations: some parse-only calls now return a program
  instead of rejecting an old unsupported lowering; other failures compare
  source spans or error categories. Check final ordinary validation before
  deciding whether these are stale expectations or missing safety checks.
- A genuine whole-global-read lowering gap: the async condition's global
  `#const fallback` was rejected as an unsupported projected address. Whole
  Copy globals now load by their resolved declaration identity without adding
  a factory capture. Explicit clone dispatch and the original unsafe context
  are preserved. Native tests execute both the constant fallback and an unsafe
  static fallback; a static read outside `#unsafe` still rejects at `fallback`.
- The aggregate while-let test hit the 20-second compilation timeout. This is
  not proof of a semantic failure; isolate and measure it before changing its
  meaning or weakening the test.

The 167/62 counts describe the pre-global-fix audit, not a completed migration.
Graph-default selection and legacy removal remain required work.

### Explicit consumption of discarded source results

The audit's parse-phase failures were not all obsolete expectations. A final
graph compilation accepted a discarded linear value-loop result: the builder
evaluated the statement but did not record that its result was ignored.
Executable graph metadata now records these statement results separately from
ordinary dead operands. Planning checks their already-known types and rejects
linear results with a Linear diagnostic at the discarded source expression.
Use an explicit binding and destruction function or `#forget` to consume them;
there is no implicit destruction.

This check precedes generated-source cache lookup, so an old cached artifact
cannot skip the source obligation. Primitive and reference results remain
exempt. Declarative type classification stays lazy for scalar statements and
is shared with emission rather than reconstructed for every discard.

Regressions check discarded Ready payloads in statement, prefix-block,
tail-block, conditional, match and value-loop contexts. Payload types obtained
from the declared child protocol receive the same check. The return/continue
loop regression now runs both scalar and linear results on graph explicitly,
and attempts to reuse the consumed linear return are rejected instead of
asserting a legacy-private enum name.

### Public single-poll regression migration

Eleven further regressions now select graph lowering explicitly: five unit
loop expressions passed as call arguments, a discarded Copy await in a block,
and five let-else failure forms involving await, panic, assertions, and
unreachable control flow. Their original native programs and expected return
values are unchanged. Generated output is checked for the public single-poll
interface instead of legacy `expression-frame` or `poll.dispatch` names.
This removes test dependencies on private staging layout without recreating
legacy helper functions or weakening the source scenarios. It is not evidence
that all graph-default failures or cancellation-interface differences are gone.

### Public cancellation protocol regression migration

The cancellation regressions for a mutated linear while-loop capture and a
let-else for-loop initializer followed by two body awaits now use the public
`work-poll-cleanup` result and source-named cancellation handlers. They no longer
declare handlers against `Lim.async.work.choice-0-body-frame` or
`Lim.async.work.choice-2-sequence-task` and their nested private staging enums.
Normal completion and the while body's direct linear return remain native
checks with their original results.

Additional native programs cancel before the first poll and at every Pending
point. The while-loop payload destructor verifies value 1 during both body
awaits and value 2 after replacement at the final condition await. Before the
payload exists, a trapping destructor must never be invoked. The for-loop
resource similarly remains absent until the first body await completes.

An instrumented resource retains a shared reference to a stack atomic supplied
as poll context. Its destruction callback increments that counter: cancellation
counts are zero before resource creation and exactly one while the resource is
retained across the second body await. Forgetting the counter before canceling
that Pending frame is rejected with Borrow at `#forget`. The negative program
removes subsequent direct counter reads, isolating the retained resource loan
from an ordinary use-after-consume error. This is checked by ordinary generated
function contracts; no async-specific loan permission was added.

### Public let-else loan-release regression and fresh default audit

The let-else success-loan regression now runs explicitly on graph lowering.
Its reference-bearing child holds the caller's exclusive loan across Pending,
writes through that reference on resume, and releases it on Ready. Native
execution returns 45 after the caller replaces the referent. The failure branch
instead completes immediately with 7 and releases the unused factory capture;
the caller can replace the referent and return 10. Mutation between polls is
rejected with `Borrow` at the original `#set` token, not a generated frame span.
No borrow permissions were changed for this migration.

A fresh temporary graph-default run of the same 229-test async integration
suite passed 184 tests and failed 45 in 94.71 seconds. The previous October 11
run passed 167 and failed 62. The default was restored to Legacy after the
audit. These numbers are regression progress, not proof that graph is ready
to become the default or that all ownership cases are covered.

The remaining failures include legacy private-layout assertions after native
execution, source diagnostic categories/spans, parse-only expectations for
formerly unsupported constructs, and one 20-second native compilation timeout
in `async_while_let_aggregate_payloads_use_declared_capture_types`. In particular,
`async_branch_prefixes_capture_only_live_values` rejects reading a forgotten
linear payload, but reports the physical Full-cell gate as `Type` instead of
the intended source `Linear` diagnostic. At this audit point, that required a
source-ownership diagnostic fix; changing the expected category would hide it.
The timeout needs an isolated measurement before classifying it as load noise
or an analysis-cost regression.

### Original source ownership before graph emission and cache lookup

Graph preparation now runs the ordinary typed-flow ownership checks on each
original lowered source body before probing generated artifacts. It reuses the
already resolved body and flow instead of reparsing or inventing a frame-based
ownership rule. Guard consumption, consumed-value uses, exit obligations and
projected replacement checks retain their ordinary diagnostic priority, source
spans and consumption labels. Deferred callee effects and layouts still require
the final ordinary-program validation; this check does not replace it.
Invalid-source emitter fixtures now assert these earlier ownership errors. A
separate adversarial fixture removes an owner initialization from an otherwise
validated graph and confirms the physical Full-cell projection gate still
rejects it; no production validation bypass was added.

This resolves the preceding audit's forgotten-payload diagnostic mismatch:
`async_branch_prefixes_capture_only_live_values` now reports `Linear` at the
original use, with a label identifying the consumption. The valid graph program
still executes natively and returns 47. Missing cleanup is rejected before a
generated cache directory is published. Source ownership also runs on cache
hits, so cached generated text cannot substitute for original-source checks.

Source ownership and emission share the planning arena's immutable linear-type
classification. Unlike the previous emission-only lazy classification, source
validation needs it even on warm generated-cache hits. A separate
`generator.async.source_ownership` timing records this added work. Five warm
debug-build checks of `examples/async_fn.lim` with graph lowering measured
0.202, 0.200, 0.199, 0.210 and 0.199 ms for that stage (median 0.200 ms).
These are stage-cost samples, not a before/after compilation speedup, and do
not show that redundant downstream checking has been eliminated.

Verification passed the 229-test async suite, the updated explicit-graph
prefix/consumption regression, 1,351 library tests (three manual benchmarks
ignored), the added independent physical-gate fixture, all 32 graph-production
tests, formatting and whitespace checks. The production suite includes cached
and standalone generated-code checks, shared/exclusive reference-bearing guard
previews, rejected-guard cleanup and caller-loan rejection. This does not prove
all five production gates complete; Legacy is still the default.

### Original declaration spans for async shadowing

Graph source validation now retains the original binder span for shadowing
instead of underlining the entire `#fn`. The shared diagnostic helper walks
declaration positions and lexical scopes in the original syntax tree. Earlier
condition reads, named call keys, comments, strings and pattern type/variant
heads cannot steal the highlighted location. Ordinary shadowing validation
still decides whether a declaration is invalid; the span helper grants no
ownership or borrowing permissions.

Literal-function shadowing validation also uses the canonical match-case
normalization before inspecting patterns, so `#case` wrappers no longer hide
arm binders. Graph source validation uses the same global-value and enum-variant
context as ordinary local renaming: global collisions are rejected before
source model resolution reports a generic duplicate-local error.

Explicit graph regressions verify exact byte offsets for nested local, match
arm and global-value collisions, plus escaped branch-local uses and linear
cleanup on continue paths. Structural span tests cover mutable declarations,
tuple destructuring, if-let/while-let patterns, range and general for loops,
let-else failure binders, repeated declarations within one block, independent
sibling scopes and Unicode binder columns. These changes resolve diagnostic
gates from the temporary default audit; they do not make graph the default or
remove Legacy.

Verification passed all 229 async integration tests, 1,353 library tests
(three manual benchmarks ignored), the targeted graph shadowing regressions,
the structural span matrix, formatting and whitespace checks.

### Public loop-poll interface regression migration

Seven loop regressions now select graph lowering explicitly and assert the
public single `work-poll` dispatcher rather than private `-wait`, `-outputs`,
`body-frame` or `body-poll.dispatch` spellings. Their Lim source programs and
native expected results remain unchanged.

Coverage includes a range-loop body await, suspension in a non-binding body
statement followed by continue/break, a general for-loop initializer whose
local spelling can be reused after the loop, an unbounded loop with terminal
match-arm transfers, an await inside a nonterminating loop that must actually
return Pending, and three distinct suspension points in one iteration. The
linear-state regression still executes reconstruction of a consumed `State`,
retains a separate linear `Token` through the loop, explicitly consumes both
at completion, and returns 3. Its separate Pending task is explicitly forgotten
as in the original test; this is not a destructor/cancellation-order proof.

These migrations remove tests' dependence on legacy staging interfaces without
changing borrow permissions, runtime semantics or the default lowering route.
They are part of the graph-default gate, not completion of the broader goal.

All 229 async integration tests passed with the unchanged default. A fresh
temporary graph-default audit then passed 194 and failed 35 in 93.35 seconds,
compared with 184 passing and 45 failing at the preceding audit. Legacy was
restored afterward. Remaining failures include private staging assertions,
source diagnostic/phase expectations, and the recurring 20-second aggregate
capture compilation timeout. The timeout is not treated as permission to
weaken the test or raise its limit; isolated analysis-cost measurement remains
necessary. Formatting and whitespace checks also passed.

### Earlier audit

A temporary graph default followed by `cargo test --test async_fn --quiet`
completed with 145 passing and 68 failing tests (213 total, 45.11 seconds).
The temporary default was restored to legacy after the audit. This is not a
claim that 68 distinct semantic bugs remain: failures include assertions about
legacy private layouts, different diagnostics, and native compilation timeouts
under parallel testing, as well as genuine lowering/borrow failures. The audit
does not justify switching the default or deleting legacy yet.

`graph_nested_destructuring_preserves_projection_types_and_retained_loans`
now exercises the explicit graph route independently of that default. It runs
ten native programs covering nested tuples, arrays, structs, aliases, pattern
initialization between awaits, mutation of two pattern leaves, and shared
external references retained through both suspension points. Both choices of a
reference selecting between two external owners return the selected value.
Forgetting the Pending frame retires its shared loan and permits subsequent
referent mutation. Negative cases preserve the original retained-loan `#set`
span and immutable pattern binding's assignment-target span.

At that audit, this evidence did not cover the live exclusive-reference aggregate
case. The incoming-path refinement described below subsequently closes three
nested destructuring variants on graph without changing their positive meaning.
Default migration still requires resolving the remaining public
interface differences and auditing the other control-flow failures.

### Exclusive destructuring: the caller-loop join

`nested_exclusive_pattern_storage_survives_loop_and_consecutive_polls` lowers the same
nested tuple/struct pattern with an external `#ref-mut #u64`. Three consecutive
straight-line polls return 42 as independently checked native ordinary code.
Forgetting the first Pending frame permits referent mutation; mutating it while
retaining that frame rejects with Borrow at the original assignment's `#set`.

The initial caller-loop probe rejected this exclusive variant from
`async_destructure.lim`. Instrumenting the conflicting origins showed the *same* original
borrow, referent and source span under two different storage paths: the initial
aggregate cell and its destructured reference cell. The caller's loop join
unions these possible locations, and argument checking treats them as
simultaneously retained exclusive handles. Straight-line calls do not introduce
that union. Thus the boundary failure was not evidence that the generated moves
physically duplicate this handle. The incoming-path refinement below resolves
this particular caller loop without discarding an origin or weakening overlap
checks. More general recurring correlations remain incomplete.

### Preserve incoming loan alternatives at unchanged binding reads

Ordinary call checking now keeps the nearest CFG join's predecessor snapshots
as alternatives when an aggregate read has overlapping exclusive may-origins.
The binding must remain unchanged from the join to its read. Unknown calls,
assignments, writes, relevant binding/scope changes and nonprimitive clone hooks
stop the query. Primitive scalar clones and arithmetic used by range loops are
transparent; they are not user callbacks. The predecessor union must exactly
match the existing snapshot's origins, or the checker falls back conservatively.
No point-specific provenance snapshot is replaced, and no async name, frame
layout, program-counter convention or pin rule enters this ordinary query.

Each predecessor remains a conservative may-state. Its coexisting loans are
never separated, and cross-argument combinations still use the existing overlap
checks and path-complexity limits. The predecessor index is built lazily once
per body, only when a potentially ambiguous aggregate read requires it.
Unit probes verify coexistence, missing-fact fallback, changed snapshots,
unknown calls, writes, scope changes and exclusive/named clone barriers.

The original exclusive variants of scoped nested patterns, awaited aggregate
destructuring and local destructuring now run explicitly on graph. The native
loop and consecutive-poll regression also verifies cancellation loan retirement.
A separate ordinary, nongenerated `Frame`/`shift` caller loop validates the same
initial-to-resumed reference-slot transfer. Retaining its frame still rejects
referent mutation. Public graph tests also reject referent mutation while
Pending and an overlapping shared waker argument at their original source
spans, while permitting mutation after Ready.

This is not a general disjunctive loan solver. For example, a nongenerated loop
that repeatedly moves its exclusive loan *back and forth* between two slots
still has both locations in its backedge may-state; this query does not split
that predecessor. More deeply recurring correlations and live parent/child
exclusive holders remain work toward complete control-flow coverage.

## Reuse shared source-loan snapshots during representation planning

The self-borrow planner previously scanned all before/after flow events once
per binding, including unchanged snapshots shared by the ordinary solver.
`FlowLoanOrigins::binding_origin_union` now collects all binding unions in one
source-ordered pass and visits each shared immutable binding snapshot once.
Snapshot identities stay live throughout the query; copy-on-write gives a new
identity when binding contents change. This skips repeated collection, not a
source solve, access check, lifetime check or emitted-program validation.
`--timings` exposes the collection as `generator.async.binding_origin_union`.

Equality tests compare the complete ordered origins against the old per-point
scan for empty-reference bodies, branch-selected local/external references,
loop-local bindings, aggregate-held references and exclusive references.
Repeated collection must also leave every point-specific query unchanged.

The ignored manual test `benchmark_shared_binding_snapshot_union` measures
only collection after source resolution and loan solving. On its 64-binding,
967-event workload, 11 debug-build samples of 20 collections had medians of
75,651 microseconds before and 6,946 after: 90.8% less collection time.
Every measured result is compared with the same ordered baseline facts.

A release whole-compiler comparison used `async_fn_poll_local_borrow.lim`,
explicit graph lowering, a fresh source/cache directory per sample, two
warmups and 20 samples per compiler. Copy/setup/teardown were outside the timer.
Median compilation was 134.60 ms before versus 132.67 ms after (1.4% lower).
Ranges overlap: 132.10–142.44 ms before, 129.50–144.42 ms after. Both produced
identical 35,850-byte executables. This small difference is not a demonstrated
general whole-compiler speedup; the collection is only part of compilation,
and warm generator-cache hits already skip this emitter path.

Verification passed all 1,340 library tests (three manual benchmarks ignored),
the manual collection benchmark, 13 immediate-borrow graph integration tests,
the ten-program nested graph regression, formatting and whitespace checks.

## Reuse provenance within outcome-contract summaries

The reference-bearing tuple case of
`async_while_let_aggregate_payloads_use_declared_capture_types` exceeded its
20-second per-compilation limit on graph lowering. Profiling a standalone copy
found repeated loan solves inside outcome-contract summaries: the summary,
its direct reads, consumed-entry profile and restoration guarantees each
requested provenance independently. The full trace recorded 103 solves
exceeding 100 ms, not one slow solve.

Each filtered outcome graph now solves ordinary provenance once and shares it
between those queries. The divergence-adjusted caller graph also reuses its
existing snapshots for direct reads. Different outcomes still solve separately;
the parent graph's facts cannot replace a filtered graph's facts. Entry-state
ownership solves remain separate, and emitted-program validation is unchanged.
The parity regression compares shared and independently solved queries and
checks that selected normal returns remain distinct. Reads on paths without a
selected normal return remain visible.

For the same standalone input with explicit graph lowering, cold generator
caches in fresh directories and the debug compiler, baseline total times were
26,203.582 and 26,171.006 ms. Afterward they were 10,917.822 and 10,619.370 ms:
58.3–59.5% below the baseline range. Inclusive provenance timing fell from
23,338.180 to 8,331.671 ms in the final sample. These are whole-compilation
debug measurements for this particular pathological input, not a claim about
release compilation or all programs. Both new executables returned 40, as
expected. Provenance remains the largest cost for this input.

All six aggregate-loop variants now run explicitly on graph lowering and pass
without increasing the timeout. Their focused integration test passed in
18.16 seconds total, and all 229 async integration tests passed in 28.99
seconds with the unchanged default. Graph is not yet the default; remaining
interface/diagnostic migrations and the broader safety goal are still open.
The final library run passed 1,354 tests (three manual benchmarks ignored).
Formatting and whitespace checks also passed.

## Move while-let helper assertions to the public graph interface

After provenance reuse, a fresh temporary graph-default async audit passed
195 and failed 34 tests in 34.07 seconds. The aggregate compilation timeout
was resolved. Legacy was restored after the audit.

Three failures happened after successful native compilation and execution:
the tests still required `expression-frame`, `body-frame`, or the private
`body-poll.dispatch` name. The scrutinee sequencing, repeated body suspension
and nested body-statement regressions now use explicit graph lowering and
assert the single public `work-poll` interface instead. Both Copy and linear
matched enum variants remain covered. The native inputs, expected results,
poll counts and timeout are unchanged.

Removing the first private-helper assertion exposed a previously unexecuted
linear matched-enum variant. Graph rejected the synthetic clone of its
computed await result; after materializing the clone, it also lacked the
result's source identity for cancellation and retained an occupied original
temporary through later cell cleanup.

Computed, reference-free owning temporaries now clone through a checked shared
pinned projection, then explicitly forget the original after the clone borrow
ends. This requires a sole-use temporary: additional action, control or edge
argument uses still reject rather than moving a reused owner. Raw erased and
reference-bearing owning clone sources remain unsupported by this path.
Await result values use their authoritative checked-site span, even when
ordinary structural normalization lost the driver's span. The span regression
also preserves execution order when other spans collapse and flow IDs change.

Native regressions cover default cloning, an observable clone hook that
increments the matched payload exactly once, and two full iterations with
repeated Pending to verify that the original value cell can be safely refilled.

The library suite passed 1,354 tests (three manual benchmarks ignored), and
the isolated async suite passed all 229 tests in 28.36 seconds. Running both
suites concurrently hit the aggregate test's unchanged 20-second timeout;
the isolated rerun passed. A fresh temporary graph-default audit then passed
198 and failed 31 in 34.67 seconds. Legacy was restored and the ordinary
compiler rebuilt. The remaining migrations still prevent the default switch.

## Public graph interfaces across branch, loop and block regressions

Seventeen more async integration regressions now use graph explicitly instead
of requiring legacy private helper names or expecting later-phase rejection.
They retain their native programs and expected outcomes: named `task`
arguments, mutable block assignments, adjacent awaits, short-circuit conditions,
pattern-gated bodies, loop initialization mismatch returns, and condition/body/
step transfers through continue, break and return. Linear return payloads still
run and are explicitly consumed; generated type capitalization remains checked.
Tests assert the single public poll function rather than a stage helper name.

The global-read regression now checks graph's original-source unknown-name
diagnostic, including the exact `missing_global` span. Existing shared-borrow,
unsafe static access and global-not-captured checks remain intact.

All 229 async integration tests passed in 34.86 seconds. A fresh temporary
graph-default audit passed 215 and failed 14 in 39.53 seconds, compared with
198/31 before this batch. Legacy was restored after the audit. Remaining
failures include obsolete unsupported-nested-await expectations, ordinary
source diagnostic differences and still-unmigrated helper-interface tests;
they are not evidence that the full safety/default-removal goal is complete.

## Source contracts and protocol/frame collision parity

The nested-await regression now runs the valid nested protocol-typed program
on graph and checks that an incompatible explicit result type identifies the
later `#u32`, rather than requiring legacy's unsupported-nesting error.
Loop body and step contract diagnostics likewise retain the exact offending
type span. A binding expecting `#u32` from a `#u64` child is checked by the
ordinary source checker at the full original await expression, rather than a
legacy-only keyword error. Protocol declaration errors use the complete graph
compilation pipeline, not an assumption about which phase rejects them.

That migration exposed a real missing check: graph accepted `Work-task` as
both the protocol bundle and generated public frame type. Graph and ordinary
expansion now share the declaration-versus-syntax-bundle validator. It runs
on the emitted program before semantic validation or fresh cache publication,
including when output came from cache. The new regression rejects fresh
output without creating a generated cache directory, then seeds a correctly
keyed/digested artifact accepted by the former path and verifies rejection
without regeneration or changing its contents.

Verification passed 1,355 library tests (three manual benchmarks ignored),
the focused fresh/cache collision test, and all 229 async integration tests
in 29.40 seconds. A fresh temporary graph-default audit passed 219 and failed
10 in 38.27 seconds, versus 215/14 before this change. Legacy was restored
after the audit and the ordinary compiler rebuilt. The remaining interface,
diagnostic and unsupported-legacy expectations still need migration before
the default switch and legacy removal.

## Loop-return interface verification

The loop-return regressions now explicitly run graph lowering for returning
after an awaited condition and after an awaited body. Both decision branches,
the explicitly typed condition, and the linear payload return are compiled
and executed with their original expected results (7 or 18). Generated output
must expose the single public `work-poll` dispatcher, without requiring
legacy-private choice or expression-ready helper names.

An incorrect explicit condition result type is checked through the complete
graph compilation pipeline. It must produce a type diagnostic for the Ready
payload mismatch and underline the original `#u64` type token. All 229 async
integration tests passed in 35.01 seconds after this change. The default is
still legacy; this verification does not establish completion of the route
removal or the full async safety goal. Legacy is to be removed, not retained
as a backward-compatibility interface for the unreleased language.

## Graph is now the default

The final ten previously failing graph-default regression groups now check the
canonical graph contract: direct and local aggregate destructuring, loop
initializers, linear ownership errors, and condition/body sequencing. Native
results, exclusive/shared retained-loan conflicts, and release on Ready or
explicit cleanup remain checked. Nested await result types come from their
declared child protocols; the obsolete unsupported-nesting expectation is gone.

The production default is graph, and `async-lowering=legacy` is rejected as an
unknown configuration value. The legacy enum variant is currently test-only.
This is not a compatibility mode: its remaining implementation and private
state/cancellation interfaces are still removal work.

The switch audit passed 1,356 library tests (three manual benchmarks ignored)
and all 229 async integration tests. A broader all-target audit exposed extra
assumptions: the mutable self-reference boundary fixture borrowed an immutable
owner, heap cancellation used obsolete per-state mappings, and error propagation
used a lowercase generated type. These now use explicit mutable ownership,
source-slot cleanup (with destructor metadata owned in a concrete wrapper), and
the capitalized result type. The immutable source is also explicitly rejected
at its original borrow expression before any generated code is accepted.

Control-flow diagnostics now structurally select the missing label or offending
break/continue keyword rather than the enclosing loop. The obsolete let-else
await rejection fixture is a real Ready-payload type mismatch instead. All
three UI tests passed. Six focused suites passed (5 boundary, 3 heap, 10 jump
table, 18 result propagation, 19 slice reborrow, and 5 timer tests). The returned
array-element test now checks both a disjoint write and a genuinely overlapping
write with a subsequent use of the returned reference.

All five native-example tests passed, including the complete declared-outcome
sweep in 42.71 seconds, after registering three previously missing examples.
Relocated build outputs and generated artifacts remain identical; the semantic
cache deliberately keys physical source paths, so its bytes are checked for
cold/warm stability within each workspace rather than equality across locations.
The reproducibility test passed. The full audit also observed two `ETXTBSY`
execution races; their focused jump-table and timer reruns passed, which does
not prove those races eliminated.

At that switch audit, one functional failure remained: a movable future forms
a shared reference selecting between two local scalars and explicitly forgets
it before awaiting. Emitted ordinary checking nevertheless reports a later
dispatcher-arm loan against an earlier initialization. The regression is kept
enabled and unreduced. This false rejection, internal legacy deletion, private
cleanup-interface removal, and the full requirement-by-requirement safety audit
remain work toward the original goal; this default switch is not completion.

## Movable poll-local selections and indexed projections

The branch-selected local-reference false rejection above is now fixed.
Single-target handles retain their ordinary lending capability; multi-target
handles retain the checked selected address and referent facts. This does not
authorize a live self-reference to move with the frame: physical reference-cell
analysis must prove every internal handle Empty on every reachable Pending
boundary. A structural regression deliberately removes that proof and requires
rejection for both representations. Original-body borrowing and completed
ordinary generated-program checks remain mandatory.

Indexed local borrows now use the saved, checked index or a proved in-bounds
literal, through a typed projection helper. Changing the source index after
selection cannot retarget an existing reference. The helper uses the actual
owner payload during the stationary poll and preserves the checked leaf type
and source mutability; it does not copy the owner or grant pinning to movable
source storage.

All 13 immediate-borrow integration tests passed, including cold/warm compilation
and independently compiling the emitted ordinary source. Added native cases
exercise both choices of different scalar values, a wide struct field versus an
array element, exclusive mixed-layout selection with referent-specific writes,
changed runtime indices, and mutable fields under indexed array elements.
Invalid shared/exclusive multi-target aliasing must still fail at the original
source expression before publishing generated cache files. Legacy implementation
deletion, private cleanup-interface removal, and the complete safety audit are
still outstanding; these passing cases do not establish goal completion.

## Legacy lowering removed

The legacy lowering and dispatcher-collapse modules have now been deleted,
along with the frontend capture-discovery/cache pipeline and its codec test.
There is no test-only legacy route left. Ordinary declaration parsing never
expands async bodies through a second implementation, and inspectable source
publication consumes the same graph output as executable compilation.
The former cancellation-state migration gate now checks rejection of the
obsolete per-state patterns directly on graph, without compiling a legacy
version first.

Independent syntax-contract tests remain test-only regression probes, not an
alternate executable lowering path. The empty expansion-plan return plumbing
and graph-private cancellation interfaces still need cleanup. Removal of the
legacy implementation alone does not prove the complete async safety goal.

Post-removal checking passed all targets. The library suite passed 1,348 tests
(three manual benchmarks ignored); the lower count reflects removal of tests
for the obsolete implementation/cache codec, not disabling graph regressions.
All 229 async integration tests, ten dependent-cancellation tests, five
standalone generated-code boundary tests, thirteen immediate-borrow tests,
and three heap-contents tests also passed.

## Empty-plan plumbing and duplicate source-publication checking removed

Frontend expansion returns the ordinary program (or an owned checked arena plus
its retained graph output), not an always-empty legacy capture-plan map. The
single-variant route selector and route-specific wrappers are gone. Compilation,
checking, source publication and editor lookup use the same graph pipeline.

Standalone inspectable-source publication previously expanded and checked the
graph to obtain that empty map, then prepared and checked it again in the writer.
It now prepares it once. A cold-publication regression requires exactly two
semantic passes: the original source and its emitted ordinary program. The
existing retained-output regression still requires zero extra semantic passes
during publication following checked owned expansion.

Measured with `nix develop -c cargo test --release --lib
graph_source_publication_cold_timing -- --ignored --nocapture`: seven cold-cache
samples after one executable-path warmup, one simple async function, same source
and fresh output directories per sample. Median publication time fell from
32.777 ms to 17.774 ms (45.8% lower), and semantic passes from four to two.
The timed region includes source loading/preparation, checking and generated-cache
writes; it excludes compiler process startup, backend emission and native linking.
This is a measurement of the standalone source writer, not a claimed 46% speedup
for normal executable compilation, which already retains its checked output.

## One cancellation interface in planning and emission

The public-cleanup mode switch is gone. Graph generation always provides
source-slot cleanup, whether called by production compilation or structural
tests. The raw-state `poll-cancel` exporter and fixed `Frame-state` declaration
are deleted; extraction uses a fresh internal struct name. Declaration planning
no longer reserves or invents these removed APIs, and registers the actual
struct frame kind for both movable and pinned generators. Configured cancellation
dispatchers take the cleanup aggregate directly, without rewriting a legacy
state signature in a later pass.

Unit fixtures now inspect public cleanup cells by source binding/await identity.
Their original destruction counts, entry/Pending/Ready cases, repeated cleanup,
external-loan conflicts, and child-before-referent checks remain enabled. A new
structural test checks the same cleanup contract for both generators and permits
a user declaration using the removed `Work-frame-state` name. Negative tests
reject the absent type/function through ordinary source diagnostics, without a
migration mode or special compatibility diagnostic; errors precede publication.

Verification passed all-target checking, 1,350 library tests (four manual
benchmarks ignored), all 229 async tests, ten dependent-cancellation tests, five
independent generated-code boundary tests, three heap-contents tests, two
self-borrow cleanup tests, the complete five-test native-example suite, and
relocated cold/warm reproducibility. The 32-test graph-production run passed 31
and encountered one `ETXTBSY` process-launch error; the affected aggregate-guard
cleanup matrix passed its isolated rerun. This does not prove the launch race
eliminated. The full requirement-by-requirement safety and performance audit
remains outstanding; interface unification is not goal completion by itself.

## Whole-element poll-local array borrows

The completion audit found that indexed scalar-field tests did not cover a
stored borrow of an entire aggregate element. A source-checked movable function
that borrowed `Counter` from an owned array, changed its index, used the borrow,
and retired it before awaiting failed ordinary checking of the generated code.
The dispatcher joined the physical exclusive loan into the array-initialization
arm. The same failure occurred for structurally Copy and explicitly linear
aggregate elements.

Numeric-index planning now certifies reference-free owned addresses independently
of Copy load permission. Ordinary projected reads and writes still pass through
the separate Copy gate. Direct owned aggregate-element references use checked
selected-pointer storage, with their original owner anchors and the existing
physical Empty proof at every movable Pending boundary. This exception does not
apply to dereferenced or slice lenders, or reference-bearing aggregate contents.

`whole_array_element_borrows_end_before_suspension` covers both ownership modes,
changing the index after borrowing and mutating both selected elements. It checks
cold/warm generated-source equality, independently parses and checks the emitted
ordinary program, and executes both compilation paths. The companion negative
test rejects destroying the live referent, an overlapping shared borrow, and
retaining the handle across suspension without pinning. It checks original-source
diagnostic locations and requires that invalid invocations publish no cache.
