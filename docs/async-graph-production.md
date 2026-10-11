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
