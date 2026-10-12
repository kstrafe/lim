# Async safety and lowering audit

This audit originally covered the five migration and cleanup improvements
listed below. Their completion does not certify the subsequent aggregate-storage,
cloning and analysis-performance goal, or formally verify the language's entire
borrow checker. The runtime remains
ordinary generated Lim source. Both original-source checking and final ordinary
generated-program checking remain mandatory, including on cache hits.

## Current follow-up scope (2026-10-11)

### Accepted direction: checked lowering with unsafe implementation details

The selected approach is to justify unsafe async storage accesses through the
original async analysis and checked lowering, not introduce a public `#storage`
type solely to make the emitted representation independently borrow-checkable.
Ordinary emitted-code checking remains mandatory for types, explicit unsafe
scopes and ordinary safe operations; it does not prove raw accesses sound.
The original source's initialization, aliasing, escaping-reference, pinning and
cancellation obligations must remain checked on cold and warm compilations.
Pinning establishes address stability, not any of these other permissions.

Frame states should carry initialization distinctions whenever possible, rather
than adding redundant per-field flags or runtime checks around proved accesses.
If different paths reaching one state have different initialization, lowering
must preserve that distinction; treating an unknown field as initialized is not
an option. Native address recipes must also respect actual stack versus
heap/global layouts. Casting an untagged address to an ascending payload is not
valid for descending stack storage, even when the frame is pinned.

Initialization analysis is separate from cell emission. Production now
specializes the dispatcher by `(source block, source and physical initialization)`.
Distinct incoming field histories remain distinct states; both Ready and
Pending edges write the corresponding specialized PC. No runtime initialization
bitset is added. Construction enters state zero, and loops deduplicate recurring
histories instead of unrolling iterations. Every specialized state's projected
accesses are checked against its own initialization facts.

Specialization is deterministic and capped at 16,384 states; exceeding the cap
reports an error at the invocation, rather than silently merging incompatible
histories. The former must/may solver remains a test-only independent oracle:
intersecting/unioning exact states agrees with it across 256 cyclic graphs.
Tests also cover correlated fields, unreachable blocks, loops, invalid domains,
state-budget exhaustion, and native branch/resume execution.
The audit also corrected reference-free Copy release: `#forget`/`#drop` now
discard a read copy without emptying the source cell or its initialization
fact. Copy field release no longer forces aggregate decomposition. Native
regressions verify subsequent borrowing/field reads and resumed values.

Reference-free Copy cell transfers now use the same unchecked, typed pinned
payload projection as Copy reads. The caller's checked flow proves Full; the
helper reads a copy, discards the old wrapper and publishes Empty, without
matching the old variant. This removes a redundant variant branch, not the
initialization tags themselves. No reference-bearing or owning transfer is
changed by this optimization. Native tests cover a multiword Copy struct across
Pending/Ready on both descending stack and ascending heap storage, and inspect
the helpers to require unchecked Copy reads while retaining owning matches.
Heap cleanup explicitly ends the poll reference before releasing the allocation.
Verification of this transfer change: 1,380 library tests pass with seven
existing ignored tests; all 22 checked-expansion, dependent-cancellation,
generated-boundary and unchecked-projection integration tests pass.
All-target checking and whitespace checks pass.

The source domain describes bindings, decomposed fields and nominal shells.
The physical domain additionally records assignments to actual frame cells
through the emission helpers: takes, stores, explicit releases, address/index
retirement and reference retirement. Edge-local effects preserve parallel
argument staging and separate Ready consumption from Pending restoration.
Initialization starts with the cells actually filled by the constructor,
including aggregate parameter parts and external reference captures, not an
unused aggregate root cell. Trace-only rendering uses a separate emitter and
performs no additional source or native semantic checking; its cost is reported
as `generator.async.physical_occupancy` in detailed stage timings.

Production cleanup now takes the union of physical occupancy at construction
and reachable Pending returns. It reuses the dispatcher specialization rather
than running a second cancellation-cell solver. The former solver remains a
test-only independent oracle. A native test inspects every emitted cell tag
at two consecutive Pending returns while a sibling reference remains live,
another aggregate field is moved and later restored, and temporary child
cells are consumed on Ready and restored on Pending. These tag inspections
are test instrumentation, not added runtime checks in normal generated code.
An intentionally incorrect occupancy expectation traps in a native negative
control, confirming that the test reaches the tag inspections.
Cleanup schemas no longer export fields proved empty at every cancellation
boundary. The async example and partial/nested cleanup callers have been
updated, including removal of the redundant `step` cancellation handler.

Verification: 1,382 library tests pass with seven existing ignored tests;
all 61 graph/expansion/cancellation/array/restoration integration tests and
38 heap/self-borrow/rejection/UI tests pass. The 236-case async run passed
234 tests; one native launch hit `ETXTBSY` and one compilation timed out
under parallel load. Both tests pass individually on rerun. All-target
checking and whitespace checks pass. This records the harness/load issues,
not a claim that they have been fixed.

Physical occupancy is not permission to access a cell: source initialization,
aliasing, escaping-reference and cancellation validation remain mandatory.

Dependent-child cancellation now dispatches on the existing externally visible
PC. Each construction/Pending case contains only children whose physical cells
are Full in that specialized state, in child-before-lender order. Ready and
previously cancelled frames select an empty case. Pinned child handlers receive
a typed unchecked payload projection justified by that state; this preserves
stack/heap reference metadata and does not move the pinned child. Movable,
reference-bearing children still use their ordinary checked consuming read.
Both cleanup/export and destruction use this path. Generated-source tests
require the PC selector, reject per-child `variant-is` conditionals, and require
unchecked rather than checked pinned-child projections. Native coverage includes
different live children at two successive awaits, mixed internal/external
references, mutable loans, nested pinned children on stack storage, and
repeated cancellation.

The heap-owned nested-child acceptance test remains ignored, explicitly
unfinished: after correctly releasing the Pending reference before reborrowing
the allocation, ordinary call-entry analysis rejects the first parent poll
with an unresolved referent contract. Staging the initial frame before
allocation does not fix it. This is not permission to bypass contract inference
or introduce an async-specific exemption. Generic unchecked-projection tests
already cover stack/heap layout, but do not establish that this nested heap
future program compiles. Resolving its allocation-backed call contract remains
part of the active goal.

The change exposed a backend bug in scalar matching: x86-64 memory comparisons
sign-extend their 32-bit immediate, so a direct comparison against `u32::MAX`
missed the completed PC. Scalar pattern emission now materializes constants
outside the signed immediate range. Native tests cover matching and fallthrough
for u32, u64, i64 and multiword u128 constants.

This removes the per-child occupancy-selection branches, not every cell guard.
Boundary Empty assertions, reference-bearing consuming matches and public
cleanup optional wrappers remain; no claim is made that the payload has already
become untagged or that pinning alone permits an unchecked access.

Verification of the PC-selected cancellation change: 1,382 library tests pass
with seven existing ignored tests; all 236 async integration cases pass with
four test threads. All 65 checked-expansion, graph-production, dynamic-array,
restoration, heap-contents, generated-boundary, rejection, self-borrow-cleanup
and unchecked-projection integration cases pass. Eleven dependent-cancellation
tests pass; the new nested heap acceptance case is explicitly ignored for the
contract limitation above. All eleven jump-table/scalar integration tests,
all-target checking and whitespace checks pass. No temporary syscall probes
or diagnostic artifact-retention code remains.

Existing Empty/Full cells and their runtime operations have not yet been
replaced; contiguous payload lowering and state-specific partial cancellation
remain required. Broader physical/native parity coverage is also still needed
before removing the representation's runtime tags.
Earlier verification: all 1,374 library tests pass with seven existing ignored tests;
23 cancellation, standalone generated-boundary, adversarial and UI integration
tests pass. All-target and whitespace checks pass. A raw-address prototype was
discarded after native testing exposed its incorrect stack-layout assumption;
neither that prototype nor a pointer-from-address keyword is retained.

Field-aware storage now supports partial moves and restoration of nested
structs, stationary sibling borrows and explicit cancellation obligations.
Owning clones preserve references for named/reused owners and computed
temporaries, including checked field/tuple paths and runtime-indexed arrays.
Whole-value clones of decomposed aggregates now snapshot their field cells
without relocating live sibling referents, preserving ordinary clone-hook
dispatch and actual reference origins.
Cold/warm and independently compiled ordinary generated-code regressions cover
these paths. See the later implementation and verification records in
[Graph async production route](async-graph-production.md).

The follow-up goal is still active. Whole aggregate borrows cannot yet
be taken over decomposed independent field cells, which are not a contiguous
instance of the original type. Preserving pointer identity and real loan origins
while supporting that access remains required; casting unrelated cells or
weakening validation is not an acceptable substitute.

The native baseline in `tests/fixtures/partial_aggregate_whole_borrow.lim`
retains a shared reference to `Owner.kept`, moves and restores `Owner.item`,
then borrows the whole `Owner`. It compares the original sibling address with
the address obtained through the whole reference and returns 42 only when
both identity and the restored value are correct. The adversarial test also
rejects exclusive whole and sibling borrows while the sibling remains
borrowed, with the conflict and original-borrow spans checked. An equivalent
pinned async body with suspension before restoration is still rejected at
`(#borrow owner)` with the contiguous-storage diagnostic. This is an open
representation limitation, not an unsupported ordinary source ownership pattern.

The existing two leaf cells have interleaved tags and payloads; the corresponding
ordinary two-field struct has adjacent payload words. Treating the first cell
payload as the whole struct would read the second cell's tag as a user field.
Reconstructing the struct elsewhere would instead change the retained sibling's
address. A replacement needs contiguous, address-stable payload storage with
separate initialization state, retaining per-field loan origins and cleanup
obligations in ordinary generated-code checking. General partial-initialization
storage is a possible language-level solution, not yet implemented or approved
as a new public primitive; no async-only checker exemption is proposed.

An existing-primitives control in
`tests/fixtures/pinned_partial_field_calls.lim` retains a pinned mutable field
reference before consuming that field. Ordinary helper calls consume and then
restore the referent through the same handle. After forgetting that handle,
the whole restored owner can be borrowed while a shared sibling reference
remains live. The native program returns 42 and compares the sibling's exact
address before and after restoration. Adversarial controls check both primary
and consumption/loan-origin spans: recreating a field reference after consuming
its referent is rejected, reading the unrestored owner through a helper is
rejected at that call, and an exclusive pinned sibling borrow conflicts with
the retained shared loan. These controls pass without checker changes.

This is evidence for exploring contiguous pinned payloads with retained field
handles, not proof of a complete async storage implementation. The fixture
does not suspend, return Pending, or cancel a partially initialized frame.
Those boundaries and cleanup obligations still need independently checked
generated-code coverage. A new general storage primitive remains a proposal,
not a demonstrated prerequisite for every possible lowering design.

A follow-up ordinary poll-shaped probe consumes a field and returns its retained
handle inside a `Pending` payload. That route fails at the return with E4200:
`returned reference may point to a consumed linear referent`. The reduced
`tests/fixtures/pinned_empty_handle_pending.lim` regression checks the complete
return-expression span and the original `#pin-read` span. Restoring the same
referent before returning permits the reference-bearing result, so the issue
is empty referent storage, not a blanket restriction on handles in results.
All five adversarial tests pass. `FlowGraph`'s returned-reference consumption
check enforces this distinction without any async-specific handling.

Consequently, retaining a field handle through ordinary helper calls does not
by itself permit transporting that handle across a Pending return. A contiguous
frame design must account for initialization at the boundary and cancellation,
not merely physical layout. Do not reinterpret a safe pinned reference as an
empty-storage capability or bypass this check with lifetime-only raw provenance.

### Historical storage proposal (not selected or implemented)

The desired positive async case is now kept in
[`async_partial_whole_borrow.lim`](../tests/fixtures/async_partial_whole_borrow.lim),
not only in a temporary audit directory. It must eventually return 42, preserving
the same sibling address across Pending and field restoration. It currently
fails with E4000 at the whole borrow; this is deliberately recorded as an open
acceptance case, not a passing regression or completed feature.

The proposed general `(#storage T)` type would own one aligned, contiguous
payload with exactly T's field offsets and a separate initialization sidecar.
It is always linear and never implicitly destroys initialized contents.
Moving an unborrowed, unpinned wrapper is permitted; a pinned local retains
the existing permanent immovability rules. A movable heap-owning handle would
retain its stationary allocation's identity under the existing pin-own rules.
Neither forgetting a pin handle nor a storage handle unpins surviving data.

Candidate spellings below are a design sketch, **not accepted Lim syntax**:

```lisp
(#let-mut slots (#storage Owner) (#storage-empty Owner))
(#storage-put (#storage-field slots kept) 40u64)
(#storage-put (#storage-field slots item)
  (#struct-literal Token (: value 1u64)))
(#let kept (#ref #u64) (#storage-borrow (#storage-field slots kept)))
(#let moved Token (#storage-take (#storage-field slots item)))
(#forget moved)
(#storage-put (#storage-field slots item)
  (#struct-literal Token (: value 2u64)))
(#let whole (#ref Owner) (#storage-borrow slots))
```

Field selection is a checked place operation, not a detached reference or
an address cast. Native loan origins must resolve to the wrapper's actual
payload and typed projection. A whole borrow overlaps every descendant; a
field borrow permits changes only to disjoint fields. Operations must not
first borrow the entire wrapper mutably, which would unnecessarily reject
restoring `item` while `kept` remains borrowed. Nested and indexed projections
must preserve existing bounds, index-evaluation and alias rules.

Initialization is independent of pinning. Taking a value clears its precise
initialization state; putting a value requires empty destination storage and
cannot implicitly overwrite a linear value. Whole access requires every
relevant field initialized. Across function boundaries or runtime state
branches, unknown initialization cannot be treated as Full: the design must
either carry a statically checked proof or retain a runtime initialization
check, like a bounds check, before forming a typed reference. The choice and
public spellings require review. A known-empty access must not pass validation.
No operation may bypass existing pinning, loan, replacement or escape rules.

Reference-bearing contents must preserve their original parameter/allocation
origins through stores, takes, returns and clones. Initialization bits alone
cannot prove those lifetimes. Cancellation must explicitly consume only live
contents and retire dependent loans before their owners; in-place destruction
of pinned children must not become a by-value take. Nominal linear obligations
remain explicit, including when all fields have individually been consumed.

Implementation requires ordinary frontend, typed-flow and native-backend
support for this general storage type. The async generator would merely emit
its operations. Original-source checking and independently checked emitted Lim
remain required on cold and warm caches; no async-only checker permission is
part of this proposal. Acceptance must include shared/exclusive whole and field
borrows, nested restoration, returned references, stack/heap pinning, early and
repeated cancellation, exact address identity, and invalid accesses/escapes.
This proposal added no keywords. The selected direction above instead relies
on checked async lowering to justify unsafe implementation operations.

The first implementation step introduces general unsafe
`#pin-get-payload-unchecked` and `#pin-get-payload-unchecked-mut` projections.
They preserve actual projected loan origins and native stack/heap reference
layout, but omit the active-variant guard. The caller must prove the variant
and payload initialization; unsafe does not bypass borrowing or lifetimes.
Generated Copy/raw slot peek helpers now use these projections and are
explicitly unsafe functions called from generated unsafe blocks. Original
source validation still runs on cold and warm expansion. Generated frames
are opaque so safe clients cannot modify the fields that establish this proof.
Empty/Full cell tags, guarded transfers and conditional cleanup still exist:
that step did not complete contiguous payload storage or state specialization.

Deep scalar borrows within independently stored aggregate leaves now lower to
references rooted in their actual field cells. Field/tuple/static-index/runtime-
index tests cover shared/exclusive ordinary and pinned references, disjoint
restoration, changed index variables, cancellation and independently checked
generated code. Movable tasks support operation-local references, not internal
references retained across Pending. See ASYNC-DEEP-FIELD-BORROW and the newer
production-route record; whole aggregate borrows remain a distinct storage gap.

Guarded/lending analysis has incremental measured improvements, not a completed
performance audit. Provenance reuse, vacuous-query elimination, use indexing,
dense transfer membership and immutable consumption snapshots reduce repeated
work.
Snapshot sharing reduces warm total check time 5.8–15.6% on four measured async
fixtures without reusing facts across independent entry/outcome analyses.
Whole-check speedups are fixture-dependent and sometimes absent; paired
measurements and their limits are recorded in the production-route journal.
Read-only binding-origin joins now avoid copying unchanged contents between
distinct snapshots. A repeated warm suspended-reference-guard comparison shows
10.2% less total checking time, with non-overlapping ranges; smaller examples
are mixed. This does not close the broader analysis-performance audit or the
whole-aggregate storage gap above.

Earlier suite counts and migration gates below are historical evidence. They
must not be read as the current verification count or as outstanding legacy
route work: production has one graph lowering route, with no legacy fallback.

## 1. Children borrowing parent locals

`async_emit::in_place_cleanup` is shared by pinned cleanup and configured
destruction. It orders occupied dependent cells before their referents, rejects
dependency cycles, and preserves reference-bearing lender storage until its
children are retired. Generated pinned children must have a safe, one-argument
unit-returning handler taking their pinned mutable reference. The handler
receives the actual stored payload; the cell is emptied only after it returns.
An ordinary movable protocol child can instead be consumed by its handler while
the parent remains stationary. This does not permit moving a pinned child.

Evidence in `tests/async_dependent_cancellation.rs` covers shared and exclusive
children, runtime-indexed owners, suspension in a for step, selected local and
external referents, generated pinned children, entry/Ready/repeated destruction,
and rejecting a by-value pinned-child handler before cache publication.
`tests/async_self_borrows.rs` also rejects moving a self-referential frame after
forgetting its Pending handle; discarding a handle does not undo pinning.

## 2. References with varying targets

Source loan origins retain resolved owner, field, variant, index, and external
parameter identities. Emission preserves the selected address rather than
reevaluating the source selection. Layout recipes validate each resolved
projection against its actual owner type. Source aliases and lifetimes are
checked separately from the physical representation.

`graph_selected_reference_mixes_slice_and_external_reference_targets` in
`tests/async_fn.rs` checks both branch choices and shared/exclusive selections
among slices, external references, fields, and arrays. It includes rejection of
overlapping inputs, illegal escapes, and conflicting writes. The pinned
local/external selection test covers stationary frame storage.
`tests/async_dynamic_array_edges.rs` covers empty layouts, nested nonempty
layouts, and two runtime coordinates, including changed source indices.

## 3. Control flow, guards, lending, projections, and reuse

`tests/async_graph_production.rs` checks shared, exclusive, pinned-exclusive,
aggregate, tuple, and alternative-pattern guards. Its cases cover suspended
preview, rejection, commit, mutation after preview release, nested field order,
caller alias rejection, and cleanup in entry/preview/committed states. Its helper
reads the generated file, substitutes it for the invocation, and independently
parses, type-checks, compiles, and runs the resulting ordinary program.

`tests/async_graph_immediate_borrow.rs` covers synchronous lending, stored local
handles retired before suspension, disjoint projections, selected addresses,
slice bounds, and owner extraction. Whole aggregate array elements are tested
in both explicitly linear and structurally Copy forms. The source index changes
after borrowing; both selected elements must still be mutated correctly. The
companion rejection test checks destruction and alias conflicts at original
source lines and refuses a live local handle across a movable Pending boundary.

Pending handles are repeatedly fed back to poll in these runtime suites.
Pinned handles keep the same frame stationary. Movable frames must have all
internal physical reference cells Empty at every reachable Pending edge;
`movable_local_references_require_complete_physical_boundary_proofs` removes
those facts deliberately and requires rejection. This includes checked-pointer
storage: using a pointer does not exempt a live handle from the boundary proof.

## 4. One implementation and cancellation interface

Production routes only through original-body graph planning and emission.
Graph lowering is the default; `async-lowering=legacy` is rejected. The old
`async_fn.rs` and `async_dispatch.rs` implementations and capture-cache plumbing
have been deleted. `async_cfg` and `async_contract` are test-only independent
contract oracles, not alternative lowering routes.

Both generator variants register their actual struct frame and always expose
source-slot cleanup. The old fixed `Frame-state` type, raw `poll-cancel` function,
and public-cleanup mode switch are gone. Private extraction storage uses a fresh
name. `cleanup_is_uniform_and_does_not_reserve_a_private_state_api` verifies both
variants and allows user declarations of the removed private type name.
Negative frontend/integration tests reject the removed APIs through ordinary
source-spanned diagnostics, rather than compatibility or migration handling.

## 5. Reuse checked facts and measure redundant work

`async_prepare::Planning` owns one resolved declaration/body/flow arena for the
invocations and shares immutable `LinearTypes` classification. Binding-origin
collection scans unique immutable snapshots once instead of scanning all events
per binding. Outcome summaries share provenance within each filtered outcome
graph, never borrowing the unfiltered graph's facts. Ordered-baseline and
filtered-graph parity tests guard these optimizations.

The standalone source writer no longer expands and checks once merely to obtain
an empty capture map, then repeats that work for publication. Its regression
requires two semantic passes: original source and emitted ordinary program.
Retained owned expansion requires zero additional passes when validating again
and publishing its already checked output. Neither optimization removes an
ownership, access, lifetime, or final generated-code check.

Measurements, methodology, and limitations are recorded in
`async-graph-production.md`: binding-origin collection fell from 75,651 to
6,946 microseconds on the measured collection workload; cold standalone source
publication fell from 32.777 to 17.774 ms and four to two semantic passes.
These are stage-specific improvements, not universal executable-build claims.
Loan solving still does real work; the jump-table dispatcher does not eliminate
source analysis, and no generic cross-graph loan-solver cache is claimed.

A fresh release run of `graph_source_publication_cold_timing` after the
whole-element fix measured a median of 18.038 ms across seven cold-cache
samples after one executable-path warmup. Every sample recorded exactly two
semantic passes. This includes validation and cache writes, excludes backend
emission/linking, and is consistent with the earlier stage-specific result;
it is not a new paired whole-compiler speedup measurement.

## Historical migration verification record

After the whole-element fix, 1,350 library tests, ten dependent-cancellation
tests, six dynamic-array tests, all 229 async tests, and five independent
generated-code boundary tests passed. All 32 graph-production tests passed,
including the longer guard/cancellation matrices. All 15 immediate-borrow tests
and 83 emitter tests passed separately. Retained-owner verification passed five
frame-restoration, three heap-contents, two self-borrow cleanup, and 25
self-borrow tests, including forgotten-Pending-handle move rejection.
All-target checking and the fresh release source-publication benchmark passed.

The preceding full all-target run passed the other suites, including all 32
graph-production cases, native examples, and relocated cold/warm reproducibility.
Two native-linking launches failed with Linux `ETXTBSY`; all 34 native-linking
tests passed in a serial rerun. This records the launch issue rather than
claiming that the parallel harness race has been eliminated.

The five migration/cleanup improvements above have verification evidence;
the current follow-up scope remains unfinished. Necessary safety boundaries
remain explicit: a local borrow crossing
suspension needs a stationary pinned frame, unsafe emitted storage does not
authorize invalid original source, and cache hits do not bypass validation.
