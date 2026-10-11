# Async safety and lowering audit

This audit originally covered the five migration and cleanup improvements
listed below. Their completion does not certify the subsequent aggregate-storage,
cloning and analysis-performance goal, or formally verify the language's entire
borrow checker. The runtime remains
ordinary generated Lim source. Both original-source checking and final ordinary
generated-program checking remain mandatory, including on cache hits.

## Current follow-up scope (2026-10-11)

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
