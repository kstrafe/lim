# Async safety and lowering audit

This audit originally covered the five migration and cleanup improvements
listed below. Their completion does not certify the subsequent aggregate-storage,
cloning and analysis-performance goal, or formally verify the language's entire
borrow checker. The runtime remains
ordinary generated Lim source. Both original-source checking and final ordinary
generated-program checking remain mandatory, including on cache hits.

## Current follow-up scope (2026-10-11)

### Exact stored-handle child ancestry (2026-10-12)

Returned child projections now preserve the precise caller slot supplying an
exclusive handle, including through forwarding helpers and typed holder reads.
Call checking suspends only that slot, not every sibling reference in its owner.
The summary distinguishes a child reborrow from an owned reference transfer;
semantic cache schema v3 serializes the distinction in both transfer modes.
Known typed holder addresses may identify their stored loan, but an opaque
lifetime anchor cannot invent a pointee identity or grant native access.

Whole-reference forwarding retains the existing transfer behavior rather than
being mistaken for a new field projection. A checked call's child retains the
actual pointee, not ownership of the intermediate pointer descriptor. Dropping
that nonowning descriptor is permitted; conflicting pointee access and pointee
destruction remain rejected. Ordinary retained slice operations still enforce
their descriptor-specific suspension rules. These are generic checker changes,
not permissions selected by async-generated names.

All 236 async integration tests pass with no filters, including the previously
failing mutable loop-body and deep-field regressions. The library suite passes
1,411 tests (eight existing ignored). The UI suite passes all three tests.
Cold/warm integrations pass three checked-expansion, nine contiguous-storage
(one explicit unfinished gate), fourteen dependent-cancellation, five generated
boundary, 26 self-borrow and ten semantic-cache tests. All-target checking passes.
Six immediate-borrow tests still assert an obsolete generated helper name;
the disjoint-field case reproduces that assertion failure on the pre-change
baseline. The stale frame-restoration representation test also remains open.
Neither failure has been counted as passing verification.

Reference-bearing contiguous async owner storage and complete physical tag
removal remain unfinished. The final architecture HTML has not been written;
it is to remain uncommitted when the async goal is actually complete.

### Refresh ordinary-code storage regressions (2026-10-12)

The fifteen immediate-borrow tests now accept inline word-backed projections
as well as the older typed-cell projection helper. Both routes still undergo
independent ordinary checking and native execution, cold and warm; helper names
are not treated as the semantic contract.

The frame-restoration regression now copies and renames the actual emitted
parameter-access functions rather than assuming that every frame field has an
Empty/Full enum. Independent ordinary code successfully replaces and reads the
same owner's storage after completion and cancellation. It asserts word-backed
operations and absence of per-cell variant guards. Replacement while Pending
traps at the explicit terminal-state guard (SIGILL), before the unsafe write.
All five frame-restoration tests pass.

This deliberately does not claim that the native checker proves unguarded raw
word writes safe. Numeric backing has no typed contained-reference identity;
the original source analysis, checked lowering and generated access contract
justify these unsafe implementation details. Removing the guard is not a valid
safe implementation, and pinning alone supplies no aliasing permission.

Final follow-up verification passes all 45 graph-production tests and all 21
heap-reference contents tests. A separate concurrent heap launch hit Linux
`ETXTBSY`; its serial rerun passed all 21 tests, as did the run following the
graph matrix. All-target checking and formatting pass after both changes.

### Untagged typed-owner backing evidence (2026-10-12)

`partial_reference_typed_owner.lim` now exercises a real typed Owner directly,
without an outer Empty/Full cell or per-field flags. The native size assertion
checks that Owner consists only of its reference and Token field widths. Its
retained field address survives unsafe sibling extraction and restoration;
the whole-owner view reads the original caller reference and returns 42.
Stack and heap implementations pass cold and warm with both shared and
exclusive contained references. Caller mutation and sibling mutation under a
whole shared view remain Borrow errors with source spans. No numeric word view
is allowed to fabricate these contained-reference origins.

The contiguous-storage suite passes thirteen tests with the one explicit async
reference-owner completion gate still ignored. This is backing-model evidence,
not integration of that model into async frames. In particular, these ordinary
owners start fully initialized. Future-local owners may initialize on a later
poll; constructors cannot hoist their observable work, forge reference values,
or reintroduce per-field runtime occupancy bits just to initialize the backing.
The emitter must also preserve partial ownership and specialized cancellation
when using the same region rather than independent leaf cells.

One concrete missing generic mechanism is visible in the existing word-storage
analysis: `#word-write` does not currently export a value's contained-reference
origins into its numeric destination, and a later typed read/view cannot recover
them. Allowing reference-bearing word reads without such an actual write-derived
provenance proof would contradict the existing missing-slot-provenance gate.
That gate remains intact. Investigate tracked typed writes and region projection
before enabling reference-bearing contiguous word storage; numeric bits alone
are not evidence of a valid contained reference.

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

The generic unsafe implementation foundation now includes `#word-read`,
`#word-write` and `#word-view`. They operate on slices of flat Lim `#u64`
value words, preserving descending-stack address metadata and explicitly
discarding packed-native-byte metadata. Owned reads and writes add no occupancy
tags or initialization sidecar. The caller must prove capacity, initialized
representation, ownership and, for pinned views, permanent address stability.
Views retain the source slice range's alias and lifetime anchor, including
through helper returns and heap-owner release. Numeric words cannot supply
missing provenance for reference-bearing fields. These operations currently
have x86-64 native emission; AArch64 still rejects slice types rather than
silently lowering them incorrectly.

The inverse `#word-view` form exposes an ordinary or pinned reference as an
explicit `(#slice #u64)` or `(#slice-mut #u64)` of exactly the referent's flat
word width. It preserves descending-address metadata rather than reinterpreting
the pointer as an ascending native array. This is unsafe and requires flat-word
backing, not packed bytes; it grants neither ownership nor reference provenance.
Exclusive results require exclusive sources. Seventeen generic word-storage
tests pass, including stack/heap execution, helper-returned aliases, rejected
local escapes, missing unsafe scopes, immutable-to-exclusive conversion and
release of a heap owner while a derived view remains live.

Native regression coverage includes scalar/floating/wide values, oversized
aggregates, packed heap versus descending stack layouts, overlapping and
disjoint ranges, helper-returned views, rejected local escapes and heap release,
and rejected invented reference provenance. A contiguous partial-ownership test
consumes one field, restores it while a sibling reference is retained, then
checks that a whole-aggregate view projects the very same sibling address.
The async emitter now uses this representation for decomposed reference-free
aggregates: one contiguous word buffer per owner, with compile-time leaf and
shell occupancy. Partial moves leave stale bytes inaccessible until restored;
they do not change a retained sibling's address. Whole and projected typed
views target only source-proved initialized ranges. Stack and heap cold/warm
regressions return 42 after suspension, restoration and address comparison.
PC-specialized cleanup exports only occupied leaves. Zero-length typed marker
fields preserve the original owner's structural Send/Sync constraints without
runtime payload words. Views retain their parameter capability past temporary
implementation anchors; result mutability does not erase alias protection.

At that milestone, reference-bearing aggregates and nondecomposed cells still
used their existing tagged representation. Their provenance migration, complete tag removal,
cloning audit and performance work remain open. This is incremental progress,
not a goal-completion claim.

Primitive source bindings now also use untagged word regions. Constructors
initialize primitive parameters, and generated parameter read/replace functions
keep their existing state and loan guards. Clearing a binding changes only
compile-time occupancy; dispatcher specialization determines which values are
available. Wide integers retain their two-word representation. A layout
regression eliminates six discriminator words (48 flat-frame bytes) across six
primitive bindings; this is a layout saving, not a measured compilation speedup.
An independently compiled, renamed generated program changes an unselected
buffer and verifies that a retained reference still selects the correct owner.

This conversion exposed an ordinary reference-holder reborrow issue. Loading a
reference through a checked reference-to-reference now lends that exact typed
holder's loan to a call, rather than conflicting with itself. Opaque lifetime
anchors do not grant that permission. Native regressions exercise repeated
mutable calls through direct and borrowed holders, and reject a mutable call
while a child immutable reference remains live. This rule is generic; it does
not recognize async-generated names or grant async-specific borrow exemptions.

Verification of the primitive conversion: 1,386 library tests pass with seven
existing ignored tests. All 49 generator-boundary, graph-production and generic
word-storage integration tests pass, as do all-target checking and whitespace
checks. Reference-bearing storage conversion remains open.

Primitive expression temporaries and frozen array-index cells now use the same
untagged representation as primitive bindings. Slot assignment follows the
deterministic slot sequence rather than a binding-only lookup. Tests assert
that primitive temporary cells have neither enum declarations nor transfer
helpers, and exercise stack/heap execution, repeated Pending, index selection,
clone hooks and independent ordinary generated-code checking. The typed-cell
fallback tests remain separate from production primitive storage selection.
All 88 emitter tests pass (one existing ignored), all 1,386 library tests pass
(seven existing ignored), and all 54 contiguous-storage, dependent-cancellation,
dynamic-array, generator-boundary and self-borrow integration tests pass.
All-target and whitespace checking pass. Whole aggregate value recipes and
reference-bearing storage still need migration; this is not complete tag removal.

Whole reference-free expression temporaries with concrete declared layouts now
use untagged word regions too. Stationary pattern inspection, guard preview and
clone access all obtain a typed payload view through the common accessor,
instead of assuming an enum wrapper around every value. Layout tests require
the exact payload width and absence of occupancy enums/transfer helpers. The
ordinary checker still checks the generated source; ownership and initialized
representation remain obligations of the checked lowering and specialized PC.

Generated child frames with deferred layouts remain on the typed path: planning
signatures cannot provide their physical widths. The deferred-layout check also
follows declared struct, enum and tuple contents. Whole undecomposed binding
recipes and reference-bearing aggregates remained open. This is not complete tag
removal and does not claim that pinning alone makes raw accesses safe.

The conversion exposed two generic native staging bugs. Nested aggregate block
results now dispatch observable clone hooks, rather than stripping `#clone` as
a transparent wrapper. Struct return register checks count payload words rather
than fields, so zero-sized typed markers consume no registers. Standalone native
regressions cover two- and seven-word clone staging and six zero-sized markers.
The full library suite passes 1,387 tests with seven existing ignored tests;
all-target and whitespace checking also pass.

All 69 contiguous-storage, generator-boundary, dependent-cancellation,
graph-production and word-storage integration tests pass. This includes cached
and independently compiled generated code, reference-bearing child frames that
remain typed, cancellation before and after suspension, and stack/heap layouts.

### Whole binding storage (2026-10-12)

Concrete reference-free whole bindings now use untagged word regions too.
Owned field, tuple, array and selected enum-payload writes address the exact
word range; they do not perform a fictitious typed ownership mutation through
an alias-only view. Selected writes retain the already evaluated address and
stage the right-hand side before acquiring writable storage. Immediate calls
and synchronous slices use the same payload accessor as other word-backed
owners. Cancellation copies initialized backing words, then exports occupied
values according to the specialized PC, including oversized arrays.

Pinned thin handles into supported reference-free frame owners use checked
address erasure. Movable poll-local aggregate handles still require a physical
Empty proof at every Pending boundary. The original source checker remains
the authority for aliasing and escape, and ordinary generated checking has no
async exemptions. A retained continuation protects its frame; retiring that
continuation does not remove the local's permanent prohibition on movement.
Explicit forget may end an otherwise inaccessible pinned frame in place.

Reference-bearing owners, deferred generated-child layouts and pinned
enum-payload anchor recipes retained their typed path at this milestone.
Their full provenance migration and complete tag removal remained open, as did
the analysis-performance audit. This milestone did not complete the async goal.

Verification: 1,387 library tests pass with seven existing ignored tests.
All 103 focused contiguous-storage, dependent-cancellation, dynamic-array,
generator-boundary, graph-production, self-borrow and word-storage cases pass.
The graph run passed 31 cases; its printing case produced the expected stdout
but failed an obsolete helper-name assertion. After replacing that assertion
with checks of the emitted operations, the printing case passed separately.
All-target checking, Rust formatting and whitespace checks also pass.

### Pinned enum payloads (2026-10-12)

Reference-free owners with pinned enum-payload borrows now use word storage.
Thin handles retain checked payload projections in their source anchors rather
than forcing the whole owner back onto the tagged path. Required active-variant
checks remain at address selection, before subsequent source operations.
Branch-selected handle reconstruction checks a candidate's active variants
before probing or materializing its payload. This adds no initialization flags.

Dynamic array address prototypes can measure the padded address of an inactive
sample payload without reading its value. Actual selections still check the
variant; prototypes only establish geometry. Native regressions cover both
variants, inactive-variant traps, nested shared and exclusive payload views,
overlapping-borrow rejection, and frozen array indices whose variables change
before suspension. The nested enum/array selection executes on both stack and
heap backing. Original-source checking and final ordinary generated checking
remain mandatory; the native checker has no async exemptions.

Reference-bearing owner provenance, deferred generated-child layouts, remaining
typed handle cells and analysis-performance work are still open. This is not a
goal-completion claim.

Verification of the payload migration: 1,389 library tests pass with seven
existing ignored tests, and all 104 focused async/word-storage integration tests
pass. All-target checking and whitespace checks pass. No source borrow rule or
ordinary generated-code validation was relaxed.

Owned parameter projections also retain explicit `#mut` metadata in typed IR
and the executable graph. Owner validation previously inspected only local
Bind/Commit actions, incorrectly rejecting exclusive projections from mutable
owned parameters. It now accepts the explicit parameter annotation, not all
parameters; graph validation rejects annotations naming nonparameter bindings.
Cold/warm native payload tests accept mutable parameters and reject immutable
ones. The follow-up passes 1,390 library tests with seven existing ignored tests,
all 43 cancellation, boundary and self-borrow integration tests, and all-target
checking. This does not change alias, escape or initialization permissions.

### Erased thin handle cells (2026-10-12)

Internal thin handles to reference-free values now store one physical pointer
word instead of an Empty/Full enum cell. Reads reconstruct the logical reference
from the same checked source anchors; writes erase the incoming temporary loan
before acquiring the destination storage. Constructors use captured pointer
values while retaining actual lifetime-bearing external captures separately.
Retirement changes dispatcher occupancy facts, not bytes or runtime tags.
Non-owning snapshots reconstruct the reference without consuming its cell.

Zero-length markers retain the physical raw pointer's structural Send/Sync
restrictions. A regression checks pointer width, anchors, absence of cell enums
and transfer helpers, ordinary generated-code validation and thread properties.
The native pending-tag oracle now includes a retained external capture, since
internal reference-free handles no longer have tags to inspect.

Handles into reference-bearing values retain typed storage and recovery helpers.
Their provenance migration, deferred generated-child layouts and the remaining
analysis-performance audit are still open. This is not complete tag removal or
a goal-completion claim.

Verification of thin-handle storage: 1,391 library tests pass with seven existing
ignored tests. All 104 focused contiguous-storage, dependent-cancellation,
dynamic-array, generator-boundary, graph-production, self-borrow and generic
word-storage integration tests pass. All-target checking, Rust formatting and
whitespace checks pass. Each converted handle removes one discriminator word;
this is a layout saving, not a measured compilation-time speedup.

### Borrowed initialization-state lookups (2026-10-12)

Initialization specialization now looks up incoming fact slices in block-local
identity tables. It copies an identity vector only when creating a new state,
not when a Pending retry or converging edge reuses one. Equal facts at different
source blocks remain different dispatcher states. Breadth-first numbering,
edge-local transfers, domain checks and state-budget errors are unchanged.
The tables allocate fixed metadata per source block, with key storage only for
discovered states; this trades that metadata for cheaper repeated lookups.

Three alternating before/after optimized standalone-module benchmark runs gave
median-of-run-medians of 24.404 to 19.827 microseconds for 32 initialization facts
(18.8% less time), and 1,300.265 to 911.020 microseconds for 4,096 facts (29.9%).
Repeating the three alternating runs with release-matched `-O`, one codegen
unit and fat LTO gave 39.804 to 28.426 microseconds (28.6% less time) and
3,130.100 to 1,795.136 microseconds (42.6%), respectively. Both binaries in each
comparison use the same flags; absolute results depend on optimization context.
Each run measures eight warmed samples of 200 solves on a 32-block cyclic graph
with retry edges and 95 exact states. These are synthetic solver measurements,
not whole-compilation speedups. The ignored
`initialization_specialization_retry_timing` test keeps the workload runnable;
it can also run through `cargo test --release --lib` with `--ignored --nocapture`.

The new regression checks duplicate edges, empty/wide domains, exact successors
and distinct-block identities at the state limit. Existing cyclic-graph parity,
correlated-history and edge-transfer regressions remain in place. Source and
ordinary generated-program validation are not skipped or cached by this change.
Reference-bearing storage, deferred child layouts and broader analysis cost
still require follow-up; this does not complete the async goal.

Verification: 1,392 library tests pass; seven pre-existing tests and the new
manual benchmark are ignored in the ordinary run. All 104 focused async and
word-storage integration tests pass. The manual benchmark also passes through
Cargo's release profile. All-target checking, formatting and whitespace checks
pass.

The contiguous clone audit exposed and corrected a physical-occupancy bug:
non-owning snapshots of linear word-backed leaves must not use the ordinary
transfer reader. They now leave the original occupancy unchanged while the
checked clone hook receives a temporary that is explicitly forgotten. A failing
occupancy-trace regression reproduced the old field-clear event. Cold/warm
native tests verify clone-hook results, the original sibling address, and export
of the still-owned original field when cancellation follows a clone and a
second Pending return. The emitter suite passes 87 tests (one existing ignored),
and all 18 contiguous-storage/dependent-cancellation tests pass.

Verification of this conversion: 1,384 library tests pass with seven existing
ignored tests, along with 76 focused async integration tests and 15 contiguous
storage/word-operation tests. Cold/warm native coverage includes stack, heap,
both branches of a selected whole-owner reference, rejected incomplete reads,
rejected exclusive overlaps, and an executed occupancy-oracle negative control.
All-target checking and whitespace checks pass.

Verification for this foundation: 1,383 library tests pass with seven existing
ignored tests; the focused async module run passes 243 tests with four existing
ignored tests. All 50 word-storage/documentation/slice/pin integration tests,
all-target checking and whitespace checks pass.

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
unused aggregate root cell. Trace-only rendering reuses the checked emitter's
immutable plans and restores all mutable rendering scratch, including on error.
It performs no additional source or native semantic checking; its cost is
reported as `generator.async.physical_occupancy` in detailed stage timings.

The reuse regression requires byte-identical ordinary output after a prior
occupancy pass. A bounded side-effect audit found no action/terminal mutation
outside the restored scratch. All 1,397 library tests, 34 graph-production
tests and the layout, cancellation, contiguous, dynamic-array, boundary and
self-borrow integrations passed. A parallel emitter executable launch failed
with `ETXTBSY`; its serial rerun passed.

A paired release benchmark used 21 alternating cold-cache checks per fixture,
after two discarded warmup pairs, with both compilers pinned to CPU 8 and no
concurrent test suites. Fresh source directories isolate caches; `--check
--timings` includes semantic validation and publication, not native linking.
Median occupancy times fell from 0.235 to 0.160 ms for composition (31.9%),
0.365 to 0.224 ms for self-reference (38.6%), and 0.571 to 0.267 ms for the
suspended reference guard (53.2%). Total medians were 31.370 to 31.272 ms,
58.335 to 57.907 ms, and 394.988 to 398.170 ms respectively. The guard total
worsened 0.8%; this is a local analysis improvement, not evidence of a
meaningful whole-compiler speedup.

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

The formerly ignored heap-owned nested-child acceptance test is now enabled.
Generic pin-owner analysis publishes the initializer's tag facts and variant
bounds at the new allocation identity. It validates reference provenance on
the consumed initializer rather than demanding origins for inactive payloads
in the address wrapper; transparent unsafe wrappers still check their children.
Inactive input-slot proofs also recognize an owning pointer, requiring a real
owned allocation identity rather than mistaking retained loans for alternate
addresses. No async-specific contract exemption is added.
Tag initialization also requires a fresh allocation identity. A loop may have
more than one live instance from one static allocation site; if an older
address or retained alias still uses that identity, analysis invalidates its
tag facts instead of replacing them with a new instance's tags. The freshness
gate checks direct loans and stored allocation/parameter contents and has an
independent regression test. This is a compile-time conservative check, not
an added runtime flag.

The native heap test allocates first, constructs into a named local, then
initializes the pin owner, polls, cancels its nested child in place, cancels
again and releases the allocation. It checks identical cold/warm assembly and
inspects the actual generated cleanup code. A negative variant omitting release
of the Pending handle fails at allocation release with a source-spanned borrow
error. Generic, non-async tests cover initially Empty and Full reference enums,
borrowing and forwarding their owners, Empty-to-Full writes, and rejection of
source mutation while a stored reference remains live. Physical tag updates
invalidate old facts rather than retaining a fictitious Empty proof.

Construction deliberately follows the existing backend's named-local
large-aggregate call convention. Directly nesting a large frame factory call
inside `#pin-own-of` reaches the existing E5000 code-generation restriction;
this change does not claim to implement arbitrary large aggregate expressions.
An opaque syscall conservatively invalidates preexisting tag facts, so the
test creates the initializer after allocation rather than before that syscall.

The change exposed a backend bug in scalar matching: x86-64 memory comparisons
sign-extend their 32-bit immediate, so a direct comparison against `u32::MAX`
missed the completed PC. Scalar pattern emission now materializes constants
outside the signed immediate range. Native tests cover matching and fallthrough
for u32, u64, i64 and multiword u128 constants.

This removes the per-child occupancy-selection branches, not every cell guard.
Boundary Empty assertions, reference-bearing consuming matches and public
cleanup optional wrappers remain; no claim is made that the payload has already
become untagged or that pinning alone permits an unchecked access.

Historical verification of the PC-selected cancellation change: 1,382 library tests pass
with seven existing ignored tests; all 236 async integration cases pass with
four test threads. All 65 checked-expansion, graph-production, dynamic-array,
restoration, heap-contents, generated-boundary, rejection, self-borrow-cleanup
and unchecked-projection integration cases pass. Eleven dependent-cancellation
tests passed; the new nested heap acceptance case was explicitly ignored at
that point and is enabled by the follow-up above. All eleven jump-table/scalar
integration tests,
all-target checking and whitespace checks pass. No temporary syscall probes
or diagnostic artifact-retention code remains.

Verification of the allocation-backed follow-up: all 1,383 library tests pass
with seven existing ignored tests; all 236 async cases pass with four test
threads. All 68 focused cancellation, checked-expansion, heap, generated-boundary,
adversarial, pin-owner, pin-projection and unchecked-projection integration cases
pass. The nested heap acceptance case is no longer ignored. All-target checking
and whitespace checks pass. This resolves that call-contract gap, not the
contiguous untagged frame representation still required below.

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
pinned async body with suspension before restoration now passes for this
reference-free owner, on stack and heap storage. Reference-bearing owners
remain a representation limitation, not an unsupported ordinary source pattern.

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
not only in a temporary audit directory. It now returns 42, preserving
the same sibling address across Pending and field restoration, in
`tests/async_contiguous_storage.rs`. That passing reference-free regression
does not complete the broader storage and provenance goal.

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

Linear aggregate previews now project the retained scrutinee rather than
initializing a second owning payload cell. `async_preview_alias` tracks preview
activation and retirement through checked graph edges. A join with inconsistent
alias lifetimes is rejected. Guard reads and borrows address the actual payload;
commit retires the alias before transferring the owner. Rejection merely ends
the preview. These are compile-time facts, not runtime initialization flags.
Projection shapes are checked before emission, with binding source spans on
failure. Physical occupancy tracing restores alias state along with its other
rendering scratch.

Cold/warm and independent ordinary-code native tests cover linear shared-reference
payload acceptance, rejection, cancellation and repeated cleanup, plus a whole
payload borrow created before suspension and read afterwards. Mutating the
external lender while the guard is suspended remains rejected at the original
`#set` token without cache publication. Movable frames inspect the retained
payload directly during poll. An occupancy regression requires that preview
does not initialize the future arm's owning cell, commit does initialize it,
and tracing leaves byte-identical generated output.

The exclusive-reference aggregate helper-lending completion gate now passes
and is no longer ignored. Its projection helper had stored `#ref-ptr` in a raw
pointer local, while ordinary loan analysis only recognizes the exact named
owner round trip directly. Emitting `(#ptr-borrow projected (#ref-ptr projected))`
preserves actual nested reference identity instead of reducing it to a lifetime
anchor. This changes emission, not the checker identity rule. A plain ordinary
Lim regression checks the nested exclusive read and rejects mutation of its
lender. Movable preview projections now pass the retained scrutinee capability
to that helper instead of borrowing an empty future arm-binding cell. Both
whole-payload and direct-field inspection pass cold/warm and independent native
verification. Direct non-Copy reference-field loads still need lending storage
and remain unfinished; no native borrowing rule is waived. Payload-binding
alternative patterns are forbidden by the
ordinary source language and retain negative publication/span coverage;
supporting them is not an async lowering obligation.

Verification after the exact identity fix: 1,399 library tests pass (eight
existing ignored tests), and all forty graph-production tests pass with none
ignored. The
contiguous, dependent-cancellation, dynamic-array, boundary and self-borrow
integration suites pass, along with the standalone occupancy parity test,
all-target checking and formatting/whitespace checks. A bounded alias-lifetime
audit found no leaked activation or ownership-cell redirection in nested
preview, commit, rejection or probe paths. Reference-bearing contiguous storage
and direct nonmoving exclusive field loads remain unfinished.

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

### Heap payload provenance and exclusive transfer permissions

Pinned payload getters now project the evaluated receiver's address rather than
requiring a lexical place. This covers a computed `#pin-own-borrow-mut` receiver
and all four checked/unchecked shared/exclusive payload getters. Event-sensitive
analysis uses the receiver's recorded evaluation snapshot. Selected retained
reference slots keep their real external pointees; payload offsets belong to
the container address, not to those pointees. Unrelated sibling slots are not
carried into the selected payload.

The previously ignored ordinary heap partial-restoration test is enabled. Like
its stack counterpart, it consumes and restores a linear sibling while retaining
a reference-bearing field's storage address, then compares that address and
reads the original caller reference. Cold and warm native runs return 42 with
identical assembly. Both provenance solvers have direct origin-identity tests.
This establishes the ordinary heap foundation, not contiguous async storage.

Shared views now clamp the permissions of loaded allocation contents. Transfer
validation also requires exclusive permission for directly transferred mutable
reference slots; a matching lifetime or storage path alone is insufficient.
Slots behind another reference boundary describe stored contents, not permission
granted by the outer handle. Lifetime-only anchors receive no new exception.
A regression rejects lending an exclusive nested reference through a shared
heap payload and accepts the equivalent exclusive payload projection.

This check exposed stdin polling through a shared task holder. The library poll
API now requires `(#ref-mut AsyncByteRead1)`, and all four affected examples use
explicit mutable task locals and mutable polling borrows. Read-only generated
array/address probes likewise no longer require the original parameter's
exclusive handle: shared reborrows and shared helper signatures express their
actual geometry-only access. Writable projection helpers remain exclusive.

Pinned external captures retain their pinned type in projection, bounds and
factory recipes. Nested slice probes take shared reborrows even when their
source descriptor is exclusive. Lexical payload projections retain their
existing place-based reborrow contract; computed heap receivers use evaluated
address provenance rather than inventing a lexical holder.

Verification: all 1,408 library tests pass (eight existing ignored tests), as do
all-target checking, formatting and whitespace checks. The broad async run
passes 234 tests with two explicitly filtered failures: loop-body restoration
through borrowed places and deep-field borrow permissions. Both failures were
reproduced unchanged in an isolated copy of committed HEAD, so they remain
separate follow-up work rather than being hidden by this milestone. A frame
restoration test also fails in that baseline because it still searches for the
old tagged Owner cell after the word-storage conversion.

All 26 self-borrow tests and the generator-boundary, heap-contents, nested-field,
reference-release, contiguous-storage, dependent-cancellation, graph-production,
checked-expansion, native I/O, syscall coverage, timer, waker, raw-reference,
heap-reference and unchecked-payload suites pass. All seventeen word-storage
tests pass serially; a parallel launch encountered `ETXTBSY`. A heavily parallel
async run also hit launch races and bounded harness timeouts; the four-thread
234-test rerun above passed. This is not a claim that the whole test suite or
async goal is complete.

The reference-bearing contiguous async completion gate below remains open.

### Preserve exclusive parentage through exact pointer round trips

An exact pointer round trip from an exclusive reference now records that named
handle as its reborrow parent in both ordinary and event-sensitive provenance.
Previously, an identity view could recover the correct address but lose the
parent relationship, so projecting through that view conflicted with its own
parent's still-live exclusive loan. This update is restricted to the outer
reference slot and the direct `(#ref-ptr same-owner)` form. Unrelated pointers
remain lifetime-only anchors, and nested stored loans acquire no fabricated
access permission.

The ordinary fixture `partial_reference_typed_payload.lim` preserves a reference
to a reference-bearing field while a sibling Token is extracted and restored
through a narrow pinned reference. It then creates a whole-owner view from the
existing exclusive capability, compares the field address and reads the real
caller reference. It returns 42 natively on stack storage, cold and warm, with
no per-field tag. Caller mutation while the contained reference is live and
sibling mutation while the whole shared view is live remain rejected.

All four exact pointer-borrow forms are tested against unrelated pointers in
both provenance solvers. The library suite passes 1,406 tests with eight existing
ignored tests, alongside 45 graph-production, fourteen dependent-cancellation
and 26 self-borrow integrations. This establishes a generic typed-storage
foundation, not a migrated async representation. The existing async contiguous
reference-owner gate remains ignored. The heap version additionally exposes an
unresolved referent call-input failure when restoring the partially moved field;
its native completion gate is explicitly ignored rather than counted as passing.

### Remove the discriminator branch from owned reference transfers

Owned transfers from typed reference-bearing cells now retain the pre-move
whole-cell snapshot, publish Empty at the original frame address, and extract
the Full payload through an explicitly unsafe local projection. Source ownership
and physical PC occupancy prove that snapshot Full. The transfer no longer
matches Empty/Full at runtime. This preserves typed provenance; it does not yet
remove the cell's physical tag or authorize numeric words to invent references.

A direct payload extraction from the original frame cell was tested and rejected:
later cleanup reads could not establish the required referent contents. The
accepted implementation preserves the entire pre-move snapshot rather than
bypassing that ordinary checker failure. An emission regression asserts branch
removal, Empty publication order and compile-time occupancy retirement, then
checks the generated program normally. A separate non-async unchecked-payload
transfer regression retains a returned exclusive loan after clearing its old
holder and still rejects caller mutation while that loan is live.

The library run passes 1,403 tests with eight existing ignored tests; the newly
added emission regression also passes independently. This is branch removal,
not a measured compilation-time speedup or complete reference-storage migration.

### Outstanding contiguous reference-bearing owner gate

`tests/fixtures/async_partial_reference_whole_borrow.lim` isolates a remaining
representation failure. `Owner.kept` contains a real caller reference, and the
program retains a reference to that field's storage. It moves out the sibling
linear `Token`, suspends, restores the sibling, then takes a whole-owner view.
The view must expose the exact same `kept` field address and preserve its nested
caller loan. Native completion should return 42, cold and warm, on stack and heap.

The current emitter rejects the whole borrow with `whole aggregate borrowing
requires contiguous owning storage`. The rejection regression passes twice and
underlines the original `(#borrow owner)` expression. The positive native test is
explicitly ignored with the missing implementation named; it is a completion
gate, not passing evidence. Existing reference-free contiguous tests still pass.
Replacing this owner with independent field buffers, rebuilding a temporary
whole value, or deriving nested reference origins from numeric words would not
meet the required address/provenance invariant. This must be resolved before
claiming completion of the storage migration or the async goal.

### Direct scalar reads through exclusive reference fields

Checked nonmoving loads of exclusive reference fields can now feed one immediate,
reference-free Copy read without materializing a duplicate reference. The emitted
ordinary reader projects through the actual evaluated parent capability. It
supports shared or exclusive parent references, pinned exclusive leaves, and
nested struct/tuple pointee projections. Deferred physical-use accounting keeps
the parent alive until the scalar read, not merely until the elided field load.

The certificate requires original-source lending permission, a pure projection,
one scalar consumer, no escaping result and no intervening effect or block
boundary. It does not permit reference-bearing results, arbitrary consumers or
references carried across suspension. Those cases remain fail-closed. Both
original and independently emitted ordinary programs are checked; no native
async-specific borrow exemption is introduced.

Sixteen lending-certificate tests pass, including parent-retirement timing,
effect barriers, block boundaries, missing source permissions and multiple
consumers. Native cold/warm tests cover exclusive and
pinned-exclusive leaves, nested struct/tuple projections, repeated reads through
an exclusive parent before and after Pending, and caller unique-loan rejection.
The library suite passes 1,401 tests with eight existing ignored tests. The
contiguous, dependent-cancellation, dynamic-array, boundary and self-borrow
integration suites pass (6, 14, 6, 5 and 26 tests respectively), as do all-target
checking and formatting. Reference-bearing storage migration remains unfinished.

All 45 graph-production tests pass. The three checked-expansion tests also pass:
frame fields cannot be read or overwritten, and a linear frame cannot be cloned,
by callers outside the generated implementation module. These checks cover both
direct expansion and independently imported generated files, cold and warm.
The privacy regression now asserts the current word-storage implementation
rather than requiring an obsolete typed payload helper. `#opaque` is the generic
module boundary protecting these representation invariants; it is not an
async-specific native checking exception.

### Concrete generated child layouts and stationary cancellation

Generated children are now emitted in dependency order before their parent
storage is classified. The planner installs actual struct, enum and alias
declarations from the emitted Lim source without renumbering original source
identities or duplicating declarations in the final program. Cached child
sources supply the same layout facts. Owning pinned descriptors also require
their child layout: fixed descriptor width does not imply that the payload
contains no retained references. Public output remains in invocation order.

Reference-free nested frames can consequently share untagged parent storage.
Pinned children cancel at their stationary address even when they retain no
parent borrow. Their cleanup slot is exported empty after cancellation, so a
subsequent cleanup cannot cancel the child again or move stale child bytes.
By-value cancellation handlers for these children are rejected before cache
publication. Stack and heap cold/warm regressions observe exactly one cancel.
Zero-length structural markers no longer require the element's physical layout.

Verification passed 1,396 library tests (eight ignored), five native-example
tests, fourteen dependent-cancellation tests, the new forward-layout cold/warm
integration, and the contiguous, dynamic-array, boundary, graph-production and
self-borrow suites. All seventeen generic word-storage tests passed serially;
one parallel executable launch had `ETXTBSY`, not a semantic failure. This
milestone does not complete reference-bearing aggregate storage migration.

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

### Actual loan provenance in typed word storage

Typed word writes now record actual contained-reference origins at their physical
word offsets. Typed reads and views recover those recorded origins rather than
inventing references from a numeric buffer or a layout marker. Scalar overwrites
retire the previous metadata. Reference-bearing writes require resolved storage
coordinates, and the ordinary scope-escape check prevents a writer from leaving
a short-lived reference in caller memory. Writer helpers export these effects;
their indexed destinations are normalized against the caller's selected slice.
The semantic cache schema is version four, invalidating older store summaries.
These are compile-time loan facts, not runtime occupancy tags or async exemptions.

The previously ignored shared-reference aggregate restoration test is enabled.
Its stack and heap variants pass cold and warm compilation and native execution:
a retained field keeps both its address and its real caller loan while a linear
sibling is moved and restored. An incomplete whole-owner borrow is rejected at
the original source expression.

The cleanup migration remains open for non-Copy reference-bearing leaves. A raw
numeric-array snapshot does not currently transfer concealed loan metadata into
the cleanup state's typed reads. Those leaves retain their typed representation;
this is an incremental migration boundary, not completion of the async goal.

A direct-extraction experiment also failed the ordinary cleanup boundary check
and was reverted. Eliminating the numeric snapshot alone is insufficient: a
separately checked function taking a numeric-backed frame has no declared
contained-reference slots for those words. The next mechanism must express
required word-slot loan inputs and validate them against actual caller writes,
including exclusive permissions. It must not seed invented loans merely because
a callee requests a reference-bearing interpretation. A new native regression
confirms that owned nested struct/tuple/array values preserve both reference
origins within one function; mutation of either pointee remains rejected.

Final verification of the committed migration passes all 236 async integration
tests with no filters or ignores, 1,411 library tests (eight existing ignored),
26 word-storage tests, 15 contiguous-storage tests, 11 semantic-cache tests,
three UI tests, three checked-expansion tests, fourteen dependent-cancellation
tests and 26 self-borrow tests. All-target checking and formatting pass. The
full async rerun used a stable compiler binary: concurrently rebuilding the CLI
midway through an earlier run invalidated that run, because these tests execute
the on-disk compiler. That contaminated run is not counted as verification.

### Inferred loan inputs for borrowed word readers

Ordinary functions can now read reference-bearing values from borrowed numeric
word memory when every caller supplies the required write-derived loan at the
selected offset. The inference records required primary capability flags and
propagates the requirements through forwarding functions, including functions
that return only scalars. Native call checking validates all reaching primary
loans, not just one favorable branch. Shared loans cannot satisfy exclusive
requirements. Thread-spawn operations inherit their worker's input requirements.
Both inference modes serialize these requirements in semantic cache schema v5;
cache hits still run the native validation gates.

These inferred slots are abstract function inputs, not initialized reference
values inferred from numeric bits. Requirements are added only for lineage
missing from the actual-content analysis: real writes in the body need no new
entry assumption, and declared optional typed payloads keep their existing
conditional contracts. The earlier uncalled numeric-reader negative now calls
the reader on untracked numeric bytes, preserving the actual safety boundary
while permitting a helper declaration with caller-validated requirements.

The full cleanup migration still remains open. Repeating direct cleanup
extraction now reaches a by-value backing transfer that lacks an inferred loan
input. Numeric-backed values moved from a function parameter into a local must
preserve the relationship between their concealed slots and that parameter's
entry requirements. The exploratory emitter change was reverted; owned
reference-bearing leaves still retain typed storage. Borrowed reader contracts
are a generic prerequisite, not a claim that by-value storage or state-specific
cleanup has been completed.

Verification passes all 236 async integration tests, 1,411 library tests (eight
 existing ignored), 30 word-storage tests, twelve semantic-cache tests, fifteen
contiguous-storage tests, fourteen dependent-cancellation tests, 26 self-borrow
tests and three UI tests. All-target checking and formatting pass. The new word
tests cover forwarding, scalar-return readers, exclusive permission, mixed
shared/exclusive branch inputs and rejection of untracked numeric input. Imported
reader tests cover identical cold/warm output and identical invalid-input errors.

### Caller-validated loans in moved numeric backing

By-value numeric arrays, including arrays in structs and tuples, now infer
concealed-slot input requirements. The initial abstract pass uses a single
symbolic candidate per numeric array; an actual typed read specializes the
required offset. Contents-aware and native validation do not treat candidates
as initialized references: callers must supply real write-derived loans with
the required capabilities. A billion-element analysis regression verifies that
one selected read does not enumerate the array's elements.

Moving a parameter into a local, or extracting its array field into a differently
named local, preserves that input relationship. Exclusive typed reads require
exclusive input, and writes through an exact stored mutable handle use its own
capability without bypassing a live child reborrow or another conflicting loan.
Spawned workers retain concealed input loans in the task until successful join;
join errors retain them in the retry task. Native regressions reject caller
mutation while the worker is running and permit it after join.

The semantic cache uses schema v6 to invalidate summaries inferred under the
older entry model. Imported by-value readers are tested cold and warm, including
identical rejection after a scalar overwrite retires the required reference
slot. These contracts are not a general raw-byte ownership transport mechanism.
Arbitrary unsafe representations still require their author's validity and
ownership proof.

### Direct cleanup of contiguous reference-bearing partial owners

Partially moved aggregate owners now use contiguous word regions even when a
leaf contains an exclusive or otherwise non-Copy reference. The earlier typed
leaf fallback is removed for these layouts. Ordinary typed reads request a
mutable slice when the value contains an exclusive capability, while shared
reads retain their shared permissions.

Cleanup extracts initialized typed values directly from the original pinned
frame's word regions, selected by the saved program counter. It no longer copies
raw numeric buffers into a temporary cleanup struct and then tries to recover
concealed reference loans there. Non-word cells still use their existing typed
transfer. This is not yet removal of every frame cell tag, nor completion of
the guard, selected-anchor or whole async goal.

Verification passes all 236 async integration tests, 1,412 library tests (eight
existing ignored), 33 word-storage tests, sixteen contiguous-storage tests,
thirteen semantic-cache tests, fourteen dependent-cancellation tests, 26
self-borrow tests, six kernel-thread tests (two existing ignored), and three UI
tests. The added exclusive-reference partial-owner test runs cold and warm and
checks the retained field address after sibling restoration. The previously
failing aggregate-clone cleanup regression passes without a raw numeric snapshot.
Formatting and diff checks pass; the compiler binary remained stable throughout
the full async integration run.

### Projected lending and writes during argument evaluation

Contiguous field addresses are pinned references to the field's storage, not the
reference value stored in that field. Projected lending leases and evaluated
exclusive snapshots now dereference the word view before using the stored handle.
A native cold/warm partial-owner test moves and restores a linear sibling, then
captures an exclusive field argument before a later argument suspends. The resumed
callee mutates the pointee and returns 42.

Its adversarial variant exposed an ordinary checking gap: simultaneous argument
alias checks did not reject a direct reference write inside a later operand after
an earlier operand captured the same loan. The ordinary checker now compares
those writes against the evaluated earlier reference inputs. It indexes reachable
write events once per body, traverses typed operand structure rather than source
text, distinguishes symbolic parameter slots and retains diagnostic source spans.
Ordinary controls accept a disjoint field and skip a write after an unconditional
unreachable instruction. This closes the direct deref-set/pin-write case, not a
claim of complete operand-effect checking through every possible callee.

A broader whole-holder word-storage experiment remains uncommitted and was
removed. It exposed missing contained-slot provenance and self-loan projection
contracts for some stationary reference-bearing owners and guards. Partially
moved owners keep the committed contiguous representation; whole reference
holders outside those layouts keep their checked typed representation. The
experiment's interrupted full async run is not verification evidence.

Final verification passes all 236 async integration tests, 1,413 library tests
(eight existing ignored), seventeen contiguous-storage tests, fourteen dependent
cancellation tests, 26 self-borrow tests, thirteen semantic-cache tests, 33
word-storage tests and three UI tests. The UI case checks exact underline width
and alignment for the offending reference write. All-target checking, formatting
and diff checks pass. Two word-storage launches in an additional parallel run
hit Linux ETXTBSY; the unchanged entire word-storage suite passes serially.

### Nested word-view addresses and retained pointees

Address projection now distinguishes an inline field address from reference
contents carried alongside that address for local and parameter roots, not only
heap allocations. Selecting a nested field advances the address's physical path;
the selected field's retained external pointees keep their own paths. Neighboring
field contents are discarded. Borrowing the projected container also cannot
upgrade a stored ordinary reference into a pinned reference or increase its
mutability.

A native nested-struct word-view regression reads 42 through two separately
borrowed field addresses. Its negative controls reject mutation of the retained
pointee, destruction of backing words before loading the reference, reference
recovery from untracked numeric bytes, and a pinned type substituted for the
stored ordinary reference. An imported helper performs the nested projections
and returns the contained reference; cold and warm semantic-cache compilations
produce identical assembly and reject the same pointee mutation. Semantic-cache
version seven invalidates summaries built with the earlier address rule.

Re-enabling whole reference-bearing holder conversion exposed further issues:
returning a projected holder address from a helper can lose contained-slot
metadata, while an attempted symbolic-content expansion duplicates return
summaries and can attach aggregate field paths beyond an external scalar
reference. Treating that metadata as additional pin-read/write destinations also
confuses move/restore tracking. The broad conversion and speculative summary
changes were removed; these failures remain work, not supported cases or
completion of the async goal. The fix above does not invent initialized
references from type shape or weaken the ordinary self-loan validator.
