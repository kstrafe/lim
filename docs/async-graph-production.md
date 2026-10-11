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
operations in a movable poll. Their selected pointers use the existing
frame-anchor representation, but movement is authorized only when every
reachable Pending boundary proves all internal reference cells and dependent
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
existing loop-mutation regression now uses graph lowering for its scalar and
struct-reference variants. Scoped local borrows also use this boundary proof:
ending the scope before suspension permits movement, but retaining the scope
across suspension still requires a pinned frame. The retained fat-slice variant
and other default-switch requirements remain open. Legacy lowering is still
the default.

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
