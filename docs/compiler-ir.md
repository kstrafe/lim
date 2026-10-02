# Typed compiler representation

This is an incremental internal migration, not a language or syntax change.
Lim still requires explicit source types and performs the existing type,
linearity, borrow, and unsafe checks before returning a `CheckedProgram`.

## Original-source async control flow

`async_cfg.rs` builds a graph before nested-task rewriting. Nodes borrow exact
`SpannedExpr` source children rather than cloning or reparsing function bodies.
Local bindings have graph-local IDs and declaration contracts; pattern types
come from explicit tuple/array/struct/enum layouts. Unknown contracts remain
unknown until ordinary type validation, not inferred from literal values.

Control edges distinguish branch selection, Ready, Pending and resolved loop
transfers. Pending retries only the await poll node, never child construction.
Match guards have separate pattern preview and commit operations, with scope
exits on rejected guards. Break values travel on their selected incoming join
edge, rather than becoming uses of every alternative. Continue in a `#for`
targets its step; continue in a `#while` targets its condition. Transfers to
outer labels explicitly exit the intervening scopes. `#for-range` preserves
ordinary desugaring: start runs once and end runs at every condition check.

Named function operands and keyed struct fields follow declaration order,
not written order or hash-map iteration order. Parameter order is part of the
async environment cache identity, including external function declarations.

Production uses the graph to reject invalid control transfers at their exact
original keyword/label spans before rewriting. Its backward data-use analysis
tracks bindings and computed operand temporaries separately. In-scope storage
candidates at suspension also retain unread locals: data-use liveness is not
permission to discard a linear value on cancellation.

This graph does **not yet emit frames** or calculate suspended ownership/loan
state. The legacy lowering still emits inspectable ordinary Lim declarations;
the normal typed checkers validate those generated functions. General graph
emission and delayed initialization of stable frame-owned storage remain open.

### Suspension storage facts

`async_storage.rs` queries the ordinary typed-flow ownership and loan solvers.
It separates future data reads, explicit linear cleanup obligations, address
dependencies and lifetime-only dependencies. Each linear leaf is Empty, Full
or Conditional; a partly consumed aggregate is not a loadable whole value.
Snapshots use resolved binding/place identities, including fields whose names
contain dots, rather than parsing names into paths.

`Declarations::suspension_storage_facts` collects the ordinary contents-aware
callee staging solution for selected bodies. Its graph, provenance and
consumption facts belong together. Callee consumption, forwarded initializer
restoration, selected result outcomes and cleared reference contents affect
storage retention. A nonreturning callee cuts off following events. Unresolved
effects propagate to continuations and cannot establish initialized storage;
opaque checked-reference contracts fail staging instead of manufacturing facts.

Loan retention reuses production NLL plus fresh unread-holder retention.
Releasing one reference field retires its loan, not its sibling's loan. A
lifetime-only raw-pointer anchor retains lifetime without claiming the pointer
addresses the anchor. Call reborrow permission is not a dependency on a
temporary parent handle's storage.

The existing async capture probe now retains linear cleanup requirements even
when a resume parameter has no subsequent data read. This cheap preliminary
mode is explicitly entry-only: without callee staging it cannot supply snapshots
at later events. The source suspension graph still needs mapping to checked
typed bodies and computed temporary storage before general frame emission can
use these facts. Staging snapshots are not a successful `CheckedProgram`
boundary and cannot waive ordinary owned-exit, borrowing or unsafe validation.

## Production ownership boundary

Typed flow now decides owned-value validity without a syntax-only rejection
fallback. The old linear checker is consulted only after typed flow has found
an error, to preserve established diagnostic wording and source labels. It
cannot reject a program that passed typed ownership validation.

Explicit `#drop` and `#forget` invalidate reference-bearing handles even when
their types need no linear cleanup. This records consumption of the handle's
slot, not destruction of its pointee. Independent shared-reference copies stay
usable, and releasing a Copy scalar does not create a move. Possible releases
join across reachable branches, while each newly bound loop-local handle has
its own initialized state. Direct typed regressions check the offending access
and prior-release spans as well as whole and projected aggregate releases.

Exclusive reference handles and aggregates containing them are move-only even
when they have no mandatory exit-cleanup obligation. Typed consumption records
their owned storage slots at bindings, aggregate construction, assignments,
patterns and returns; it never substitutes the pointee for a moved handle.
Direct reference arguments use call-duration reborrows, while owned aggregates
passed by value transfer their handles. Repeated reads, writes and helper calls
through a still-owned reference remain valid.

For a known owned field, tuple slot, array index or enum payload, extraction
transfers only that slot. Live-loan validation ignores the consumed source slot
but retains the destination's origin and the container's other loans. The
retired syntax-checker bridge used checked slot paths rather than inventing
referent projections from field names, and detaches the source loan without
ending its transferred borrow. Shared-reference copies retain independent loan
counts. Tests distinguish handle use-after-move from returning a reference to
a consumed pointee; the latter audit uses explicit forwarding calls to keep
source handles available while retaining a reference snapshot.

Typed call validation also checks known child reborrows against reference
arguments. Reading a parent pointer as an argument grants the callee referent
access; it must not bypass a live child retained through aggregate moves or
referent restoration. The argument's own owned slot and its reborrow ancestors
supply permission for calls through the child. Borrowed pointee contents are
not extra references lent by the argument, and separate pointer slots in one
parameter keep distinct symbolic referent identities. Call-site origins map
those slots back to caller places. Shared result traversal covers conditional,
matched, block and labeled/unlabeled loop arguments without interpreting field
names as referent projections. Independent typed regressions verify ordinary
and pinned parent rejection, cleanup, child calls and restored holder loans;
a UI fixture checks the offending argument and original child-borrow spans.

Reference-return summaries also retain the caller's immediate exclusive
reference handle as the reborrow parent. This covers returned field references
and references retained inside returned aggregates, including forwarded calls.
The parent is selected from the argument's result-producing bindings, not from
references merely stored in its borrowed pointee. Shared Copy arguments and
loaded pointer slots keep their existing provenance.

Call reborrows restrict access to a retained referent, not destruction of a
temporary parent handle. The origin records this distinction separately from
ordinary handle-dependent reborrows: releasing the handle does not destroy its
pointee or retire a live returned loan. This matters when generated pinned
poll functions release temporary projection handles before restoring the frame
state. Referent consumption and scope escape remain independently checked.
Labeled value-loops resolve to the inner loop's checked break-result identity
for both cached and event-specific loan queries; erasing the label without
resolving its result previously lost returned-reference origins.

Production now checks borrowing with typed flow and borrowed-storage contracts
alone. The lexical borrow model is compiled only for differential regression
tests; it cannot reject a program accepted by the typed checker. The returned
reborrow matrix requires production acceptance after cleanup for direct,
block and conditional arguments, including ordinary/pinned, shared/exclusive
and aggregate results. Dead pattern-produced copies still use ordinary NLL.

Fresh reference-bearing bindings retain their loans until their first owned
use, explicit release or scope exit, even if the value is never read. Forward
may-state joins this retention across branches; ordinary backward liveness
then governs loans after use. An address-only borrow or a Copy load through a
pin does not retire the original holder. Derived borrows and direct unpinned
call access can retire otherwise dead parent/backing holders; consumption and
retained destination loans are checked independently.

Aggregate construction also checks simultaneous fresh loans before any local
holds its result. Path alternatives preserve exclusive branch/variant choices.
Symbol operands use their evaluated snapshots, shared once per function, not
the enclosing constructor's later binding state. Reassigning a reference in a
later operand cannot erase a loan already copied into an earlier operand.
Symbolic parameter slots retain distinct referent places during this check.
Mutable slice metadata reads also respect live element reborrow permissions.
Scoped mutable access permission does not authorize an overlapping access
through a suspended parent reference. Diagnostics select source access order
rather than reverse CFG allocation order, and display the resolved offending
projection, not a dynamically indexed held loan. Dots in identifiers remain
ordinary name characters, not path syntax.

This is not proof of arbitrary-body async support or delayed pinned-owner
initialization. Several sections below document earlier staging milestones;
their descriptions of production syntax borrowing are historical.

Borrowed-storage contracts are now prepared before production live-loan,
scope-escape, returned-reference and argument-alias checks. Their contents-aware
loan solution retains references installed by callees and uses result-conditioned
clearing for Ready/cancellation paths. Preparing contracts after these checks
previously left them using returned-reference-only summaries and accepting
mutation of a callee-stored referent. Contract errors are still reported at
their existing ownership diagnostic boundary. The naive may-store-only solver
remains an audit tool, not the production loan solution: its unions alone
cannot prove that a Ready result released a pinned self-reference.

## Why retain an IR?

An intermediate representation is the compiler's checked model of the program,
not a runtime layer or an external backend dependency. The original syntax says
what was written; the checked representation also records which declaration a
name refers to, the exact operand types, and the control flow. Keeping those
answers avoids independently rediscovering them during native emission.

For future ordinary-function async lowering, suspension must preserve every
live value and outstanding loan. An explicit typed control-flow representation
provides a common input for that analysis and the generated state machine.
Frozen syntax collections do not require it, and manually declared task states
can already use the existing checker. It is a foundation for richer lowering,
not a prerequisite imposed on every generator.

### Earlier borrowed-storage staging milestones

The following records the experiments leading to the production boundary
above. Its staging descriptions are historical, not the current activation
status of borrowed-storage entry contracts or contents-aware live-loan checks.

Typed consumption analysis has a referent-resolved staging mode exercised by
tests. Independently, production ownership validation checks permission for
consuming linear referents: only resolved mutable, unpinned, non-anchor loans
authorize safe moves or explicit releases. This shares the ordinary move-flow
facts and computes loan origins only when an indirect consumption needs them.
Referent restoration, call effects, and escaping initialization are still
separate unfinished obligations. The referent-resolved staging mode is used by
tests. Raw-pointer borrow origins carry a lifetime-only
marker: their anchor is not a physical pointee identity. Such origins cannot
prove referent consumption or restoration in staging. Return summaries
retain this marker, and call transfer combines it with the incoming origin's
marker so forwarding functions cannot erase it. The staging mode is exercised by
direct tests, not yet used as a production validation boundary. Return
summaries also retain the referent's projection separately from the input and
output reference-storage slots. Call transfer appends that projection to the
argument's referent, preserving field identity through forwarding calls.
Ordinary reborrows follow selected reference-storage slots through local
aliases, retaining lifetime-only provenance and original parameter slots.
Taking an aggregate's address does not inherit every reference field's
provenance. Tests distinguish safe and raw-pointer fields in the same holder.
It follows
stored reference origins to stable loan roots so losing an alias does not
erase a move from its referent. Original parameter storage-slot metadata
distinguishes borrowed targets reached through different fields of one
aggregate parameter. A known-target write clears the corresponding move
facts. Multiple possible targets produce may-consumption facts, not definite
proofs; an ambiguous write does not erase every possible moved referent.
Missing provenance is recorded as an unresolved access, including nested
reference-field projections. It cannot create a definite-consumption proof or
clear possible moves. An unresolved write also invalidates definite facts,
since it may have restored any one of their targets. Reachable unresolved
events appear in the consumption dump; unreachable events do not.

At that stage, ordinary production mode kept its existing identities without
the extra referent tables. Promotion required access permissions, unresolved
provenance handling, call effects, referent initialization checks and precise
diagnostics. Staging facts alone did not establish those properties; see the
production boundary above for the checks now activated.

## Implemented: resolved declarations

`CheckedProgram` now retains the declaration tables produced by validation.
The native backend consumes their resolved struct fields, enum payloads,
global types, and ordinary function signatures instead of rebuilding those
tables from syntax. Generated Lim functions follow the same path. Source
syntax rejects generic function declarations and angle-bracket calls; user
generators expand to concrete declarations before checking. A legacy backend
specialization path remains for programmatically constructed ASTs and still
uses name-based type resolution. It is not reachable from accepted source.

Function declarations have dense `FunctionId` identities, assigned in sorted
name order, and retain their source spans when source metadata is available.
Generated function bodies retain source IDs and exact spans into their
materialized text; imported declaration and call nodes retain their module
source spans as well.
IDs are local to a checked program, not persistent identities or cache keys.
Globals and aggregate types also have dense IDs assigned by sorted name.
Field and enum-variant IDs pair their owner's aggregate ID with their index
in declaration order. Thus identically named fields on different structs are
distinct, while an alias or reference resolves to the underlying owner's ID.
Resolved declaration metadata remains accessible through these IDs. Adding a
declaration may renumber IDs; they must not be stored as generator cache keys.
The immutable borrow of the original program prevents invalidating checked
information before emission. Repeated emission does not rerun validation.

Validation and the remaining AST-based backend paths share one recursive
alias resolver, including aliases nested inside references, pointers, slices,
cells, atomics, arrays, and tuples. Resolving an alias cycle is an error; the
backend no longer silently substitutes unresolved struct field types.

## Implemented: typed body arenas

Validation retains expression types rather than running a second type-checking
pass. Each ordinary function has a body arena with dense expression and local
binding IDs, source spans, numeric operation/type/overflow metadata, callee
IDs, and structured statements (loops, assignments with projections, returns,
breaks, and continues). Expression `if`, `match`, and individual match arms
also have dedicated nodes with explicit child IDs; arm patterns and values keep
their binding scopes. Named-call operands remain in declaration order; sourced
calls also retain a separate permutation of operand indices in written order.
That metadata records provenance, not evaluation order: arguments are evaluated
in parameter declaration order. Calls synthesized without complete source spans
have no written-order permutation. Syntax-only nodes such as type operands and
patterns have no runtime type.
Numeric operations use a closed opcode enum, not an arbitrary operation string;
their exact scalar operand type records width and signedness, and a separate
mode records wrapping or saturation. The backend reads these checked values
when selecting numeric instructions.

Local identities are allocated at declarations, including unused destructured
and match-bound names, rather than inferred from the first variable use.
Pattern declaration nodes and their uses refer to the same binding ID. Match
arms, nested blocks, loops, and let-else failure bodies have separate scopes;
the for-loop step can see declarations in its body, matching current checking
semantics. Assignment roots distinguish local binding IDs from global IDs.
Visible-name shadowing is rejected before lowering. The parser may still assign
distinct internal names to same-spelled bindings in disjoint sibling scopes;
those compiler identities are separate from the typed IR's binding IDs.

The current ownership passes still operate on reconstructed syntax. Their
branch join now retains loans from paths where they remain active without
resurrecting loans released on every path. Lexical blocks propagate releases
of references that existed before the block; newly declared block references
stay scoped. A native aggregate-reference example covers the release case.
The borrow pass also tracks which owner names are visible at a binding or call
site. Block-result provenance follows local aliases and destructuring, so a
reference to a block-local owner is rejected when retained outside the block;
reference-typed call parameters include aliases, while scalar block results
remain valid. This check is transitional until ownership
uses typed binding and place identities throughout.
Match-arm payloads now inherit the reference origins of the aggregate
scrutinee, including origins stored in its reference-bearing fields. The
conservative union prevents a locally owned referent from escaping through
an enum payload. Direct enum and struct constructors preserve those origins
as well; typed arm-place provenance remains future IR-04 work.

Checked bodies are now lowered before the ownership passes. Each has a
retained, address-free control-flow graph keyed by body node and binding IDs;
it represents branches, matches, short-circuit evaluation, loops, labeled
transfers, returns, and diverging expressions. The debug IR dump includes the
graph and its reachable nodes. Definite-binding analysis is the first typed
ownership preflight: a local read or assignment must be bound on every live
incoming path. Move and loan tracking still use the transitional syntax pass.
Match dispatch preserves source order: a pattern or guard failure tries the
next arm, while payload bindings appear only on the successful pattern edge.
The impossible failure after the last exhaustive arm diverges in the graph.
Each checked flow also retains backward binding liveness before and after its
nodes. Whole-local replacement kills the old value; projected writes read the
aggregate. Liveness tracks future reads only: it cannot by itself prove that
linear values were consumed or that loans may be released at suspension.
Bind, assignment, and pattern actions retain the checked value node that
supplied them. Match pattern actions point to the scrutinee; destructuring
actions point to their initializer. These stable origins are available to
future move and loan transfer without looking back into source syntax.
Direct borrow expressions also have dedicated flow actions retaining the
resolved access place, mutability, and exact borrow node. Expressions whose
referent place is not yet resolved continue as ordinary evaluation nodes.
For computed `#deref-set` targets, live-loan conflict checking resolves known
origins from the target's evaluation snapshot and checks the resulting places
as writes. Reference-returning calls participate through their checked return
origins. Tests cover an accepted write after child-loan release and rejection
when its computed write event precedes that release. Missing-origin behavior
and referent ownership/reinitialization obligations remain unfinished.
Explicit `#clone` of a resolved place similarly retains a dedicated action
with the checked place and source node; unresolved computed clone operands
continue as evaluation nodes. This action does not yet replace the lexical
linearity checker.
Return actions retain their optional checked result node ID. The return
expression is evaluated before the transfer action, then lexical cleanup runs
on the edge to function exit. This lets ownership transfer inspect the
escaping value and its origins before the returning scope is cleared.
Value-carrying break actions retain their checked loop-result node ID by the
same rule; their expression and transfer precede cleanup on the edge to the
loop's break target.
An observational forward may-analysis now tracks direct loan origins held by
bindings, including simple aliases and conditional results. It unions origins
at flow joins, retains the first exact borrow span, and clears a dropped
binding without clearing aliases. The typed-IR debug dump includes these
states. A typed preflight now rejects a direct borrow that overlaps a direct
origin retained by a live reference or aggregate binding when either is
mutable. It also rejects symbol reads or clones through a mutable loan, or
writing to or destroying a borrowed place. Checked place IDs preserve both
source spans. Projected reads check the final field/index/payload place;
intermediate base evaluation is not treated as a whole-base read.
Indirect referents, moves, and complete loan lifetimes still require the full
ownership transfer; the lexical checker remains in place.
Direct `#drop` and `#forget` of a resolved local place now produce explicit
release actions with checked place and expression IDs. Loan-state transfer
clears only the selected aggregate origin; a dynamic index retains possible
origins because it cannot identify one definite slot. Indirect values and
complete conflict enforcement still need the full ownership migration.
Constructor values for structs, enums, tuples, and arrays contribute their
contained direct origins to the resulting aggregate binding; value-block
results preserve those origins as well.
Reference-returning checked calls conservatively merge origins reachable
through their arguments. A direct result sheds any aggregate-storage path
from its arguments; precise callee return summaries are not yet available.
Slice creation, range, and element-reference forms forward the originating
array loan through derived values. Mutable-slice splitting carries that loan
through both tuple positions into destructured halves, retaining the original
borrow span. Complete disjoint-range transfer and reborrow enforcement remain
open.
Each origin also retains its structural storage path. Pattern transfers match
owner-qualified fields, tuple and array positions, and variant payload IDs
before assigning origins to destructured bindings, so other fields or variants
cannot contaminate a binding's provenance.
Checked aggregate reads select matching stored origins and strip the selected
field, payload, tuple, or array slot from the storage path. A dynamic array
index may select any indexed origin. Projected assignment updates known slots
and retains prior origins when a dynamic index makes the target uncertain.
Explicit scope-exit flow actions clear origins of bindings declared in blocks,
match arms, loop scopes, and the function's root local scope. Nonlocal break,
continue, and return edges run the relevant cleanup actions too. Root locals
remain available at a return transfer and clear on the following exit edge.
These transitions make the observational state scope-aware; conflict
enforcement is still pending.
Loop fixed-point regressions confirm that an explicitly released
iteration-local reference has no origin at the next loop condition, while an
outer mutable loan remains live across loop back edges.
Read and write places now have structural identities: a `BindingId` or
`GlobalId` root followed by owner-qualified field/variant IDs, tuple positions,
or concrete/dynamic array indices. A dotted identifier remains one binding,
not a field path. Assignment flow nodes retain these places directly; complete
move and indirect-loan rules remain in the pending ownership migration.
Place reads now also have explicit typed flow actions retaining their checked
value and place IDs. A role bit distinguishes an intermediate place base or
dedicated borrow/clone/release operand from a value read; the loan preflight
uses only the latter, while binding liveness still sees both.
Direct value transfers from a checked place into a binding, assignment,
pattern, return, or break now contribute a possible linear-consumption fact on
the typed graph. Explicit linear releases contribute the same fact. Later
overlapping reads or releases are rejected with both source sites. Direct
transfer roots follow conditional branches, match arms, value blocks, labels,
and unsafe wrappers through their selected results. Resolved ordinary-call
arguments are also treated as value transfers when their checked type is
linear. Checked tuple, array, enum, and normalized struct constructors also
transfer linear member values. Mutable-slice splitting consumes its source,
while indexing and length inspection borrow it. Other builtin operand modes,
nested expression uses, and complete exit obligations remain with the
syntax-side linear checker.
For remaining checked builtin forms, nested operands are treated as value
inputs unless the form is known to borrow or inspect a place. Contextual
one-slot `#array-repeat` consumes its source; the syntax-side checker agrees.
Array repetition is checked separately: a zero- or multi-slot repeat requires
a duplicable element. Mutable references are not duplicable even though they
need no explicit destruction; nested aggregate members are checked too.
One typed borrow preflight compares direct `#borrow` and `#borrow-mut` call
arguments using those place identities. It retains borrow origins through pure
aggregate construction and expression-valued branches, comparing only loans
that can coexist on one path. Initial bindings in value-producing blocks,
including `#let-mut`, retain their loan origins by stable binding ID; an
assignment invalidates that origin. It rejects overlapping places when either
loan is mutable and reports both source sites. Control-flow joins, references
returned from calls, and longer-lived loans
still require the full flow-sensitive loan transfer in IR-04.
For a call argument that is a reference binding with known direct origins,
the preflight uses the typed flow state to recover those origins and source
spans. Joined direct origins become separate bounded alternatives; a conflict
on any alternative is rejected. Bound aggregate symbols contribute all their
stored loans as coexisting call arguments, and typed field, payload, tuple, or
index projections select matching origins while retaining any nested storage
path. Correlated alternatives across conditional aggregates, separate
bindings, and indirect referents are still deferred to the full loan analysis.
For a projected direct borrow through a reference binding with known direct
origins, the preflight appends the checked projection to each referent place
before overlap comparison, following known reference-binding chains with a
bounded alternative set and cycle detection. Unknown chains remain pending.
Equivalent borrow paths are collapsed by place identity and mutability before
the bounded path limit is applied; the first matching source origin is retained
for diagnostics.

Global reads and borrows, named field/payload projections, concrete aggregate
and variant constructors, and pattern constructors retain declaration IDs.
Named assignment projections retain field/variant IDs rather than names.
Replacing a symbol with its resolved identity preserves the node's source
span. Per-body debug dumps include a deterministic name table for referenced
declarations; they do not enumerate every unused declaration in the program.
The compatibility reconstruction step obtains these spellings from the ID
table, without resolving the original spelling again.

Native lowering reconstructs its instruction-selector input from these bodies,
erases unsafe wrappers, and carries retained expression types through to
emission. The numeric and call identities determine the reconstructed heads.
Node IDs remain independent of allocation addresses. A temporary address index
connects original syntax to nodes during lowering and is then discarded. The
emission-local overlay now also marks every checked expression, including
syntax-only nodes without value types. When codegen asks for a checked node's
type and none was retained, it receives no type rather than reconstructing one
from syntax. Numeric operator selection also uses the retained operation,
operand type, and overflow mode rather than reparsing the dotted spelling.
If a checked numeric expression lacks that metadata, emission reports an
internal error instead of interpreting its spelling again. Backend-synthesized
expressions without checked nodes still use the compatibility parser.
Emission also checks that a numeric node's retained result type matches its
typed opcode, including boolean results from comparisons and logical forms.
Each checked operand must retain the opcode's scalar type, except logical
`&&`/`||`, whose operands are `bool` under the current source semantics.
Direct checked scalar and aggregate-specialized calls select their ABI and
canonical source assembly symbol by retained `FunctionId`; the reconstructed
name remains available for diagnostics. Aggregate dispatch guards use the
same checked identity; backend-synthesized calls retain the legacy name lookup.
Checked scalar call operands must also retain a type that agrees with their
resolved ABI parameter; missing or mismatched metadata is an internal error.
All checked call results, including indirect-return aggregates, must retain a
type matching their resolved ABI return type; missing or mismatched metadata
is an internal error.
Checked calls to declared functions also require their retained `FunctionId`;
they cannot fall back to name-based ABI resolution if that identity is lost,
including indirect-return aggregate calls.
Synthesized calls still use the compatibility lookup.
The overlay is
still address-indexed internally; it is
neither exported nor cached as an identity.
An executable regression verifies that erasing `#unsafe` wrappers preserves
the typed node order and numeric metadata association. This validates the
current order-based bridge, not a future address-free mapping.
The bridge also rejects same-length shape drift, including reordered literal
values and changed binding/declaration names, before attaching checked
metadata to reconstructed syntax. It also checks form heads against retained
builtin, numeric, or callee identity. It remains
an address-keyed compatibility bridge until IR-02 removes that dependence.
`CheckedProgram::dump_typed_ir()` exposes a deterministic
debugging view (not a stable interchange format).

## Remaining migration

### Reference-bearing writes across calls

The test-only `staged_store_loan_origins` solver supplements return-origin
summaries with final reference contents a callee stores through an argument. It
builds summaries bottom-up over the same acyclic call graph, substitutes
actual argument loans (including original input slots and physical destination
projections), and adds the retained references to caller-owned storage.
Ordinary, pinned, field-wise, forwarded, conditional, and computed writes are
covered. Stored contents are unioned across normal returns, while physical
write guarantees are intersected. Sequential writes replace prior contents;
whole-value and field effects account for overlapping storage. A destination
written on every normal return can replace caller loan contents, but ambiguous
or dynamic targets and missing input provenance cannot supply that permission.
Conditional writes preserve pre-call loans. These reference-content facts do
not prove linear initialization, consumption, or ownership restoration.
Missing input loans do not become references merely because a type contains
reference slots. `examples/callee_reference_store.lim` exercises a valid store
and consumption of its holder before the referent is mutated.
`examples/callee_reference_clear.lim` clears its holder explicitly in a callee
before mutating the referent. Returned references selected from entry storage
use the call's pre-write snapshot, so clearing the holder cannot release loans
retained by a returned old value.

This experiment is not enabled in production. It detects caller-side mutation
and block-local escape cases currently missed by production return-only
summaries. Conversely, possible stores alone cannot establish that Ready or
cancellation cleared a self-reference: explicit regressions preserve the
resulting migration failures for all three self-reference async examples.
Test-only summaries now distinguish final stores for known returned enum
variants, including nested branches and loop breaks. Unknown returns remain
possible in every variant summary; writes after constructor evaluation are
included. The three self-reference poll examples have clearing Ready summaries
and retaining Pending summaries. A separate test-only caller solver now refines
direct call results and uniquely defined local move chains at a matching variant
pattern. Each move must reach its original binding definition without intervening
assignment, release, or scope exit; later reinitialization of a moved-from binding
does not change the moved result. The solver substitutes
the original call snapshot, retains source-snapshot wakeup dependencies, and
requires every backward path to reach that call without an intervening effectful
form evaluation or indirect write. Constructor evaluation is pure, but operand
effects are checked as separate events. Assignment, release, and scope exit of
the destination invalidate refinement. Only exact, definitely written local
destinations can be replaced. Unknown builtin effects are not assumed pure.
`examples/callee_variant_clear.lim` now passes this staged caller solver, while
Pending mutation, intervening writes/calls, and reassigned results still fail
with the original mutation span. `examples/callee_variant_alias_clear.lim`
exercises two explicit result moves and exits 42. The staged solver also joins
`#if`, `#match`, and block-valued results, including branch-local moves and
different callees. Each normal result path must identify a call, and multiple
calls must be mutually exclusive before the selected pattern. Only destinations
definitely written by every alternative are replaced; incoming loans are unioned
using each call's original snapshot. Unknown results, different destinations,
missing writes, and sequential call selection cannot fabricate clearing.
Returned old values retain their separate loans. Snapshot dependencies include
every call alternative. `examples/callee_variant_branch_clear.lim` exercises
both branches and exits 84. Loop results additionally trace reachable value
breaks for that exact loop identity, in stable event order. Nested loops keep
separate results, unreachable breaks do not contribute, and a loop without a
reachable value break supplies no clearing proof. Continue-before-call paths
can still establish clearing; unknown breaks and post-call writes/calls cannot.
`examples/callee_variant_loop_clear.lim` continues once, exercises both break
branches, and exits 84. The frontend now preserves loop-control context through
nested expression blocks without leaking it afterward, and treats plain/labeled
break and continue transfers as diverging branches. Repeated-call version
correlations, projected/aggregate scrutinees, parameter contents, and restoration
still need integration; this is not enabled
in production.

A further opt-in test solver keeps parameter pointee contents separate from
local reference handles. Entry reference slots are seeded once, indexed by the
original input pointer slot, including nested reference boundaries. Direct and
callee stores update that table; whole and projected loads and summary input
selection consult actual contents rather than reconstructing schema loans on
every load. Branch joins union possible contents. Whole-value and pinned-field
replacement tests distinguish the new reference source from the entry source
while preserving the parameter handle. Clearing and missing table facts do not
resurrect schema loans. Symbolic array input slots match concrete selections
conservatively, retaining their entry facts alongside possible new sources.
The replacement/load case remains a staged regression fixture: the legacy
production checker rejects the projected read after replacement. Pinned field
writes now address the container field, not its stored
reference's pointee. The typed staged solver releases old local field loans and
retains new ones, but the legacy checker still rejects local reference RHSs for
projected pinned-field stores. Production return summaries, initialized/moved
storage, restoration, conditional parameter clearing, and exact symbolic-array
overwrites remain integration work; this contents table proves none of those.
An opt-in interprocedural pass now recomputes return and store contracts with
this contents solver in callee-before-caller order. Only direct callee tables
are supplied during inference, including return-variant store tables, then
the completed tables are shared across bodies. Direct, callee, and pinned-field
replacement contracts select the replacement input through forwarding calls;
conditional writes retain both inputs, and a saved pre-write reference retains
its original input. A staged caller regression permits mutation of the released
old input and rejects mutation of the retained replacement, with the exact
offending statement span. This is test-only contract integration, not production
promotion: initialized/moved contents and restoration remain unproved.
The staged contents solver also distinguishes consuming pinned reads using
the shared linear-type classification recorded during typed lowering. A
proven exact mutable parameter destination loses its stored reference facts
after a consuming `#pin-read`; later binding/return transfer uses that read's
pre-move event snapshot. A following pinned write restores replacement source
facts without changing the already-moved value's source. Copy-valued pinned
reads leave contents intact. Regression checks retain the handle, transferred
and restored sources, and exact consumption spans; the native
`parameter_pin_restore.lim` example explicitly consumes, forgets, and restores
parameter storage and exits 42. Empty facts still do not establish ownership
initialization, and ambiguous destinations are not strongly cleared. The legacy
checker still rejects restoration while a moved reference-bearing value is
live; general consumption, conditional restoration, and production promotion
remain open.
Ordinary destruction is now reflected in the staged parameter-contents table.
Linear `#forget`/`#drop` operands are classified during lowering, and destruction
resolves the container address through dereferences and field/array projections,
including aliases, nested pointer inputs, and transparent unsafe wrappers.
Only one proven mutable concrete destination can be strongly cleared; Copy
operands, dynamic indices, and ambiguous destinations retain their facts.
Whole destruction removes all contents, field destruction preserves siblings,
and nested destruction leaves the outer pointer slot and handle intact.
These reference facts are not initialization/restoration proofs or outgoing
consumption effects. The syntax-only ownership rejection fallback has since
been removed; production validates borrowed-storage entry contracts separately.
This historical contents milestone alone does not establish general borrow
checking or arbitrary-body async lowering.
The staged interprocedural contents pass now exports a separate table of
destruction destinations proved cleared on every normal return. These are not
write summaries and must never count as initialization or restoration evidence.
Definite clear facts are intersected across branches and normal returns; an
overlapping possible write invalidates a clear, and calls or unclassified
effects conservatively invalidate prior proofs before applying any final callee
clears. Non-returning bodies export no clears. Caller substitution requires an
exact mutable destination and updates local or parameter stored reference facts,
preserving the handle and sibling fields. Nested input selectors follow current
pointer contents, including redirected pointers. Return-value substitution uses
the original pre-call snapshot when the call clears contents, so old references
escaping from the callee still retain their loans. Staged regressions cover
forwarding, whole/field destruction, sibling protection, nested redirection,
conditional clearing, later restoration/calls, non-returning bodies, and exact
escaped/sibling mutation spans. Conditional consumption, complete ownership
contracts, and production migration remain open.
Opting into the interprocedural contents pass now also records that provenance
mode on staged bodies. Subsequent ordinary `loan_origins` queries, including
consumption, entry-contract, restoration, and borrow passes, use the same
contents-aware solver instead of silently returning to entry-schema loads.
Default test bodies and production builds keep their previous behavior. A
combined regression verifies destroy/restore forwarding with reference-bearing
storage across both ownership contracts and live loans. Reading the destroyed
field before restoration remains an error despite empty reference facts, with
the exact read span and destruction label. Constant return-variant summaries
now intersect output-relative enum facts across every reachable normal return
and flow through constructor/forwarding calls. Unknown or differing returns
remove facts; pointer/reference results never manufacture owned discriminants,
and raw/kernel writes invalidate existing facts. This lets caller initialization
prove inactive payload slots rather than demanding nonexistent reference inputs
from a fresh frame. All three self-referential async examples pass combined
staged entry-contract inference and live-loan checking for every function.
Negative regressions still reject destruction of a frame while its Pending
reference is needed by the next poll, underlining the exact destruction form.
Default-mode polling-input gaps remain covered separately. This closes one
staged integration gate, not production migration or arbitrary-body suspension.
The contents experiment now also summarizes destruction separately for each
explicit returned variant. It reuses the store solver's return-path filtering,
retaining unknown alternatives and intersecting all paths with the selected
outcome. Caller matching applies only common exact mutable physical clears
from mutually exclusive calls, with the same stale-result barriers as stores
plus conservative release/assignment invalidation. Clearing a field preserves
its siblings and the address handle. Published pattern-clear events let these
facts propagate through functions that match and reconstruct their outcomes.
Direct-call and bound-result matching preserve escaped reference payloads via
original pre-call snapshots, even when the matched branch destroys storage.
Regression checks cover explicit/nested/loop returns, unknown and same-variant
alternatives, restoration/later calls, branch-result joins, forwarding, stale
results, sibling retention, and exact mutation spans for escaped loans.
Matched consuming-clear contracts now also mark their exact physical targets
definitely consumed in the staged ownership solver. This is based on actual
linear destruction/moves, not empty reference contents, and records originating
call-site spans for diagnostics. A reference-free linear resource regression
proves that Ready can be explicitly restored before reading it, while Pending,
stale calls, same-variant alternatives, and unknown outcomes cannot justify
replacement. Reading Ready storage before restoration still fails at the exact
read span. The positive path passes combined replacement/use validation and
entry-contract inference. This proves consumption only on a matched destructive
outcome: absence of a clear is not an initialized/unconsumed guarantee on other
outcomes.

The opt-in ownership summary pass now also publishes complete may/must exit
effect summaries for each explicit returned variant, including whether any
reachable normal return exists and any unresolved consuming accesses. Unknown
alternatives remain in every selected group; absent groups are unknown rather
than empty contracts. Initialized-entry effects remain separate from an
optional profile under the actual inferred consumed-entry requirements. A
conditional initializer therefore has no outgoing consumption on Ready but
retains definite consumed state on Pending in its consumed-entry profile.
These outcome tables do not weaken whole-function entry requirements, even
when a consuming path diverges rather than returning normally. Tests cover
explicit/nested/loop results, possible versus definite consumption, unknown
and same-variant alternatives, consumed-and-restored storage, nested callee
destruction, sibling destinations, unreachable returns, and raw unknown access.
Caller matching now uses these full outcome tables to reconstruct affected
storage from original pre-call consumption snapshots, preserving earlier
consumption instead of deleting it with the callee's contribution. Mutually
exclusive call sources join may state and intersect must state. Both fixed-point
passes register snapshot dependencies, wait for every required snapshot, and
wake matching nodes when a source changes even if ordinary successor facts do
not. A loop regression isolates that dependency by using a callee destruction
whose span was already present in the unrefined outgoing call state.
The consumed-entry profile carries exact input descriptors; substitution must
prove their actual destinations before a conditional initializer can replace
caller entry state. Pending retains the original caller destruction label;
Ready initializes only the selected exact storage, never every possible alias.
Fresh-result barriers remain conservative across writes/calls, releases,
relevant assignments/scope exits, and potentially consuming accesses. Plain
linear result moves to unrelated local slots preserve the correlation.
Direct callee tables are cleared at the start of every staged analysis run,
including callers never reached when a callee fails, then repopulated from the
new run. Profiles from one entry-assumption mode cannot leak into another.
Regressions cover Pending
reads, prior destruction, ambiguous/unknown outcomes, stale calls, branch and
loop result joins, explicit forwarding, linear result moves, sibling states,
conditional initialization, ambiguous aliases, changing loop snapshots, and
successful inference followed by an early failed run and successful reinference.
Production ownership migration, complete initialization/escaping-reference and
owned-exit validation, and arbitrary-body async lowering remain unfinished.

The instruction selector still uses AST-shaped inputs. Compiler-synthesized
expressions and internal legacy generic specializations retain the old type
lookup path. Specialization provenance and a uniform ownership-place model
still need a fully unified identity scheme before removing that path. Numeric
nodes use typed metadata for operation selection, but their operand trees are
still recursively emitted from reconstructed syntax; ordinary calls select
their ABI by ID but still obtain the assembly symbol from reconstructed names.
Ownership analyses still run on the original AST; they have not yet consumed
the explicit branch nodes or been replaced by typed control-flow dataflow. No
SSA optimizer or arbitrary-function async transformation is implemented.

The explicit task-composition generators do not need that full transformation:
their states are ordinary enums that go through the existing ownership checks.
Suspending arbitrary function bodies would additionally require liveness,
move/loan state per suspension point, and stable-storage rules.

Existing UI, native-example, numeric differential, reproducibility, and
single-validation tests remain migration acceptance criteria. New tests cover
resolved declaration metadata, deterministic function IDs, nested alias
resolution/cycles, and an executable aliased-reference/slice example.
