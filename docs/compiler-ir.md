# Typed compiler representation

This is an incremental internal migration, not a language or syntax change.
Lim still requires explicit source types and performs the existing type,
linearity, borrow, and unsafe checks before returning a `CheckedProgram`.

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
The parser's existing shadow-renaming remains a compatibility aid for the
legacy backend, not the IR's binding identity scheme.

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
referent place is not yet resolved continue as ordinary evaluation nodes;
alias-aware referent provenance remains part of the pending loan transfer.
An observational forward may-analysis now tracks direct loan origins held by
bindings, including simple aliases and conditional results. It unions origins
at flow joins, retains the first exact borrow span, and clears a dropped
binding without clearing aliases. The typed-IR debug dump includes these
states. It does not yet replace the lexical borrow checker or resolve indirect
referents or enforce complete loan lifetimes.
Constructor values for structs, enums, tuples, and arrays contribute their
contained direct origins to the resulting aggregate binding; value-block
results preserve those origins as well.
Each origin also retains its structural storage path. Pattern transfers match
owner-qualified fields, tuple and array positions, and variant payload IDs
before assigning origins to destructured bindings, so other fields or variants
cannot contaminate a binding's provenance.
Checked aggregate reads select matching stored origins and strip the selected
field, payload, tuple, or array slot from the storage path. A dynamic array
index may select any indexed origin. Projected assignment updates known slots
and retains prior origins when a dynamic index makes the target uncertain.
Explicit scope-exit flow actions clear origins of bindings declared in blocks,
match arms, and loop scopes. Nonlocal break, continue, and return edges run
the relevant cleanup actions too. These transitions make the observational
state scope-aware; conflict enforcement is still pending.
Read and write places now have structural identities: a `BindingId` or
`GlobalId` root followed by owner-qualified field/variant IDs, tuple positions,
or concrete/dynamic array indices. A dotted identifier remains one binding,
not a field path. Assignment flow nodes retain these places directly; move and
loan overlap rules still belong to the pending ownership migration.
One typed borrow preflight compares direct `#borrow` and `#borrow-mut` call
arguments using those place identities. It retains borrow origins through pure
aggregate construction and expression-valued branches, comparing only loans
that can coexist on one path. Initial bindings in value-producing blocks,
including `#let-mut`, retain their loan origins by stable binding ID; an
assignment invalidates that origin. It rejects overlapping places when either
loan is mutable and reports both source sites. Control-flow joins, references
returned from calls, and longer-lived loans
still require the full flow-sensitive loan transfer in IR-04.
For a call argument that is a reference binding with one known direct origin,
the preflight now uses the typed flow state to recover that origin and its
source span. Multi-origin aliases, aggregate symbols, and indirect referents
are still deferred to the full loan analysis.
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
Direct checked scalar and aggregate-specialized calls select their ABI and
canonical source assembly symbol by retained `FunctionId`; the reconstructed
name remains available for diagnostics. Aggregate dispatch guards use the
same checked identity; backend-synthesized calls retain the legacy name lookup.
Checked scalar call operands must also retain a type that agrees with their
resolved ABI parameter; missing or mismatched metadata is an internal error.
Checked scalar call results must likewise retain a type matching their
resolved ABI return type; missing or mismatched metadata is an internal error.
Checked calls to declared functions also require their retained `FunctionId`;
they cannot fall back to name-based ABI resolution if that identity is lost.
Synthesized calls still use the compatibility lookup.
The overlay is
still address-indexed internally; it is
neither exported nor cached as an identity.
An executable regression verifies that erasing `#unsafe` wrappers preserves
the typed node order and numeric metadata association. This validates the
current order-based bridge, not a future address-free mapping.
The bridge also rejects same-length shape drift, including reordered literal
values, before attaching checked metadata to reconstructed syntax. It remains
an address-keyed compatibility bridge until IR-02 removes that dependence.
`CheckedProgram::dump_typed_ir()` exposes a deterministic
debugging view (not a stable interchange format).

## Remaining migration

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
