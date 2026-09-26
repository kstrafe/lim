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
The overlay is
still address-indexed internally; it is
neither exported nor cached as an identity.
An executable regression verifies that erasing `#unsafe` wrappers preserves
the typed node order and numeric metadata association. This validates the
current order-based bridge, not a future address-free mapping.
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
