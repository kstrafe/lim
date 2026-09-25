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
tables from syntax. Generated Lim functions follow the same path. Internal
legacy generic specializations, which are created later, still resolve their
specialized signatures during lowering.

Function declarations have dense `FunctionId` identities, assigned in sorted
name order, and retain their source spans when source metadata is available.
IDs are local to a checked program, not persistent identities or cache keys.
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
IDs, and structured statements (loops, branches through expression forms,
assignments with projections, returns, breaks, and continues). Named-call
operands remain in declaration order; their spans retain source order.
Syntax-only nodes such as type operands and patterns have no runtime type.

Local identities are allocated at declarations, including unused destructured
and match-bound names, rather than inferred from the first variable use.
Pattern declaration nodes and their uses refer to the same binding ID. Match
arms, nested blocks, loops, and let-else failure bodies have separate scopes;
the for-loop step can see declarations in its body, matching current checking
semantics. Assignment roots distinguish local binding IDs from global names.
The parser's existing shadow-renaming remains a compatibility aid for the
legacy backend, not the IR's binding identity scheme.

Native lowering reconstructs its instruction-selector input from these bodies,
erases unsafe wrappers, and carries retained expression types through to
emission. The numeric and call identities determine the reconstructed heads.
Node IDs remain independent of allocation addresses. A temporary address index
connects original syntax to nodes during lowering and is then discarded. The
legacy instruction selector still uses an emission-local address-to-type
overlay; it is not an exported or cached identity.
`CheckedProgram::dump_typed_ir()` exposes a deterministic
debugging view (not a stable interchange format).

## Remaining migration

The instruction selector still uses AST-shaped inputs. Compiler-synthesized
expressions and internal legacy generic specializations retain the old type
lookup path. Global and field/variant projection identities and specialization
provenance still need a fully unified identity scheme before removing that
path. Ownership analyses still run on the original AST; they have not been
replaced by typed control-flow dataflow. No SSA optimizer or arbitrary-function
async transformation is implemented.

The explicit task-composition generators do not need that full transformation:
their states are ordinary enums that go through the existing ownership checks.
Suspending arbitrary function bodies would additionally require liveness,
move/loan state per suspension point, and stable-storage rules.

Existing UI, native-example, numeric differential, reproducibility, and
single-validation tests remain migration acceptance criteria. New tests cover
resolved declaration metadata, deterministic function IDs, nested alias
resolution/cycles, and an executable aliased-reference/slice example.
