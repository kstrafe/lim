# Typed compiler representation

This is an incremental internal migration, not a language or syntax change.
Lim still requires explicit source types and performs the existing type,
linearity, borrow, and unsafe checks before returning a `CheckedProgram`.

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

## Remaining migration

This declaration layer is not yet a typed expression or control-flow IR.
Expression types and local identities are still reconstructed by the backend;
ownership analyses still operate on the AST. Before migrating them:

1. Assign stable local binding and expression IDs during lowering. Preserve
   source spans through named-argument reordering, generated code, unsafe
   erasure, and internal specialization. Do not persist AST addresses as IDs.
2. Retain checked operand and result types on expressions. Represent numeric
   operations by explicit operation, width, signedness, and overflow behavior;
   represent calls by function IDs and arguments in declaration order.
3. Move scalar and call emission to those nodes, then migrate aggregates and
   control flow. Remove redundant backend type reconstruction as each path
   moves, rather than silently falling back for an allegedly migrated node.
4. Move ownership analyses to shared binding/place identities and control
   flow. Preserve exact diagnostics and related-origin spans throughout.

Existing UI, native-example, numeric differential, reproducibility, and
single-validation tests remain migration acceptance criteria. New tests cover
resolved declaration metadata, deterministic function IDs, nested alias
resolution/cycles, and an executable aliased-reference/slice example.
