# Predicate evidence and contracts

Lim now uses local predicate evidence and explicit function contracts. The
symbolic execution engine, Boolean circuit/SAT solver, theorem declarations,
induction machinery, theorem CLI and bounded symbolic collection models have
been removed. Historical mathematical/theorem experiments remain in Git.

The [language reference](language.md#predicate-contracts-and-constrained-types)
defines the syntax. [contracts.lim](../examples/contracts.lim) is executable.

## What the compiler verifies

- A call has evidence for every declared requirement.
- Successful `#if-valid` branches grant facts about exactly the checked subjects.
- Joins retain facts common to every continuing path.
- Possible writes revoke facts and saved Boolean evidence that depend on them.
- Structural read/write footprints cross calls; semantic contracts require
  explicit annotations at every intermediary.
- Constrained bindings, fields, parameters and results require evidence.
- Fixed storage constraints must be restored when exclusive loans end. A
  returned/reborrowed alias carries the same obligation.
- Specifications name pure Boolean predicates or typed scalar comparisons and
  type-correct, pure observations. Unsupported analysis fails closed.

It does **not** prove `#ensures`, `#preserves`, or `#assume` true. These are the
explicit trust boundary. Instrumented execution audits function promises over
the exercised inputs; tests cannot establish their universal correctness.
Requirements and restoration rules remain compiler obligations in production.

## Local analysis

`src/contracts` replaces the former `src/proof` and `src/theorem.rs` modules:

- `mod.rs` collects explicit clauses and constrained types before erasure.
- `summaries.rs` records transitive structural reads, writes and returned
  reference origins. It never infers semantic contracts.
- `flow.rs` tracks subject identities, predicate facts, dependency versions,
  branch joins, mutable loans and fixed storage obligations.
- `lowering.rs` erases ghost forms and optionally emits native contract checks.

Facts are opaque named applications, matched by predicate and argument
identity. There is no SAT solving, arithmetic implication discovery, predicate
unfolding, symbolic execution of function bodies, or hidden runtime proof
object. The rule checker follows ordinary control flow and declared interfaces.
Checked function/type metadata is tied to its lowered AST; modifying a parsed
program cannot retain contracts for a different body.

Typed scalar comparisons also form exact atomic facts. They carry their
operator, scalar type and operand identities; a comparison does not imply a
different bound automatically. Explicit helper calls may require one claim
and promise another through `#ensures`, audited in instrumented execution.
This is contract-directed code, not a separate proof kernel or tactic engine.

Scalar comparisons can use ordinary named calls, for example
`(#call #usize::lt (: left index : right 4usize))`. The compiler generates the
typed intrinsic signature and lowers it to the same operation and fact identity
as `(#usize::lt index 4usize)`. This spelling change introduces no new inference.

`#index-proven` accepts a reference to a fixed array and a `#usize` index. Its
implicit requirement is exactly `(#usize::lt index N)` for the array length.
Production omits the bounds check; instrumented lowering uses ordinary checked
indexing at the access. Named predicates require an explicit helper to establish
the comparison claim. [index_contracts.lim](../examples/index_contracts.lim)
demonstrates the helper, a constrained index assignment and the proven access.
Ordinary `#index` and dynamic slice operations retain their checks.

`#generate #array` emits concrete accessors with explicit comparison requirements,
a named bounds validator and an explicit `prove-in-bounds` helper connecting its
claim to the required comparison. Copy elements also receive a by-value getter;
linear elements use shared or mutable borrows. These are inspectable ordinary
functions, checked and instrumented like handwritten code.
[generated_array.lim](../examples/generated_array.lim) demonstrates intrinsic
calls, a programmer-written implication helper and a generated getter.

Ordinary functions in programs containing async code retain their original
contracts across planning. The completed generated program receives normal
evidence checking and instrumentation. Planning uses checked projections and
cannot authorize a production proven access.

Writes to a sibling field need not invalidate a predicate that only reads the
other field. Unknown aliases, raw memory and opaque effect boundaries use
conservative invalidation rather than assuming disjointness. Baseline Lim
ownership, initialization and borrow checking remains mandatory.

## Runtime behavior

Use `lim --check-contracts INPUT ...` or `--cfg contracts=check` for test builds.
`contracts=test` also enables assertions through `CompileConfig`.

| Form | Production | Instrumented execution |
| --- | --- | --- |
| `#if-valid` | Execute the validation branch | Same |
| `#requires` | Check evidence at compile time | Also assert on entry |
| `#ensures` | Trust the declared promise | Assert on every normal return |
| `#preserves` | Preserve incoming evidence conditionally | Assert only if initially true |
| `#assume` | No evaluation | No evaluation |
| `#old` | Identity of entry observation | Capture an entry snapshot |
| `#where` | Same layout as the base type | Same layout; boundary contracts audited |
| `#index-proven` | Require bounds evidence; omit the bounds check | Also check the index at the access |

An assumption never disables an independent contract assertion. A predicate
failure uses Lim's normal panic path. Panic/divergent exits have no normal
postcondition obligation.

## Deliberate boundaries

The checker matches conjunctions of named predicates. Disjunction does not
grant either operand, and an ordinary `#if` grants no evidence. Equal arithmetic
expressions or two predicates with equivalent bodies are not interchangeable.
Loops use conservative entry facts; no induction or inferred loop invariant is
performed. Unknown aliasing may require explicit validation or a contract.

After an element reference ends, its owner stays unavailable for general use
until the fixed invariant is restored. A base-input predicate can observe the
owner for validation, or `#assume` can supply the closing evidence without
execution. A mutable reference returned while an invariant is open transfers
that pending obligation; the call does not claim the owner is already valid.

Fixed arrays are expanded up to 1024 constrained elements; type traversal has
a depth limit of 64. At most 4096 facts and 200,000 local analysis steps are
accepted. Individual identities are limited to 16 KiB; cumulative identity and
state-snapshot work is limited to 64 MiB of logical analysis data. These work
weights are not a measurement of compiler RSS. Exceeding a limit rejects the
program without accepting partial evidence.

`#old` supports snapshot observations rather than mutable reference handles.
Dynamic containers should place a named predicate on the whole collection,
for example `#where (value VecU64) (sorted (&value))`, rather than depend on
inferred elementwise relationships. Unsupported nested constraint shapes are
rejected with a diagnostic; they never silently lose their requirements. Nested
constraints in slices, raw pointers, pinned owners, atomic slots, enum payloads
and recursive aggregates currently require a predicate on the enclosing value.
Constrained global storage is rejected; construct validated values in functions.
Constrained reference handles use immutable bindings; `#ref-mut` still permits
mutation of the referent. Mutable parameter bindings cannot appear directly in
postconditions; use scalar `#old` observations or return the value.
