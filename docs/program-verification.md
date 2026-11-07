# Symbolic program verification

Lim’s compile time `#theorem` checker symbolically executes checked, expanded
Lim programs. It reasons about program behavior with machine-width values,
path conditions, modeled storage, and bounded control flow. It is a separate
feature from the former dependent mathematical proof kernel; mathematical
types, universes, and proof-term checking are not required for this direction.
Symbolic verification supplements ordinary type, borrow, and linearity checks;
those checks remain mandatory.

The checklist below separates current implementation from work that should be
built. A theorem that cannot be decided within the supported semantics and
resource limits must remain **unproved**. Unsupported behavior, solver errors,
and exhausted budgets must never be treated as success.

## Implemented checks

These capabilities are present in `src/proof/mod.rs`, `symbolic.rs`,
`validation.rs`, and `logic.rs`, and are illustrated in
[`examples/proofs.lim`](../examples/proofs.lim). Support is bounded and
program-shape dependent; this list is not a claim of completeness.

- **Universal input contracts.** `#proof-for-all` introduces symbolic values
  for supported scalar and aggregate types. `#proof-contract` relates a
  function’s result and state to its old inputs. Implications and path guards
  constrain which executions an obligation covers. Contracts can assert
  relations, but arbitrary quantified formulas, unbounded domains, and every
  Lim type are not supported.
- **Machine integer semantics.** Modeled bitvectors preserve width and
  signedness. Explicit wrapping and saturating arithmetic, comparisons, casts,
  and supported division are evaluated using machine behavior. Checks such as
  `#proof-no-overflow` can establish a condition under a precondition.
  Overflow, division by zero, signed corner cases, and every operator/backend
  combination still need direct coverage; mathematical integers are not a
  substitute for machine semantics.
- **Feasible paths and calls.** Branch conditions become symbolic guards, so
  contradictory paths do not create false counterexamples. Calls to modeled
  Lim functions execute symbolically within call-depth and step limits.
  Execution-trace claims check call ordering and that a call occurs only under
  a specified observed condition.
- **Structural calls and effects.** Direct/transitive call-graph assertions
  describe the program's structural graph, which can include infeasible
  branches. They are distinct from execution-trace claims. Conservative
  effect checks can exclude IO, allocation, mutation, globals, unsafe code,
  external calls, and assembly, or restrict unsafe operations to an explicit
  allowlist. Unknown effects cannot establish an absence claim.
- **Native stack bounds.** An explicit target and entry function can be checked
  against the compiler's bounded native stack analysis. This does not bound
  heap use, operating-system work, or separately running threads.
- **Validation before action.** Execution-local validation facts track storage
  identity. Writes through aliases, projections, and referenced dependencies
  revoke affected facts. The checker can verify that a validation gates an
  action and that a later mutation cannot leave stale validation in force.
  Facts and dependency tracking have explicit limits; validation does not
  certify arbitrary external state.
- **Loops with supplied invariants.** `#proof-with-invariants` supplies a
  predicate and rank for a named loop. The engine checks entry, preservation,
  and exit obligations for the modeled loop. Loop unrolling and symbolic
  execution are bounded; unsupported state changes and unsupported invariant
  forms fail closed. The countdown example demonstrates a result proved via
  an invariant rather than iterating through every input value.
- **Arrays and aggregates.** Small fixed arrays, tuples, records, enums, and
  modeled references can be symbolic values. Directly constructed arrays can
  be checked for sortedness and permutation within a limit. Indexing and
  supported projections carry path conditions, allowing bounds-related claims
  when the relevant conditions are modeled. Borrowed slices over modeled
  arrays preserve their backing storage, start, length and mutability. Array
  borrows, nested ranges, element references, length queries and mutable splits
  carry bounds obligations; writes through a view update the original array.
  A range may be empty at the end boundary. Symbolic array inputs and slice backing
  arrays are capped at 64 elements. Arbitrary slice inputs, dynamically sized
  allocations and broad collection algorithms are not generally modeled.
- **References and modeled memory.** Ordinary and pinned references denote
  symbolic storage locations; reads, writes, aliases, and projections update
  the modeled heap. Raw pointers may be represented as address bitvectors, but
  that does not model dereference or unsafe memory effects. Validation facts
  reached through slices depend on the elements selected by their ranges,
  including any references stored in those elements.
- **Proof reports and failure.** A false obligation reports a counterexample
  when the solver can provide one. Scalar witnesses use typed literal
  spellings. Arrays, records and active enum payloads show their values;
  references and slices identify their initial storage and contents. Repeated
  aliases share an identity, and inaccessible record representations stay
  hidden. Unsupported semantics, malformed proof
  values, circuit errors, and exhausted execution/storage/solver budgets
  report failure or an inconclusive `unproved` result. They do not discharge
  the theorem.

[`examples/symbolic_slices.lim`](../examples/symbolic_slices.lim) demonstrates
read and mutation contracts over borrowed subranges. Quantify an array or
array reference to bound the backing storage, then call a function with a view
of that array. A contract taking an arbitrary slice directly does not acquire
an implicit length bound. For old contents, put the entire read inside
`#proof-old`, for example `(#proof-old (#index values 0usize))`; saving an old
reference or slice handle alone does not snapshot its referent.

## Reading counterexamples

The checker freezes symbolic inputs before executing the function. For example,
this contract is false because `overwrite` replaces the original byte:

```lisp
(#fn overwrite (: source (#ref-mut #u8)) ()
  (#deref-set source 7u8)
  (#return ()))

(#theorem unchanged
  (#proof-contract overwrite
    (#u8::eq (#deref source) 1u8)
    (#proof-eq (#deref source) (#proof-old (#deref source)))))
```

The error includes `source = mut-ref#0(1u8)`. This is the initial byte, even
though the final byte is `7u8`. An immutable reference uses `ref#0(...)`; pinned
references retain a pin label. IDs describe modeled storage within that
witness, not native addresses. A later alias can appear as `ref#0` without
repeating the same contents. Slice witnesses include start, length and the
selected initial elements. A native replay regression verifies this mutation
example; general automatic witness replay is still future work. These reports
describe modeled inputs, not a complete capture of global or environmental
state. A claim with no named inputs says so explicitly.

Witnesses belong to individual logical claims. A successful negation or
disjunction discards irrelevant failures. A false disjunction of universal
claims may show several numbered witnesses, each establishing failure of one
subclaim with its own storage identity scope; they need not be a single shared
input assignment.

Invariant induction introduces arbitrary loop-head values. Its failure report
therefore labels an **inductive obligation witness** and explicitly says the
initial inputs are not a concrete execution replay. Such a result can show
that an invariant or rank is insufficient without establishing a reachable
bug in the function. Unsupported semantics and solver exhaustion remain
unproved results.

Rendering is bounded to 12 inputs, eight entries per aggregate, 12 nested
levels, 256 visited values, eight compound witnesses and 8192 bytes per rendered
witness payload. Truncation uses an explicit `...` marker. An elided or private value
does not provide a complete replay fixture. Rendering reads the solver's
validated model and frozen state without executing functions or creating new
symbolic gates.

## Properties Lim should prove about real programs

These are targets for symbolic checking, not promises of current support.
Add them as capabilities only when the corresponding execution semantics are
modeled and the checker fails closed for everything outside that model.

- **Function contracts:** universally quantified preconditions and
  postconditions over supported input domains; result, mutated state, and
  ownership-relevant state relations; compositional contracts for calls;
  explicit exceptional or early-return outcomes; and clear distinctions
  between all inputs, precondition-satisfying inputs, and reachable states.
- **Integer safety and intent:** no unintended overflow; exact wrapping or
  saturation behavior; division and remainder safety; signed minimum divided
  by negative one; safe shifts and casts; and preservation of invariants across
  arithmetic. Each property must follow the selected Lim operator semantics.
- **Path feasibility and call sequencing:** whether guards are satisfiable;
  whether authorization, validation, or initialization always precedes an
  action; whether forbidden calls are unreachable; and whether call ordering
  survives helper extraction and interprocedural summaries.
- **Validation freshness:** prove that a checked property still holds at the
  use site for the same object and relevant dependencies. Any intervening
  write, aliasing call, replacement, or external mutation should invalidate
  the fact unless a sound frame condition proves independence.
- **Loops:** inductive invariants for every loop, termination arguments where
  termination is claimed, and safe treatment of `break`, `continue`, and early
  returns. Establish explicit unrolling, path, solver, and wall/resource
  budgets; when any budget is exceeded, return inconclusive rather than
  success.
- **Arrays and slices:** prove every access is in bounds; reason about lengths,
  offsets, and aliasing; establish sortedness, uniqueness, and permutation;
  preserve these properties through updates and loops; and handle empty and
  boundary-sized inputs. Slice and dynamic-size support requires a sound model
  of their runtime representation and operations.
- **References and memory:** establish valid lifetime and provenance for each
  access, separation or permitted aliasing, initialization before read,
  borrow exclusivity, and frame conditions for writes. Unsafe operations need
  explicit models or trusted boundaries; address arithmetic alone is not a
  memory-safety proof.
- **Effects:** specify and check observable IO, global state, allocation and
  deallocation, resource ownership, and failure behavior. A proof must say
  which effects are modeled, which are abstracted, and which invalidate a
  claim; an omitted effect cannot silently be assumed absent.
- **Protocols and resources:** model state machines for files, locks, sockets,
  transactions, handles, and other resources; prove legal transition order,
  cleanup on every exit, and absence of use after close. These proofs require
  a declared state model and effect summaries.
- **Async and concurrency:** when task and synchronization semantics are
  modeled, prove cancellation safety, wakeup and completion obligations,
  race freedom, mutual exclusion, and protocol invariants across interleavings.
  Sequential symbolic execution does not establish concurrent correctness.
- **Counterexamples and inconclusive results:** provide reproducible input
  values and path traces for concrete failures where possible. Distinguish a
  proved property, a concrete counterexample, an unsupported construct, and a
  resource-limited inconclusive result in diagnostics and machine-readable
  output. Never collapse the last two into success.
- **Verification evidence:** independently check solver certificates where
  practical, replay counterexamples against ordinary execution, and retain
  assumptions and source/configuration identities with results. Differential
  testing strengthens the implementation but does not replace a checked
  certificate or establish the correctness of the verifier itself.

## Scope and limits

The checker operates on validated Lim semantics; it does not execute native
code or prove that the compiler, backend, operating system, or external
libraries are correct. Its symbolic model, solver, and resource bounds define
the scope of each result. Every theorem should be read with its assumptions,
modeled effects, and limits in view. Broader proof coverage should follow from
implementing those semantics explicitly, not from treating unsupported
constructs as unconstrained truths.
