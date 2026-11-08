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
  Lim type are not supported. A contract covering no inputs produces a
  nonfatal W8001 warning identifying its impossible precondition or infeasible
  enclosing proof path.
- **Explicit contract reuse.** `#proof-using` selects separately verified
  direct contract theorems for calls in its body. Reference results use checked
  parameter-origin summaries, validated against symbolic return values before
  reuse. Checked store-origin summaries also preserve reference identities
  when a callee changes a reference-bearing pointee. Inputs and results may
  carry references inside owned aggregates.
  Functions cannot implicitly access globals or perform unsafe, IO, allocation,
  external or assembly operations. Owned local and borrowed-target mutation are
  modeled using the caller's actual storage locations.
  The caller must establish the selected precondition on every feasible path;
  the postcondition constrains a fresh result. Contract dependencies are checked
  in topological order, including forward references, and cycles are rejected.
  These summaries describe results and borrowed state, not execution traces.
  Trace claims inspect actual callee bodies even when result/state contracts
  are selected; those contracts cannot hide observed calls.
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
  an invariant rather than iterating through every input value. Calls inside
  the loop body or for-step can use explicitly selected, verified contracts,
  including borrowed inputs and reference results. Argument expressions still
  contribute their writes to the loop's abstract state. Borrowed data is
  abstracted while stable reference identities remain unchanged. When a loop
  changes handles, a bounded graph abstraction covers existing reference
  locations, reference-bearing enum variants and slice geometries instead.
  Trace claims can combine these invariants with finite call-history monitors,
  preserving call order and same-object validation across modeled loops.
  Collection predicates may describe the arbitrary loop-head state: entry and
  every continuing iteration must establish their sortedness, multiplicity or
  uniqueness requirements. Specification comparator calls are isolated from
  runtime trace monitors and retain ordinary specification-call restrictions.
- **Arrays and aggregates.** Small fixed arrays, tuples, records, enums, and
  modeled references can be symbolic values. Directly constructed arrays can
  be checked for sortedness, permutation and uniqueness within a limit. These
  predicates also observe borrowed slices, using only selected elements even
  when range bounds are symbolic. Indexing and
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
- **Checked constants.** Scalar and aggregate global initializers are evaluated
  from their checked ASTs in their own local scope and definition context.
  Normalized compiler spelling does not weaken the canonical syntax rules for
  user-written specifications. Initializer evaluation retains specification
  purity and restores caller access permissions before continuing the proof.
- **Proof reports and failure.** A false obligation reports a counterexample
  when the solver can provide one. Scalar witnesses use typed literal
  spellings. Arrays, records and active enum payloads show their values;
  references and slices identify their initial storage and contents. Repeated
  aliases share an identity, and inaccessible record representations stay
  hidden. Unsupported semantics, malformed proof
  values, circuit errors, and exhausted execution/storage/solver budgets
  report failure or an inconclusive `unproved` result. They do not discharge
  the theorem.
- **Checked SAT refutations.** Nonconstant SAT queries can establish
  unsatisfiability only by returning a clause-derivation certificate. A
  separate checker replays it against the original CNF and previously proved
  clauses, without using the searcher's assignments, watches, decision levels
  or reasons. Invalid derivations and exhausted checking budgets remain
  failures. Satisfying assignments still receive independent circuit-model
  validation.

[`examples/symbolic_slices.lim`](../examples/symbolic_slices.lim) demonstrates
read and mutation contracts over borrowed subranges. Quantify an array or
array reference to bound the backing storage, then call a function with a view
of that array. A contract taking an arbitrary slice directly does not acquire
an implicit length bound. For old contents, put the entire read inside
`#proof-old`, for example `(#proof-old (#index values 0usize))`; saving an old
reference or slice handle alone does not snapshot its referent.

[`examples/proof_collection_views.lim`](../examples/proof_collection_views.lim)
sorts the middle two elements through a mutable slice. Its contracts prove
sortedness of that range, permutation of the old owned array, preservation of
outside elements, and uniqueness when the two input values differ.
`#proof-unique` uses modeled pairwise equality rather than a comparator.
Sortedness calls the named comparator only on selected reversed adjacent
pairs. Empty and singleton ranges need no calls, but the comparator signature
is still checked. These properties do not establish comparator laws or model
unbounded collection storage.
Comparator specifications reject active cycles and have a nesting limit of
four active comparator calls. This bound covers nested specification loops
independently of ordinary call/expression limits. Sequential comparisons do
not accumulate nesting depth. Cycle/depth errors remain resource-limited
results under negation; the checker does not substitute a Boolean result.

[`examples/proof_collection_loop.lim`](../examples/proof_collection_loop.lim)
uses these predicates in a checked loop invariant. Each iteration conditionally
sorts a pair, preserves its multiset and preserves uniqueness. With an unroll
limit of one, the invariant and decreasing unsigned rank prove the contract
for every byte-sized repetition count, including zero. A nonzero count yields
a sorted pair; zero repetitions preserve the original contents. The comparator
is part of the specification, so calls inside it cannot satisfy or violate a
claim about calls made by the program being checked.

## Contract coverage

A universal contract with an impossible precondition is logically true. It
does not establish behavior for any execution. For example, this deliberately
mistaken specification produces W8001, underlining `(#u8::gt value 255u8)`:

```lisp
(#fn identity (: value #u8) #u8
  (#return value))

(#theorem empty-domain
  (#proof-contract identity (#u8::gt value 255u8) false))
```

The checker tests satisfiability across every evaluated precondition branch;
one feasible branch is enough to avoid this warning. A contract reached only
under an infeasible enclosing proof guard has a distinct warning explanation.
This observation does not change the meaning of negation or turn empty-domain
proofs into concrete execution evidence. Nor does a feasible precondition
establish that each runtime branch is reachable: the postcondition must still
hold on every modeled execution admitted by the precondition.

Warnings are published after all program theorems pass, including dependency
theorems not explicitly selected by the command line. They retain source
locations through file aliases and generated code, are recomputed on warm
generator caches, and appear as LSP warning diagnostics. In JSON mode,
`--check-theorem` still writes its success record to stdout; warnings go to
stderr with `"code":"W8001"`, `"severity":"warning"`, `"category":"proof"`
and `"proof_outcome":null`. Library clients collect them with `with_warnings`.
An incomplete coverage query fails with its typed checker/resource diagnostic;
it cannot establish either satisfiability or unsatisfiability by default.
Coverage source mapping is capped at 100,000 nodes per theorem, with at most
1,024 source clauses tracked per theorem. Reporting is capped across all
theorems at 1,024 warnings and 16 MiB of diagnostic storage, including attached
source and generator-provenance snapshots. Exceeding these limits reports
E4403 rather than silently dropping coverage observations or retaining
unbounded diagnostic copies.

## Reusing checked contracts

[`examples/proof_contract_reuse.lim`](../examples/proof_contract_reuse.lim)
proves a countdown helper using an invariant and reuses that contract to check
its caller. The caller has an unroll limit of one, so it cannot prove the result
by expanding the countdown loop for every input:

```lisp
(#theorem work-contract
  (#proof-using (countdown-contract)
    (#proof-loop-limit 1
      (#proof-contract work true (#proof-eq (#proof-result) input)))))
```

Every selected theorem must first prove a direct `#proof-contract`, optionally
wrapped in `#proof-using`, `#proof-with-invariants` or `#proof-loop-limit`.
Negated contracts, implications, disjunctions and arbitrary Boolean theorems
cannot become assumptions. Dependencies may be declared later in a file or
referenced through file aliases. All program safety checks and all theorem
dependencies still run when the command line selects a single theorem.

The selected contract binds actual arguments to the callee's declared parameter
names. Its pre/postconditions use the contract's definition context for private
representations; they do not grant the caller permission to inspect those
fields. `#proof-old` sees the state at that call, and a saved caller result is
restored after checking the summary. Calls written inside the selected
pre/postconditions execute normally, preventing a specification from assuming
itself recursively. Other calls in the scope use the selected summaries.
Only one contract per function may be selected in a scope; selections do not
leak outside the `#proof-using` body. An empty selection list is allowed.

A failed precondition or insufficient postcondition reports E4407
`contract_failure`. An abstract summary result is not a concrete program
counterexample: the checker cannot prove the negation of a contract merely
because the selected summary is too weak. Abstraction tracking is conservative
for the entire theorem, so a later failed claim can also remain unproved after
a summary was used. Strengthen the selected contract or inspect the actual
callee body to obtain a concrete counterexample.

Mutable references define the writable frame. For a call that may mutate,
the checker replaces the contents of each active mutable argument target with
fresh symbolic values, then constrains them with the verified postcondition.
References inside owned records, tuples, arrays and active enum payloads also
contribute targets, including references reached through other references.
Reference handles retain their original locations; storage outside the writable
targets retains its contents. Shared handles do not themselves permit writes.
Subobject and symbolic element borrows affect only those subobjects/elements,
including element references obtained from modeled slices. Heap updates use
the ordinary validation-invalidation path.

A mutable reference to a whole array permits the whole array to change. A
contract must therefore state any unchanged-element guarantees its callers
need; the checker does not infer an exact body write set for the summary.
Purely reading functions preserve all caller storage, including targets passed
through mutable handles. Mutating summaries cannot be invoked from specification
expressions. Trace proofs still inspect bodies to establish call ordering.
[`examples/proof_borrowed_contracts.lim`](../examples/proof_borrowed_contracts.lim)
proves a borrowed-field update and preservation of its sibling field while
reusing a bounded-loop contract under a caller unroll limit of one.

Write frames are bounded to 256 mutable locations per alternative, 256
alternatives and 4096 total writable entries. Exceeding a bound remains an
unproved resource-limit result, including under logical negation.

Returned references retain actual caller locations. The checker substitutes
parameter slots, stored-reference loads, fields, enum payloads and array element
projections from the borrow checker's origin summaries. Returned records, tuples,
arrays and enums retain their reference slots, including array slot correspondence
and checked constructor bounds. Before a reference-returning contract can be
reused, symbolic execution checks that those origins and constructor bounds cover
its actual returned values. Missing, unsupported or incomplete provenance cannot
prove a contract by dropping an execution. Reference-free result data remains
symbolic, including character validity constraints.

Checked providers also retain the conditions selecting possible return origins
and reference-bearing enum constructors. These conditions are captured during
provider verification, checked by replay against the provider circuit, and
published only after the contract succeeds. A compact Boolean template binds
the caller's entry-state argument, aggregate and pointee data. Abstract choices
and inactive input payloads receive fresh bits shared across that invocation's
conditions, preserving correlations between returned components. Calls reuse
the template and checked origin list; they do not re-execute the provider body.
Numeric result fields still require explicit postconditions.

Conditions also distinguish physical subobjects within a single checked origin.
Each array selection in its input-storage and referent projections contributes
the concrete backing-array index to a stable projection sequence. Provider
execution checks each candidate against the reference actually returned or
stored, retaining a condition for that exact source and sequence. Replay resolves
the same projections against caller storage and applies the matching condition.
These indices are relative to the checked input projection, not provider heap
IDs or enumeration ordinals; inactive payloads and aliased caller inputs do not
rename candidates. Missing or invalid projection keys cannot fall back to some
other candidate.

This retains dynamic and computed indices, nested subobjects and physical offsets
through modeled slice ranges. A weak contract can therefore preserve which
location a later write changes even when sibling values happen to be equal.
The same mechanism handles indexed input slots whose references are returned or
stored, and composes through explicitly selected helper contracts.
[`examples/proof_projected_origins.lim`](../examples/proof_projected_origins.lim)
proves that a write through an indexed returned reference changes the selected
byte and preserves its sibling. Native replay checks every byte pair, both
indices and three replacement values, including zero and 255.

[`examples/proof_guarded_returns.lim`](../examples/proof_guarded_returns.lim)
uses a weak contract for a reference selector, then proves that writing its
result changes the selected caller location and preserves its sibling. Native
replay covers every byte pair with both selectors. A correlated tuple of nine
references now keeps the two feasible combinations instead of inventing 512
independent origin combinations.

The same template retains conditions selecting stored reference origins and
reference-bearing constructors, including branches that keep an entry reference.
Stored and returned components share the invocation's abstract choices. Sources
and conditions are bound before any caller memory is freshened, preserving swaps
and references returned from overwritten fields.

Refinement keeps conservative May-origins for mutating functions with exclusive
pinned inputs or possible typed overlap between a parent and an input referent.
The overlap check walks storage physically contained in records, arrays, tuples
and enum payloads, stopping at reference handles. Thus a record containing only
reference handles can be refined, but an inline byte plus a reference to a byte
can conceal a self-alias and retains the conservative model. Fresh roots alone
never establish absence of internal aliases. Array accesses to reference-bearing
element types use the guarded path splitting described below. Templates are
kept in RAM for the current checked program, not persisted as proof caches.
Limits include 256 captured origin/constructor conditions per provider and
64 MiB of retained templates/bindings across providers. Input binding storage
is checked before retaining more descriptors. Replay consumes the existing
evaluation and circuit budgets; exhausted or invalid replay remains unproved.

Several possible origins and projection sequences remain separate alternatives,
capped at 256, and each retained condition counts toward the provider's condition
and byte limits. Providers without checked conditions retain conservative
May-origins. Equal referent contents do not establish identity; location
refinement comes from the verified provider's selection conditions. A caller's
write-through-reference property remains unproved if those conditions or the
modeled frame cannot establish it. Negation cannot turn uncertainty or a resource limit into
a proof. [`examples/proof_reference_contracts.lim`](../examples/proof_reference_contracts.lim)
demonstrates a projected mutable return updating its caller while preserving a
sibling field; native replay tests every byte value, including wraparound.

[`examples/proof_loop_contracts.lim`](../examples/proof_loop_contracts.lim)
combines a helper contract with an invariant and decreasing rank. Its loop
calls `decrement`, whose selected contract requires a positive input and
guarantees subtraction by one. The loop guard establishes that precondition;
the helper's postcondition establishes strict decrease. The checker proves the
countdown result for every byte input with an unroll limit of one. Omitting the
selected contract leaves the helper call unsupported. A weak postcondition or
an unestablished precondition remains unproved, including under negation.

[`examples/proof_borrowed_induction.lim`](../examples/proof_borrowed_induction.lim)
uses a memory contract inside a loop over a borrowed record. Its invariant
preserves a sibling field while the helper's postcondition establishes decrease
of the borrowed counter. The proof covers every byte input with one abstract
iteration; native replay checks all byte values as well.

The stable induction path separates stored reference handles from numeric data. Possibly
written owned roots and targets reachable through mutable handles receive fresh
symbolic contents. Handles keep their original locations, including references
inside records, arrays, tuples and active enum payloads. A mutable borrow created
inside the loop contributes its source root to the write frame; an alias cannot
hide a loop-carried update. Updates use ordinary heap writes and invalidate
affected validation facts. Readonly loops retain their borrowed contents.

[`examples/proof_trace_induction.lim`](../examples/proof_trace_induction.lim)
checks three execution properties for every byte count with an unroll limit of
one: each action has a successful validation of that same object, validation
completes before the action, and a failed validation excludes actions. Trace
proofs execute the actual bodies of checked helpers, including calls in a
for-step. Helpers must have modeled effects; implicit globals, unsafe code, IO,
allocation, external calls and assembly remain unsupported in induction.

The trace analysis computes a fixed point of call-history states under the
supplied invariant. Backedge guards retain entry-input conditions and forget
arbitrary values introduced for an iteration. The checker verifies that this
abstraction does not omit any transition. Exact zero-iteration exits and
post-iteration exits preserve the call history and validation facts needed by
later code. Entry/preservation and unsigned strictly decreasing rank checks
remain mandatory for continuing paths.

Validation within an iteration tracks storage identity and write dependencies.
New validation facts are conservatively discarded on backedges. Prefix facts
can survive readonly loops that never call the validator; they are discarded
at abstract heads if a loop may call it, since a later failure could revoke an
earlier success. Protocols relying on a validation from a previous iteration
need an explicit evidence invariant, described below. This is a conservative
model, not a general temporal logic. Abstract violations are induction failures,
including under negation, rather than claimed concrete executions. The history analysis is
bounded to 64 fixed-point waves, 256 retained exit paths and 64 MiB of retained
exit states, in addition to the existing graph, circuit and evaluator limits.

[`examples/proof_cached_validation.lim`](../examples/proof_cached_validation.lim)
validates once and reuses that evidence on later iterations. Its invariant
connects the program's cached Boolean to the object it describes:

```lisp
(#proof-with-invariants
  ((process again
    (#proof-implies checked
      (#proof-validated (#parameter-of validate user) user))
    remaining))
  (#proof-requires-validation process
    (#parameter-of validate user) (#parameter-of perform user)))
```

`#proof-validated` requires evidence for that same storage object from the
claim's exact validator and parameter. It is checked against actual validation
facts on loop entry and after each continuing iteration. At an arbitrary head,
the checker introduces symbolic evidence and assumes the supplied predicate,
then executes the body and proves preservation. No runtime fields or checks are
added. Updating an object or a referenced dependency revokes its evidence;
failed revalidation does too. A program must clear or reestablish any cached
flag whose invariant would otherwise claim stale evidence.

Evidence is a lower bound on successful validation, rather than an exhaustive
history log. Requirements may occur positively under `#proof-and`, `#proof-or`,
the consequent of `#proof-implies`, or branches of pure `#if`/`#match` forms.
They cannot be negated, compared, placed in an implication's antecedent, used
as conditions or ranks, or queried outside loop predicates. This restriction
prevents omitted evidence from becoming a proof that validation never happened.
Different queried locations may alias: seeding a later location excludes aliases
already represented, and failed checks or writes revoke all matching evidence.
The existing fact/dependency limits also apply to these symbolic requirements.

Separate fresh referents model input contents; they do not prove that shared
parameters denote different objects. Failed revalidation through another
possibly aliased shared input conservatively revokes prior evidence, including
for subobjects and references reached through shared parents. Writes revoke
possibly overlapping dependencies too. Exclusive inputs retain the ordinary
borrow checker's disjointness guarantees; a mutable reference stored behind a
shared parent is still potentially aliased through that parent. Successful
revalidation preserves prior evidence even when the objects might alias.

This guard does not enumerate every input alias relationship. A failed claim
that depends on those conservative revocations is reported as unproved, not a
concrete execution counterexample, and negation cannot turn it into a proof.
An explicit caller passing the same object supplies a known identity and can
produce a concrete counterexample.

For ambiguous validation claims over shared Boolean, character and integer
referents, the checker can now enumerate the possible scalar input identities.
The conservative check remains the fast path. Only a typed input-alias failure
triggers this refinement; unrelated unsupported operations and resource errors
never do. Each partition maps references to canonical storage, constrains
aliased input values to agree, and records which remaining scalar roots are
distinct. Owned records and tuples may carry those shared scalar references.
If any new referent is a parent aggregate, reference, slice, raw pointer
or zero-sized object, scalar enumeration alone is incomplete and the
conservative guard remains in force. This includes exclusive pinned parents:
retained references can point to their own fields. Typed in-place projections
preserve these possible internal aliases during the conservative check, too.
Globals and earlier origins also retain their uncertainty.

[`examples/proof_input_aliases.lim`](../examples/proof_input_aliases.lim)
proves a negative theorem: some caller can invalidate validation of `second`
through `first`, then call the action. The concrete witness gives both inputs
the same `ref#` identity. Negating the universal protocol claim asserts that
such a counterexample exists; it does not assert that every caller fails.
Equal-valued, distinct objects and actual aliases remain separate cases.

All enumerated cases are checked, with existing invariant, unsupported-operation
and solver failures still propagating. Partial exploration cannot establish a
claim or its negation. Limits are 64 relevant scalar roots, 256 cases and 64 MiB
of retained cases including argument values. Work and circuit budgets remain
cumulative across the conservative attempt and refinement. SAT search and
query preparation have a cumulative 64-million-work-unit limit per circuit;
individual searches and certificate production/checking retain their separate
phase limits. Resource exhaustion is sticky, including for subsequent trivial
queries. General aggregate, subobject and heap alias enumeration remains open.

The checker can exclude same-object identity when modeled immutable contents
differ. Failed revalidation is therefore guarded by a necessary equality of
scalar fields, arrays, tuples, enum tags and active payloads. Reference fields
contribute no address or pointee comparisons, and slices contribute only their
stored length: modeled backing roots and relative offsets do not establish
distinct addresses. Equal contents never establish identity or authorize an
action on an unvalidated object. Writes retain the broader conservative
dependency invalidation described above.

[`examples/proof_distinct_validation.lim`](../examples/proof_distinct_validation.lim)
demonstrates a useful consequence without extra source annotations. A pure
validator checks a user's immutable ID. Rechecking one input preserves earlier
success for the other: if the objects alias, their contents
and check results agree; if results differ, their contents distinguish them.
The invariant connects the cached success to that same user across iterations.
Native replay covers all byte counts with both validation outcomes, including
explicitly aliased inputs. The bounded symbolic proof covers all modeled input
values, rather than only those native samples.

Before establishing preservation or forwarding a loop exit, the checker verifies
that existing reference identities and tags of reference-bearing enums are
unchanged. Slice handles also retain their backing location, start and length.
Changes leave this stable path and trigger the bounded graph model described
below. Frame discovery is bounded
to 256 writable regions, 4096 visited values and nesting depth 32. These are conservative
frames: an invariant must state any unchanged sibling data needed after the loop.

[`examples/proof_reference_induction.lim`](../examples/proof_reference_induction.lim)
proves a loop that replaces a reference stored in a borrowed struct. A zero
count preserves the original contents; every positive count selects the
alternate reference's contents. Native replay checks all 65,536 combinations
of byte seeds and counts. Related tests prove clearing and populating enums
with reference payloads, including their pointed-to contents, and shrinking a
slice stored in a borrowed struct until it is empty.

For changing graphs, candidates come from existing handles, their projected
storage and explicitly borrowed sources. Shared sources do not grant mutable
access. Abstract references select those locations; fresh unrelated referents
are never allocated. Enum alternatives include absent and present payloads.
Slice alternatives retain array backing and enumerate bounded valid ranges.
All potential mutable targets contribute to every loop head's write frame,
including targets written by earlier iterations and later lost by retargeting.
Conditional payload writes and symbolic indices conservatively widen to
enclosing initialized storage.

The checker verifies graph coverage on entry, continuing steps and forwarded
exits, then checks the supplied invariant and decreasing rank. Equal contents
do not establish reference identity. A reference to storage outside the
catalog, an insufficient invariant or exhausted budgets leaves the theorem
unproved, including under negation. Reference choices and widened frames are
conservative; some valid programs need stronger invariants or remain outside
this model. General heap allocation and environmental references are not
inferred from this bounded storage model.

Graph catalogs are limited to 4,096 locations and 4,096 existing handles;
write frames to 256 regions; graph combinations to 256; and type/layout nesting
to 32. Catalogs and retained combinations also have separate 64 MiB charged
representation budgets, checked before cloning combinations. Large type names,
potential enum payloads and source-frame metadata contribute to those budgets.
Readonly enum matches in invariants use the ordinary `#match`/`#case` syntax,
with scoped payload bindings, no shadowing, one pure value per case and at
most 256 cases. Blocks, user calls and effects remain unsupported there. LSP
navigation retains the usual variant and payload-binding scopes.

[`examples/proof_slice_induction.lim`](../examples/proof_slice_induction.lim)
proves that a slice loop completes, sets every selected byte to zero and
preserves every backing element outside its input range. The array's contents
and the slice's start and end remain symbolic; the three-element backing array
provides the finite storage bound. The invariant bounds the remaining count
and states that each processed cell is zero. Each access, the invariant's
preservation and the decreasing rank are checked with an unroll limit of one.
Omitting a processed-cell clause or writing a nonzero value leaves the theorem
unproved, including when the contract is negated.

Read-only implications retain guarded bounds checks but combine their results
into a Boolean formula, avoiding a separate execution state for every true or
false premise. This does not skip malformed expressions under false premises,
erase counterexample evidence or admit effectful specifications. During
induction, slice indexing can enumerate concrete backing locations under
checked start/index guards. Missing feasible paths and exhausted solver or
execution budgets still cannot establish a theorem.

Mutable slice frames use guarded element updates: only membership in the
selected range permits fresh data. Nested views and slices in aggregates keep
their storage identity. References or slices stored inside selected elements
contribute reachable targets under the same membership guard. Empty ranges,
including one at the end boundary, permit no element writes. Overlapping frames
merge updates against current storage rather than restoring old snapshot data.
Native replay checks all valid ranges of the example's array and every byte
seed, including the actual clearing behavior.

Invariant predicates, ranks and loop conditions remain restricted to pure
expressions; general user-call expressions, bindings and statement blocks are
not permitted. Modeled slice views, lengths and element reads, explicit array
values, and collection predicates are permitted. The named sortedness
comparator retains specification-call checks and does not record program
trace events. Its own calls and execution still consume proof budgets.
Direct unbounded slice inputs remain unsupported: construct a view from a
bounded array in the proved wrapper or quantified call. Selecting a reusable
contract still does not provide an implicit slice bound. Changing reference
graphs or view geometry, global write destinations and implicit environmental
effects need additional models.

Stored references use the borrow checker's final store-origin summaries. A
definite replacement can discard the entry reference; a possible write retains
both the old and replacement alternatives. Sources are loaded from the call-entry
snapshot before any replacement is applied. This preserves swaps and references
returned from overwritten slots. Before reuse, symbolic execution checks that
the summaries cover the actual stored reference identities. Equal referent
contents do not justify substituting a different location. Missing origins and
unsupported destinations remain unproved.

For eligible providers, guarded store conditions refine the possible-source set.
The conditions come from checked provider execution, not declarations trusted
from the caller. A no-write branch selects the entry source; a replacement
selects the checked new source; enum constructors and payload identities retain
their shared condition. The same substitution preserves correlations through
explicitly selected transitive contracts.

[`examples/proof_guarded_stores.lim`](../examples/proof_guarded_stores.lim)
proves that a conditional replacement returns either the new referent's byte or
the preserved entry byte, reusing a provider with a `true` postcondition. Its
native replay checks every byte pair with both branches. The test suite also
covers swaps, enum payloads, returned retired references, aliased caller inputs,
wrong claims and negation.

Array indexing splits handle-bearing element types into separate executions for
each feasible concrete index. The test follows the declared element type,
including reference-bearing aggregates, inactive enum payload types and slice
handles. Every access first proves its full bounds obligation under the current
path condition; enumerating valid elements cannot erase an out-of-bounds
execution. Each resulting guard retains the original index equality, and the
selected reference keeps its actual caller location. Numeric elements retain
compact multiplexers instead of creating a path per element.

This supports symbolic-index reads, direct writes, borrowed element targets and
reused contracts that conditionally replace a selected reference-bearing slot.
The selected slot changes while siblings retain their prior handles; repeated
and independent indices preserve last-write ordering. Nested indices compose
their guards. Concrete projection writes skip unselected array elements before
descending into fields or payloads, so an unrelated absent enum payload is not
inspected or modified. The existing evaluation, solver and path limits apply;
handle-bearing arrays are capped at 64 elements, including directly constructed
arrays. These are finite execution splits, not an unbounded array model.

[`examples/proof_dynamic_reference_arrays.lim`](../examples/proof_dynamic_reference_arrays.lim)
proves both selected and sibling values after a conditional indexed store,
reusing a weak provider contract. Native replay checks all byte pairs with both
indices and both store/no-store branches. Adversarial checks retain bounds and
resource errors under negation, reject incorrect sibling claims, and exercise
independent writes, nested indices, enum payloads and slice backing selection.

Postconditions must still specify numerical contents and unchanged sibling data
that a caller needs. Store provenance describes locations, not arbitrary scalar
relations. Composed store alternatives are capped at 256 paths and 4096 prepared
replacements. Providers excluded by the parent-alias or pinned-input guard retain
the checked possible-source set without conditional refinement.

Direct slice parameters/results, raw pointers, implicit global
access (including named global constants) and external effects remain outside
reusable summaries. Ordinary symbolic execution supports some of these cases
without summary reuse. General input-alias relationships, complete environment
models and general counterexample replay remain open work.

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

Invariant induction introduces arbitrary loop-head values. A failed induction
obligation is **unproved**, not a refutation of the function contract. Its
report labels an **inductive obligation witness** and explicitly says the
initial inputs are not a concrete execution replay. This result stays unproved
under negation or other logical composition; it cannot certify the opposite
contract. A sufficient invariant can still establish the contract. Unsupported
semantics and solver exhaustion also remain unproved results.

Rendering is bounded to 12 inputs, eight entries per aggregate, 12 nested
levels, 256 visited values, eight compound witnesses and 8192 bytes per rendered
witness payload. Truncation uses an explicit `...` marker. An elided or private value
does not provide a complete replay fixture. Rendering reads the solver's
validated model and frozen state without executing functions or creating new
symbolic gates.

## Structured outcomes

`CheckedTheorem.outcome`, `Diagnostic::proof_outcome()` and
`TheoremFileError::proof_outcome()` expose typed results. The checker assigns
failure kinds where they occur; identifiers, diagnostic wording and added
context cannot change the classification.

| Outcome | Code | Meaning |
| --- | --- | --- |
| `proved` | Success | The checked obligation holds in the supported model. |
| `counterexample` | E4401 | A model refutes a supported obligation. |
| `unsupported` | E4402 | Required execution or specification semantics are not modeled. |
| `resource_limit` | E4403 | A circuit, solver, execution, path or storage bound was exceeded. |
| `invalid` | E4404 | The proposition or theorem selection is invalid. |
| `induction_failure` | E4405 | Supplied invariants or a rank do not establish the obligation. |
| `checker_error` | E4406 | The checker encountered an internal inconsistency or invalid solver model. |
| `contract_failure` | E4407 | Selected contract preconditions or postconditions do not establish the caller's obligation. |

Unsupported operations, resource limits, invalid propositions, failed induction,
contract failures and checker errors are errors rather than false Boolean
propositions. Logical negation cannot turn them into proofs. Concrete counterexamples can still
refute a universally quantified assertion, including one explored through
bounded execution. [`examples/proof_induction.lim`](../examples/proof_induction.lim)
shows a sufficient sum invariant and a decreasing rank for every `#u8` input.

Program parse/type/borrow failures are separate diagnostics with no proof
outcome. E4400 remains a generic unclassified proof diagnostic for string-only
interfaces or manually constructed diagnostics; it does not imply a
counterexample. Use the structured APIs when the distinction matters.

For command line tools, request JSON explicitly:

```sh
lim --check-theorem examples/proof_induction.lim identity-contract --diagnostic-format=json
```

The successful check writes this result to stdout:

```json
{"schema_version":1,"category":"proof","theorem":"identity-contract","proof_outcome":"proved"}
```

Failed checks exit unsuccessfully and write a JSON diagnostic to stderr with
`proof_outcome`, the code, source location and labels. Timing output stays on
stderr. Ordinary text output remains available without the JSON option. LSP
diagnostics carry the typed value in `data.proof_outcome` as well as the
diagnostic code. These are reports from the current full-program check, not
exported full-program proof certificates. SAT refutations are independently
checked in memory during that check.

## SAT evidence

The circuit layer retains the immutable original query CNF outside the
searcher. The searcher emits derived clauses and ordered clause hints tied to
that CNF; a valid refutation of a different query cannot establish this one.
To check a derived clause, the certificate checker assumes its
negation, then follows the hints. Each hinted clause must already be proved
and must either be satisfied, force one literal, or contradict the current
assumptions. A clause with several distinct unset literals cannot justify an
assignment. Every derivation must finish with the empty clause, establishing
that the query has no model.

The checker uses its own assignment array and clears only touched entries
between steps. It does not run SAT search or reuse the searcher's backtracking
and propagation implementation. Original duplicate and tautological clauses
retain their identities even when search normalizes them. Self/forward hints,
out-of-range variables, zero literals, fabricated learned clauses and missing
contradictions fail with E4406. Only literal Boolean constants can settle a
query without invoking search or constructing this certificate.

Search retains its existing 2,000,000-unit work limit and 100,000 learned-literal
limit. Certificate input/storage is capped at 2,000,000 charged clause, literal
and hint entries. Certificate production and checking each have a separate
2,000,000-unit work budget, with at most 100,000 variables. Exhaustion is E4403
and remains sticky at the circuit boundary. `--timings` reports the aggregate
checking time as `proof.sat_certificate`.

These certificates cover CNF unsatisfiability. They do not establish the
correctness of symbolic execution, bitvector encoding, theorem assumptions or
the native backend. Certificates are currently consumed in memory; portable
proof exports, source/configuration identities and general native
counterexample replay remain separate work.

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
- **Behavioral equivalence:** compare an optimized implementation with a
  simple reference implementation over the same modeled inputs and effects;
  prove encoder/decoder round trips, representation conversions, and helper
  extraction preserve results and externally visible state. Equivalence must
  include early exits and error behavior, not just successful return values.
- **Failure atomicity:** prove invalid inputs and failed operations leave
  protected state unchanged, return the specified error, and never perform a
  forbidden action. Allocation and IO failures require explicit nondeterministic
  effect models before these properties can cover them.
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
