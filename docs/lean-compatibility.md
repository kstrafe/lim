# Lean compatibility and the Fermat port roadmap

Lim currently provides shared theorem-declaration syntax, a small constructive
dependent kernel, and an adapter for accepted procedural obligations. This is a
foundation for further work, not a replica of Lean, a Mathlib port, or a completed
proof of Fermat's Last Theorem (FLT). The full FLT proof remains unimplemented
in Lim. The [kernel guide](kernel.md) describes the supported rules and bounds;
the [language reference](language.md#constructive-mathematical-proofs) lists the
public syntax.

## Pinned upstream reference

The reference development is
[anthropics/fermats-last-theorem, commit `6e837e75355538c7f80bab5b956861e86c4eacc2`](https://github.com/anthropics/fermats-last-theorem/commit/6e837e75355538c7f80bab5b956861e86c4eacc2),
committed September 24, 2026. This is a reproducible reference revision, not a
moving branch name or a claim that its proof has been imported.

| Input | Pin or source |
| --- | --- |
| Lean toolchain | `leanprover/lean4:v4.33.1`, in the pinned [lean-toolchain](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/lean-toolchain). |
| Mathlib | Commit `db584cd6d46c92f209a44c0f1c829460d327499d`, required by the pinned [lakefile.lean](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/lakefile.lean). |
| Formalization metadata | [formalization.yaml](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/formalization.yaml), including scope, axiom dependencies, and license. |
| Target and axiom audit | [FinalCheck.lean](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/FinalCheck.lean), including the pinned natural-number statement and the Mathlib target. |

Upstream reports a completed Lean proof, 29,511 documented theorems, a
37.8 GB exported environment, individual build modules needing up to 36 GB,
and a recommendation to allow 300 GB for comparator replay. These are upstream
reports, not checks reproduced here.
[Source: pinned README](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/README.md).

The full development under consideration is roughly 13 million source lines;
that planning scale has not been independently counted in this task. A full
port includes the transitive mathematical dependency closure, not only the
short final theorem declaration.

## License and provenance

The metadata identifies the project as Apache-2.0, and the pinned
[LICENSE](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/LICENSE)
contains the license. The project's
[NOTICE](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE)
and [ATTRIBUTION.md](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md)
record material derived from the Imperial College London FLT project,
flt-regular, and Mathlib. The license and axiom inventory are also recorded in
[formalization.yaml](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/formalization.yaml).

The local FLT artifact expresses a mathematical statement and copies no
upstream FLT proof text or source code. Small genuine Lean export fixtures now
include foundational declarations from Lean's `Init.Prelude`, with exact source
hashes, module mappings, the original notice and preserved license texts in
[their provenance manifest](../tests/fixtures/lean_export/real-provenance.json).
A future FLT source or term import must keep a
provenance manifest with exact revisions, source declarations, licenses, and
applicable notices and attribution; generated translations must be identified
as translations rather than original upstream files.

## What the local FLT file establishes

[theorems/fermat_statement.lim](../theorems/fermat_statement.lim) defines
addition, multiplication, and exponentiation on mathematical Nat using
structural natural-number recursors. It then defines the closed proposition
`fermats-last-theorem-statement` as a `#math-definition` with type `#pt-prop`.
Its mathematical content is:

```text
for all a, b, c, n : Nat,
  Eq Nat
    (add (power (succ a) (n + 3)) (power (succ b) (n + 3)))
    (power (succ c) (n + 3))
  -> False
```

Here `n + 3` is represented by three successors. The bases `succ a`, `succ b`,
and `succ c` range over all positive naturals; the exponents range over all
naturals at least three. These quantifiers are unbounded mathematical Pi types,
not machine integers, bounded samples, or a finite-exponent result. Equality
implying False expresses the required inequality constructively.

Checking that definition establishes that the proposition is well typed. It
does not produce a term inhabiting the proposition. There is no FLT theorem or
certificate in this file, and no full upstream proof has been translated.
The intended correspondence to the upstream positive-natural statement is
visible in the formula; it has not been established by an imported proof or a
cross-kernel equivalence certificate. The upstream target and its comparison
with Mathlib are specified in
[FinalCheck.lean](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/FinalCheck.lean).

In particular, this must fail because the selected declaration is a definition:

```sh
lim --check-theorem theorems/fermat_statement.lim fermats-last-theorem-statement
```

A successful parse or normal validation of a proposition-valued definition must
never be reported as verification of FLT. Defining a proposition, checking
bounded examples, or trusting the upstream result by name is not a proof port.

## Shared declarations and theorem checking

The public mathematical theorem form is:

```lisp
(#theorem nat-reflexive
  (#universes)
  (#parameters (#parameter n #pt-nat))
  (#statement (#pt-eq #pt-nat n n))
  (#proof (#pt-refl #pt-nat n)))
```

The procedural shorthand is `(#theorem NAME CLAIM)`. Data definitions use
`(#math-definition NAME (universes...) TYPE VALUE)`; regular inductives use
`(#math-inductive NAME (universes...) (parameters...) SORT (constructors...))`,
and indexed inductives add a nonempty `#indices` telescope and constructor
result indices. The regular syntax remains unchanged.
`#proof` is only a theorem evidence clause. Private kernel wrappers are not
public declaration syntax. The inner `#pt-` language remains explicit, including
universe instantiation, typed binders, applications, and induction.

`lim --check-theorem INPUT NAME` loads the input through normal import and cfg
resolution and validates all obligations before accepting an actual theorem
target. It rejects definitions, missing or cfg-excluded targets, false or
unproved claims, and other validation failures. It emits no native outputs.
Sharing a declaration shape and a check command does not provide Lean source
compatibility, elaboration, tactics, or Mathlib declarations.

## Kernel and environment gaps

| Required area | Current boundary | Work needed for a full port |
| --- | --- | --- |
| Inductive families | Regular and indexed families with explicit index telescopes, direct recursion and strictly positive function fields using terminal `#pt-self`/`#pt-self-at` codomains under zero or more `#pt-pi` binders. Checked `#pt-let` wrappers along Pi codomains are allowed only when their annotation and value contain no current-family occurrence; both are checked before zeta substitution and positivity continues in the instantiated body. Function domains cannot contain the current family, including double-negative positions. Recursive aliases in definitions, recursion hidden in primitive Sigma types or arbitrary type functions, and current-index occurrences remain unsupported. Native nested declarations use previously checked nominal container constructors and explicit physical type selectors in #pt-nested-induct. Explicit mutual groups have shared universes/parameters/sort, independent index telescopes, atomic positivity validation and family-specific motives/IHs/computation. Mutual predicates only eliminate into Prop; unit/K/record shortcuts exclude group components. Index types scope over parameters and earlier indices; fields over parameters and earlier fields; result indices over parameters and all fields. Exact arity and universe checks apply. | Audit positivity, fibre-sensitive recursors, and computation against imported elaborated terms; audit scoped nested replay against the full dependency closure and the emitted nested-case source wrappers against that closure. |
| Universe theory | Explicit general Sort via #pt-sort, Prop and Type aliases, successor, max, and imax; Pi sorts use imax and symbolic level relationships are checked for all nonnegative assignments under bounded work budgets. Under the zero-family-sort guard, empty inductives and single-constructor inductives whose every non-proof field occurs directly as a bare variable among the constructor result indices may eliminate into data universes; proof fields need no such exposure. Computed or partial exposure and multiple constructors do not qualify. No universe inference, cumulativity, or type-in-type. | Integrate these rules into a version-pinned importer and audit them against the complete elaborated dependency closure. Full-environment translation, resource scaling, and replay remain open; these universe features alone do not complete the FLT port. |
| Conversion | Beta, transparent delta, typed-local-let zeta, iota, primitive Sigma projections, J, and typed definitional proof irrelevance for well-typed proofs of the same proposition. Symmetric type-directed Pi/Sigma eta compares any two same-typed terms through fresh applications or dependent projections, with rigid neutral head/subject comparison preventing repeated expansion. It retains shifted binder contexts and fully infers source evidence before reduction; opaque theorem bodies stay opaque. Unit-like data conversion and fieldless neutral data recursion require an unindexed, fully applied one-constructor zero-field family. Indexed zero-field singleton propositions also admit neutral computation when their supplied indices convert to the specialized constructor indices; indexed data and mismatching fibres do not. Checked projections and typed fieldwise eta apply to unindexed, nonrecursive single-constructor mathematical records; neutral recursors respect the reconstruction when its projections are legal. Guarded checks prevent extracting data from Prop. No indexed/recursive record eta or cumulativity. | Audit the implemented rules against imported elaborated terms and the full dependency closure; implement any remaining required conversion behavior explicitly. This capability is not full Lean conversion parity or an FLT proof port. |
| Quotients and axioms | Checked quotient computation and an explicit fixed native logical basis. Opt-in replay accepts only the three pinned axiom signatures through checked opaque adapters for nominal equality and nonemptiness. Native inventories must match the imported target's transitive closure; default replay rejects axioms and there is no generic admission interface. | Audit the full dependency closure against this fixed basis, preserving exact statement correspondence and rejecting any additional foundation. |
| Mathematical environment | Small explicit definitions and theorem terms; no Mathlib import. | Translate the full dependency closure, preserving declaration identity, types, universes, bodies, constructors, and recursors. |
| Source and elaboration | Explicit Lim theorem terms, without a Lean elaborator or tactic engine. | Export already elaborated Lean proof terms, then implement a version-pinned translator and term checker; parsing Lean surface syntax alone is insufficient. |
| Dependency and axiom audit | Local dependency ordering and checked procedural adapters. | Produce a complete source-to-target declaration map, dependency graph, axiom closure, and reproducible replay report for the actual FLT target. |
| Storage and checking scale | Small per-declaration and global budgets documented in the kernel guide. | Design streaming import, bounded working sets, dependency storage, conversion caching, and measured resource budgets without trusting unchecked cached declarations. |

General Sort and `imax` cover a universe prerequisite, not all of Lean's
kernel. The mathematical level and Pi rules are referenced against the pinned
Lean 4.33.1 [level implementation](https://raw.githubusercontent.com/leanprover/lean4/v4.33.1/src/kernel/level.cpp)
and [type checker](https://raw.githubusercontent.com/leanprover/lean4/v4.33.1/src/kernel/type_checker.cpp).
Level variables have unbounded natural-number semantics and exact symbolic
order checks, not sampled instantiations. Representation limits are 65,535 for
constants and affine offsets, 256 normalized monomials and 64 nonzero guard
variables per term. Normalization permits 200,000 work units per operation;
comparison permits 50,000 per inequality, independently of the 200,000-step
core budget per term declaration and the unchanged 32-source-parameter limit.
Exhaustion returns an error, never an accepted theorem. These bounds are
resource limits, not a finite model of universe values.

Guarded large elimination requires a proposition-valued motive whenever the
family sort is zero, unless the family is empty or has one constructor whose
non-proof fields all occur directly as bare variables among its result indices.
Proof fields satisfy the universe-zero implication without index exposure;
computed or partial exposure and multiple constructors do not qualify. Matching
family and motive variables retain their correlation; independent levels must
satisfy the condition for every assignment. This follows Lean 4.33.1's
[`elim_only_at_universe_zero`](https://raw.githubusercontent.com/leanprover/lean4/v4.33.1/src/kernel/inductive.cpp#L483-L536)
rule. Type-valued accessibility recursion is now allowed when its data field
is exposed by the constructor result index and its recursive field is
proof-valued. The [accessibility example](../examples/proof_accessibility.lim)
defines `well-founded-recursion (u v)`, proves the generic
`well-founded-recursion-unfolds` equation, constructs `no-predecessors (u)` as
actual accessibility evidence, and proves `empty-relation-recursion-computes`
for every Nat. The focused 11-test suite passes, including the complete
example; a negative poison case that mis-types the pointwise induction
hypothesis for `lower` as data is rejected with a type mismatch. Full-environment nested replay, quotient soundness, a full Lean
importer, and the FLT port remain open. Lim's kernel is not formally verified
and this does not establish full Lean parity.

Typed definitional proof irrelevance is now supported for well-typed proofs of
the same proposition, following the concept in Lean 4.33.1's
[`is_def_eq_proof_irrel`](https://raw.githubusercontent.com/leanprover/lean4/v4.33.1/src/kernel/type_checker.cpp#L870-L879).
Conversion retains the local typing context through dependent Pi, lambda, and
Sigma binders and checks the shared proposition, rather than relying on syntax
alone. Proposition types and distinct opaque native-program fact atoms are not
identified by this rule. Data and generic Sort-polymorphic values remain
distinct unless their type's sort is provably zero. Opaque theorem bodies stay
opaque, and the rule introduces no axiom, admit, or tactic.

Typed function eta (`f` versus `lambda x. f x`) and primitive dependent Sigma
pair eta (`p` versus its first/second reconstruction at the same Sigma type)
are supported in both directions as type-directed rules for any two terms
of a shared Pi or primitive Sigma type. Neither side must be an explicit
constructor. Functions compare fresh applications, while pairs compare
dependent projections; rigid neutral head and subject comparison avoids
repeated eta expansion. Neutral Sigma values containing only proof fields
therefore convert consistently with proof irrelevance.

Conversion checks the shared type, shifts terms and contexts through binders,
and fully infers source evidence before reduction. Fresh applications must
definitionally compare; arbitrary pointwise equality proofs alone do not
suffice. The [eta regression suite](../tests/kernel_eta.rs) and
[kernel context tests](../src/proof/kernel/core_tests.rs) cover symmetry,
dependent indices, context shifts, and ill-typed negative cases. These rules
do not unfold opaque theorem bodies. Unindexed, nonrecursive single-constructor
mathematical records now have checked projections and typed fieldwise eta,
including neutral records and proof-field transitivity. Dependent field types
substitute earlier projections, and guarded Prop checks forbid hidden witness
extraction. Indexed/recursive projection targets remain unsupported.
Cumulativity remains unsupported; quotient-soundness export replay requires
the explicit fixed foundation policy, while quotient
computation uses separate checked primitives. This is not full Lean eta or conversion parity. The implemented
kernel is not formally verified, and these changes do not supply the missing
FLT proof.

A separate unit-like data rule compares well-typed values of a fully applied,
unindexed user datatype with exactly one zero-field constructor, including
neutral variables, neutral results, and constructor values. Indexed families
are excluded because their indices identify distinct fibres. The rule is symmetric
and universe-polymorphic, with the same nominal family, checked parameters,
and universe instantiation required. It does not equate datatype types,
different families or parameter/level applications, data-bearing or recursive
constructors, Nat, or False. Neutral recursors for qualifying unindexed data
reduce to the sole branch, consistently with the existing fieldless
singleton-Prop rule; indexed data families receive no such optimization.
Pi and primitive Sigma eta compose with these value rules and proof irrelevance
through proof or qualifying unit-like components, after source typing has been
checked. Mathematical record eta and neutral record recursor computation are
separately checked for unindexed nonrecursive single-constructor families,
with guarded restrictions against projecting data from proofs. The full FLT
proof and the other compatibility gaps remain open.

For indexed propositions, a one-constructor zero-field recursor can compute
on a neutral proof when its supplied indices definitionally match the
constructor's result indices after parameter and universe specialization.
Generic or mismatched fibres remain stuck, as do fielded propositions and
indexed data. Typing checks precede this computation, and opaque theorem
bodies remain opaque. This follows the shape of Lean's restricted
[`init_K_target`](https://raw.githubusercontent.com/leanprover/lean4/v4.33.1/src/kernel/inductive.cpp#L552-L573)
criterion; it is not an admission rule or a completed Lean importer.

Typed local lets are supported as
`(#pt-let (#parameter NAME TYPE) VALUE BODY)`, with annotation and value in the
outer scope and the name bound only in the body. No existing local or universe
parameter may be shadowed. The checker establishes the annotation's sort and
the value's type, then substitutes the value before inferring the body;
weak-head normalization performs zeta reduction. This supports true type
aliases and is not implemented semantically by merely lowering to a lambda
application. Even an unused invalid value or a budget failure rejects the term.
There is no implicit typing or recursion. A local let is not a standard Lean
term importer, and does not discharge the missing dependency closure or FLT
proof.

The pinned metadata lists `propext`, `Classical.choice`, and `Quot.sound` as the
axioms used by the upstream full result. Lim now supplies three fixed native
foundation constants referenced explicitly with `#pt-use`. Their signatures
are compiler-owned, checked and opaque; no input can install an arbitrary
assumption. Choice accepts a Church encoding of propositional nonemptiness;
ordinary checked induction bridges the standard nominal Nonempty type to and
from that encoding. Native theorem checking reports transitive assumptions
from types and bodies, including opaque initializers and erased evidence,
while excluding unrelated declarations. These are logical axioms, not proved
lemmas or a claim that the FLT proof was checked. Default Lean replay still
rejects all axiom records. Explicit opt-in now accepts only the three pinned
signatures, checks ordinary opaque initializers using nominal adapters, and
compares the native theorem inventory with the imported target's closure.
The [foundation fixture](../tests/fixtures/lean_export_foundations/README.md)
reproduces all three adapters and their Prelude/Core source and license
attribution. These checks do not supply the full FLT proof or its dependencies.
[Source: formalization metadata](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/formalization.yaml).

A native procedural certificate cannot fill these mathematical gaps. It
certifies only the corresponding obligation after its existing checker passes;
it does not certify an upstream Lean environment, compiler correctness, or an
unprovided mathematical proof term.

## Resource-aware port plan

This task's execution budget is 2 GiB of memory and 200% CPU. The upstream
resource requirements exceed that budget. No full FLT checkout, Mathlib
installation/build, or full upstream proof export/replay was attempted.
A standalone Lean 4.33.1 release was downloaded and verified against the
release archive SHA-256
`890afd185370f85666025b883914ab4f4b339136f8c96167b69cfb62aecaf235`;
its runtime reports the pinned revision. The exact pinned exporter and original
small proof sources were compiled and run inside the existing resource guard.
The expanded regeneration run's peak child RSS was 2,002,652 KiB; the cgroup
retained its 2 GiB memory and 200% CPU limits throughout.
Lim now has a
[version-pinned bounded NDJSON reader](lean-export.md), exercised with local,
independently hand-authored fixtures for polymorphism, indexed equality,
dependent records and mutual recursors. Those fixtures are not exported Lean
proofs. Nine genuine outputs from the pinned producer now replay through Lim,
including a nonempty nested fold, universe-polymorphic roots, indexed containers,
two list specializations and dependent Sigma parameters. Their source/module/
license provenance is committed. Scoped recursion cases are derived from checked
container constructors; exported auxiliary recursors and rules are rechecked.
See [nested replay](lean-nested-replay.md) for the checks and scope.
The reader rejects unauthorized axioms, unsupported rules and resource exhaustion.
The pinned four-record quotient computation package now replays as checked
wrappers around native primitives, with an explicit foundation inventory and
a genuine fixture covering lifts, overapplication and propositional induction.
Its source, original modules, hashes and licenses are recorded in a separate
[provenance manifest](../tests/fixtures/lean_export_quotient/provenance.json).
The bounded native translator emits and rechecks ordinary Lim declarations
for this accepted subset, with twelve committed genuine
[proof-source translations](../theorems/lean_replay/README.md). Full upstream FLT
provenance, required foundations and full-environment replay remain unfinished.

Natural literals now stay compact as canonical decimal values rather than
magnitude-sized unary constructor graphs. They have the exact nominal
zero/successor semantics of the independently checked natural-number family;
one constructor is exposed when elimination or conversion requires it. The
[genuine large-literal fixture](../tests/fixtures/lean_export_naturals/README.md)
checks successors, predecessors and constructor discrimination beyond native
integer widths. Every literal is bounded to 4,096 decimal digits as a resource
limit; arithmetic still uses checked definitions and may exhaust work budgets.
This does not provide the full mathematical dependency closure or its proof.

The remaining work is a staged port, not a completed deliverable:

1. Freeze the upstream, toolchain, and Mathlib revisions, and define the intended
   statement correspondence and accepted axiom policy before changing trust.
2. Specify the missing kernel rules with focused positive and negative checks,
   then audit their interaction with substitution, universes, conversion, and
   inductive elimination. Keep unsupported rules rejected until implemented.
3. Build a streaming translator for elaborated declarations and their
   dependencies. Preserve provenance and reject unknown term forms, missing
   dependencies, mismatched universes, and unauthorized axioms.
4. Replay progressively larger dependency slices on suitable infrastructure,
   measure peak memory and conversion work, and publish the exact checked
   closure. Do not infer full coverage from a small test slice.
5. Translate and check the complete FLT dependency closure, prove or check its
   relationship to the pinned target statement, and produce a final axiom and
   dependency audit with reproducible resource measurements.

Until that final stage is complete, the accurate status is an implemented
constructive kernel and bounded replay subset, genuine regression exports,
and an unproved FLT statement with a compatibility roadmap. Even a
future successful replay would remain conditional on the implemented checker,
translator validation, and explicitly declared axioms; it would not make Lim a
formally verified kernel or establish parity with all of Lean and Mathlib.
