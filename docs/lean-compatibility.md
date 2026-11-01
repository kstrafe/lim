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

This task copies no upstream proof text or source code. The local FLT artifact
expresses a mathematical statement. A future source or term import must keep a
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
`(#math-inductive NAME (universes...) (parameters...) SORT (constructors...))`.
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
| Inductive families | Regular parameterized datatypes with direct recursive fields. No indices, mutual recursion, or nested self occurrences. | Implement and audit indexed, mutual, and nested inductives, their positivity conditions, recursors, and computation rules. |
| Universe theory | Explicit general Sort via #pt-sort, Prop and Type aliases, successor, max, and imax; Pi sorts use imax and symbolic level relationships are checked for all nonnegative assignments under bounded work budgets. Prop elimination and singleton-field conditions retain shared-variable guards. No universe inference, cumulativity, or type-in-type. | Integrate these rules into a version-pinned importer and audit them against the complete elaborated dependency closure. Full-environment translation, resource scaling, and replay remain open; these universe features alone do not complete the FLT port. |
| Conversion | Beta, transparent delta, iota, projections, and J; opaque theorem bodies. No proof irrelevance. | Account for Lean's definitional proof irrelevance and other conversion behavior actually used by the dependency closure. Adding a rule requires an explicit kernel and trust review. |
| Quotients and axioms | Constructive subset without quotients or an axiom-admission mechanism. | Decide and document the required quotient support and trusted-axiom policy rather than silently replacing unsupported evidence. |
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
family sort is zero, unless the empty/singleton-proof exception holds. Matching
family and motive variables retain their correlation; independent levels must
satisfy the condition for every assignment. Proof irrelevance and indexed,
mutual, and nested inductives are still absent, as is a full FLT proof port.

The pinned metadata lists `propext`, `Classical.choice`, and `Quot.sound` as the
axioms used by the upstream full result. Lim currently supplies none of these
as an automatic import or admission rule. A future compatibility mode must
explicitly identify its chosen axioms and distinguish that trust policy from
the present constructive subset.
[Source: formalization metadata](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/formalization.yaml).

A native procedural certificate cannot fill these mathematical gaps. It
certifies only the corresponding obligation after its existing checker passes;
it does not certify an upstream Lean environment, compiler correctness, or an
unprovided mathematical proof term.

## Resource-aware port plan

This task's execution budget is 2 GiB of memory and 200% CPU. The upstream
resource requirements exceed that budget. No full clone, Lean or Mathlib
installation, dependency download, export, build, or independent replay was
attempted here. Inspection was limited to small metadata and text requests.

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

Until that final stage is complete, the accurate status is shared syntax and
an unproved FLT statement with a documented compatibility roadmap. Even a
future successful replay would remain conditional on the implemented checker,
translator validation, and explicitly declared axioms; it would not make Lim a
formally verified kernel or establish parity with all of Lean and Mathlib.
