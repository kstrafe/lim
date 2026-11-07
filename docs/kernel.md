# Dependent proof kernel

Lim has two compile-time proof layers. Procedural proofs check claims about the
validated native program using structural analysis, bounded symbolic execution,
and target-specific certificates. The mathematical kernel checks explicit terms
in a constructive dependent core, with three explicitly referenced optional
logical axioms described below. Both expose named `#theorem`
declarations, but their terms, types, and evidence are distinct. Mathematical
data and datatype declarations use `#math-definition`, `#math-opaque`, and `#math-inductive`.

The kernel is inspired by Lean 4's use of dependent types, universes, inductive
types, and a small proof checker. It is not full Lean 4, does not provide mathlib,
and makes no compatibility, feature-parity, or formal-verification claim. The
rules and syntax below describe Lim's supported subset. The
[Lean compatibility and FLT roadmap](lean-compatibility.md) records the pinned
upstream reference, missing features, trust differences, and remaining porting
work; no full Lean or Fermat's Last Theorem proof port is complete.

## Declare a definition, theorem, or datatype

A mathematical definition has an explicit universe-parameter list, type, and
value:

```lisp
(#math-definition identity
  (u)
  (#pt-pi ((A (#pt-type u)) (x A)) A)
  (#pt-lambda ((A (#pt-type u)) (x A)) x))
```

`u` is a universe parameter, not a runtime argument. `A` and `x` are term
parameters. A definition is transparent: conversion may unfold its checked
value. Every binder has an explicit type, and every application is explicit.
For example, applying this identity to a natural number is:

```lisp
(#pt-app (#pt-use identity (0)) #pt-nat (#pt-numeral 3))
```

A mathematical theorem uses explicit universe, parameter, statement, and proof
clauses. Its statement must be a proposition, meaning a term whose type is
`#pt-prop`. Parameters are bound in both the statement and the evidence:

```lisp
(#theorem nat-reflexive
  (#universes)
  (#parameters (#parameter n #pt-nat))
  (#statement (#pt-eq #pt-nat n n))
  (#proof (#pt-refl #pt-nat n)))
```

The theorem's proof term is checked and then remains opaque to conversion.
`(#pt-app (#pt-use nat-reflexive ()) #pt-zero)` uses its type and evidence;
it does not unfold the theorem body. A declaration with a data type such as
`#pt-nat` as its statement is rejected: use a definition for data.

The public declaration shapes follow. `#math-opaque` checks TYPE and VALUE just like `#math-definition`, then makes VALUE unavailable to definitional conversion. It provides no axiom or admission.

```text
(#theorem NAME
  (#universes u...)
  (#parameters (#parameter name TYPE)...)
  (#statement CLAIM)
  (#proof EVIDENCE))

(#theorem NAME PROCEDURAL-CLAIM)

(#math-definition NAME (universe...) TYPE VALUE)
(#math-opaque NAME (universe...) TYPE VALUE)

(#math-inductive NAME (universe...)
  ((parameter Type)...)
  SORT
  ((constructor-label ((field Type)...))...))
```

For a mathematical theorem, write `(#universes)` and `(#parameters)` when their
lists are empty. `#parameter` introduces one explicitly typed term parameter;
`#statement` contains the proposition and `#proof` contains its evidence.
`#proof` is only a clause within this theorem form, never a top-level declaration.
The parameter clauses lower to a closed Pi type and lambda evidence; the kernel
independently checks the resulting terms. The procedural shorthand has one claim
and no mathematical evidence clause. Private kernel wrappers are implementation
details, not accepted public syntax.

The outer names follow ordinary proof-name rules. Constructor labels identify
constructors within their datatype; they are selected explicitly by
`#pt-construct`. Constructor field lists and parameter lists are mandatory even
when empty. Mathematical declarations are compile-time objects, not native
functions, structs, enums, or runtime layouts.

## Propositions, types, and explicit universes

`(#pt-sort L)` denotes the general sort `Sort L`. `#pt-prop` is `Sort 0`,
equivalently `(#pt-sort 0)`, and `(#pt-type L)` is
`(#pt-sort (#pt-level-succ L))`. Thus `(#pt-type 0)` is `Sort 1`, the first
data-type universe, not `Prop`. A sort at level `L` is itself classified in
`Sort (L + 1)`; it does not inhabit itself. A proposition such as
`(#pt-eq #pt-nat n n)` is an inhabitant of `#pt-prop`.

Sort arguments are explicit: there is no missing-level inference. General
Sort polymorphism permits a declared level parameter to range over both zero
and positive levels; using `#pt-type` alone always selects a successor level.

Levels are explicit syntax:

| Level syntax | Meaning |
| --- | --- |
| `0`, `1`, ... | Nonnegative integer universe levels. |
| `u` | A universe parameter declared by this mathematical declaration. |
| `(#pt-level-succ u)` | Successor of a level. |
| `(#pt-level-max u v)` | Maximum of the listed levels. |
| `(#pt-level-imax u v)` | Zero when `v` is zero; otherwise `max(u, v)`. Exactly two operands. |

Level expressions are not arbitrary native or kernel term computations.
There is no implicit universe inference or cumulativity: inhabiting one
universe does not automatically coerce a term into a larger universe.

Symbolic level equalities and inequalities must hold for every nonnegative
assignment to the declared universe parameters, not just sampled levels or
values below a fixed maximum. The same parameter retains its correlation in
all occurrences. A symbolic level is not rejected simply because it might be
zero or positive: the checker analyzes those guards exactly. Normalized level
terms, guard analysis, and comparisons have finite resource budgets; exceeding
a budget reports an error rather than guessing equality, inequality, or safety.

```lisp
(#math-definition sort-identity (u)
  (#pt-pi ((A (#pt-sort u)) (x A)) A)
  (#pt-lambda ((A (#pt-sort u)) (x A)) x))
```

This identity accepts a proposition at level zero as well as a type at a
positive level, with explicit universe and term arguments at each use.

A global mathematical reference is always `(#pt-use NAME (level...))`.
The level list is required, including `()` for a monomorphic declaration.
Supply the declared number of universe arguments, then use `#pt-app` for term
arguments. This separates universe instantiation from term application:

```lisp
(#pt-use nat-reflexive ())
(#pt-use identity ((#pt-level-max 0 1)))
```

Explicit universe polymorphism supports compile-time mathematical generic
reasoning. It does not add generic native functions or change Lim's native
generation and monomorphization rules.

## Dependent functions and application

`(#pt-pi ((x A) (y B)...) C)` is a dependent function type. Later binder types
and the result may mention earlier binders. When the result is a proposition,
this expresses universal quantification or implication. For one binder, if
`A : Sort u` and the result type has sort `Sort v`, the Pi type has sort
`Sort (imax(u, v))`. In particular, a proposition-valued result stays in Prop
even when the domain inhabits a higher sort. Multiple binders apply this rule
from the innermost Pi outward. Symbolic zero/positive cases are checked without
rejecting a declaration merely because a level's zero status is not fixed.
These universe rules follow the concepts implemented in Lean 4.33.1's pinned
[level operations](https://raw.githubusercontent.com/leanprover/lean4/v4.33.1/src/kernel/level.cpp)
and [Pi type checking](https://raw.githubusercontent.com/leanprover/lean4/v4.33.1/src/kernel/type_checker.cpp);
this does not import Lean's other conversion rules into Lim. A dependent function
is introduced with `#pt-lambda` using the same explicit binder-list syntax:
`(#pt-lambda ((P #pt-prop) (p P)) p)`. The equivalent theorem uses explicit
parameter clauses, which bind `P` and `p` in its statement and evidence:

```lisp
(#theorem keep-proof
  (#universes)
  (#parameters (#parameter P #pt-prop) (#parameter p P))
  (#statement P)
  (#proof p))
```

Use `(#pt-app FUNCTION ARGUMENT...)` to apply a function or proof. Local
variables are bare identifiers; global mathematical declarations use `#pt-use`.
A lambda is checked against its dependent function type, including substitution
of actual arguments into later types. There are no implicit arguments,
metavariable holes, or elaborator-generated missing proofs.

Mathematical Pi quantification is distinct from procedural `#proof-for-all`.
A Pi proof is a checked function term; it does not enumerate values or invoke
the bitvector solver.

## Typed local lets and aliases

`(#pt-let (#parameter NAME TYPE) VALUE BODY)` is a genuine typed local binding.
`TYPE` and `VALUE` are checked in the outer scope; `NAME` is visible only in
`BODY`. The name cannot shadow an existing local or universe parameter. The
annotation is required, and the value cannot recursively reference its own
new binding.

The kernel checks that `TYPE` has a sort and that `VALUE` has that type before
substituting the value into `BODY` and inferring the substituted body. This
supports a local type alias whose definition is known while checking the body:

```lisp
(#theorem zero-via-alias
  (#universes)
  (#parameters)
  (#statement (#pt-eq #pt-nat #pt-zero #pt-zero))
  (#proof
    (#pt-let (#parameter Alias (#pt-type 0)) #pt-nat
      (#pt-refl Alias #pt-zero))))
```

Here `Alias` becomes Nat before the body is inferred. Simply lowering the let
to a lambda application would instead check a body with an abstract type
parameter and would not implement these alias semantics.

Weak-head normalization uses zeta reduction to substitute the checked value.
Neither an unused binding nor later reduction excuses an ill-typed value,
malformed annotation, source error, or exhausted checking budget. Errors fail
closed even when the body does not mention the new name. This feature adds
no implicit typing, general recursion, or Lean environment importer.

## Dependent pairs

`#pt-sigma` takes exactly one binder in a binder list:

```lisp
(#pt-sigma ((n #pt-nat)) (#pt-eq #pt-nat n n))
```

This describes a pair whose second component is a proof about the first.
Construction includes the entire Sigma type, followed by the two components:

```lisp
(#math-definition zero-with-evidence
  ()
  (#pt-sigma ((n #pt-nat)) (#pt-eq #pt-nat n n))
  (#pt-pair
    (#pt-sigma ((n #pt-nat)) (#pt-eq #pt-nat n n))
    #pt-zero
    (#pt-refl #pt-nat #pt-zero)))
```

`(#pt-first PAIR)` returns the first component. `(#pt-second PAIR)` returns
the second, with the first projection substituted into its dependent type.
For more than two components, nest Sigma types explicitly. No general tuple
or native aggregate coercion is implied.

## Equality and dependent transport

`(#pt-eq A left right)` is propositional equality in `A`. Both endpoints must
have type `A`; the result has type `#pt-prop`. Reflexivity is explicit:
`(#pt-refl A value)` proves `(#pt-eq A value value)`.

The equality eliminator has this operand order:

```text
(#pt-eq-elim A lhs motive base rhs equality)
```

The motive is a dependent function taking both `x : A` and
`h : (#pt-eq A lhs x)`. The base supplies the motive at `lhs` and its reflexive
proof. Given `equality : (#pt-eq A lhs rhs)`, elimination produces the motive
at `rhs` and `equality`. This is dependent equality elimination (J): the motive
is checked at a fresh generic endpoint and an equality to that endpoint, not
just at the supplied concrete `rhs`. A motive that works only for that one
endpoint is insufficient. For example, this transports reflexivity along an
explicit equality proof:

```lisp
(#theorem transport-reflexivity
  (#universes)
  (#parameters
    (#parameter a #pt-nat)
    (#parameter b #pt-nat)
    (#parameter h (#pt-eq #pt-nat a b)))
  (#statement (#pt-eq #pt-nat b b))
  (#proof
    (#pt-eq-elim
      #pt-nat
      a
      (#pt-lambda ((x #pt-nat) (e (#pt-eq #pt-nat a x))) (#pt-eq #pt-nat x x))
      (#pt-refl #pt-nat a)
      b
      h)))
```

Conversion and propositional equality are different. Conversion computes with
transparent checked terms; an equality hypothesis requires elimination when
its endpoints do not already convert. Definitional proof irrelevance also makes
any two well-typed proofs of the same proposition definitionally equal.
The checker verifies that both terms have the same proposition as their type.
Their inferred proposition types must themselves pass typed conversion; merely
being propositions, matching syntax, or looking like evidence is insufficient.

```lisp
(#theorem proof-irrelevance
  (#universes)
  (#parameters (#parameter P #pt-prop) (#parameter p P) (#parameter q P))
  (#statement (#pt-eq P p q))
  (#proof (#pt-refl P p)))
```

Reflexivity initially proves `(#pt-eq P p p)`. Typed conversion recognizes `p`
and `q` as proofs of the same `P`, so it also checks against the stated equality.
No new proof form, axiom, admission rule, or tactic is involved.

This rule compares proofs, not arbitrary propositions. Distinct proposition
types remain distinct unless another conversion rule already identifies them.
In particular, native-program facts `(#pt-program first-law)` and
`(#pt-program second-law)` are separate opaque atoms; their certificates cannot
be substituted for each other merely because both facts have accepted proofs.
Data values are not collapsed. Neither are arbitrary values of `A : Sort u`
unless the sort of `A` is provably zero, rather than merely possibly zero.

Conversion carries the local typing context, Gamma, through Pi, lambda, and
Sigma binders. Dependent comparisons extend that context with each checked
binder before comparing terms in its scope. It checks the shared proposition
in that context, not just two syntactic annotations without their bindings.
Opaque theorem bodies remain opaque: proof irrelevance does not unfold them
or bypass checking their statements. The reference concept is Lean 4.33.1's
[`is_def_eq_proof_irrel`](https://raw.githubusercontent.com/leanprover/lean4/v4.33.1/src/kernel/type_checker.cpp#L870-L879);
Lim's implementation remains a checker whose correctness is trusted, not a
formally verified kernel.

## Natural numbers and induction

`#pt-nat` is the mathematical natural-number type in `(#pt-type 0)`.
`#pt-zero` is its zero constructor; both are symbols, not empty applications.
`(#pt-succ n)` constructs a successor. `(#pt-numeral INTEGER)` accepts a
nonnegative source integer of at most 128 as a zero/successor abbreviation.
`(#pt-nat-literal FAMILY "DECIMAL")` checks a canonical unsigned decimal
string of up to 4,096 digits against an explicit global family reference. The
family must already be checked, monomorphic, parameterless and indexless, with
Type 0 sort and exactly zero and successor constructors, in that order; axioms
are not accepted. Values stay compact; induction and conversion expose one
constructor at a time. Values are arbitrary precision, subject to finite
representation and work budgets. The [native example](../examples/proof_natural_literals.lim)
checks large successors and predecessors. [Genuine pinned exports](../tests/fixtures/lean_export_naturals/README.md)
also replay and translate through these same rules.

Structural affine folds can compute in decimal digits instead of one recursion
step per numeric value. For a checked natural family and constant natural-valued
motive, a step `ih + k` still reduces a closed count `n` to `base + n*k`.
More general steps `a*ih+b`, with a constant natural multiplier and closed
count, use binary composition: composing the step with itself yields
`a*a*ih + (a*b+b)`. Exact decimal halving chooses the count bits without a
machine-integer conversion. The final unused square is not computed.

The recognizer unfolds transparent definitions, beta/zeta redexes and
constructor projections. Nested folds keep distinct coefficient slots for
their current accumulator and already selected outer accumulators, shifting
the variable map past both binders. Predecessors and unrelated free locals
never enter that map. An affine product requires one variable-independent
factor; two variable-dependent factors retain ordinary evaluation. Iteration
with a nontranslation multiplier requires a closed count, and a positive reset
fold can discard its base only when its count is known nonzero.

This supports the explicit addition/multiplication definitions in
[`proof_natural_arithmetic.lim`](../examples/proof_natural_arithmetic.lim) and
the powers and nonzero-offset recurrence in
[`proof_natural_powers.lim`](../examples/proof_natural_powers.lim), including
operands larger than machine integers. Definition names do not
authorize arithmetic. Nominal family identities and opaque bodies remain
distinct, and every source body and erased let still undergoes ordinary typing.

There is also a guarded decreasing rule. The constant-natural-motive recursor
whose zero branch is zero and whose successor branch returns its predecessor
computes `max(n-1,0)`. A fold whose step applies that exact predecessor recursor
to its accumulator computes `max(base-count,0)` for closed natural operands.
The recognizer checks both recursor shapes, nominal families, motives, branch
domains and binder indices. A predecessor of another local, a changed zero or
successor branch, or an opaque predecessor cannot authorize this rule. Unknown
operands stay symbolic; truncated subtraction is not generally affine in them.
[`proof_natural_subtraction.lim`](../examples/proof_natural_subtraction.lim)
shows large subtraction and saturation at zero through ordinary definitions.
When the checked base is computed by a case or another ordinary reduction,
conversion verifies the same full predecessor recurrence, normalizes the base
once in its actual typing context, and subtracts the compact count. It does
not construct one nested predecessor per count. The
[`computed-base example`](../examples/proof_computed_subtraction.lim) checks
both a nonzero result and exhaustion with no additional foundations or budgets.
Open or opaque bases remain symbolic; changed branches and binder references
retain their own meaning.

Digit addition, truncated subtraction and grade-school multiplication use exact decimal arithmetic.
They charge digit work and temporary allocation before computation against the
existing kernel budgets; results exceeding 4,096 digits fail. A zero count
returns the checked base without executing arithmetic in the unused step,
which still undergoes ordinary typing. A reset can discard its checked base,
and a zero fixed point avoids constructing an unused huge power. Dependent motives,
other predecessor-dependent or nonlinear steps, and other recursion shapes retain
ordinary bounded iota computation. This optimization adds no source keyword,
axiom or unchecked arithmetic declaration.

Two structural fusion rules expose a natural-valued recurrence inside a more
complex carrier. Projecting the first field of a record-valued natural fold
can become a fold of that field if the step uses its previous state only
through the same first-field projection. The checked carrier must be an
unindexed, nonrecursive data record whose first field is its first type
parameter. The observed type must be a constant natural family or completed
finite Type-0 data family, or a function from the natural family to one of
those scalar types. Finite families must be monomorphic, parameterless and
indexless, with no constructor fields. Reading another history field or passing the
whole old state prevents fusion. The projected base stays suspended.

Likewise, applying a function-valued natural fold at a fixed argument can
become a natural-valued fold only if every use of its old function applies
that same argument. Binder-aware replacement checks the actual argument and
rejects other arguments or whole-function uses. A separate nonrecursive-case
rule can push a fixed argument of another type into the branches. Its function
domain must be definitionally independent of the case index and its range
must be a closed scalar type. The step cannot use the old function after
checked definitional normalization, including in annotations and erased terms.
The transformed branch retains that normalized body before changing its
unused hypothesis type; the original source still undergoes full typing.
This exposes histories passed through Lean's matchers without permitting
arbitrary recursive calls at changing arguments. Constructor-headed natural
recursors select branches through ordinary iota; zero literals return their
base without inspecting the unused step. Other inductive families retain
their normal evaluator. Source typing, including unused fields and local
bindings, is always checked before conversion.

Paired-predecessor recursion has a separate rule for a completed finite data
result family. It checks all four cases: `F(0,0)=a`, `F(0,y+1)=b`,
`F(x+1,0)=c`, and `F(x+1,y+1)=F(x,y)`. A constant zero-left function is
the special case `a=b`. The recognizer checks both natural motives, branch
domains and exact binder indices, including the second operand of the zero-left
case. Closed counts compare by canonical decimal length and digits; the
result is the actual terminal from the checked body. Constructor order and
names do not assign truth values or authorize a computation. Symbolic operands
remain in their real scope rather than being normalized in an empty context.
The [native comparison example](../examples/proof_natural_comparison.lim)
shows the less-or-equal recurrence, and direct constructor-iota tests also
cover three distinct terminals. Work and transformation budgets are unchanged.

A separate Euclidean observation recognizes a particular checked history fold.
Its selected field must be `Nat -> P -> Nat`, where `P` is a proposition.
For a positive constant `d`, the successor step must match one of two exact
recurrences:

| Observation | State below `d` | State at or above `d` |
| --- | --- | --- |
| Quotient | Return zero. | Apply the previous field to `max(x-d,0)`, then add one. |
| Remainder | Return the current state. | Apply the previous field to `max(x-d,0)` unchanged. |
The guard's complete paired-predecessor recurrence, predecessor iteration,
record projection, binders and finite case tags are checked structurally.
Finite decision fields may contain only propositions; the observer cannot
inspect their proof payloads. No operation or constructor name grants authority.

For a normalized input `x`, exact decimal long division computes `q = x/d`.
Scratch storage is charged up front; comparisons and subtraction/compaction
passes are charged before execution. Equal-length operands do not pay for
unperformed worst-case subtractions at every input digit. The rule additionally
requires strictly more than `q` units of actual fuel: `q` positive steps and one
terminal step. It never assumes a proof argument establishes sufficient fuel.
Insufficient or unknown fuel retains ordinary reduction, preserving an arbitrary
base function. A known successor can establish positive fuel without forcing
its unused tail. Zero fuel does not inspect the successor step. Every source
body, annotation and proof argument still undergoes inference.

This is an additional trusted conversion optimization, tested against separately
materialized history records and altered recurrences. The
[division corpus](../tests/fixtures/lean_export_division/README.md) independently
checks the genuine pinned standard body and native translation, including a
quotient larger than a machine integer. The
[composition corpus](../tests/fixtures/lean_export_division_composition/README.md)
adds computed dividends, divisors and fuel, including powers and equal operands.

Noncompact numeric operands can use an optional normalization attempt through
the existing checked affine rules. Each attempt is capped at 16,384 additional
work units, 2 MiB of transformation payload and 48 additional depth levels,
within the enclosing limits. Nested attempts inherit the tighter caps. Declining
a quota or an unrepresentable arithmetic result returns to ordinary reduction;
work and allocations already charged remain charged. Operations refused before
execution do not incur their predicted cost. Other errors propagate, and the
enclosing budget is restored on every result. This adds no arithmetic equation,
proof admission or cached theorem authority. Initial source inference remains
mandatory even when normalization erases a malformed annotation or value.
The [remainder corpus](../tests/fixtures/lean_export_remainder/README.md) checks
both literal/computed operands and unbounded zero controls against the genuine
standard definitions. The remainder observation adds a trusted conversion rule
for the exact state-return/unchanged-recursion pattern; it does not infer that
behavior from an operation name. Both observations require the same actual fuel
bound even though their terminal results differ.

The guard's context-independent numeral reduction can also simplify an exactly
matching application argument before exposing the subtraction recurrence.
This avoids unfolding the same computed divisor repeatedly. Different syntax
retains ordinary normalization, and the complete predecessor-iteration shape,
base state and constant count must still match. This is local value reuse;
all source annotations/proofs still pass initial checking.

Application conversion compares identical global or local heads before
unfolding their bodies, checking each argument by ordinary conversion. If
needed, up to eight candidates across both operands expose wrappers and
selected cases. A bounded inspection of transparent bodies and computational
argument heads can select a left reduction before expanding the right worker.
This inspection only chooses a direction; it proves no equality and cannot
select an unknown or incorrect branch. Candidate normalization contracts
beta/zeta/iota while leaving unrelated global heads neutral, so a common worker
can be compared without expanding its implementation twice. Every candidate
uses at most 16,384 extra work units,
2 MiB of transformed payload and 48 extra depth within the enclosing limits.
Speculative argument congruence for closed function calls uses these same bounds
so it cannot consume the entire phase before head reduction. Matched checked
datatype heads whose remaining parameters and indices all have the same explicit
natural-number type instead use ordinary argument comparison after bounded
spine inspection. Both the datatype and its natural-number parameter must
already be resident, and the latter must pass the existing zero/successor
structural recognizer. Their applications have no delta body to expose;
declining a valid scalar argument comparison would only repeat it through
fallback. The scheduling hint borrows existing shared metadata without cloning
its payload or paging in a declaration. Structured types, missing or nonresident
heads, transparent functions and opaque functions keep bounded speculation.
Using ordinary comparison for every datatype application was insufficiently
selective: it reintroduced resource refusal on the changed ASCII proof. An
opaque proof-valued function can also need proof irrelevance after its arguments
differ. The scalar scheduling hint establishes no equality or injectivity: a
failed comparison still uses the ordinary converter. Comparisons under local
binders retain their existing reduction path and accounting.
Nested probes inherit tighter limits, spent charges remain spent, and only
explicit internal declines fall back. Unknown names and invalid universes still
fail. The existing converter handles nonmatching heads, unequal arguments of a
constant function and longer wrapper chains; this is not an injectivity rule.
Explicit lambda and let heads use the same bounded candidate path: contract
their beta/zeta redex before unfolding the resulting named call. In particular,
an unused proof binder must not force both copies of an open well-founded
worker to normalize. Substitution preserves outer variables and checks every
source annotation even when subsequent reduction erases an argument.
Consecutive explicit lambda arguments use simultaneous substitution in this
lazy path too, sharing the eager path's binder and allocation checks. This
batching never unfolds a global head; partial and overapplication retain their
remaining lambda or neutral call.
If no candidate establishes equality, ordinary fallback resumes from the last
completed reductions of either operand. It does not repeat their completed
wrapper/beta prefixes. Reuse stays inside the same comparison and typing
context; there is no cross-comparison cache or checked-signature shortcut. A declined
attempt publishes no partial result, while earlier completed reductions remain
usable. All spent work and payload charges remain charged. The original source
still requires full typing, even when normalization erases a bad annotation.
No operation name authorizes conversion. Full source inference remains required.

For aligned canonical constructors of a completed Type-0 record, a failed
field comparison is already a mismatch. The shortcut requires an unindexed,
nonrecursive single-constructor family, matching levels/constructor/parameters,
and checked arities. Its specialized sort must equal 1 exactly; Prop and
symbolic-sort cases retain ordinary conversion and proof irrelevance. Field
conversion still uses the existing rules. This avoids re-inferring the whole
record and repeating its field comparisons through eta after a data mismatch.
All source arguments and sibling proof fields still undergo initial checking.

This reduction strategy checks the genuine general `Nat.mod_lt` theorem and
its `Nat.modCoreGo_lt` dependency within the original budgets. The theorem
quantifies over all natural dividends and all positive natural divisors; it is
separate from the corpus's closed remainder computations and zero identities.

The [well-founded equation corpus](../tests/fixtures/lean_export_well_founded/README.md)
checks the actual `WellFounded.Nat.fix_eq` proof for arbitrary input sorts,
result families, natural-valued measures and recursive steps. Its 141 genuine
declarations and exact native translation require `Quot.sound`, used by
function extensionality, and the `quotient-computation-v1` primitive foundation.
Raw replay requires explicit `--lean-foundations`; the constructive default
refuses it. Native checking reports the same `Quot.sound` logical basis. This
is not a new axiom or an admission of the equation by its name.

The [GCD corpus](../tests/fixtures/lean_export_gcd/README.md) checks 284 genuine
declarations, including the unary and binary GCD defining equations.
Three targets quantify over arbitrary naturals: zero on either side and the
successor recurrence. Exposing checked selectors and lambda wrappers on the
left avoids prematurely unfolding a matching recursive worker on the right.
Both raw and native checks report `Quot.sound` for zero-left and successor;
zero-right additionally requires `propext`. The primitive foundation remains
`quotient-computation-v1`, and raw replay requires explicit authorization.
The separate [GCD self corpus](../tests/fixtures/lean_export_gcd_self/README.md)
checks `Nat.gcd n n = n` for arbitrary naturals through 335 genuine declarations.
It uses the explicit 1,000,000-work/128-MiB-phase/1-GiB-total profile and reports
exactly `Quot.sound` and `propext`, plus the quotient primitive package. Raw
replay, emitted native source and independent native checking retain the same
basis. The default work budget correctly refuses this larger proof closure;
selecting its recorded budget changes no proof rule. Source ownership includes
the independently pinned `Init.Data.Nat.Div.Basic` fuel-congruence proof.
The [GCD calculation corpus](../tests/fixtures/lean_export_gcd_calculation/README.md)
checks `Nat.gcd 84 30 = 6` by applying already checked successor/zero-left
lemmas and computing the intermediate remainders. All 278 original and native
declarations check with the same explicit resource profile, exactly
`Quot.sound`, and the quotient primitive package. No GCD name authorizes an
equation. This is an explicit mathematical calculation. A separate
[direct GCD fixture](../tests/fixtures/lean_export_gcd_closed/README.md) now
checks `Nat.gcd 84 30 = 6 := rfl` by evaluating the original exported worker.
All 251 declarations check without axioms or primitive foundations, and its
emitted native theorem checks independently. Both forms also pass the
unchanged default proof budget. This does not complete general GCD development
or the full FLT proof.

A term shift by zero shares its immutable argument root after the ordinary
work/depth check. It needs no payload transformation. For a compound argument,
identity alone does not prove absence of free variables: later nonzero shifts
still inspect every annotation and binder scope before reusing an invariant
result. Declaration scope, universe and type checking remain independent and
still traverse all source terms, including ignored arguments and erased lets.

Nonzero shifts, beta substitutions and universe substitutions preserve shared
subtrees within one transformation. Their scratch memo keys the immutable
input node by pointer, binder count and absolute traversal depth. The input
root stays alive for the operation, and results never pass into another
substitution or declaration. Each cache hit still checks current depth/work;
its descendants previously completed the same transformation at the same
depth. Variable mappings and universe maps are fixed for that operation.
Occurrence-sensitive node rewrites keep the uncached path, and source
inference still checks the resulting terms independently.

The memo activates after 64 visits and keeps at most 4,096 entries, charging
256 bytes before each insertion. Small transformations allocate no table;
exhausting memo capacity resumes ordinary traversal. This preserves DAG
sharing without introducing a new reduction rule, proof judgment cache or
larger resource profile.

The regression compares a depth-16 shared DAG with the existing uncached
transformer and checks complete resulting syntax, over 100-fold fewer work
units and over 100-fold less transformation allocation accounting. A separate
depth-48 case stays within the ordinary budget. These are syntax stress
measurements, not additional mathematical proofs. All 384 kernel tests and
147 relevant integration tests pass; all 23 committed genuine translations
retain their complete source hashes and receipt bytes against the saved
compiler. All-target checking remains warning-free.

Five alternating debug0 samples on the accepted corpus measure the following
median wall times in milliseconds. Inputs, proof budgets and the separate
2-GiB/two-core host guard match. The change bounds repeated DAG work; it does
not make these small examples faster.

| Corpus | Raw before → after | Native before → after |
| --- | --- | --- |
| GCD equations | 382.793 → 408.564 | 816.661 → 831.861 |
| GCD self | 578.942 → 617.595 | 1,265.231 → 1,278.618 |
| GCD calculation | 489.399 → 525.763 | 936.395 → 954.916 |
| Division composition | 330.029 → 356.093 | 492.659 → 506.700 |
| Remainder | 345.739 → 371.217 | 555.021 → 573.295 |

Reproduce the paired measurements with
`python3 scripts/benchmark-proof-transforms.py --before OLD --after NEW --iterations 5`
inside the resource guard. The driver copies immutable inputs, checks exact
complete success output, and records input/compiler hashes before using fresh
timing workers. At that stage, direct GCD `rfl` refused the
20M-work/1-GiB-phase/2-GiB-total profile at export line 8342. The subsequent
complete-call evaluator described below resolves that reproduction. The
complete FLT export and proof replay remain open.

Checked global bodies also have a phase-local universe-substitution cache in
`src/proof/kernel/specialization.rs`. Each caller still retrieves the checked
declaration and validates universe arity before reuse. The key uses the original
immutable root and the complete substitution map. A weak root handle prevents
address reuse without independently retaining the original body. Cached results
carry their full term height; each use checks the current depth allowance.
Source-scoping walks remain uncached, and opaque declarations remain opaque.

The cache retains at most 64 entries and an estimated 2 MiB including result
graphs, keys and tables. Keys larger than 64 KiB use ordinary substitution.
A source-address index selects candidate slots; full map equality decides a
hit. Eviction updates the index when moving a slot. All lookup, metadata-walk
and eviction work is charged, and table/key allocations are charged before
reservation. The completed substitution bounds a metadata preflight; when
insufficient work or bytes remain, retention is skipped. Resetting the phase
releases both results and metadata. Optional reduction probes use ordinary
substitution because their depth allowance is narrower.

Freshly decoded bodies without another strong owner also use ordinary
substitution: their pointer identity cannot survive the call for later reuse.
This matters when declarations are forced out of memory. Attempting to cache
those bodies initially regressed three genuine arithmetic fixtures; the final
policy preserves all of their original budgets. Fifteen focused tests cover
reuse, map/source separation, eviction, byte caps, depth, reset, exhausted
budgets, source ownership, validation and metadata error propagation. All 399
kernel tests and 147 relevant integration tests pass; all 23 genuine proof
artifacts and complete receipts match the saved compiler byte for byte.

Five alternating debug0 before/after pairs compare compiler executable
SHA-256 prefixes `d4fe2335` and `f44f2587` on the accepted proof replay corpus.
All ten controls were accepted; proof inputs and budgets match, with a
2-GiB memory cap and `CPUQuota=200%` (two cores). The table reports median wall time in
milliseconds from 100 successful JSON rows. Wall-time changes range from
0.05% to 4.89%; the smallest shifts are near measurement noise. Median peak
RSS changes range from -0.9% to +3.4%, roughly unchanged. These are proof
replay benchmarks, not ordinary program compilation latency.

| Corpus | Raw before → after | Native before → after |
| --- | --- | --- |
| GCD equations | 407.657 → 402.648 | 827.081 → 824.633 |
| GCD self | 615.981 → 606.358 | 1,282.003 → 1,281.312 |
| GCD calculation | 531.265 → 505.295 | 954.866 → 936.400 |
| Division composition | 359.930 → 348.048 | 510.534 → 502.620 |
| Remainder | 369.357 → 362.512 | 573.654 → 560.520 |

The specialization-cache change alone still refused direct GCD `rfl` at
export line 8342 under the 20M-work/1-GiB-phase/2-GiB-total limits. Complete-call
evaluation below resolves that allocation failure. The full FLT export is
absent, and its proof remains unchecked.

Head exposure retains completed beta/delta/zeta reductions beneath a stuck
application, record projection or Sigma projection. Previously, an unsuccessful
fusion returned the original enclosing expression, so ordinary reduction repeated
the same substitutions. The exposed function or subject now stays in the result;
repeating exposure of that result is stable. New wrapper allocations still charge
the transformation budget. A bare local dividend declines closed Euclidean
observation before inspecting its recurrence, since it cannot be a closed
numeral. Source inference still checks the entire original expression, including
proof arguments and annotations that arithmetic recognition does not inspect.

Seven regressions cover typed open functions, record/Sigma projections,
stable repeated exposure, opacity, invalid sources and resource refusals.
All 406 kernel and 147 relevant integration tests pass without Rust warnings;
all 23 pinned native proof sources and complete receipts match the saved
compiler. Five alternating debug0 pairs compare executable SHA-256 prefixes
`f44f2587` and `dc6f6de8` under identical proof profiles and the 2-GiB/two-core
host guard. All ten raw/native controls accept. Median wall times decrease
1.48–6.29%, with median peak RSS decreasing 1.67–4.04%:

| Corpus | Raw before → after (ms) | Native before → after (ms) |
| --- | --- | --- |
| GCD equations | 397.741 → 382.978 | 827.538 → 805.175 |
| GCD self | 600.772 → 570.733 | 1,276.277 → 1,242.378 |
| GCD calculation | 498.170 → 478.778 | 931.142 → 917.386 |
| Division composition | 345.406 → 323.668 | 502.226 → 480.300 |
| Remainder | 360.940 → 339.827 | 568.533 → 545.893 |

These are accepted proof replay measurements. Retaining partial heads alone
still exceeded the direct GCD `rfl` phase budget. Inspecting the actual export
identifies `WellFounded.Nat.fix.go`, a
natural-number fuel recursor. The pinned
[Lean definition](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/Init/WF.lean#L454-L459)
confirms this path, distinct from the noncomputable accessibility recursor.
The remaining allocation samples include repeated beta substitution and
argument shifting; no need to unfold opaque accessibility proofs was established.

A subsequent closed-shift fact-cache experiment was removed. It recorded
closedness and full height during a required nonzero, cutoff-zero shift,
retained only weak source identities in a 256-entry table, and kept all
ordinary source and resource checks. Its nine regressions and all 562 relevant
candidate tests passed, with exact agreement for the 23 proof artifacts.
However, five alternating pairs on ten accepted raw/native cases ranged from
1.55% faster to 1.10% slower, with no clear overall improvement. The failing
GCD phase performed 91,915 lookups but only 496 matches (0.54%) and still
exhausted the same 1-GiB phase budget. Reusing closed-root facts did not solve
that workload. The source was restored exactly to the preceding validated
state; no closed-shift cache or profiling instrumentation remains in the
compiler.

An operation-local closure evaluator now delays substitution for exposed,
fully applied higher-order recursors and record projections in closed
conversion. It keeps immutable source terms, captured environments and
continuations in indexed arenas, including recursive hypotheses that return
functions. No recursive closure ownership chain is built or dropped. Shared
thunks memoize their weak heads, while original recursor templates remain
immutable. Scalar affine and power folds keep their existing fast path;
partial recursor applications that can only return another function skip this
probe.

Completed results are restricted to closed numerals and fieldless data
constructors. Ordinary beta/delta/zeta, projection and supported iota rules
justify each step; nominal checked family descriptors, rather than declaration
spellings, authorize compact natural recursion. Stuck proof projections and
applications can reach an enclosing equality or singleton eliminator, but
their internal neutral markers cannot become output syntax or equality
endpoints. Indexed singleton K reduction retains the ordinary Prop and
convertible-index restrictions. Unsupported recursive datatypes, mutual or
nested induction, open captures and other non-scalar results fall back to
ordinary reduction. Every original declaration and erased argument still
passes ordinary scope and type checking.

The evaluator has a 65,536-work-unit and 8-MiB transformation probe allowance,
clamped to every enclosing probe and the proof's existing hard budgets.
Arena growth, copied universe maps and a maximum of 64 operation-local
specialized bodies are charged before allocation. Declaration descriptors use
their existing shared owners instead of copying family metadata on each
step. Every body-cache lookup still validates its declaration and exact
universe arguments. Probe refusal does not refund work or allocations, and
genuine errors propagate. The operation guard and enclosing limits are
restored on both success and failure.

Validation covers 427 distinct kernel tests (the full 425-test run plus two
additional universe-cache regressions), 147 integration tests, warning-free
all-target checking and exact agreement for all 23 pinned proof artifacts and
receipts. The added cache tests exercise repeated Prop specialization and
reject reusing that body for a Type-level indexed singleton. Five alternating
debug0 benchmark pairs improve the accepted GCD calculation replay from
486.276 to 436.532 ms raw (10.2%) and from 929.477 to 878.392 ms native
(5.5%). Other accepted cases range from 1.07% faster to 0.92% slower, while
median RSS increases by 0.13–3.55%. These figures compare identical accepted
inputs and unchanged proof budgets under the same 2-GiB/two-core host guard.

An identity-base function fold also admits tail-composition fusion:
`F(0,x)=x; F(n+1,x)=F(n,U(x))` becomes scalar iteration of `U` starting at
`x` for a computationally known count. Unknown counts retain ordinary
conversion; the propositionally equal iterators do not become a new open
judgmental equality. Both function types must be this exact nominal natural family. The
complete retained update, including annotations and let values, must not use
the predecessor or old function; binder-aware substitution replaces the
argument with the scalar accumulator and shifts outer locals. Nonidentity
bases and extra recursive-function occurrences retain ordinary reduction.
All source inference and existing work/depth/allocation checks remain required.
The resulting scalar fold uses existing affine arithmetic rather than a new
shift evaluator. The [pinned left-shift corpus](../tests/fixtures/lean_export_left_shift/README.md)
checks a shift beyond `u128`, the arbitrary-input zero identity, and the actual
unbounded standard-library `Nat.shiftLeft_eq` proof. General right-shift lemmas and large
bitwise evaluation remain separate gaps.

Complete calls that build a nonrecursive record and pass it to another
function now receive a separate early observation attempt when their result
is a checked natural family. The filter inspects checked syntax and constructor
wrappers without substitution. It follows at most eight transparent forwarding
declarations, carrying unapplied caller arguments across aliases and partial
applications. Record-tail workers may themselves capture explicit arguments.
The original root's result type must still be a completed natural family;
opaque intermediates, partial results and longer chains decline. Its constructor template is only scheduling
metadata; evaluation always receives the original application and validates
actual universe arguments. The attempt runs after common-head congruence and
before conversion expands wrappers, as well as before ordinary head exposure.
No function spelling establishes an arithmetic operation or a proof.

This handles the checked `Nat.land`/`lor`/`xor` forwarding chain through
`Nat.bitwise` and its worker with a captured Boolean function. The genuine
385-declaration [bitwise fixture](../tests/fixtures/lean_export_bitwise/README.md)
preserves each original reflexivity proof and native correspondence, with
explicit `propext` foundations. This is coverage of the forwarding/evaluation
path, not complete large-operand bitwise or shift acceleration. The fixture's
separate stress source retains the larger cases still needing work.

Each phase permits at most 256 bounded classification checks and four wider
observations, each capped at 262,144 work units and 32 MiB of transformation
traffic. These remain inside the existing hard proof budgets. The observation
also reserves a quarter of remaining work and half of remaining phase bytes
for ordinary reduction. A million-step scalar fold regression confirms that
declining linear evaluation leaves enough budget for the existing affine
recognizer. Up to four weak input handles suppress repeated failed attempts
without caching mathematical judgments or retaining expression graphs. Phase
reset clears these hints. Ordinary delayed observations keep their smaller
allowance, and wider observations are skipped inside an existing probe.

Closed projections of natural fields from completed, monomorphic,
nonrecursive Type-0 records also use the existing closure evaluator before
ordinary head exposure. This matters when a Nat recursor returns division
data: substituting the earlier record through each field can repeatedly
recompute the same remainder. The scheduling filter checks the actual
family and scalar field type, and the evaluator must compute the result
from the checked source. It does not authorize a proof or a new equality
rule. Polymorphic fields decline without implicit universe instantiation.
Four projection attempts per phase have a separate counter from wrapper
observations; both retain the existing enclosing work/byte/depth limits
and fallback reserves. Phase reset clears the projection counter.
Tests compare ordinary reduction, check a longer record fold and a false
result, and cover the attempt cap, reset and polymorphic fallback.

This now checks the original 450,075-byte `GcdProbe.closed` export and its
independently checked native translation. The fresh pinned producer recreates
the exact original export hash, all 251 declaration origins, six upstream
source pins, preserved licenses, native mapping and an empty logical basis.
Tests reject changed results, corrupted worker/proof bodies and small budgets;
renaming GCD and fuel-worker name components preserves the proof. Forced
spilling preserves the complete report and native source. Both representations
pass the unchanged default 200,000-work/64-MiB-phase/256-MiB-total budget, as
well as the original explicit 20M-work/1-GiB-phase/2-GiB-total profile.
All 438 kernel tests and 158 relevant integration tests pass with warning-free
all-target checking; the older 23 proof sources and complete receipts remain
byte-identical. Five fresh default-budget samples give median 285.200 ms and
25,912 KiB RSS for raw replay, and 512.948 ms and 33,944 KiB RSS for native
checking. The older compiler refuses this input, so these are measurements of
new coverage. Five alternating pairs on ten previously accepted cases range
from 0.17% faster to 3.49% slower, with median RSS -1.37% to +1.58%.
General fixpoint completeness and full FLT support remain separate work.

Shifts and universe walks share immutable numeral and monomorphic-global leaves
instead of copying their owned payloads. The node callback and depth/work checks
still run; globals with universe arguments still invoke universe substitution.
Initial inference still validates declaration existence and arity. This reduces
real allocation, without a new reduction rule or theorem cache. The composition
corpus now checks all fifteen division targets together under the unchanged
256 MiB cumulative replay limit. More expensive composition, larger environments
and arbitrary course-of-values algorithms can still exceed the global budgets.

These rules expose the pinned Lean standard `Nat.add`, `Nat.mul`, `Nat.pow`,
`Nat.sub`, `Nat.ble` and `Nat.beq`
recurrences without constructing their `Nat.brecOn` history tables. The
[genuine standard arithmetic corpus](../tests/fixtures/lean_export_arithmetic/README.md)
checks thirty targets over 78 declarations, including large powers, zero/one
bases, generic right-zero and zero-exponent identities, nested arithmetic and
an affine recurrence with a nonzero offset, large truncated subtraction and its
zero/equal-operand cases, Boolean relations/equality, generic zero-left
comparison and nested arithmetic operands. The [native observation example](../examples/proof_observed_arithmetic.lim)
shows both rules directly. No declaration spelling, hash, source comment or
exporter claim authorizes a computation. Fusion and decimal arithmetic use
the existing work, transformation and result-size bounds. Other arithmetic
operations and arbitrary course-of-values algorithms are separate work.

Natural induction is explicit:

```text
(#pt-nat-induct motive zeroCase stepCase n)
```

The motive maps a natural number to the desired type or proposition. The zero
case inhabits the motive at zero. The step takes a natural number and an
induction hypothesis at that number, and returns the motive at its successor.
This defines doubling without general recursion:

```lisp
(#math-definition double
  ()
  (#pt-pi ((n #pt-nat)) #pt-nat)
  (#pt-lambda
    ((n #pt-nat))
    (#pt-nat-induct
      (#pt-lambda ((k #pt-nat)) #pt-nat)
      #pt-zero
      (#pt-lambda ((k #pt-nat) (ih #pt-nat)) (#pt-succ (#pt-succ ih)))
      n)))
```

Induction checks a zero case and a general successor case; it is not bounded
symbolic testing. Kernel `Nat` has no fixed width or overflow. There is no
implicit coercion from native `#u64`, another machine integer, or a procedural
symbolic value to `#pt-nat`.

## User inductives, constructors, and branches

User inductives support both the original regular form and an indexed form.
The regular `#math-inductive` syntax and bare `#pt-self` behavior remain
unchanged. An indexed declaration has a nonempty explicit `#indices` clause;
its index telescope follows the datatype parameters, and each index type may
refer to those parameters and earlier indices:

```lisp
(#math-inductive NAME (u...)
  ((parameter Type)...)
  (#indices (#parameter index TYPE)...)
  SORT
  ((constructor ((field TYPE)...) (result-index...))...))
```

Constructor fields may refer to datatype parameters and earlier fields. Each
constructor supplies one result index per declared index, and those terms may
refer to the parameters and all its fields. Field types and result indices are
checked at exact arity and universe. `#pt-self-at` marks direct recursive
fields in an indexed family and takes explicit index terms; datatype parameters
are inherited implicitly from the declaration. `#pt-self` and `#pt-self-at`
may also occur as terminal codomains under zero or more `#pt-pi` binders. This
supports strictly positive function fields, including dependent function
telescopes; the current family may not occur anywhere in a function domain,
including double-negative positions. No self occurrence is allowed in the
current family's indices. Explicit mutual groups and checked nominal nested
containers are described below. Direct recursion under primitive `#pt-sigma`
is unsupported; a previously declared dependent-pair datatype can be a container.

A checked `#pt-let` wrapper is permitted along a Pi codomain only when its
annotation and value contain no occurrence of the current family. The kernel
sort-checks the annotation and type-checks the value before zeta substitution,
then continues the positivity check in the instantiated body. This does not
allow recursive aliases in definitions or recursion hidden in Sigma types or
applications.

A small datatype with no parameters is:

```lisp
(#math-inductive ticks
  ()
  ()
  (#pt-type 0)
  ((tick-zero ()) (tick-next ((previous #pt-self)))))
```

Its type is referenced as `(#pt-use ticks ())`. Construction supplies universe
arguments, datatype parameters, the constructor label, and a field list:

```lisp
(#pt-construct ticks () () tick-zero ())
(#pt-construct ticks () () tick-next
  ((#pt-construct ticks () () tick-zero ())))
```

For a parameterized declaration, the parameter types are checked and actual
parameters are supplied in the separate parameter list of `#pt-construct` and
`#pt-induct`. They are not constructor fields. A reference via `#pt-use`
instantiates universes; apply its datatype parameters with `#pt-app` when a
parameterized datatype term is needed in a type. For example:

```lisp
(#math-inductive option
  (u)
  ((A (#pt-type u)))
  (#pt-type u)
  ((none ()) (some ((value A)))))

(#math-definition some-natural
  ()
  (#pt-app (#pt-use option (0)) #pt-nat)
  (#pt-construct option (0) (#pt-nat) some ((#pt-numeral 2))))
```

Here `(0)` instantiates `u`, `(#pt-nat)` supplies the datatype parameter `A`,
and `((#pt-numeral 2))` supplies the single field of `some`. None of these lists
is interchangeable with another.

The eliminator has this shape:

```text
(#pt-induct datatype (levels...) (parameters...) motive (branches...) subject)
```

The motive maps a subject of the instantiated datatype to the desired result
sort. Supply one branch per constructor, in declaration order. Each branch
receives the constructor fields in order, with an induction hypothesis
immediately after each direct recursive field. For fields `left : #pt-self`,
`value : A`, `right : #pt-self`, the branch arguments are
`left, ih-left, value, right, ih-right`, not all fields followed by all hypotheses.
A fieldless branch is just a term of the required result type.

For `ticks`, counting constructors is:

```lisp
(#math-definition count-ticks
  ()
  (#pt-pi ((t (#pt-use ticks ()))) #pt-nat)
  (#pt-lambda
    ((t (#pt-use ticks ())))
    (#pt-induct
      ticks
      ()
      ()
      (#pt-lambda ((x (#pt-use ticks ()))) #pt-nat)
      (#pt-zero (#pt-lambda ((previous (#pt-use ticks ())) (ih #pt-nat)) (#pt-succ ih)))
      t)))
```

An indexed vector family illustrates constructor result indices and recursive
fields. The `cons` constructor returns a vector at the successor length:

```lisp
(#math-inductive vector
  (u)
  ((A (#pt-type u)))
  (#indices (#parameter n #pt-nat))
  (#pt-type u)
  ((nil () (#pt-zero))
   (cons ((k #pt-nat) (head A) (tail (#pt-self-at (k))))
         ((#pt-succ k)))))
```

Here the `k` field is the predecessor length, the recursive tail has that
length, and the constructed vector has its successor length. A vector at
length two has type
`(#pt-app (#pt-app (#pt-use vector (0)) #pt-nat) (#pt-numeral 2))`.

The indexed eliminator puts generic indices before the subject in the motive.
The generic index binders are fresh, preventing the motive from freezing an
index to the subject's particular index. The subject has the family at those
generic indices:

```text
(#pt-induct family (levels...) (parameters...)
  (#indices index-terms...) motive (branches...) subject)
```

Each branch follows constructor field order. A direct recursive field is
immediately followed by an induction hypothesis at that child's indices. The
branch result is checked at the constructor's declared result indices.
Regular `#pt-induct` keeps its existing syntax and behavior.

For function-valued recursive fields, the branch supplies the field followed
by a pointwise induction hypothesis. For example, a fan node may carry
`children : Π key : Nat, Self`; its branch receives `children` and then
`ih : Π key : Nat, motive (children key)`. During reduction the recursive
branch is applied as `λ key, recurse (children key)`, using each child's
actual indices for indexed families. Existing direct recursive-field cases
retain their branch shape and reduction behavior.

As a proposition-valued example, this family has evidence only at zero:

```lisp
(#math-inductive zero-index
  ()
  ()
  (#indices (#parameter n #pt-nat))
  #pt-prop
  ((zero-index-proof () (#pt-zero))))

(#math-definition zero-index-identity
  ()
  (#pt-pi ((n #pt-nat))
    (#pt-pi ((h (#pt-app (#pt-use zero-index ()) n)))
      (#pt-eq #pt-nat n #pt-zero)))
  (#pt-lambda ((n #pt-nat) (h (#pt-app (#pt-use zero-index ()) n)))
    (#pt-induct zero-index () () (#indices n)
      (#pt-lambda
        ((generic-n #pt-nat)
         (generic-proof (#pt-app (#pt-use zero-index ()) generic-n)))
        (#pt-eq #pt-nat generic-n #pt-zero))
      ((#pt-refl #pt-nat #pt-zero))
      h)))
```

The kernel checks constructor types, strictly positive recursive positions,
result indices, branch types, and universe constraints. It rejects negative
and current-index occurrences of the family. Nested recursion is accepted
only through checked nominal container constructors, not primitive Sigma or
arbitrary type functions.

## Falsehood and elimination from propositions

`#pt-false` denotes an empty proposition and has no introduction constructor.
There is no `admit` or axiom declaration that supplies a proof of it.

An inductive proposition normally eliminates into propositions. When a family
sort can be zero, large elimination into a data-type universe is allowed for
an empty family or for a single-constructor family when every non-proof field
is exposed directly as a bare field variable among that constructor's result
indices. Each such field must be recoverable this way; a computed index such
as `succ field`, or an index that exposes only part of a field, does not count.
A field whose type has sort zero satisfies the ordinary proof-field condition
and needs no index exposure. More than one constructor does not qualify, even
if its fields expose data. Constructor field universes must also satisfy
`imax(fieldSort, familySort) <= familySort` for all universe assignments.
Thus a hidden `Nat` field prevents large elimination, as does a field
`P : #pt-prop` unless `P` itself is a result index: `#pt-prop` has sort 1, so
such a proposition-valued datum is not a proof field. Directly exposing only a
projection or other part of a data field is insufficient.

For families polymorphic over general Sort, large elimination is checked under
the guard that the family sort is zero. Unless the empty or singleton
recoverable-field exception applies, the motive's result sort must also be zero
under that guard.
A family in `Sort u` with a motive in `Sort u` preserves the same-variable
correlation and is permitted by this restriction. A motive in an independent
`Sort v` is rejected when `u = 0` and `v > 0` is possible. It is not enough that
some instantiations permit the elimination, and an ambiguous zero status alone
does not cause rejection when the implication can be proved.

This prevents arbitrary extraction of computational data from propositional
witnesses. Definitional proof irrelevance identifies well-typed proofs of the
same proposition; it does not waive this elimination restriction or identify
data values. The restriction is a kernel rule, not a runtime representation
or erasure promise. Indexed data families have no unit conversion or neutral
recursor shortcut, since indexed families have distinct fibres. A restricted
proof computation rule for matching fibres is described below.
Mutual and nested predicates follow the stricter group elimination rule
described below.

This recoverable-field condition follows Lean 4.33.1's
[`elim_only_at_universe_zero`](https://raw.githubusercontent.com/leanprover/lean4/v4.33.1/src/kernel/inductive.cpp#L483-L536)
rule.

This exception permits Type-valued accessibility recursion when the data field
is the constructor's direct result index and the recursive function field is
proof-valued. The [accessibility example](../examples/proof_accessibility.lim)
contains the `well-founded-recursion (u v)` definition and the generic
`well-founded-recursion-unfolds` equation theorem. It also proves
`no-predecessors (u)` as an actual accessibility proof and
`empty-relation-recursion-computes`, which computes for every Nat. The focused
11-test suite passes, including this complete example; a negative poison case
that mis-types the pointwise induction hypothesis for `lower` as data is
rejected with a type mismatch. This focused evidence does not establish full
Lean parity or formal verification of Lim's kernel.

## Reuse evidence about native programs

A procedural proof can be exposed as a proposition atom and checked evidence:

```lisp
(#fn identity-native ((value #u8)) #u8 (#return value))

(#theorem identity-native-law
  (#proof-for-all ((x #u8)) (#proof-eq (#call identity-native (: value x)) x)))

(#theorem identity-native-evidence
  (#universes)
  (#parameters)
  (#statement (#pt-program identity-native-law))
  (#proof (#pt-certificate identity-native-law)))
```

`(#pt-program NAME)` is the proposition atom for the named procedural proof.
`(#pt-certificate NAME)` is evidence of that same atom only after the existing
procedural checker has accepted the obligation. Naming a failed, unsupported,
or unchecked procedural claim cannot manufacture evidence. Certificates retain
the procedural checker's semantics and resource restrictions; they do not
translate machine arithmetic into mathematical natural arithmetic or prove a
stronger claim than the original obligation.

The bridge is directional. It does not execute a mathematical proof as native
code or turn a theorem into an assumption that bypasses the procedural checker.

## Evidence for a validation protocol

Storage-specific validation is a procedural obligation, declared with the
shared theorem shorthand:

```lisp
(#theorem safe
  (#proof-requires-validation process (#parameter-of validate user) (#parameter-of perform user)))
```

Each descriptor is exactly `(#parameter-of FUNCTION PARAMETER-NAME)`.
The selector references an existing parameter in that function's declaration,
not in the entry function or theorem scope, and introduces no theorem binding.
It is accepted only in a validation descriptor position; old bare pairs are
rejected without compatibility. This differs from `(#parameter name TYPE)`,
which declares a new mathematical theorem parameter. Both selected validation
parameters must be ordinary or pinned references to the same
resolved referent type, and `validate` must return `#bool`.

For universally quantified entry inputs, every reachable action entry through
the synchronous call tree must have an earlier completed validator call that
returned `true` for that same storage location. A distinct object with equal
contents, a `false` result, or validation completing after the action does not
satisfy the claim. A later `false` validation for the same object revokes an
earlier success. Writes overlapping the validated object or its transitive
referenced dependencies invalidate prior validation, including transitive
primitive reference dependencies; a new successful validator call can restore
it after a write or false result. The checker executes the validator body and checks its
result, without proving that it implements the desired business rule.
Dependency guards preserve the active enum variant. Observing a child with
another validator call does not count as a write to its parent; only actual
writes or a later false check of the same object revoke that object's evidence.

All branches and complete bounded loops from the explicit entry are checked.
Using `main` covers its synchronous tree, while separate roots require separate
claims. Unsupported operations, external or unavailable implementations, and
resource exhaustion are unproved. Existing `#proof-calls-before` and
`#proof-calls-when` remain weaker call-order/observation claims without this
same-object freshness requirement. This theorem emits no runtime proof code
and does not insert validation calls.

Validation tracking is limited to 64 facts, 128 dependencies per fact, and
256 dependencies total per symbolic state. Reference-dependency traversal depth
is limited to 32, and the existing 100,000 symbolic execution steps still apply.
Exhaustion is unproved, not evidence that a stale validation is safe.

After `safe` passes its procedural checker, a mathematical theorem may use
`(#pt-program safe)` as its proposition and `(#pt-certificate safe)` as evidence
through the existing adapter. This retains the procedural model and trust
assumptions; it does not turn a failed protocol check into mathematical evidence.
See the [full validation example](language.md#compile-time-proofs) for complete
function declarations and helper calls.

## Check a named theorem from the CLI

```sh
lim --check-theorem INPUT NAME
```

For example, save the `nat-reflexive` declaration above in `identity.lim`, then
run `lim --check-theorem identity.lim nat-reflexive`. The command resolves the
input normally, including imports and cfg selection, and performs normal
validation of all obligations. It also requires `NAME` to identify an actual
theorem declaration. A mathematical definition whose value happens to be a
proposition is not a theorem and cannot satisfy this request.

A missing target, a target excluded by cfg, a false or unproved obligation, or
another validation failure makes the command fail. Checking a name does not
skip other obligations in the input's checked program. This mode produces no
native outputs and does not compile or run a native executable.

[theorems/fermat_statement.lim](../theorems/fermat_statement.lim) defines Nat
addition, multiplication, and power with structural recursors, then the exact
closed positive-natural FLT proposition `fermats-last-theorem-statement` with
exponent `n + 3`. All four natural parameters are unbounded; successor bases
express positivity. This is a `#math-definition` of a proposition only: it
supplies no proof, no certificate, and no successful FLT theorem target.
`lim --check-theorem theorems/fermat_statement.lim fermats-last-theorem-statement`
must reject it as a definition. No upstream proof text or source code is copied.
Expressing that proposition does not establish Fermat's Last Theorem. See the
[compatibility roadmap](lean-compatibility.md) for the remaining full-port scope.

## Checking, conversion, and caching

Validation checks procedural obligations first. Mathematical declarations are
then checked in dependency order, using a topological sort; dependency cycles
are rejected. A forward reference does not authorize recursion. All proofs are
rechecked on warm-cache validation, and mathematical declarations have zero
native emission. A cached native artifact is not proof authority.

The dependency planner retains numeric declaration/group IDs and deduplicated
edges. Ready groups are chosen by their earliest source position; explicit
mutual groups retain the declared member order and reciprocal membership
checks. A definition's self-edge remains a cycle. Only internal edges of a
validated inductive group can be handled together.

Dependency collection parses one declaration at a time and releases its term
trees. Once a group is ready, the checker reparses that immutable source,
revalidates the group shape, and calls the same kernel definition/inductive
operations. Only that group's parsed terms need remain live. Scheduling
cannot establish a theorem, and later unused invalid declarations still fail
the whole check. Work and cumulative transformation accounting are unchanged.
Completed native declarations use the same bounded protected storage as raw
replay, with eviction only after a complete checked group. The source program
AST and dependency graph still reside in memory for general programs. Closed
mathematical-only `--check-theorem` files instead use a protected frozen text
snapshot and a names/roles/span directory, reparsing one ready group through
the same checker. The file adapter bounds source storage to 128 MiB, each
form to 8 MiB and its directory estimate to 32 MiB. The closed adapter's
4,096-declaration default and configured proof budgets still apply. Unsupported forms
and source syntax errors use the general frontend on the frozen bytes. Every
declaration remains mandatory before target selection, and the foundation
audit rereads the same snapshot. These adapters are prerequisites for larger
source checking, not a complete streaming source frontend or a full FLT
replay profile.

An ordinary source graph uses its actual, already inventoried declaration
count for scheduling. It does not stop at the closed artifact adapter's
default batch size. Every loaded declaration remains mandatory, including
unused bodies after that boundary; explicit artifact profiles keep their
selected limits. Per-declaration work, transformation and depth checks are
unchanged. Tests check a valid imported graph above 4,096 declarations and
reject an unused false theorem beyond that boundary with a type mismatch.

Kernel proof declarations also bypass runtime match normalization. Their
terms and constructor names belong to the mathematical grammar; walking
them mutably both misinterpreted a constructor named `case` and detached
shared syntax trees. The theorem entry point releases prepared syntax
after expansion has produced its owned program and source locations.

Derived nested-family views also use protected invocation-local storage.
Their exact signatures and source-container metadata have separate bounded
stores, with the same 8-MiB resident estimate and 4-MiB eviction target as
ordinary declarations. The internal metadata envelope never becomes a global
declaration or mathematical evidence. A view keeps its scoped identity across
eviction; global-name and constructor inference still reject auxiliary names.
Updates during an inductive group remain resident until every member's final
signature and group membership are installed. Both stores must succeed, and
observed corruption or a partial paired operation invalidates later judgments.
Budget resets do not clear storage failure. Native emission and correspondence
preserve ordered root membership through fallible lookups. These are bounded
storage prerequisites, not a complete large-environment replay profile.

Definitional conversion supports beta reduction of lambda applications, delta
unfolding of transparent definitions, and iota computation of eliminators on
constructors. Pair projections compute on pairs. Equality elimination J
reduces to its base when its endpoints are definitionally equal, even when the
equality evidence is an opaque proof. Its motive must still pass the genuine
fresh-endpoint check; agreement only at the supplied endpoint is insufficient.
A recursor for a fieldless singleton proposition also reduces to its single
branch when its proof subject is opaque. These proof-aware reductions do not
unfold opaque theorem bodies or provide full Lean eta.
Theorems remain opaque. Typed local `#pt-let` bindings support zeta reduction:
weak-head normalization substitutes the checked value into the body. There is
no cumulativity. Typed conversion also identifies
well-typed proofs of the same proposition, carrying the local context through
dependent binders; it does not identify arbitrary proposition types or data.
Conversion is not an unrestricted simplifier or a tactic search engine.

Exact structural syntax equality is checked before reduction and again after
weak-head normalization. It compares every binder index, universe, nominal
family, selector and child; a mismatch falls through to ordinary conversion.
Each substitution reuses the shifted argument at the same binder depth within
that substitution only. Natural-fold inspection leaves unrelated recursors
to the generic reducer and preserves bodies already independent of the local
being eliminated. These avoid repeated normalization of dependent predicates
without adding equality rules, trusting declaration names, or skipping source
typing, erased values, universe validation or opaque-body boundaries.

Consecutive lambda binders can reduce together: the checker substitutes all
their supplied arguments in one body walk rather than repeatedly copying the
remaining curried body. Argument order, free-variable shifts and any binders
remaining in the body retain ordinary beta semantics. Initial source checking
still validates every domain annotation, argument and erased value. Universe
specialization and term substitution share that walk: retained callee syntax
receives the callee's universe map, while inserted caller arguments retain
their own universes, including identically named parameters.

Depth accounting follows the contracted body beneath any remaining
applications. Each argument keeps the depth check for its own original
position in the input application spine. Consumed lambda/application frames
are no longer counted as traversed body frames. This changes which reductions
fit the existing depth limit of 96; it does not raise that limit or weaken
the separate traversal that validates original source syntax.

Each immutable term node derives a conservative loose-variable range and a
universe-dependence bit from all its children, including annotations, let
values and eliminator metadata. Substitution shares a subtree only when these
summaries prove that the operation leaves it unchanged. Overflow remains
conservative. The summaries cannot be supplied by proof input or serialized
cache metadata: construction and scratch decoding recompute them. Source
scope validation still traverses the original syntax in full.

Operation-local argument and traversal reuse tables remain metered and
bounded. The separate phase-local universe-specialization cache retains weak
source identities, exact universe maps and complete result heights. Its
optional sizing scan has its own allowance: if a large shared subtree makes
sizing too expensive, substitution returns its completed result without
caching it. Spent work and allocations remain charged. An identity result
needs no cache entry. None of these changes adds a mathematical equality rule,
unfolds opaque bodies, or authorizes a declaration by name.

Five alternating fresh-process pairs across seventeen accepted raw/native
controls show median replay times 6.70–33.65% lower and peak RSS 0.96–9.34%
lower than the preceding delayed-Euclidean build. Successful output matches
exactly. Two altered-evidence controls still finish with type mismatches in
every sample, giving 190 measured processes in total. These debug0 measurements
use identical proof profiles, a serial 2-GiB/two-core host guard, and ordinary
runtime allocator settings:

| Accepted replay | Median milliseconds before → after |
| --- | --- |
| Raw division composition | 341.039 → 226.272 |
| Native bitwise | 2,287.707 → 1,571.827 |
| Raw right shift | 221.383 → 178.990 |

This improves accepted replay and removes the general right-shift helper's
previous depth refusal. That general proof still exceeds the unchanged
1M-work profile at `Nat.shiftRight_add._f`; full bitwise stress and FLT replay
remain unfinished. Passing a larger diagnostic profile is not acceptance at
the required profile.

Typed function eta and primitive dependent Sigma pair eta are supported:

- At a checked function type, `f` converts to
  `(#pt-lambda ((x A)) (#pt-app f x))`, with a fresh `x`.
- At the same checked primitive Sigma type `S`, `p` converts to
  `(#pt-pair S (#pt-first p) (#pt-second p))`.

These examples are instances of type-directed comparison of any two terms
at a shared Pi or primitive Sigma type, not a restriction to a comparison with
one explicit lambda or pair constructor. Functions are compared by applying
both to a fresh argument and definitionally comparing the resulting bodies.
Pairs are compared through their first and second projections, retaining the
dependent type of the second component. Both rules are symmetric.

The checker verifies the shared type and shifts terms and typing contexts under
binders so existing free variables retain their meaning. It compares rigid
neutral heads and projection subjects without repeatedly eta-expanding those
same neutrals. Consequently, neutral Sigma values containing only proof fields
can convert through their projections consistently with proof irrelevance;
an explicit pair constructor is not required on either side.

The source evidence is fully inferred before eta reduction; comparison cannot
hide an ill-typed function argument, pair component, or dependent type.
Function eta is definitional conversion, not arbitrary equality-proof-driven
function extensionality. Proofs that two functions agree pointwise do not by
themselves make the functions definitionally equal: their fresh applications
must definitionally compare. Pair eta applies to the primitive dependent
Sigma type; mathematical record eta is checked separately below. Opaque theorem bodies stay
opaque. These rules do not imply full Lean eta or conversion parity.

The [eta regression suite](../tests/kernel_eta.rs) and
[kernel context tests](../src/proof/kernel/core_tests.rs) cover both orientations,
dependent result indices, capture-free context shifts, and rejection of
mismatched or ill-typed components. Neutral proof-field Sigma comparisons must
retain the same proof-irrelevance behavior under type-directed comparison,
without recursive re-expansion or collapse of distinct data components.

A separate unit-like data conversion rule identifies any two well-typed values
of the same fully applied, unindexed user datatype when that datatype has
exactly one constructor with zero fields. Indexed families are excluded
because their indices identify distinct fibres. The rule covers neutral variables, neutral
function results, and the constructor value in either comparison orientation.
It is universe-polymorphic, but both values must have the same checked nominal
family, universe instantiation, and datatype parameters.

This is value conversion at an already checked type, not a rule identifying
datatype types themselves. Different nominal datatypes, universe instantiations,
or parameter applications are not equated by it. A constructor with a data
field or recursive field does not qualify. Neither Nat nor the empty proposition
False qualifies. Such cases must still be checked by the other conversion
rules; this rule supplies no shortcut for their distinct values.

A recursor over qualifying unindexed fieldless data reduces to its sole branch
even when the subject is neutral, just as for the existing fieldless
singleton-Prop recursor. Indexed data families receive no such optimization. This
preserves computation congruence with the value conversion;
it does not require unfolding an opaque theorem body or inventing an inhabitant.
Source evidence and the shared fully applied type must be checked before the
rule is used.

A neutral recursor for an indexed proposition with exactly one zero-field
constructor reduces to its sole branch only when every supplied index converts
to the corresponding constructor result index. The constructor's universe
levels and uniform parameters are specialized before this comparison. This
uses proof irrelevance at the same fibre; it does not identify different
indices or unfold opaque theorem bodies. Generic or mismatching indices,
indexed data, and constructors with fields receive no such shortcut. Subject,
motive, indices, parameters, and branches still undergo full typing before
normalization. The [singleton proof example](../examples/proof_singleton_prop.lim)
and [regressions](../tests/kernel_singleton_prop.rs) exercise this distinction.

Type-directed Pi and primitive Sigma eta compose with proof irrelevance and
this unit-like data rule: applications or projections can compare through their
proof or qualifying fieldless components. This does not add arbitrary
equality-proof-driven function extensionality or full Lean conversion parity.

### Mathematical record projections and eta

`(#pt-project FAMILY INDEX SUBJECT)` projects a zero-based field of an
unindexed, single-constructor, nonrecursive mathematical inductive record.
The family is explicit; its parameters and universe instantiation come from
the checked subject type. The ordinal is an untyped nonnegative integer,
not a term or a name to resolve. Wrong families, out-of-range ordinals,
indexed families, and direct or function-recursive records are rejected.
Projections from constructor values reduce to the corresponding checked field.

Later fields retain their dependent types: the checker specializes the
constructor telescope with parameters, then substitutes earlier projections
of the same subject. For a record holding `A : Type u` followed by `value : A`,
projection 1 has the type given by projection 0. Both remain compile-time
mathematical terms; native structs and their access rules are unchanged.

Record eta compares all field projections of any two values at the same
checked nominal record type. Thus reconstructing a record from its fields
converts to the original value, in both orientations. Neutral records with
only proof fields compare consistently with proof irrelevance; records with
different data fields remain distinct. Rigid comparison of projection subjects
prevents repeated eta expansion. Eligible neutral record recursors compute
through the reconstruction too, preserving congruence with eta.

Projection cannot extract data from Prop. The guarded-universe implication
must establish that a requested field is proof-valued whenever the record is
a proposition. It also applies to earlier fields needed by the remaining
telescope: a final proof projection cannot expose a hidden data witness
through its dependent type. A syntactically unused predecessor can be skipped.
Neutral recursor reconstruction is disabled when it would require forbidden
data projections. These checks precede reduction, including for constructor
fields that would otherwise be erased. Opaque theorem bodies stay opaque.

See the [record example](../examples/proof_records.lim),
[source regressions](../tests/kernel_records.rs), and
[navigation tests](../tests/kernel_projection_navigation.rs). This restricted
record rule does not supply quotient soundness or the full FLT dependency
replay. Bounded proof-source translation and quotient computation replay use
the separate [export reader](lean-export.md). Nested groups use the rule below.

### Mutual inductive groups

Each family remains a separate `#math-inductive` declaration. Put the same
ordered `(#mutual FAMILY...)` clause directly after its parameter list,
before any `#indices` clause, on every member. A group has 2 through 16
distinct families, includes each declaration itself, and shares universe
parameter names, a uniform parameter telescope, and result sort. Each member
may have its own dependent index telescope and constructor set.

```lisp
(#math-inductive tree () () (#mutual tree forest) (#pt-type 0)
  ((node ((children (#pt-recur forest ()))))))
(#math-inductive forest () () (#mutual tree forest) (#pt-type 0)
  ((empty ())
   (cons ((first (#pt-recur tree ())) (rest (#pt-recur forest ()))))))
```

`(#pt-recur FAMILY (index-terms...))` selects a group member for a recursive
field, inheriting the group's parameters and universe instantiation. It may
be the terminal codomain of a strictly positive dependent function field.
Bare `#pt-self` and `#pt-self-at` still select the current family. Explicit,
fully applied group-family types are also checked for the same uniform
parameters, universes and index arity; using an arbitrary type expression
does not waive positivity.

No group member may occur in a function domain, group parameter/index type,
recursive argument's indices, constructor result indices, or a let's
annotation/value. Unknown containers and recursive aliases remain rejected.
Headers are checked before provisional installation; the complete group is
installed only if every constructor checks. Failure removes every provisional
member, preserving preexisting declarations. Ordinary dependency cycles do
not implicitly declare a mutual group.

```text
(#pt-mutual-induct SELECTED (levels...) (parameters...)
  (#indices selected-index-terms...)
  ((FAMILY motive (branches...))...)
  subject)
```

The case list covers every member exactly once in declaration order. The
`#indices` clause is always present and is empty for an unindexed selected
family. Each motive binds its family's fresh generic indices and then a
subject of that family. All motives and branch sets are checked, including
siblings unused by the concrete subject. `#pt-induct` cannot eliminate a
mutually declared family.

A recursive field is immediately followed by the induction hypothesis for
the **child's family and actual indices**. A function field gets a pointwise
hypothesis with the same dependent argument telescope. Later field types,
all motives, and captured branch terms retain their binder meanings when IHs
are inserted. Computation applies the branch to fields and these child
recursors; it does not call an external prover or assume an axiom.

Mutually declared propositions eliminate only to Prop, even when one member
alone has a singleton constructor. Every motive must satisfy this guarded
restriction for Sort-polymorphic groups. Unit, indexed-singleton K and record
projection/eta shortcuts do not apply to components of a mutual group.
Native functions still cannot recurse; these are compile-time mathematical
inductive terms.

## Nested inductive groups

A recursive field can apply a previously checked inductive container to an
explicit, fully applied reference to the new family. For example:

```lisp
(#math-inductive seq () ((Element (#pt-type 0))) (#pt-type 0)
  ((nil ()) (cons ((first Element) (rest #pt-self)))))
(#math-inductive tree () () (#pt-type 0)
  ((leaf ())
   (node ((children (#pt-app (#pt-use seq ()) (#pt-use tree ())))))))
```

The checker derives a recursion case for `tree`, followed by one for `seq tree`.
It specializes the container's checked constructors and verifies every field's
positivity. It keeps the original container types and constructor names; no
private auxiliary identifier needs to appear in source.

```text
(#pt-nested-induct FAMILY (levels...) (parameters...) CASE-INDEX
  (#indices selected-index-terms...)
  ((#pt-case PARTIALLY-APPLIED-FAMILY-TYPE MOTIVE (BRANCHES...))...)
  SUBJECT)
```

The `FAMILY` operand names the owner declaration whose nested group is used.
`CASE-INDEX` is an explicit untyped, zero-based integer selecting the case to
eliminate: `0` selects the first root and `1` selects `seq tree` in this example.
The subject and index terms must have the selected case's type and indices;
out-of-range indices are rejected. This permits container recursor wrappers
without naming internal identifiers or inferring a case from the subject.

Cases cover all declared group roots in declaration order, followed by the
specialized containers in breadth-first derivation order. Identical structural
specializations share a case; distinct specializations remain separate. For the
example above, the selectors are `(#pt-use tree ())` and
`(#pt-app (#pt-use seq ()) (#pt-use tree ()))`. Each selector is a checked term,
then compared definitionally with the expected family type. A type alias can
therefore select the same case, but an ill-typed argument cannot disappear
through conversion. Selectors declare no bindings. `#pt-case` is only valid
inside this case list.

Selectors apply uniform parameters but leave indices unapplied. An indexed
container selector is `vector tree`, rather than `vector tree length`; its
motive binds all generic indices followed by its subject. All branch lists use
original constructor order, with each recursive field immediately followed by
its family-specific IH, including pointwise IHs for function fields. Every
motive and branch is checked, even for an empty subject. The selected case's
index clause is explicit, including `(#indices)` when it has no indices.

Nested parameters cannot capture constructor-local variables or surrounding
function arguments, change the root's uniform parameters/universes, or put the
root in container indices. Negative occurrences and unchecked type functions
are rejected. Nested `#pt-self` markers are not container arguments: spell the
root's type and parameters explicitly. Direct recursion under primitive
`#pt-sigma` is unsupported; a declared dependent-pair container is checked by
specializing its constructor just like any other container. Construction,
projection and elimination of provisional families remain forbidden. Nested
propositions retain the mutual Prop elimination restriction.

The [native example](../examples/proof_nested.lim) implements both the tree
and container counts, proves their generic defining equations, and checks a
nonempty tree's result by reflexivity. The export reader uses the same
checked group and additionally verifies exported auxiliary recursor types and
rules; see [nested replay](lean-nested-replay.md). The [bounded export translator](lean-export.md#native-proof-source-translation)
emits these native wrappers and independently rechecks its output. Full upstream
FLT translation and replay remain unfinished.

The [tree/forest example](../examples/proof_mutual.lim) defines both count
functions, checks their general defining equations, and computes a concrete
count. The [functional example](../examples/proof_mutual_function.lim) checks
pointwise sibling recursion at each child's index. Neither completes the
full-environment proof-source translation and FLT replay work.

The kernel has no cumulativity, `admit`, general recursion,
metavariable holes, or automatic proof synthesis. Finite source, checking, and
normalization resources still apply; resource exhaustion must fail checking,
not stand in for evidence. Unsupported features are not enabled by selecting a
larger universe or reusing a cache entry.

Three reserved global logical foundations are available only through explicit
`#pt-use` references: propositional extensionality, Church-encoded choice, and
quotient soundness. They are axioms rather than proved facts. Choice accepts
propositional nonemptiness evidence and returns a value without exposing a
data witness or adding a computation rule; quotient soundness does not create
definitional equality between representatives. Application checks each
premise by the ordinary kernel rules. These are exactly the logical foundations
matching Lean's pinned FLT axiom basis; they are not an FLT proof or an
axioms-free result. Raw Lean imports still reject axioms by default. The native
theorem CLI reports the transitive foundation inventory, excluding unused
foundations elsewhere in the environment. See the [language reference](language.md#compile-time-proofs).
Explicit [pinned axiom replay](lean-export.md#explicit-logical-foundations)
checks opaque adapters for only these three fixed assumptions and compares
the imported target's inventory with the rechecked native theorem.

## Resource bounds

Mathematical checking accepts an explicit `ProofBudget` through
`CompileConfig::set_proof_budget`. The checking commands also accept
`--proof-work N`, `--proof-phase-bytes N`, and `--proof-total-bytes N`.
Omitted values retain the defaults below. Values must be positive ASCII decimal
integers; work is limited to 100,000,000, phase traffic to 1 GiB, and cumulative
traffic to 64 GiB. These are accounting limits, not measurements of live memory.
The separate host memory/CPU guard, recursion depth, numeral bounds, source
validation and logical foundation policy remain in force. No limit grows
automatically, and exhaustion establishes no theorem.

For example, a deliberately selected larger replay budget is:

```sh
lim --check-theorem proof.lim theorem-name --proof-work 1000000 \
  --proof-phase-bytes 134217728 --proof-total-bytes 1073741824
```

For compiler development, the `proof-kernel-tests` Cargo feature keeps every
proof test enabled while compiling frontend modules with their production
test-hook configuration. This avoids building the unrelated frontend unit
tests into the same large executable. It changes no mathematical rule,
runtime compiler behavior, or default test selection. Under the host guard:

```sh
bash scripts/limited-run.sh nix develop -c env \
  CARGO_PROFILE_DEV_DEBUG=0 CARGO_PROFILE_TEST_DEBUG=0 CARGO_INCREMENTAL=0 \
  MALLOC_CONF=narenas:1,dirty_decay_ms:0,muzzy_decay_ms:0,tcache:false \
  MALLOC_ARENA_MAX=1 cargo test --features proof-kernel-tests --lib
```

Also run ordinary `cargo check --all-targets` under the guard, without this
feature, to type-check the complete default frontend test configuration.
Ordinary `cargo test` retains the full test suite. The isolated proof harness
has checked all 537 kernel tests plus 24 other proof tests within the 2-GiB cap;
two manual storage benchmarks remain ignored.

A native program accumulates mathematical transformation traffic across its
checked declarations and complete mutual groups. A raw export accumulates it
across replay phases. Cumulative accounting is audited at phase boundaries.
Translation rechecks its native output independently
using the same selected limits; each check has its own counters. Ordinary
procedural theorem/SAT budgets are separate. Resource errors identify the
exhausted counter or fixed recursion depth. The returned `CheckedTheorem`
records its selected budget.

Nondefault `lim.lsp` contexts retain the same three settings as bare numeric
`proof-work`, `proof-phase-bytes`, and `proof-total-bytes` entries. This keeps
editor checking consistent with `--check --write-lsp-config`.

The current implementation applies these limits independently of the
mathematical meaning of a type:

| Resource | Limit |
| --- | --- |
| Core checking and conversion work | 200,000 core steps per declaration or complete mutual group. |
| Term transformation allocations | 64 MiB accounted nodes, payloads and traversal/reuse tables per core budget. |
| Cumulative mathematical transformations | 256 MiB accounted traffic per native program or raw replay. |
| Recursive kernel depth | 96. |
| Parsed mathematical nodes | 50,000 per declaration. |
| Mathematical parser nesting depth | 64. |
| Universe parameters and explicit universe arguments | At most 32 per list. |
| Mutual inductive families and eliminator cases | 2 through 16, checked as one group. |
| Pi/lambda binders, term application arguments, and recursor branches | At most 64 per list. |
| Source universe constants and normalized affine offsets | At most 65,535; not a bound on level-variable values. |
| Normalized level monomials | At most 256 per term. |
| Nonzero guard variables | At most 64 per term. |
| Level normalization work | 200,000 work units per normalization operation. |
| Symbolic level comparison work | 50,000 work units per inequality. |
| Inductive parameters | At most 64. |
| Constructors | At most 64 per datatype. |
| Constructor fields | At most 64 per constructor. |
| Native mathematical declarations | Closed artifacts default to 4,096 with explicit `NativeProofLimits` profiles. Ordinary source schedules its complete, finite loaded graph. |
| `#pt-numeral` abbreviation | Source integers from 0 through 128. |
| `#pt-nat-literal` decimal length | At most 4,096 canonical unsigned decimal digits. |

Universe normalization, zero-status guard analysis, and level comparisons have
separate bounded work budgets in addition to the 200,000-step core checking
budget per term declaration. These budgets are independent: a normalization
operation has its own 200,000-work limit, and an inequality has its own
50,000-work limit. Exhaustion returns an error, never a successful comparison,
an accepted elimination, or a theorem.

The source constant and affine-offset bound of 65,535 is a representation and
resource bound, not a finite model of universe parameters. Level variables
still range over all natural numbers without an upper bound. Symbolic order is
checked exactly over those assignments; no sampling checker substitutes a
finite collection of universe values. The existing limit of 32 source universe
parameters is unchanged.

Parser limits and kernel limits are separate checks. A term that parses may
still exceed checking or conversion resources. Exhaustion rejects the
obligation; it does not permit an unchecked term or count as a proof of
unreachability. The numeral bound limits source expansion, not Nat: larger
naturals can be described by constructors and checked definitions, subject to
resources, and universal natural-number proofs remain unbounded.

Transformation accounting also bounds expansion of shared term graphs during
substitution and universe instantiation; a small input DAG cannot authorize
unbounded allocation. It includes temporary nodes and owned identifier/level
payloads, rather than measuring exact RSS. Structural comparison also charges
its pending pairs and visited set, and substitution charges its local reuse
table before inserting entries. The
normalizer reuses an already checked monomorphic declaration's immutable body
when no universe substitution is needed. Global type lookup likewise reuses
its checked monomorphic signature; polymorphic signatures are still explicitly
specialized without changing the original. Source scope validation still walks
every declaration, including erased terms; explicit universe arity, polymorphic
substitution and opacity checks remain in force. The
[elaborated export reader](lean-export.md) additionally bounds line buffers,
primitive tables, graph depth, dependency receipts and cumulative transformations
across declarations. Exported types, bodies and recursor rules are checked by
this same kernel; cached receipts and exporter claims cannot bypass it.

For a focused comparison of monomorphic signature reuse, build two compiler
versions with the same profile and run:

```sh
bash scripts/limited-run.sh python3 scripts/benchmark-proof-signatures.py \
  --before /path/to/before/lim --after target/debug/lim
```

The benchmark checks 200 reflexivity theorems over a function type with 20
explicit parameters, alternates compiler order and reports wall medians and
child CPU means. This targeted workload does not predict every corpus's speed.

## Trust assumptions

This is an implemented proof checker, not a formally verified kernel. Accepting
a term relies on the correctness of its parser, scope and dependency handling,
universe checks, type checker, substitution, and conversion implementation,
as well as the surrounding validation machinery. Structural arithmetic and
observational fusion are part of this trusted conversion implementation;
their pattern guards and differential tests do not formally verify them.
Explicit evidence and
rechecking reduce reliance on cached results; they do not establish the
implementation's soundness by themselves.

The three explicit logical foundations are additional mathematical assumptions,
not proved lemmas. Their fixed signatures are constructed directly by the
kernel, without parsing an input-supplied postulate, and checked before use.
Checking a signature does not prove the axiom or the consistency of the theory.
The selected theorem's inventory conservatively follows types and bodies,
including opaque initializers and erased local values; it excludes unrelated
declarations. The [example](../examples/proof_foundations.lim) shows each basis
entry separately. There is no general axiom or proof-hole interface.

The native certificate adapter additionally trusts the existing procedural
checker and its program model, including the analyses, solver, or target-stack
analysis used by the named obligation. A certificate proves only the
corresponding checked proposition atom under those assumptions. It is not a
proof of compiler correctness, faithful code generation, a native executable's
entire behavior, or the runtime, operating system, and hardware. In particular,
mathematical type checking does not independently verify a procedural solver's
implementation merely by consuming its accepted certificate.

## Conceptual background

Lean's official documentation explains the background ideas, rather than Lim's
syntax or exact rules:

- [Universes](https://lean-lang.org/doc/reference/latest/The-Type-System/Universes/)
  explains sorts and universe polymorphism.
- [Propositions and proofs](https://lean-lang.org/theorem_proving_in_lean4/Propositions-and-Proofs/)
  introduces the propositions-as-types view.
- [Inductive types](https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/)
  explains constructors, recursors, and elimination restrictions.

Lean also has features absent here, including full-environment replay and richer
inductive families. Definitional proof irrelevance is supported, but does not establish
full conversion parity. Use the rules in this guide for Lim, not an inference that a term
accepted by Lean or a mathlib theorem is available in Lim. For the procedural
layer and the complete builtin reference, see [the language reference](language.md#compile-time-proofs).

### Quotient terms

The source forms `#pt-quot`, `#pt-quot-make`, `#pt-quot-lift`, and
`#pt-quot-induct` construct immutable quotients by an arbitrary binary relation
`TYPE → TYPE → Prop`; the relation need not be an equivalence. Their exact
operand layouts and typing checks are listed in the [language reference](language.md).
Universe levels are explicit. The lift checks its respect proof before computing
on constructors, and induction is restricted to Prop. The pinned four-record
quotient computation package also [replays and translates](lean-export.md)
through independently checked wrappers, with an explicit primitive foundation
inventory. Quotient soundness is available only through the explicit opaque
`#pt-foundation-quot-sound` logical foundation; no representative computation
or definitional equality follows from it. See the
[native quotient example](../examples/proof_quotient.lim).

Closed applied history projections can now observe their checked Euclidean
recurrence inside the delayed machine. The unchanged source validator certifies
the nominal natural family, first-field function type, guard, state decrement,
recursive field, terminal and result increment. Recognition happens before
operand forcing, using a private positive-count view only to inspect the
successor template; the original subject stays in its thunk. Unrelated history
folds retain their lazy payloads. Input and fuel stay in their own environments
and are forced through continuations. Success requires actual
fuel strictly greater than the quotient; a proof argument never supplies that
bound. The uninterrupted projection/input/proof frame suffix prevents crossing
an update that memoizes a function or record. Only the complete application is
replaced with a fresh literal.

Models are local to one machine. Reuse requires the same record and nominal
natural family and exact immutable motive/step code with equal free captured
sources. The binder-aware dependency collector includes annotations and let
values. It retains source ownership, never uses a neutral head as a term, and
conservatively misses on unsupported distinct recursive thunks. The arbitrary
base and actual fuel are excluded from the model key because sufficient fuel
prevents reaching the base; the fuel test repeats for every invocation.
Monomorphic code templates share the same metered VM cache as universe
specializations, preserving source identity under declaration paging.
Already available natural inputs up to 32 retain ordinary reduction: a bounded
peek follows existing memo entries and captured variable aliases without forcing
an operand. This avoids model setup for small computations, particularly with
cold declaration tables.

The original complete call is scheduled before eager wrapper exposure, including
higher-order wrappers whose intermediate result is an applied motive rather
than a literal Pi telescope. Eligibility still requires the original root's
checked scalar result and scalar parameter types; no template or function name
establishes a result. Newly eligible forwarded scalar folds get a bounded
compact-arithmetic attempt first. Existing packed-record wrappers retain their
original observation schedule. Remaining scalar folds use
the existing wider observation policy after affine/subtraction decline, with
fallback reserves and enclosing hard/probe limits intact. The [right-shift corpus](../tests/fixtures/lean_export_right_shift/README.md)
records the accepted runtime proofs. The separate
[general division corpus](../tests/fixtures/lean_export_right_shift_general/README.md)
checks the original unbounded `Nat.shiftRight_eq_div_pow` proof over 489
declarations in raw and native form, with exactly `propext`, at the explicit
20M-work/1-GiB-phase/4-GiB-total profile. Its 1M-work replay remains an
optimization gap. Raw input `LeanExportLimits` are separate from these kernel
budgets: selecting larger cumulative input totals never grants mathematical
authority or increases resident cache sizes. Native source and scratch format
bounds remain independently enforced.


Closed mathematical artifacts can select cumulative native output, declaration,
source-directory and original/native correspondence limits through
`NativeProofLimits`. This is separate from `ProofBudget` and `LeanExportLimits`.
The original limits remain defaults, and per-form/depth bounds remain fixed.
`--check-proof-artifact` freezes and checks the complete emitted source in a
fresh kernel without imports, generators, general-source fallback or cached
judgments. Every unreachable or later declaration remains an obligation.
Nondefault profiles are audit data in generated source comments and receipts.
See the [native profile reference](lean-export.md#resource-limits-and-unsupported-features).


Raw replay and fresh native proof checking select kernel scratch capacity
explicitly and independently. `LeanExportLimits.max_scratch_bytes` and
`NativeProofLimits.max_scratch_bytes` default to 128 MiB per backing file.
The selected capacity reaches original and cold declaration directories,
encoded declaration blobs, and both nested-family stores, while their
resident thresholds and per-record bounds remain fixed. This selects storage
capacity only: checked objects still round-trip before release, cold bytes
remain authenticated within the same invocation, and no source or receipt
can insert a cached judgment. Kernel work and source-snapshot bounds remain
independent.

The native declaration scheduler resolves dependency names incrementally
against the immutable source-name directory. It retains numeric compressed
group and reverse-edge lists, preserving source priority and explicit mutual
member order without retaining all dependency strings. Its metadata remains
planning data: every ready declaration is reparsed and checked, all explicit
mutual groups are revalidated, and unreachable or later bodies are never
omitted. The graph is still resident and scales with actual declarations and
distinct group edges; the synthetic scheduler benchmark does not establish
full-proof checking or a real full-environment memory bound.
