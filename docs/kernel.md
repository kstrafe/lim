# Constructive proof kernel

Lim has two compile-time proof layers. Procedural proofs check claims about the
validated native program using structural analysis, bounded symbolic execution,
and target-specific certificates. The mathematical kernel checks explicit terms
in a constructive dependent type theory. Both expose named `#theorem`
declarations, but their terms, types, and evidence are distinct. Mathematical
data and datatype declarations use `#math-definition` and `#math-inductive`.

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

The public declaration shapes are:

```text
(#theorem NAME
  (#universes u...)
  (#parameters (#parameter name TYPE)...)
  (#statement CLAIM)
  (#proof EVIDENCE))

(#theorem NAME PROCEDURAL-CLAIM)

(#math-definition NAME (universe...) TYPE VALUE)

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
nonnegative source integer of at most 128 and expands it into a Peano successor
spine. This resource bound does not bound the mathematical type or its universal
quantifiers.

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
current family's indices. Mutual recursion and recursion nested in containers
or Sigma types remain unsupported.

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
and current-index occurrences of the family, as well as recursion nested in
containers or Sigma types.

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
Mutual and nested inductives remain unsupported.

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
Sigma type, not general user-inductive records. Opaque theorem bodies stay
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
proof or qualifying fieldless components. This does not add eta for arbitrary
user-inductive records with fields, arbitrary equality-proof-driven function
extensionality, or full Lean conversion parity. No public syntax is added.

The kernel has no cumulativity, quotients,
classical axioms, `admit`, general recursion,
metavariable holes, or automatic proof synthesis. Finite source, checking, and
normalization resources still apply; resource exhaustion must fail checking,
not stand in for evidence. Unsupported features are not enabled by selecting a
larger universe or reusing a cache entry.

## Resource bounds

The current implementation applies these limits independently of the
mathematical meaning of a type:

| Resource | Limit |
| --- | --- |
| Core checking and conversion work | 200,000 core steps per declaration. |
| Recursive kernel depth | 96. |
| Parsed mathematical nodes | 50,000 per declaration. |
| Mathematical parser nesting depth | 64. |
| Universe parameters and explicit universe arguments | At most 32 per list. |
| Pi/lambda binders, term application arguments, and recursor branches | At most 64 per list. |
| Source universe constants and normalized affine offsets | At most 65,535; not a bound on level-variable values. |
| Normalized level monomials | At most 256 per term. |
| Nonzero guard variables | At most 64 per term. |
| Level normalization work | 200,000 work units per normalization operation. |
| Symbolic level comparison work | 50,000 work units per inequality. |
| Inductive parameters | At most 64. |
| Constructors | At most 64 per datatype. |
| Constructor fields | At most 64 per constructor. |
| Mathematical declarations | At most 4,096. |
| `#pt-numeral` abbreviation | Source integers from 0 through 128. |

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

## Trust assumptions

This is an implemented proof checker, not a formally verified kernel. Accepting
a term relies on the correctness of its parser, scope and dependency handling,
universe checks, type checker, substitution, and conversion implementation,
as well as the surrounding validation machinery. Explicit evidence and
rechecking reduce reliance on cached results; they do not establish the
implementation's soundness by themselves.

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

Lean also has features absent here, including quotients and richer inductive
families. Definitional proof irrelevance is supported, but does not establish
full conversion parity. Use the rules in this guide for Lim, not an inference that a term
accepted by Lean or a mathlib theorem is available in Lim. For the procedural
layer and the complete builtin reference, see [the language reference](language.md#compile-time-proofs).
