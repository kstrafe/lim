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

`#pt-prop` denotes `Sort 0`, the sort of propositions. `(#pt-type L)` denotes
`Sort (L + 1)`: `(#pt-type 0)` is the first data-type universe, not `Prop`.
Thus `#pt-prop` is itself a term classified in a higher sort; a proposition
such as `(#pt-eq #pt-nat n n)` is an inhabitant of `#pt-prop`.

Levels are explicit syntax:

| Level syntax | Meaning |
| --- | --- |
| `0`, `1`, ... | Nonnegative integer universe levels. |
| `u` | A universe parameter declared by this mathematical declaration. |
| `(#pt-level-succ u)` | Successor of a level. |
| `(#pt-level-max u v)` | Maximum of the listed levels. |

Level expressions are not arbitrary native or kernel term computations.
There is no implicit universe inference or cumulativity: inhabiting one
universe does not automatically coerce a term into a larger universe.

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
this expresses universal quantification or implication. A dependent function
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
its endpoints do not already convert. There is no proof-irrelevance conversion
rule: arbitrary proofs of the same proposition are not automatically equal.

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

The initial user-inductive language supports parameters and direct recursive
fields. It does not support indices, nested recursive occurrences, or mutual
recursion. Write `#pt-self` only as the complete type of a direct recursive
constructor field, not inside a Pi, Sigma, parameter application, or another
type former. It is not a general reference to the enclosing declaration.

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

The kernel checks constructor types, recursive positions, branch types, and
universe constraints. A declaration is not accepted merely because its surface
syntax resembles a familiar inductive datatype.

## Falsehood and elimination from propositions

`#pt-false` denotes an empty proposition and has no introduction constructor.
There is no `admit` or axiom declaration that supplies a proof of it.

An inductive proposition normally eliminates into propositions. Elimination
from `Prop` into a data-type universe is restricted to empty inductives or
single-constructor inductives whose fields are all proofs. Merely having one
constructor is insufficient if a field carries data. This prevents arbitrary
extraction of computational data from propositional witnesses. The restriction
is a kernel rule, not a runtime representation or erasure promise.

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
constructors. Pair projections compute on pairs, and equality elimination J
computes at reflexivity. Theorems remain opaque. There is no zeta reduction
for term lets, since term `let` is unsupported, and no eta conversion,
cumulativity, or proof-irrelevance conversion. Conversion is not an unrestricted
simplifier or a tactic search engine.

The initial kernel has no term `let`, eta conversion, proof irrelevance,
cumulativity, quotients, classical axioms, `admit`, general recursion,
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
| Constant universe level | At most 65,535. |
| Inductive parameters | At most 64. |
| Constructors | At most 64 per datatype. |
| Constructor fields | At most 64 per constructor. |
| Mathematical declarations | At most 4,096. |
| `#pt-numeral` abbreviation | Source integers from 0 through 128. |

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

Lean also has features deliberately absent here, including definitional proof
irrelevance. Use the rules in this guide for Lim, not an inference that a term
accepted by Lean or a mathlib theorem is available in Lim. For the procedural
layer and the complete builtin reference, see [the language reference](language.md#compile-time-proofs).
