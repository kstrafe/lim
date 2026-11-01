# Nested inductive replay

The export reader checks nested inductives by deriving a finite recursion
group from the new declarations and the constructors of previously checked
containers. For `Rose.node : List Rose -> Rose`, the group has a case for
`Rose` and a case specialized to `List Rose`. The latter has the original
`List.nil` and `List.cons` constructors, with fields specialized to `Rose`.
Its head field recurses into the Rose case; its tail recurses into the list
case. This supplies both hypotheses without treating an arbitrary type
application as positive.

The implementation follows the purpose of Lean 4.33.1's
[nested-inductive transformation](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/kernel/inductive.cpp#L1003),
using checked views of the original containers rather than installing global
auxiliary datatypes. Every view retains its physical type, such as `List Rose`,
and constructor identities. Private case identifiers cannot be used as global
constants or constructors. Existing container declarations remain unchanged.

## Construct the group

All main headers are checked before their provisional signatures are visible.
When a field applies a checked container to arguments containing a new family,
the complete application is type checked. Parameter arguments are scoped over
the declaring group's uniform parameters. They may bind their own lambdas,
but cannot capture constructor fields or surrounding function-field binders.
All new-family occurrences in those arguments must retain the declaration's
parameters and universe instantiation, including occurrences that later beta
reduction could erase. A new family cannot occur in a container index.

The source constructor telescopes are specialized and checked in full before
their fields are normalized. This supports dependent parameters such as
`Sigma (fun n : Nat => Rose)`, whose second field becomes Rose after applying
the parameter to the first field. Unused arguments and annotations still have
to type check. Positivity is checked on every specialized field, so a checked
container with a contravariant parameter is rejected at its negative field.
There is no trusted user-supplied covariance flag.

Main and auxiliary cases share the uniform parameter telescope and result
sort. Auxiliary index types cannot refer to the new family. Source mutual
members retain declaration order, even when a later member introduced the
specialization. Further container occurrences are processed in a queue.
Structural comparison, with bounded work and shared-node tracking, deduplicates
repeated specializations. It performs no conversion through provisional types.
The expanded group is limited to 16 cases. A failure removes every new main
signature and scoped view, preserving the prior checked environment.

Constructors, projections and eliminators of a provisional family cannot be
used while checking that group's signatures. Otherwise a parameter expression
could incorrectly use an unfinished family as if it were empty. This applies
even to phantom parameters whose values disappear from the specialized fields.

## Check and compute recursors

The derived group determines all motive and branch types. A recursive field's
hypothesis uses its own case and actual indices. Functional fields receive
pointwise hypotheses. Fields and hypotheses stay interleaved in Lim's kernel;
the export adapter checks functions that translate Lean's fields-first calling
convention into that order. Dependent later fields are shifted across inserted
hypothesis binders.

The primary declarations have their standard `.rec` wrappers. Scoped cases
correspond to `.rec_1`, `.rec_2`, and subsequent wrappers on the first main
declaration. Their types, universe parameters, counts, constructor ownership,
rule coverage and K flags must match the independently derived group. Each
supplied rule is type checked and compared with the derived wrapper applied
to the corresponding original constructor. Exported rules never become
reduction authority.

Computation consumes the original constructor fields and dispatches every
recursive child to its case, including children inside other containers.
Mutually recursive propositions retain the Prop elimination guard; nesting
does not authorize extracting hidden data. Unit/K/record shortcuts do not
apply to a component merely because its specialized shape has one constructor.

## Evidence and scope

The committed [genuine producer fixtures](../tests/fixtures/lean_export/README.md)
cover a nonempty list fold, universe-polymorphic parameters, an indexed vector
container, two distinct list specializations and dependent Sigma parameters.
Kernel tests cover repeated specializations, source mutual order, both child
hypotheses, negative fields, local capture, erased nonuniform parameters,
provisional elimination and Prop-to-data attacks. Corrupted exported counts,
flags and rules must still fail. Resource exhaustion establishes no theorem.

This is currently an elaborated-replay capability. Native `.lim` mathematical
declarations and eliminator syntax have not gained an auxiliary-case form,
and native proof-source translation remains unfinished. The kernel is not
formally verified; these fixtures do not establish complete Lean compatibility
or check the full FLT proof. Existing input, universe, work and allocation
[bounds](lean-export.md#resource-limits-and-unsupported-features) continue to apply.
