# Lean export fixtures

All files here are independently hand-authored protocol fixtures, not exports
from Lean or FLT. They contain no copied upstream proof text. They use the
pinned lean4export NDJSON 3.1.0 protocol.

`identity.ndjson` contains a polymorphic transparent `Audit.identity`
definition (`forall A : Sort u, A -> A`) and
`Audit.identity.theorem`, a constructive proof of `forall P : Prop, P -> P`
that specializes the definition at `Prop`. This exercises universe parameters,
specialization, and declaration dependency closure.

`inductives.ndjson` adds independently declared nominal `Nat`, indexed `Eq`,
and a dependent record `Package`. Its checked recursors compute doubling and
equality transport, and its projection theorem checks a dependent record
projection. Targets are `Replay.doubleTwo`, `Replay.transport` and
`Replay.projection`; all 15 declarations are checked for any target.

`mutual.ndjson` extends that fixture with `Tree` and `Forest`, both recursors,
and depth functions. `Forest.cons` has two recursive fields, so its exported
branch binds both fields before both hypotheses and exercises the adapter to
Lim's interleaved convention. Target `Replay.mutualDepth` computes a depth of
two; all 25 declarations are checked.

Metadata pins lean4export 3.1.0, Lean 4.33.1 at git hash
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, and format 3.1.0. The record
shapes follow the primary format document:
<https://raw.githubusercontent.com/leanprover/lean4export/v4.33.0/format_ndjson.md>.

See [the replay guide](../../../docs/lean-export.md) for commands, trust,
receipt hashes, bounds and unsupported forms. Passing these fixtures does not
establish compatibility with arbitrary Lean exports or the full FLT proof.
