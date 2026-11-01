# Checking elaborated Lean exports

Lim can replay a bounded subset of lean4export's NDJSON declarations through
its dependent proof kernel. The exporter supplies syntax, not evidence that a
declaration has been checked. Every accepted type, definition, theorem,
constructor and recursor is checked locally. No Lean process is executed.

```sh
lim --check-lean-export tests/fixtures/lean_export/identity.ndjson \
  Audit.identity.theorem --report /tmp/identity-replay.json --timings

lim --check-lean-export tests/fixtures/lean_export/mutual.ndjson \
  Replay.mutualDepth
```

These commands check hand-authored protocol fixtures. Additional genuine
producer outputs are recorded in the [fixture guide](../tests/fixtures/lean_export/README.md#actual-pinned-producer-outputs):

```sh
lim --check-lean-export tests/fixtures/lean_export/real-mutual.ndjson \
  ReplaySource.mutualDepth
```

Four real exports of original small Lean proofs replay successfully; the
nested-inductive fixture is intentionally rejected. They do not check the
upstream Fermat proof. The reader does not yet emit equivalent native `.lim`
source or handle the complete Lean/Mathlib environment. See the
[port roadmap](lean-compatibility.md) for the remaining work.

## Exact protocol pins

| Component | Required value |
| --- | --- |
| Exporter metadata | `lean4export`, version `3.1.0` |
| NDJSON format | `3.1.0` |
| Lean version | `4.33.1` |
| Lean revision | `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` |
| Reference exporter revision | `15f6055e299ad5b89345e533cc2192f4cc00f659` (`v4.33.0`) |

The metadata versions are distinct from the exporter's repository tag. The
record shapes follow the pinned
[NDJSON specification](https://github.com/leanprover/lean4export/blob/15f6055e299ad5b89345e533cc2192f4cc00f659/format_ndjson.md)
and [exporter](https://github.com/leanprover/lean4export/blob/15f6055e299ad5b89345e533cc2192f4cc00f659/Export.lean).
The reader requires matching metadata. Metadata is a compatibility claim, not
authentication of the producer or the source repository revision.

## What is checked

Names preserve string-segment boundaries and distinguish numeric segments from
strings. A name containing a literal dot cannot impersonate a hierarchical
name. Universe levels support zero, successor, parameters, `max` and `imax`.
Expressions support bound variables, general sorts, explicitly instantiated
constants, applications, lambdas, dependent function types, typed local lets,
record projections and metadata wrappers. Metadata wrappers do not supply
typing rules. Natural literals expand to constructors of the imported,
independently checked standard `Nat` signature; they cannot rebind Lim's
internal natural-number type by sharing its printed name.

Definitions and opaque definitions must have checked bodies. Theorem bodies
must inhabit proposition-valued types and stay opaque after checking. Unknown
or unchecked dependencies, unsafe or partial declarations, duplicate identities,
free variables, metavariables and unknown record forms are rejected. Table IDs
must be contiguous; table references must point backwards. Every record has a
checked schema, and duplicate JSON keys are rejected.

For regular, indexed and mutual inductive blocks, Lim reconstructs the family
headers and constructors and runs its own positivity, parameter, index and
universe checks. It constructs recursors from those checked families, rather
than installing exported reduction rules. Lean's minor premises bind fields
before induction hypotheses; adapters reorder these into Lim's interleaved
field/hypothesis convention and are themselves type checked. Exported recursor
types and every supplied computation rule must check and agree with the
derived recursor. Constructor ownership, rule coverage, field counts, family
membership and the restricted K flag are checked against the derived shapes.

The selected target must be an actual theorem, not a proposition-valued
definition. Success requires reaching EOF and checking all declarations,
including those after the target. A later malformed record or read error
invalidates the entire run. The command emits no native binary. A report is
published atomically only after success; input aliases, including hard links,
cannot be used as report destinations.

## Replay receipt and identity

`--report PATH` writes JSON with schema `lim-lean-replay-v1`. It records the
target, exact input byte count and SHA-256, record count, protocol/toolchain
pins, and every accepted declaration's display name, canonical identity, kind,
record line, SHA-256 and direct dependencies. The axiom inventory is empty
because all axiom and quotient records are rejected. Dependencies within a
mutual inductive block refer to the other identities checked in that block;
those are family relationships, not permission for cyclic definitions.

Canonical identities start with `$lean:`. Each string component is encoded as
`sBYTE_LENGTH:CONTENTS`; each numeric component as `nDECIMAL;`. For example,
`Audit.identity` has identity `$lean:s5:Audits8:identity`. The CLI accepts either
the unambiguous display name or canonical identity as the target selector.

A declaration's digest covers the complete export prefix through its record,
including primitive tables and preceding declarations. Hashing only its final
JSON record would miss changes hidden behind numeric IDs. Inductive members
share their block's prefix digest but have separate canonical identities. This
conservative hashing can also change after an unrelated earlier record changes.

Receipts are audit output. The reader never loads them as proof authority or
skips checking because a digest matches. The input digest authenticates no
external source: source project revisions, source-to-target declaration maps,
license identifiers and notices still need a separate provenance manifest
before importing an upstream development. This reader does not supply that
manifest for arbitrary inputs or claim the upstream FLT proof was checked.
The committed genuine fixtures have a separate `real-provenance.json` with
per-declaration source modules, source hashes and notices, license texts and
artifact hashes. Those records provide reproducibility and attribution; only
kernel replay establishes the accepted theorem's typing judgment.

## Resource limits and unsupported features

| Resource | Limit |
| --- | --- |
| Input | 64 MiB total; 8 MiB per record line |
| JSON nesting | 64 |
| Interned names | 100,000 entries; 256 components; 16,384 bytes per display/key; 16 MiB combined payload |
| Universe table | 20,000 entries; 64 KiB accounted payload per level |
| Universe parameter identity | 512 bytes |
| Expression table | 200,000 entries; graph depth 256 |
| Primitive payload accounting | 64 MiB, including all expanded natural-literal constructors |
| Checked declarations | 4,096, including families, constructors and recursors |
| Dependency receipts | 1,000,000 entries; 16 MiB accounted payload |
| Universes per declaration/application | 32 |
| Mutual families | 16 |
| Parameters, indices, constructors, fields and per-family rules | 64 each |
| Natural-literal abbreviation | 0 through 128 |
| Core checking | 200,000 steps and recursive depth 96 per checking phase |
| Core transformations | 64 MiB accounted allocations per phase; 256 MiB cumulatively per replay |

Allocation accounting charges term nodes, owned identifiers and normalized
universe payloads, including temporary transformations. These are explicit
work/payload budgets, not exact process RSS measurements. Input is read one
bounded line at a time, but primitive tables and the checked environment remain
in RAM. This is not a disk-backed replay implementation for enormous exports.
The execution guard used for development separately limits the process tree to
2 GiB memory and 200% CPU. Limits and unsupported rules return errors and
establish no theorem; they never authorize an admission or unchecked cache.

Nested inductive export blocks, auxiliary recursor schemes, string literals,
large natural-literal representations, quotient foundations, classical axioms,
Lean surface syntax/tactics, native `.lim` translation and full-environment
storage/replay are not implemented. General mathematical Nat and universe
quantification remain unbounded; representation limits are not finite models.

The [kernel's trust assumptions](kernel.md#trust-assumptions) still apply.
Local rechecking and adversarial tests do not formally verify the checker.
