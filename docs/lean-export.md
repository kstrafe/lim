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

Thirteen real exports of original small Lean proofs replay and translate to
rechecked native `.lim` source, including universe-polymorphic, indexed,
multiply nested, Sigma container, quotient computation and compact natural
literal cases, standard natural arithmetic, plus explicitly authorized logical
foundations. They do not check the upstream Fermat proof or the complete
Lean/Mathlib environment. See the
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
typing rules. Natural literals retain canonical arbitrary-precision decimal
values, of at most 4,096 digits, in the imported, independently checked
standard `Nat` family. Induction and conversion expose a zero/successor
constructor when needed. No magnitude-sized unary graph is allocated, and
values never wrap or truncate to machine integers. They cannot rebind Lim's
internal natural-number type by sharing its printed name. The
[genuine natural-literal corpus](../tests/fixtures/lean_export_naturals/README.md)
checks seven theorems and their native translations. Checked
constant-increment structural recursors can batch closed counts using exact
decimal addition/multiplication, independently of declaration names, through
the [ordinary native rule](kernel.md#natural-numbers-and-induction). Other
recursion shapes still use ordinary computation and finite work budgets.
Guarded first-field and fixed-argument fusion also expose the pinned standard
`Nat.add`/`Nat.mul`/`Nat.pow` recurrences inside their course-of-values records, without
recognizing those names as privileged operations. The
[standard arithmetic corpus](../tests/fixtures/lean_export_arithmetic/README.md)
replays eleven actual targets and independently rechecks their ordinary native
translations with empty logical-assumption inventories.
Affine recursors track selected outer accumulators without confusing them
with predecessors. Constant-affine iteration uses bounded decimal halving and
squaring; unknown nontranslation counts and nonlinear products keep ordinary
computation. No source operation is authorized by its spelling.

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

Nested blocks additionally reconstruct scoped cases by specializing the
constructors of already checked containers. Their actual number and order
determine the extra motives, branches and `rec_1`, `rec_2`, ... wrappers.
The exported nested count and auxiliary recursor metadata must match that
reconstruction. [Nested replay](lean-nested-replay.md) describes parameter
scope, positivity, original constructor identities and remaining boundaries.

The four `quot` records must form the pinned, ordered package `Quot`,
`Quot.mk`, `Quot.lift`, `Quot.ind`. Primitive tables may occur between them;
other declarations may not. Missing, duplicate, reordered or altered members
fail. Lim checks the existing standard nominal `Eq`/`Eq.refl` family, every
provided signature's typing, universe arity and conversion to a fixed schema.
Only then does it independently check ordinary wrappers around the native
[`#pt-quot` computation primitives](kernel.md). A typed equality-induction
adapter supplies the lift's primitive equality evidence. No exported record
can add a reduction rule or assert equality of related representatives.
`Quot.ind` remains restricted to proposition-valued motives. The
[genuine quotient fixture](../tests/fixtures/lean_export_quotient/README.md)
records reproducible source/module/license provenance and all three native
theorem targets. Axiom records require the separate explicit policy below.

## Explicit logical foundations

Default replay rejects all axiom records. `--lean-foundations` opts into only
the pinned `Classical.choice`, `propext` and `Quot.sound` identities. It is a
boolean option for `--check-lean-export`, accepted alongside the output flags;
duplicates, values and unknown options fail. It permits these mathematical
assumptions, not arbitrary admitted lemmas or unchecked proof bodies.

```sh
lim --check-lean-export tests/fixtures/lean_export_foundations/foundations.ndjson \
  BasisProbe.quotientRelated --lean-foundations --report /tmp/basis.json \
  --emit-proof /tmp/basis.lim
```

Every accepted axiom has the exact `name`, `levelParams`, `type`, `isUnsafe`
schema. Unsafe flags, unknown identities, altered universe counts and changed
signatures fail. The provided signature is typechecked before conversion can
erase unused expressions. Lim validates standard `Eq`, `Nonempty` and `Iff`
constructor shapes and requires the complete checked quotient package for
`Quot.sound`. Ordinary checked adapters bridge nominal nonemptiness and
equality to the fixed native logical basis. The accepted declaration becomes
opaque only after its initializer checks at the original imported signature.
The same initializer appears as standard `#math-opaque` source and is rechecked
independently. No axiom record installs an arbitrary type or reduction rule.

The receipt distinguishes all declared `axioms` from `target_axioms`, the
selected theorem's transitive closure. The CLI and source header distinguish
them too. Translation checks that the native theorem's inventory agrees;
comments and receipts cannot authorize extra assumptions. The
[genuine foundation corpus](../tests/fixtures/lean_export_foundations/README.md)
checks all three adapters and default refusal, with original Prelude/Core
module and license provenance. The library equivalents are
`check_lean_export_with_policy` and `translate_lean_export_with_policy`, taking
`LeanFoundationPolicy::Lean4`; the original APIs retain constructive checking.

The selected target must be an actual theorem, not a proposition-valued
definition. Success requires reaching EOF and checking all declarations,
including those after the target. A later malformed record or read error
invalidates the entire run. The command emits no native binary. A report is
published atomically only after success; input aliases, including hard links,
cannot be used as report destinations.

## Native proof-source translation

Add `--emit-proof PATH` to emit a standard Lim proof file after successful
replay. The translator rechecks the complete emitted source through the normal
frontend and kernel before returning it or publishing the file. With no output
flag, the reader keeps its replay-only behavior and does not retain opaque
initializers for source emission.

```sh
lim --check-lean-export tests/fixtures/lean_export/real-identity.ndjson ReplaySource.identityProof --emit-proof identity.lim
lim --check-theorem identity.lim lean-1-ReplaySource-identityProof
```

The success output gives the native theorem name. `--report` and `--emit-proof`
may appear in either order. Duplicate, unknown, missing and empty options fail.
Input aliases and colliding output paths, including hard links, are rejected.
Replay, translation, and source-checking failures leave both outputs untouched.
Each successful file write is atomic; publishing two files is not a filesystem
transaction if a later output write fails.

Every checked declaration gets a deterministic native identifier containing its
ordinal and a readable original name. The ordinal distinguishes names even when
sanitization or truncation produces the same suffix. File comments record Lean
and exporter pins, the exact input hash, the native theorem target, and each
original declaration's identity, export line and prefix hash. Names in comments
are escaped so embedded newlines cannot inject source forms. The
[`translate_lean_export`](../src/proof/kernel/export.rs) library API returns
`LeanExportTranslation { report, target, source }` after the same checks; `target`
is the native identifier and `report.target` keeps the original Lean name.

Inductive headers use explicit native parameter/index telescopes and mutual
membership. Original constructor constants become typed wrappers around
`#pt-construct`. Recursor constants become checked native definitions, including
`#pt-nested-induct` wrappers with physical type selectors and explicit case
ordinals. Private auxiliary identities do not appear as native constants.
Theorems and opaque definitions retain their explicit, checked initializers;
`#theorem` and `#math-opaque` keep those values unavailable to conversion.

Universe parameters and term binders are renamed separately. Normalized universe
levels are reconstructed using successor, max and imax. Guard ordering is chosen
using exact symbolic dominance checks, and the complete result must be equivalent
to the original level before emission. A source representation or resource failure
rejects translation; it cannot change a theorem's universe or establish a claim.
No source-level axiom, replay directive, certificate bypass or proof hole is emitted.

A separate correspondence pass parses the emitted declarations and relocates
native constants and universe parameters back to their original identities.
It checks declaration inventory and opacity, compares inductive parameters,
indices, sorts, constructor fields and result indices, and verifies every
translated definition/theorem type and initializer in the original checked
environment. Exact typed syntax is compared before normalization to avoid
recomputing identical mathematical expressions. Otherwise the ordinary kernel's
definitional conversion must agree. A different well-typed data body or a valid
proof of a different proposition fails correspondence. This pass uses no source
comments as authority and does not formally verify the translator or kernel.


The [committed native translations](../theorems/lean_replay/README.md) reproduce
the thirteen-file genuine producer corpus. Their manifests map every original
declaration to its native name and hash both input and output files, linking the original source,
module and license provenance. The regeneration script checks byte-for-byte
reproduction and independently runs ordinary `--check-theorem`. These small proofs
are not the full upstream Fermat development.

## Replay receipt and identity

`--report PATH` writes JSON with schema `lim-lean-replay-v1`. It records the
target, exact input byte count and SHA-256, record count, protocol/toolchain
pins, and every accepted declaration's display name, canonical identity, kind,
record line, SHA-256 and direct dependencies. `axioms` inventories all accepted
fixed axiom declarations; `target_axioms` records the selected theorem's exact
transitive closure. Both are empty under the default constructive policy.
A separate `foundations` list records
`quotient-computation-v1` when the complete checked primitive package is used;
otherwise it is empty. The same inventory is written in the native source
header when nonempty. Dependencies within a
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
| Primitive payload accounting | 64 MiB, including owned compact decimals, identifiers and universe payloads |
| Checked declarations | 4,096, including families, constructors and recursors |
| Dependency receipts | 1,000,000 entries; 16 MiB accounted payload |
| Universes per declaration/application | 32 |
| Mutual families | 16 |
| Expanded nested recursion group | 16 total main and scoped container cases |
| Parameters, indices, constructors, fields and per-family rules | 64 each |
| Natural-literal representation | Canonical unsigned decimal string, at most 4,096 digits |
| Core checking | 200,000 steps and recursive depth 96 per checking phase |
| Structural arithmetic | Decimal digit work counts against the core budget before each addition/multiplication; at most 4,096 result digits |
| Core transformations | 64 MiB accounted allocations per phase; 256 MiB cumulatively per replay |
| Native translation source | 8 MiB before and after formatting; 1,000,000 expanded term visits; recursive render depth 96 |
| Source correspondence | 1,000,000 relocated nodes, depth 256, and 64 MiB accounted node/name/universe allocations across a translation |
| Universe source reconstruction | 64 KiB per level; at most 64 variable successors, guard/successor depth 80, and 4,096 symbolic guard-order comparisons |

Allocation accounting charges term nodes, owned identifiers and normalized
universe payloads, including temporary transformations. These are explicit
work/payload budgets, not exact process RSS measurements. Input is read one
bounded line at a time, but primitive tables and the checked environment remain
in RAM. This is not a disk-backed replay implementation for enormous exports.
The execution guard used for development separately limits the process tree to
2 GiB memory and 200% CPU. Limits and unsupported rules return errors and
establish no theorem; they never authorize an admission or unchecked cache.

String literals, arbitrary axiom declarations, Lean surface syntax/tactics,
other standard arithmetic operations and full-environment storage/replay are
not implemented. Bounded native proof-source translation is supported for the
accepted export subset. General mathematical Nat and universe
quantification remain unbounded; representation limits are not finite models.
Native Lim also supports explicit type-selected nested cases through
[`#pt-nested-induct`](kernel.md#nested-inductive-groups). The translator uses that form to preserve the checked auxiliary recursor
wrappers in ordinary source.

The [kernel's trust assumptions](kernel.md#trust-assumptions) still apply.
Local rechecking and adversarial tests do not formally verify the checker.
