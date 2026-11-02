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

The committed genuine exports of original small Lean proofs replay and translate to
rechecked native `.lim` source, including universe-polymorphic, indexed,
multiply nested, Sigma container, quotient computation and compact natural
literal cases, standard natural arithmetic, generic discrimination and the
equality-to-Boolean bridge, plus explicitly authorized logical
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
`Nat.add`/`Nat.mul`/`Nat.pow`/`Nat.sub`/`Nat.ble`/`Nat.beq` recurrences inside their course-of-values records, without
recognizing those names as privileged operations. The
[standard arithmetic corpus](../tests/fixtures/lean_export_arithmetic/README.md)
replays thirty actual targets and independently rechecks their ordinary native
translations with empty logical-assumption inventories.
Affine recursors track selected outer accumulators without confusing them
with predecessors. Constant-affine iteration uses bounded decimal halving and
squaring; unknown nontranslation counts and nonlinear products keep ordinary
computation. Checked predecessor-shaped recursors also support closed truncated
subtraction, requiring the correct zero/successor branches and accumulator
subject. Decimal borrow arithmetic preserves saturation and arbitrary precision;
unknown operands do not acquire an affine interpretation. No source operation
is authorized by its spelling. Completed finite data observations and guarded
nonrecursive case application expose Boolean histories. An exact paired-
predecessor rule checks every zero/successor case and binder, then selects the
actual terminal by closed decimal comparison. It neither guesses constructor
truth values nor permits arbitrary changing recursive arguments.

The [generic subtraction bridge](../tests/fixtures/lean_export_subtraction_bridge/README.md)
checks three universal cancellation proofs across 60 actual declarations,
including the standard induction and congruence proof for successor
cancellation. Batched ordinary beta reduction avoids repeated substitutions
through curried helper bodies under the unchanged work/depth/allocation limits.
All original and native targets have empty axiom and foundation inventories.

The [division corpus](../tests/fixtures/lean_export_division/README.md) retains
the standard fuelled history recurrence and checks eight closed targets,
including zero divisors, exact/inexact division and a quotient beyond 64 bits.
A structurally checked Euclidean observation requires sufficient actual fuel,
the exact comparison/subtraction/increment step and normalized operands. This
adds a trusted conversion optimization, rather than a name-based assumption.
Every raw and native target is independently checked with empty inventories.
The [composition corpus](../tests/fixtures/lean_export_division_composition/README.md)
checks fifteen targets together, including seven computed-operand cases using
bounded optional normalization through the existing arithmetic rules. Sharing
immutable numeral and monomorphic-global leaves avoids needless copies during
shifts/universe walks while retaining node, scope and depth/work checks. It retains the cost of attempted work and
restores enclosing limits on success, decline or error. Expensive expressions
and larger combined corpora can still exceed the work/allocation limits; these
fixtures do not establish arbitrary division algorithms or full FLT.

String literals of at most 4,096 UTF-8 bytes expand through the previously
checked standard `Char.ofNat`, `String.ofList`, `List.nil` and `List.cons`
identities, following the pinned kernel's
[constructor expansion](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/kernel/inductive.cpp#L1368-L1399).
The reader verifies the helper signatures, closed types and universe arities,
including `Char`, `String`, `List` and the nominal natural-number family.
Every helper body is independently checked through normal replay. Decoding
uses Unicode scalars and preserves embedded NUL: the reference
[string wrapper](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/runtime/string_ref.h#L23-L30)
and [decoder](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/runtime/utf8.cpp#L198-L207)
use explicit byte lengths. Invalid UTF-8 and unpaired surrogate escapes fail JSON parsing.
Larger constructor sequences use closed, balanced lambdas whose ordinary beta
reduction recovers the exact list. No new string primitive or proof admission
is installed. Expansion storage and depth are accounted before constructing
even unused syntax; normal work, depth and transformation limits still apply.
The [genuine string corpus](../tests/fixtures/lean_export_strings/README.md)
checks five raw/native targets across 378 declarations, with empty assumption
inventories and the explicit 1M-work/128-MiB-phase/1-GiB-total profile. Default
work refusal occurs earlier in `Char.ofNat._proof_2`. A false altered-literal
control currently exhausts ordinary conversion work; that refusal is not a
completed string-inequality decision.

The [remainder corpus](../tests/fixtures/lean_export_remainder/README.md) adds
fifteen targets over 256 genuine declarations, including computed sums/powers
and unbounded `0 % n` / `n % 0` controls. The observer recognizes the exact
state-return terminal and unchanged recursive result under the same guard,
update and actual-fuel checks. Reusing a guard's validated numeral for an exact
syntax match reduces repeated divisor unfolding; all update-shape checks remain.
Private origins include the case-analysis helper from pinned `Init.Data.Nat.Basic`.
Raw/native proofs are independently checked with empty assumption inventories.
The general `Nat.mod_lt` closure, including `Nat.modCoreGo_lt`, now checks for
arbitrary naturals and a positive divisor. Common-head application congruence
and bounded lazy delta candidates avoid unfolding the same worker twice; all
argument comparisons still use ordinary conversion, and unmatched terms retain
the existing fallback. This does not complete standard arithmetic or the FLT port.

The [well-founded equation corpus](../tests/fixtures/lean_export_well_founded/README.md)
retains 141 genuine declarations and the generic `WellFounded.Nat.fix_eq`
proof. Explicit lambda/let candidates expose a common call before expanding
its worker, preserving substitution scope and the same conversion budgets.
When a common call is not found, fallback reuses only completed reductions
inside that same comparison, retaining original source checks and all charges.
Declined operations contribute no partial candidate or theorem authority.
Raw replay requires the existing `--lean-foundations` policy: both declared
and target axiom inventories contain exactly `Quot.sound`, with
`quotient-computation-v1` as primitive foundation. The native translation
independently reports `Quot.sound`. Source hashes, notices and canonical
ownership include pinned `Init.WF` and `Init.SimpLemmas`.

The [GCD corpus](../tests/fixtures/lean_export_gcd/README.md) adds 284 genuine
declarations and three unbounded targets: `Nat.gcd_zero_left`, `Nat.gcd_succ`
and `Nat.gcd_zero_right`. Bounded candidates across both comparison operands
expose transparent wrappers and selected branches before expanding a common
worker. Head inspections guide reduction only; the checker still establishes
every equality by its existing rules. Raw and native target bases are exactly
`Quot.sound` for zero-left and successor, and `Quot.sound, propext` for
zero-right. The export registers both axioms and requires explicit
`--lean-foundations`; its primitive basis is `quotient-computation-v1`.
Canonical private ownership and source attribution additionally pin
`Init.Data.Nat.Gcd`.

The [GCD self corpus](../tests/fixtures/lean_export_gcd_self/README.md) checks the
actual `Nat.gcd_self` dependency closure and its unbounded statement. All 335
declarations replay under the explicitly recorded 1,000,000-work, 128-MiB-phase,
1-GiB-total budget. Exact native translation and independent native checking
report the same `Quot.sound, propext` basis and quotient primitive package.
Both raw and native checking refuse the unchanged default work budget;
constructive replay still refuses the imported axioms even with more work.
Canonical private ownership additionally pins `Init.Data.Nat.Div.Basic`.
The [GCD calculation corpus](../tests/fixtures/lean_export_gcd_calculation/README.md)
checks the closed result `Nat.gcd 84 30 = 6` using actual `Nat.gcd_succ` and
`Nat.gcd_zero_left` proofs, with remainders checked by ordinary conversion.
Its 278 declarations replay and translate independently with the same explicit
budget, exactly `Quot.sound`, and quotient primitive computation. Direct `rfl`
worker evaluation and the full FLT dependency closure remain open.

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

## Source graph lifetime

Replay-only checking stores primitive expressions as compact source nodes with
backward references to names, universes and earlier expressions. Record shapes,
references, literal spelling, graph depth and payload accounting are checked
while reading, including for unused expressions. A declaration materializes its
required source roots and still checks every type, value, universe scope and
proof body through the kernel.

The reader shares immutable syntax while it has a live owner. It caches no
inferred type or successful judgment. After checking a declaration it releases
unowned proof trees and their weak handles; opaque theorem bodies therefore do
not remain alive just because their numeric source IDs exist. The compact nodes
can reconstruct the same source syntax when a later declaration references it.
Transparent metadata aliases are flattened to avoid adding reconstruction depth.
Changed universe binders and expected types always trigger ordinary checking.

Compact source graphs spill before growing beyond a 2-MiB allocation estimate.
The source-node bytes and fixed index use separate append-only temporary files,
removed from the directory immediately after opening. Each keeps at most four
64-KiB read pages and one pending page. Completed pages carry SHA-256 digests
held by the running checker; read errors, truncation and checksum mismatches
fail replay. The live syntax memo becomes sparse after spilling, so unused
numeric IDs need no retained tree or dense weak-handle array. Scratch bytes
and source/table limits remain bounded. These files are local to one invocation
and contain source syntax, never accepted theorem signatures or judgments.

Spilling trades some replay time for bounded resident source storage. The
[measurement tools](#measuring-replay-memory) support `--lets 64 --total-bytes
4294967296` for a larger checked-proof workload and `--declarations 1 --lets 1
--unused-expressions 190000` for primitive-table retention. Larger traffic
profiles must be selected explicitly; the tools do not grow a budget after
failure. Neither workload is a genuine Lean proof corpus or an FLT result.

Against `b3a3f18b`, five alternating debug0 samples of 3,000 checked theorems
with 64 erased lets each reduce median compiler RSS from 32,984 to 23,936 KiB
(27.4%), while wall time rises from 5,679.570 to 6,551.998 ms (15.4%). Three
paired primitive-table samples reduce RSS from 26,288 to 18,172 KiB (30.9%),
with wall time rising from 849.870 to 1,100.988 ms (29.5%). These measurements
use fresh compiler processes under the unchanged 2-GiB/two-core guard; the
first workload explicitly selects a 4-GiB cumulative transformation budget.
The committed small corpora remain below the spill threshold.

Native source emission uses the same compact, paged expression graph. A small
table indexed by declaration ordinal retains the original source expression ID
for each theorem or opaque initializer, rather than owning every proof tree.
Emission and independent correspondence reconstruct the original root when
needed. The three fixed axiom adapters have no source initializer and retain
their checked native terms. Dead reconstruction handles are released between
declarations. There is no persisted typing result or new proof authority.
Input, source/table/payload, work/depth and transformation limits are unchanged.
Native output strings and parsed source remain bounded, eager structures; this
does not provide full-environment replay or an FLT proof.

The expanded name table also spills above a 1-MiB resident allocation estimate,
in both replay and native emission. Exact key, display spelling and component
depth move to separate data and fixed-index scratch files, with four 64-KiB
read pages and one pending page each. An in-memory index retains randomized
64-bit hashes and numeric candidate IDs. Hash collisions compare complete
canonical keys, so they cannot merge names or change symbol identity. Lookup
of original nested-constructor names uses that index. Every name's fields are
compared independently after encoding before its in-memory form is released.
Scratch pages remain protected by SHA-256 digests held by this invocation.

Name records are bounded to 32,778 encoded bytes. Input name counts, cumulative
key/display payload limits, component depth, UTF-8 and backward-ID checks remain
unchanged, including unused names after the selected theorem. The candidate-ID
index remains in RAM; this does not make the whole environment constant-space.

The universe table spills above a 2-MiB estimate of its owned representation,
in replay and native emission. It stores the exact normalized monomials,
optional bases, sorted nonzero guards and offsets produced by the existing
arithmetic. Decoding validates fields and restores that representation without
normalization, approximation or recomputation. Independent equality with the
original value is required before release. Numeric IDs and duplicates remain
distinct entries; no typing result or universe substitution is cached. An
additional cache of at most 32 exact recent values and a 256-KiB allocation
estimate lets repeated representations reuse data bytes. Every ID keeps its
original full payload weight, even when its data record is shared. Equality
here compares stored fields, without semantic normalization.

Protected data and index files keep the same bounded page caches as names.
The index preserves each value's original payload-accounting weight, checked
again on materialization. Records are bounded to 64 KiB, 256 monomials and 64
guards per monomial. The 64-KiB accounted payload limit is also enforced during
decoding, before constructing its trees. Scope, explicit universe arity,
combined primitive-payload accounting and full-EOF validation still run normally.

Replay and native emission store completed original kernel declarations in
invocation-local scratch storage when their conservative resident estimate
exceeds 8 MiB. The store releases
older declarations down to 4 MiB and keeps later reads within the remaining
8-MiB working-set allowance. A single larger declaration is returned to its
checking caller without entering the read cache. A declaration being checked,
the checker’s temporary terms, source memos and name/index metadata have their
own bounds; 8 MiB is not a process RSS cap.

Only successful complete declaration records can trigger eviction. The scratch
codec preserves shared term DAGs, exact universes, transparent values, opaque
signatures and all inductive-family metadata. Before releasing a checked object,
the kernel compares its structure with the decoded representation independently
of the encoder. Reads verify both page and complete-record SHA-256 digests held
in the current process. Identical complete representations may share bytes;
their nominal declaration names remain distinct. Mutation invalidates a stored
representation. I/O errors and integrity failures fail replay.

These immediately unlinked files are temporary backing storage for the current
kernel environment. No earlier process’s judgment or persistent cache can
insert a declaration. Records are bounded to 32 MiB, one million term nodes and
depth 256; the scratch file is bounded to 128 MiB. The original export
environment can spill during native emission too. Nested-family views, name
candidate IDs, native report inventories and the independently parsed native
environment still need further work for very large exports.

The common mathematical checker now plans dependencies with numeric IDs,
reparses only a ready declaration/group, and lets its completed native
declarations use protected backing storage too. It preserves ordinary kernel
checks and explicit mutual membership; see [checking and
caching](kernel.md#checking-conversion-and-caching). The native source string,
frontend AST, name maps, report materialization and dependency metadata still
need a streaming design before the full upstream environment can be ported.

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

The CLI streams the receipt through a 64-KiB buffer into same-filesystem
staging and publishes it only after all writes succeed. It does not construct
a second JSON object tree or complete serialized string. The library method
`LeanExportReport::write_json` writes the same canonical bytes to an ordinary
Rust writer and propagates errors; `render_json` remains available for callers
that need a string. Writer failures leave an existing destination untouched.

Raw replay also has a paged declaration-inventory API:
`check_lean_export_receipt_with_budget` returns a `LeanExportReceipt` with
`declaration_count`, `axioms`, `target_axioms`, `write_json` and `into_report`
methods. The raw `--check-lean-export` CLI uses this path and streams its
receipt without materializing every declaration report. The existing
materialized report API and its behavior are unchanged; `into_report` provides
the explicit materialization path for callers that need the full report.
Replay records the selector match and authorized axiom names as declarations
pass checking; target validation still waits for all input records. Target
axiom-closure calculation can read paged reports. The receipt schema, hashes,
declaration order and JSON bytes remain unchanged.

Internal declaration reports spill above a 1-MiB resident allocation estimate
to protected, invocation-local, immediately unlinked data and index files.
Before releasing an in-memory report, replay structurally compares every
field with the decoded record. A record is bounded to the existing 16-MiB
dependency accounting limit plus 65,536 bytes; reads use 64-KiB chunks. This
bounds retained report inventory. The checked-name candidate IDs, closure
visit flags and integer worklist remain resident. Native source and native
translation reports remain eager, and the 64-MiB input and 4,096-declaration
limits are unchanged.
This storage does not establish full-FLT-scale checking. The synthetic
[measurements below](#measuring-replay-memory) describe its memory/time tradeoff.

Replay's checked-name index retains randomized 64-bit fingerprints and numeric
report IDs instead of another copy of each canonical name. A fingerprint hit
only selects candidates: membership compares the complete canonical identity
bytes in the report inventory. Paged membership reads just the bounded name
and identity fields, without rebuilding that report's dependency list. Page
protection and exact identity checks still apply; display spellings never
establish membership.

The target axiom audit uses report IDs for its worklist and one visit flag per
declaration. It marks IDs when scheduling them, so repeated edges cannot queue
more than one work item per declaration. Declared axioms must still exactly
match the reachable fixed native foundations, and missing dependencies fail.
These indexes contain no proof terms and authorize no new foundation. Kernel
declaration keys and nested-family views still retain their existing storage;
this change does not complete full-environment scaling.

Canonical identities start with `$lean:`. Each string component is encoded as
`sBYTE_LENGTH:CONTENTS`; each numeric component as `nDECIMAL;`. For example,
`Audit.identity` has identity `$lean:s5:Audits8:identity`. The CLI accepts either
the unambiguous display name or canonical identity as the target selector.

A declaration's digest covers the complete export prefix through its record,
including primitive tables and preceding declarations. Hashing only its final
JSON record would miss changes hidden behind numeric IDs. Inductive members
share their block's prefix digest but have separate canonical identities. This
conservative hashing can also change after an unrelated earlier record changes.
The reader updates its streaming hash for every record, but finalizes a prefix
only when a declaration needs it. Multiple members checked from the same record
reuse that prefix. Unused primitive records still contribute to the final input
digest, and primitive records between declarations affect every later prefix.

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

The table lists default counters. Both raw replay and native checking accept
explicit resource choices through `ProofBudget` or `--proof-work N`,
`--proof-phase-bytes N`, and `--proof-total-bytes N`. The existing convenience
APIs keep these defaults. `check_lean_export_with_budget` and
`translate_lean_export_with_budget` take both the foundation policy and budget;
selecting more work never authorizes an axiom. Work and allocation failures
still establish no theorem, and successful receipts record the selected
`proof_budget` independently of the logical axiom inventories.

For example:

```sh
lim --check-lean-export proof.ndjson Original.target --lean-foundations \
  --proof-work 1000000 --proof-phase-bytes 134217728 \
  --proof-total-bytes 1073741824 --report receipt.json --emit-proof proof.lim
```

The selected limits also apply to the independent native source recheck.
Their counters restart for that check; the receipt's raw input hash and full
declaration/assumption audit retain their existing meaning. No receipt is
trusted as a replacement for later checking. The CLI prints nondefault budgets
on successful checking, and native theorem API results expose their budget.
Maximum selectable work is 100,000,000, phase traffic is 1 GiB and cumulative
traffic is 64 GiB. Fixed recursion depth, source/table/payload limits and
explicit axiom authorization are unchanged. Keep demanding replay commands
inside the separate host memory/CPU guard.

| Resource | Limit |
| --- | --- |
| Input | 64 MiB total; 8 MiB per record line |
| JSON nesting | 64 |
| Interned names | 100,000 entries; 256 components; 16,384 bytes per display/key; 16 MiB combined payload |
| Expanded name storage | 1 MiB resident estimate before spilling; 32,778-byte records; separate protected data/index scratch files |
| Universe table | 20,000 entries; 64 KiB accounted payload per level |
| Universe storage | 2 MiB resident estimate before spilling; 64-KiB records; exact values and original accounting weights in protected scratch files |
| Universe parameter identity | 512 bytes |
| Expression table | 200,000 entries; graph depth 256 |
| Primitive payload accounting | 64 MiB, including owned compact decimals, identifiers and universe payloads |
| Checked declarations | 4,096, including families, constructors and recursors |
| Dependency receipts | 1,000,000 entries; 16 MiB accounted payload |
| Report inventory storage | 1 MiB resident estimate before spilling; records at most 16 MiB + 65,536 bytes; separate protected data/index scratch files, each capped at 128 MiB |
| Universes per declaration/application | 32 |
| Mutual families | 16 |
| Expanded nested recursion group | 16 total main and scoped container cases |
| Parameters, indices, constructors, fields and per-family rules | 64 each |
| Natural-literal representation | Canonical unsigned decimal string, at most 4,096 digits |
| String-literal representation | Valid UTF-8, at most 4,096 bytes; Unicode scalar expansion through checked helpers |
| Core checking | 200,000 steps and recursive depth 96 per checking phase |
| Structural arithmetic | Decimal digit work counts against the core budget before each addition/multiplication; at most 4,096 result digits |
| Core transformations | 64 MiB accounted allocations per phase; 256 MiB cumulatively per replay |
| Completed original declaration storage | 8 MiB resident estimate in raw replay and native emission, eviction down to 4 MiB; 128 MiB invocation-local scratch |
| Native initializer inventory | One optional source expression ID per declaration; the three fixed checked axiom adapters retain native terms |
| Declaration scratch records | 32 MiB encoded bytes, 1,000,000 unique term nodes, depth 256; 256 MiB decode allocation accounting |
| Native translation source | 8 MiB before and after formatting; 1,000,000 expanded term visits; recursive render depth 96 |
| Source correspondence | 1,000,000 relocated nodes, depth 256, and 64 MiB accounted node/name/universe allocations across a translation |
| Universe source reconstruction | 64 KiB per level; at most 64 variable successors, guard/successor depth 80, and 4,096 symbolic guard-order comparisons |

Allocation accounting charges term nodes, owned identifiers and normalized
universe payloads, including temporary transformations. These are explicit
work/payload budgets, not exact process RSS measurements. Input is read one
bounded line at a time, and replay-only expression nodes can spill to bounded
scratch storage. Completed raw-replay declarations also have bounded resident
storage, and expanded names and universe values can spill. Name and checked-name
candidate IDs, nested-family views and per-declaration closure flags remain in
RAM. Raw CLI report
inventory can spill as described in the
[receipt section](#replay-receipt-and-identity); native source and native
translation reports remain eager. This does not provide full-environment
storage for enormous exports.
The execution guard used for development separately limits the process tree to
2 GiB memory and 200% CPU. Limits and unsupported rules return errors and
establish no theorem; they never authorize an admission or unchecked cache.

Arbitrary axiom declarations, Lean surface syntax/tactics,
other standard arithmetic operations and full-environment storage/replay are
not implemented. Bounded native proof-source translation is supported for the
accepted export subset. General mathematical Nat and universe
quantification remain unbounded; representation limits are not finite models.
Native Lim also supports explicit type-selected nested cases through
[`#pt-nested-induct`](kernel.md#nested-inductive-groups). The translator uses that form to preserve the checked auxiliary recursor
wrappers in ordinary source.

The [kernel's trust assumptions](kernel.md#trust-assumptions) still apply.
Local rechecking and adversarial tests do not formally verify the checker.

## Measuring replay memory

Run the measurement tools inside the development resource guard:

```sh
bash scripts/limited-run.sh nix develop -c python3 scripts/benchmark-proof-memory.py \
  --lim target/debug/lim --iterations 3 --case raw_gcd_self --case native_gcd_self
bash scripts/limited-run.sh nix develop -c python3 scripts/benchmark-proof-retention.py \
  --before /path/to/old/lim --after target/debug/lim --iterations 5
bash scripts/limited-run.sh nix develop -c python3 scripts/benchmark-proof-report.py \
  --before /path/to/old/lim --after target/debug/lim --iterations 5
```

For native proof emission and independent checking, the native-retention tool
extends the pinned identity fixture with 100 additional checked theorems,
four erased typed lets each, and 190,000 unused expression records. It compares
complete receipt and emitted-proof fingerprints before timing and after every
fresh-worker sample:

```sh
bash scripts/limited-run.sh nix develop -c python3 scripts/benchmark-proof-native-retention.py \
  --before /path/to/old/lim --after target/debug/lim --iterations 5
```

Against `88333da4`, five alternating debug0 samples reduce median compiler
peak RSS from 67,884 to 33,336 KiB (50.9%). Median wall time increases from
561.130 to 788.445 ms (40.5%); protected source backing storage and later
reconstruction cost time. Both versions use default work/per-phase limits,
an explicit 1-GiB cumulative transformation budget and the same 2-GiB/two-core
host guard. The 4,308,676-byte source has SHA-256
`26ffe8236f7387a3f3e8ac6de4cee8d6fa61c574c393f56e2edd7ec837f112df`.
All samples emit the same 23,884-byte receipt, SHA-256
`48982614e1b238236e07e1c2e6427f6c5e4c3b34b32cb885842484c972bf3357`,
and 78,448-byte Lim proof source, SHA-256
`b3cd359380dcc60b01ff34dbb654065cf1e8dac1d6629a06cc0990c4761fc8a6`.
This isolates retained syntax during native translation; it is synthetic
storage evidence, not additional FLT proof coverage. Output formatting,
parsing, native report materialization and independent checking still have
their existing finite limits.

The common native theorem checker can be measured separately from raw export
parsing with the scheduling tool. It generates 3,000 independent identity
theorems with 16 typed lets in each proof and checks the complete program
through `--check-theorem`:

```sh
bash scripts/limited-run.sh nix develop -c python3 scripts/benchmark-proof-schedule.py \
  --before /path/to/old/lim --after target/debug/lim --iterations 5
```

Against `0072854d`, five alternating debug0 samples reduce median wall time
from 2,657.787 to 2,182.027 ms (17.9%) and compiler peak RSS from 940,608 to
910,504 KiB (3.2%). Both use default work/per-phase limits, an explicit 1-GiB
cumulative transformation budget and the unchanged 2-GiB/two-core host guard.
The 2,824,890-byte source has SHA-256
`bcb20ae2e10322c72c8ae5ba2550b19195ea8c44021009402c6f439bbeadcd37`.
The tool requires exact theorem-selection confirmation from both preflights;
source hashes are provenance, not proof authority. It produces no export
receipt or translated proof fingerprint. Source frontend memory remains a
substantial scaling problem on this synthetic workload, and these identity
proofs add no genuine FLT dependency coverage.

Sharing source-child storage reduces a second layer of frontend duplication.
`SpannedExpr` clones share their child vectors until a writer detaches them;
the underlying `Expr` values remain owned. Against `4ad3f76b`, the same five
alternating debug0 samples reduce median wall time from 2,188.901 to
1,867.993 ms (14.7%) and compiler peak RSS from 909,172 to 651,412 KiB
(28.4%). Input bytes, hash, proof budgets, exact preflight output and the
2-GiB/two-core host guard are unchanged.

A separate allocation probe on that input counts requested live allocation
bytes, rather than allocator overhead or RSS. Cloning the parsed source adds
190,245,780 bytes before sharing and 15,127,890 bytes afterwards (92.0%
less). Whole-check peak requested allocation falls from 615,952,393 to
435,951,430 bytes (29.2%). Initial parsing still stores 4,329,000 expression
nodes across its 396,000 span nodes, because each source node owns its raw
expression subtree. Sharing does not eliminate that duplication or make
native-source checking incremental; the complete FLT input and replay remain
unverified.

Formatting now parses, renders and releases one top-level source tree at a
time through the ordinary parser. It preserves input-relative spans, comment
placement, declaration spacing and parser failures. The complete token and
comment tables, raw output and formatted string still remain resident. The
later ordinary program parser, typechecker, correspondence and foundation
checks are unchanged, as are the source byte, node and depth limits.

For `--format` on the 3,000-theorem input above, five alternating debug0
samples reduce median peak RSS from 349,812 to 68,664 KiB (80.4%) and wall
time from 1,424.555 to 1,323.037 ms (7.1%). Both versions produce the same
5,884,890 formatted bytes, SHA-256
`8fa8ce9f9076231da971d4381b5eb9fa43d42d6c997dcd454cec0521c77b6cbb`.
All 702 non-cache example, library and UI source files produce identical
formatted bytes or identical errors. The 23 pinned genuine exports also
regenerate their complete committed proof files byte-for-byte, with receipts
identical to the previous compiler. These comparisons preserve existing
evidence; they do not establish the missing complete FLT proof.

The native emission workload can exercise this separately from source-only
theorem checking:

```sh
bash scripts/limited-run.sh nix develop -c python3 scripts/benchmark-proof-native-retention.py \
  --before /path/to/old/lim --after target/debug/lim \
  --declarations 500 --lets 16 --unused-expressions 0 --iterations 5
```

Against `9e6bd1b6`, five alternating debug0 samples reduce median wall time
from 5,813.444 to 5,699.962 ms (2.0%). Peak RSS is effectively unchanged,
197,104 versus 197,336 KiB, because later whole-program checking dominates.
Both compilers use default work/per-phase limits, explicit 1-GiB cumulative
accounting and the unchanged 2-GiB/two-core host guard. The synthetic export
has 709,124 bytes and SHA-256
`411cdfcfd2cfe4291623dc51cd501aa1c43c1681180580bb33fa6243840426b0`.
Every sample preserves the complete 116,737-byte receipt, SHA-256
`be090892357c8356325caf5c6a4ccb9b21a57b1ff64d4d90a5d4296e290d8790`,
and 1,181,204-byte proof source, SHA-256
`65747feed96fc11e78dc2f5a2dde106af5f23e768b10b46f01a8473acc232799`.
These measurements describe a formatting prerequisite and do not add FLT
proof coverage.

Before selecting larger importer limits, inspect an available export without
retaining its tables:

```sh
bash scripts/limited-run.sh python3 scripts/audit-lean-export.py proof.ndjson \
  --max-input-bytes 68719476736
```

The tool reads bounded records and reports the exact input SHA-256, byte and
record counts, primary record categories, maximum table IDs, largest record
and largest direct UTF-8 string value. Its summary state has fixed categories,
including an unknown bucket. Defaults are 64 MiB total and 8 MiB per line;
larger total input is explicit and capped at 64 GiB. Read, UTF-8, JSON,
duplicate-key, nesting and size failures produce a line diagnostic rather
than a success summary. This is source inspection only: it does not validate
declarations, establish a theorem, change compiler limits, or supply proof
authority. Its byte/string metrics are not retained-kernel-memory estimates.

Add `--target fermat_last_theorem` (repeat for up to 32 simple dotted names)
to inventory selected scalar declarations and the known foundation/admission
names without retaining the source tables. The optional `source_inventory`
records declaration kind, line, type/value IDs and an exact inclusive prefix
SHA-256. Missing targets remain explicit; a successful scan does not prove
that a target exists or that its proof checks. The fixed axiom names are
candidates only, with no signature or dependency-basis validation. See the
[full FLT input guide](flt-input.md) for the pinned producer commands, actual
target names, and the distinction between the proved solution and the
deliberately admitted comparator challenge.

The first tool selects original/native targets and explicit budgets from the
committed fixture manifests. Each sample starts a fresh Python worker and one
compiler child, so process peak RSS belongs to that sample rather than an earlier
larger child. JSON records include input size, selected budget, status, wall/CPU
time and peak RSS in KiB. Checker failures and finite timeouts fail the tool;
proof source and receipts are not printed. Repeat `--case` to select cases.

The retention tool generates synthetic protocol stress from the hash-pinned
identity fixture: by default, 3,000 additional theorem declarations with 32
well-typed erased lets each. Every theorem is still checked. It records the
exact input hash and alternates compiler order across samples. The input uses
an explicit 1-GiB cumulative transformation budget; the default work and phase
limits stay unchanged. These synthetic tautologies measure storage behavior,
not new mathematical coverage or a genuine Lean producer output. Temporary
inputs are removed afterwards. Neither tool invokes the resource guard again
inside its workers or treats a measurement as proof authority.

The report tool measures a synthetic checked environment with 3,000 simple
theorems and 1,024-byte declaration-name components. It streams source and
receipt fingerprints, requires identical receipt bytes across every sample,
and uses the same fresh-worker memory measurements. Name length, declaration
count and sample count are explicitly bounded options. The case stresses
receipt serialization, not the upstream FLT proof or a genuine Lean export.
Against `998a3d6e`, five alternating debug0 samples reduce median compiler
RSS from 64,840 to 41,024 KiB (36.7%) and wall time from 443.969 to
377.149 ms (15.1%). Every sample emits the same 6,752,270-byte receipt with
SHA-256 `7342fb49cb070e239ac261d97fc8e73e3b30a4efda4da4293a1c7e9b557f8c63`.
The explicit 1-GiB cumulative budget and separate 2-GiB/two-core guard are
identical for both compilers.

Paging the raw declaration inventory against `43fee588`, with five alternating
debug0 samples of the same 3,000-declaration/1,024-byte-name workload, reduces
median compiler RSS from 33,656 to 29,092 KiB (13.6%). Median wall time rises
from 586.929 to 909.680 ms (55.0%); exact encoding, structural verification,
protected writes and later reads cost time. Target selection and declared
axiom inventory are accumulated during checking to avoid an extra full scan.
The 3,793,424-byte input has SHA-256
`bc6c56d006b6ca9472ab20d4d928b2952862f400c711354d528dfd830f9ece22`.
Every sample emits the same 6,752,270-byte receipt and hash recorded above.
Proof budgets and the host guard are unchanged. This is importer storage
stress, not new mathematical coverage or a full FLT replay.

The compact checked-name index and integer closure worklist are measured
against `fba13a2a` with five alternating debug0 samples per compiler:

| Synthetic workload | Before peak RSS (KiB) | After peak RSS (KiB) | Before wall (ms) | After wall (ms) |
| --- | ---: | ---: | ---: | ---: |
| 3,000 reports, 1,024-byte names | 27,204 | 24,972 | 907.087 | 891.639 |
| 1,000 closure nodes, 16 prior neighbors | 19,944 | 19,980 | 478.194 | 530.966 |
| 2,500 closure nodes, 32 prior neighbors | 28,964 | 21,900 | 2,876.218 | 3,408.492 |

The long-name case reduces RSS by 8.2% and wall time by 1.7%. On the wider
closure, RSS falls 24.4% while time increases 18.5%; the smaller graph is 11.0%
slower with approximately unchanged RSS. Exact key reads have a cost, while
bounding the pending frontier matters more as shared dependencies grow.
These are complete checker/receipt measurements, not isolated audit timings.

The closure tool generates closed identity proofs that depend on previous
theorems through checked typed lets. It uses the hash-pinned identity fixture,
consumes the entire stream, and compares complete receipt fingerprints before
sampling and after every sample. The two graph cases explicitly select a
4-GiB cumulative transformation budget; work and per-phase limits remain at
their defaults. The report case retains its 1-GiB cumulative budget. The same
2-GiB/two-core host guard applies to both versions in every case:

```sh
bash scripts/limited-run.sh nix develop -c python3 scripts/benchmark-proof-closure.py \
  --before /path/to/before/lim --after target/debug/lim --iterations 5 \
  --declarations 2500 --width 32
```

The wider source has 7,022,593 bytes and SHA-256
`d4086d21797f2a7af3917f1789e96a223d5936c0da8cd411d7b328d8c37fbf35`.
Its identical 7,578,369-byte receipts have SHA-256
`196896bc27d96d40b052effbc7eb9b8434143597ca924ccb292debb41309d24b`.
Synthetic graphs do not add a genuine mathematical theorem or establish
full-FLT-scale support.

Deferring prefix finalization until a declaration needs it preserves every
receipt hash while avoiding per-primitive digest work. Against `abad273f`, five
paired debug0 samples reduce the 3,000-proof/64-let median from 6,573.652 to
5,970.663 ms (9.2%) and the 190,000-unused-expression median from 1,092.175 to
597.735 ms (45.3%). Peak RSS is approximately unchanged. The same budgets and
2-GiB/two-core guard apply; these are synthetic importer measurements.

The declaration tool exercises retained signatures instead of discarded proof
bodies. It adds 1,800 marker definitions and 1,800 checked theorems, each with
48 unused typed lets in its signature. Each signature references a distinct
marker, so identical-signature deduplication cannot erase the workload. It
checks equal complete receipt fingerprints before the timed fresh workers:

```sh
bash scripts/limited-run.sh nix develop -c python3 scripts/benchmark-proof-declarations.py \
  --before /path/to/before/lim --after target/debug/lim --iterations 5
```

Against `f7b368cb`, five alternating debug0 samples reduce median compiler RSS
from 41,432 to 30,408 KiB (26.6%). Median wall time increases from 2,954.887 to
3,444.346 ms (16.6%); encoding, independent structural verification and reloads
cost time. The 7,627,039-byte input has SHA-256
`5b700a3c1ab7dad6e58741f16ddca9fb49d880f139cbff7c496158afb1008c63`.
Both compilers emit the same 830,046-byte receipt with SHA-256
`49c2817e40f7285a914250c3fd258be815a5fa966ff8adadff4e820d03224f38`.
The default work/phase limits, explicit 4-GiB cumulative transformation budget
and separate 2-GiB/two-core host guard match. This measures storage scaling;
it adds no genuine mathematical theorem or FLT dependency coverage.

The name tool appends 12,000 unused 512-byte name components to the identity
fixture. They contribute 12,588,126 bytes of expanded keys/displays, while the
reader must still validate every record after the theorem. Preflight requires
equal complete receipt fingerprints, then five alternating fresh workers use
the unchanged default proof budgets and 2-GiB/two-core host guard:

```sh
bash scripts/limited-run.sh nix develop -c python3 scripts/benchmark-proof-names.py \
  --before /path/to/before/lim --after target/debug/lim --iterations 5
```

Against `a372a85c`, median debug0 compiler RSS falls from 34,472 to 17,764 KiB
(48.5%). Wall time increases from 343.947 to 625.294 ms (81.8%); this workload
isolates retained names and pays for protected backing storage. Its
6,590,262-byte input has SHA-256
`a8c7195d1d4c13da6be896827a963539f79b9e27dd9f76fbceff0027f841f8e2`.
Both compilers emit the same 1,012-byte receipt with SHA-256
`25bed32876f119316c749613a1782491639cee674c60e787972160bf4b429b52`.
This is synthetic importer storage evidence, not a genuine additional proof
or a measurement of the full FLT environment.

The universe tool appends 19,000 parameter levels with 256-byte parameter
components. The default case repeats one value; `--distinct` uses a different
parameter for every level. Both retain the original 6,899,797-byte primitive
payload charge, including the fixture, and require equal complete receipt
fingerprints before alternating fresh-worker measurements:

```sh
bash scripts/limited-run.sh nix develop -c python3 scripts/benchmark-proof-levels.py \
  --before /path/to/before/lim --after target/debug/lim --iterations 5
bash scripts/limited-run.sh nix develop -c python3 scripts/benchmark-proof-levels.py \
  --before /path/to/before/lim --after target/debug/lim --iterations 5 --distinct
```

Against `6465111e`, five paired debug0 samples per case yield:

| Universe values | Median RSS before → after (KiB) | Median wall time before → after (ms) |
| --- | --- | --- |
| Repeated | 31,076 → 18,392 (40.8% lower) | 50.919 → 70.806 (39.1% higher) |
| Distinct | 33,056 → 20,296 (38.6% lower) | 598.329 → 851.445 (42.3% higher) |

The repeated input is 427,540 bytes, SHA-256
`b8de994d1857f2b01465354103a1a9b6b5343e61d454e7f192db269a660d85dc`;
its matching 1,011-byte receipt has SHA-256
`1abbdc1d1b00828daa77ed1a1feb1e5cf72bd4c5b77761913186ffafff55e5e8`.
The distinct input is 6,067,070 bytes, SHA-256
`522687fa1c645c2cc5bbb6daffbbbfb7129dba934a670eda09914884185aa3a5`;
its matching 1,012-byte receipt has SHA-256
`eea125d06204c32813a18262a539b7722a7b3f6923d1a4ad1e29a46cd520f5e5`.
Default proof counters and the separate 2-GiB/two-core host guard match.
Paging and integrity checks trade time for bounded retained values. Recent
exact-value reuse avoids repeatedly encoding identical representations; it
does not discount input accounting or add mathematical proof coverage.
