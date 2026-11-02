# Lean export fixtures

The separate [quotient computation corpus](../lean_export_quotient/README.md)
adds a tenth genuine producer output, its native translation, original source
and reproducible declaration/module/license provenance. It checks the pinned
quotient computation package without accepting `Quot.sound` or other axioms.

The [compact natural-literal corpus](../lean_export_naturals/README.md) adds
an eleventh genuine export with seven natural-literal/arithmetic theorems,
native proof source, and its own source/module/license provenance and
regeneration command.

The [fixed-foundation corpus](../lean_export_foundations/README.md) adds a
twelfth genuine export. It explicitly opts into only the pinned choice,
propositional extensionality and quotient soundness axioms, with checked opaque
adapters and distinct declared/target assumption inventories. Default replay
continues to reject that corpus.

The [standard arithmetic corpus](../lean_export_arithmetic/README.md) adds a
thirteenth genuine export, with thirty targets over the actual pinned `Nat.add`,
`Nat.mul`, `Nat.pow`, `Nat.sub`, `Nat.ble` and `Nat.beq` definitions plus an explicit affine recurrence.
It retains their course-of-values bodies in source,
checks them through structural observation fusion, and independently audits
the native targets with empty assumption inventories.

The [generic discrimination corpus](../lean_export_discrimination/README.md)
adds a fourteenth genuine export. Five unbounded targets exercise constructor
discrimination, successor injectivity and the standard equality-to-Boolean
bridge, including private Prelude helpers and arbitrary functions into naturals.
Its raw and native proofs are independently checked with empty assumption
inventories and reproducible ownership keyed by exact declaration identities.

The [generic subtraction bridge](../lean_export_subtraction_bridge/README.md)
adds a fifteenth genuine export: three universal cancellation proofs with
their induction/congruence dependencies, exact native translations and empty
assumption inventories. Its own manifest and producer retain source, module,
license and exact-identity provenance.

The [division corpus](../lean_export_division/README.md) adds a sixteenth
genuine export. Eight closed targets retain the actual standard fuelled
division body, exact native translations and empty assumption inventories.
Its guide describes the structural conversion rule and remaining operand
composition limits, with pinned source, module and license provenance.

The [division-composition corpus](../lean_export_division_composition/README.md)
adds a seventeenth genuine export: fifteen combined targets, including seven
computed-operand cases, with complete standard dependency bodies, exact native
translations and empty assumptions.
It has separate source, ownership, hash and license provenance.

The [remainder corpus](../lean_export_remainder/README.md) adds an eighteenth
genuine export. Fifteen targets include literal/computed remainders, two
unbounded zero controls and the general positive-divisor remainder bound. Its exact native translation, empty assumptions and
source/module/license provenance include the pinned `Nat.Basic` helper used
by case analysis.

The [well-founded equation corpus](../lean_export_well_founded/README.md) adds
a nineteenth genuine export. Its 141 declarations check the generic natural
measure fixpoint equation using the explicit `Quot.sound` foundation policy;
constructive replay refuses it. Exact private ownership, native mapping and
attribution include independently pinned `Init.WF` and `Init.SimpLemmas`.

The [GCD corpus](../lean_export_gcd/README.md) adds a twentieth genuine export.
Its 284 declarations check zero-left, successor recurrence and zero-right for
arbitrary naturals. The first two target closures use `Quot.sound`; zero-right
also uses `propext`. Explicit foundation authorization, exact native mappings,
private ownership and attribution include pinned `Init.Data.Nat.Gcd`.

The [GCD self corpus](../lean_export_gcd_self/README.md) adds a twenty-first
genuine export. Its 335 declarations check `Nat.gcd n n = n` for arbitrary
naturals with the explicitly recorded larger resource profile. Exact original
and native checks retain `Quot.sound`, `propext` and quotient computation;
more work never authorizes a missing assumption. Private source attribution
additionally pins `Init.Data.Nat.Div.Basic`.

The twenty-second [GCD calculation corpus](../lean_export_gcd_calculation/README.md)
checks the explicit recurrence-based proof of `Nat.gcd 84 30 = 6`, with 278
raw/native declarations, exactly `Quot.sound`, the quotient primitive package
and a recorded 1,000,000-work/128-MiB-phase/1-GiB-total profile. It preserves
source ownership, licenses and hashes. It does not assert that direct `rfl`
worker unfolding, the full GCD development, or FLT replay is complete.

The three files `identity.ndjson`, `inductives.ndjson` and `mutual.ndjson` are
independently hand-authored protocol fixtures, not exports from Lean or FLT.
They contain no copied upstream proof text. They use the pinned lean4export
NDJSON 3.1.0 protocol. Files starting with `real-` are actual Lean exports,
described below.

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

## Actual pinned producer outputs

`Source.lean` is original Lean source with explicit proof evidence and no
axioms, admissions, `sorry`, or native-decision shortcuts. Its `noncomputable`
definitions use checked mathematical recursors; this annotation skips Lean's
runtime code generator, which does not compile these recursor applications.
It does not admit a definition or skip kernel checking.

The following files were generated by unmodified lean4export at revision
`15f6055e299ad5b89345e533cc2192f4cc00f659`, using Lean 4.33.1 at revision
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`:

| File | Target | Lim result |
| --- | --- | --- |
| `real-identity.ndjson` | `ReplaySource.identityProof` | Checked, 2 declarations |
| `real-inductives.ndjson` | `ReplaySource.doubleTwo` | Checked, 10 declarations |
| `real-projection.ndjson` | `ReplaySource.projection` | Checked, 18 declarations |
| `real-mutual.ndjson` | `ReplaySource.mutualDepth` | Checked, 35 declarations |
| `real-nested.ndjson` | `ReplaySource.nestedCount` | Checked, 36 declarations; computes three nodes |
| `real-nested-poly.ndjson` | `ReplaySource.polyNested` | Checked, 14 declarations; explicit universe and element parameters |
| `real-nested-indexed.ndjson` | `ReplaySource.indexedNested` | Checked, 22 declarations; indexed container and auxiliary motive |
| `real-nested-deep.ndjson` | `ReplaySource.deepNested` | Checked, 14 declarations; two container specializations |
| `real-nested-sigma.ndjson` | `ReplaySource.sigmaNested` | Checked, 22 declarations; dependent pair specialization |

`real-provenance.json` binds every artifact to its SHA-256 and byte count,
records tool revisions and source hashes, and maps every declaration to its
defining module using Lean's imported module table. It retains the source
notice and hash for `src/Init/Prelude.lean`, where the upstream dependencies
in these fixtures originate. The two `*-LICENSE.txt` files preserve Lean's
and the exporter's Apache-2.0 license texts. The manifest is audit metadata,
not proof authority or a substitute for replay.

`NestedChecks.lean` checks the pinned producer's nested-inductive boundary:
positive Sigma nesting is accepted, an equality parameter capturing a
constructor-local variable is rejected, and a negative occurrence hidden in a
previously declared container is rejected. Expected errors use `#guard_msgs`;
these checks are not theorem evidence and are never imported into the replay
environment. Regeneration checks this file and records its source hash too.

These are small constructive tests, not an FLT proof or proof-dependency
slice from the upstream FLT project. Nested exports are checked using derived,
scoped recursion cases for the original containers. No exported rule supplies
a trusted reduction axiom. See the [nested replay guide](../../../docs/lean-nested-replay.md).

To reproduce, provide an existing pinned Lean installation and lean4export
checkout; the script verifies the exact exporter source hashes and Lean's
reported version/revision. It downloads nothing:

```sh
bash scripts/limited-run.sh python3 scripts/regenerate-lean-replay.py \
  --lean-root /path/to/lean-4.33.1-linux \
  --exporter-dir /path/to/lean4export
```

On NixOS, `--loader /path/to/ld-linux-x86-64.so.2` can run the release binary
without changing it. The script compiles the producer and source in a temporary
directory, exports only the named roots and their dependencies, queries source
modules, then publishes the files and manifest. Identical outputs are not
rewritten. `--output DIRECTORY` allows regeneration into a separate directory.
Use `--check` to rebuild and compare all twelve generated files byte for byte
without publishing them. This reproduction check has passed for the committed
artifacts.
The runtime reader, ordinary compiler tests and replay command need neither
Lean nor Python.


The [native Lim translations](../../../theorems/lean_replay/README.md) contain
ordinary proof source for all nine genuine exports. Their manifest preserves
input/output hashes and every original-to-native declaration mapping, linking
this directory's source/module/license provenance. They can be rechecked with
`--check-theorem` without Lean or the exporter. These remain small constructive
fixtures, not the complete FLT proof port.
