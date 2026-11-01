# Pinned logical-foundation replay

[`Source.lean`](Source.lean) is an original small fixture using Lean's
`Classical.choice`, `propext` and `Quot.sound`. It contains no user-declared
axioms, admissions, `sorry`, native-decision shortcuts or FLT proof.
It was compiled with Lean 4.33.1 at
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, then exported with unmodified
lean4export `15f6055e299ad5b89345e533cc2192f4cc00f659`.

[`foundations.ndjson`](foundations.ndjson) has 34 declarations. Default replay
rejects its first axiom record. Explicit `--lean-foundations` permits only
the pinned three canonical identities with exact checked signatures and safe
metadata. Lim independently checks the standard equality, nonemptiness and
bi-implication families and the quotient computation package. It derives
opaque native initializers using the fixed logical basis, ordinary induction,
record projections and equality elimination. No imported record can supply
an arbitrary postulate or a reduction rule.

The three user theorem targets exercise choice reflexivity, propositional
extensionality and equality of related quotient representatives. The complete
input declares all three axioms. Each target's actual closure contains only
one; the generated auxiliary nonemptiness proof has an empty closure. The
receipt reports `axioms` and `target_axioms` separately. These are proofs
relative to the explicit logical assumptions, not proofs of those axioms.

The ordinary native source is
[`theorems/lean_replay/foundations.lim`](../../../theorems/lean_replay/foundations.lim).
Its opaque initializers remain present and checked; their values are hidden
from conversion. Translation independently verifies source correspondence and
the target's native assumption inventory. Source comments provide attribution,
not checking authority.

```sh
lim --check-lean-export tests/fixtures/lean_export_foundations/foundations.ndjson \
  BasisProbe.quotientRelated --lean-foundations --emit-proof /tmp/foundations.lim
lim --check-theorem theorems/lean_replay/foundations.lim lean-19-BasisProbe-choiceReflexive
lim --check-theorem theorems/lean_replay/foundations.lim lean-24-BasisProbe-propositionEquality
lim --check-theorem theorems/lean_replay/foundations.lim lean-33-BasisProbe-quotientRelated
```

[`provenance.json`](provenance.json) records input/output hashes, all original
and native identities, actual defining modules, source hashes, original
Prelude/Core copyright notices and links to the preserved
[Lean](../lean_export/LEAN-LICENSE.txt) and
[exporter](../lean_export/EXPORTER-LICENSE.txt) licenses. Keep this attribution
with copied artifacts. It also records the expected per-target inventories.

Reproduce the raw export, native translation and provenance together with
previously downloaded pinned tools and a built compiler:

```sh
bash scripts/limited-run.sh python3 scripts/regenerate-lean-foundations.py \
  --lean-root /path/to/lean-4.33.1-linux \
  --exporter-dir /path/to/pinned-lean4export --lim target/debug/lim --check
```

Add `--loader /path/to/ld-linux-x86-64.so.2` when the release executable
requires an explicit loader. The script downloads nothing. It validates
tool, source and license pins, compiles fresh producer modules in an isolated
`LEAN_PATH`, queries original declaration ownership, replays every target,
checks native inventories, and verifies default refusal. Omit `--check` to
publish changed artifacts only after every check passes. Lim and Cargo can
consume the committed artifacts without a Lean installation.
