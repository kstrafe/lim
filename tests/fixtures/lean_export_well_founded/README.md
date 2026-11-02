# Pinned well-founded equation replay

[`Source.lean`](Source.lean) is the generic `WellFoundedProbe.equation`
fixture. It quantifies over the input sort, result family, measure, step and
input value. It exercises Lean's well-founded
recursion equation for arbitrary result sorts. Lean 4.33.1 at
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6` exports 141 declarations.

The export declares only `Quot.sound`; the target's closure uses that axiom
and the `quotient-computation-v1` primitive foundation. Replay refuses the
corpus by default. `--lean-foundations` opts into the checked quotient
foundation adapter and reports both inventories. The exact native translation is
[`theorems/lean_replay/well-founded.lim`](../../../theorems/lean_replay/well-founded.lim),
and is independently checked. Declaration ownership is recorded using the canonical
private origin reader and pinned owners: `Init.Core`, `Init.Data.Nat.Basic`,
`Init.Prelude`, `Init.SimpLemmas`, `Init.WF`, and `Source`.

The corpus also checks that renaming the names of well-founded recursion
helpers does not grant proof authority, while changing the fixed `Quot.sound`
identity or corrupting the target proof is rejected.

Regenerate with already installed pinned tools; the producer downloads
nothing:

```sh
bash scripts/limited-run.sh python3 scripts/regenerate-lean-well-founded.py \
  --lean-root /path/to/lean-4.33.1-linux \
  --exporter-dir /path/to/pinned-lean4export --lim target/debug/lim --check
```

Omit `--check` to atomically write the raw export, native translation, and
provenance after all validations succeed. Preserved Lean and exporter license
files accompany the provenance.
