# Generic subtraction bridge fixture

[`Source.lean`](Source.lean) defines three generic, unbounded theorems in
`SubtractionBridgeSource`. `successorCancellation` applies
`Nat.succ_sub_succ_eq_sub` directly. `doubleCancellation` composes that lemma
twice with `Eq.trans`. `mappedCancellation` applies the same lemma to the
outputs of an arbitrary function from any sort to `Nat`. The source imports no
modules explicitly because Lean's default Prelude supplies these declarations.

The producer exports the genuine pinned Lean dependency graph to
`subtraction-bridge.ndjson`, records exact private declaration ownership in
`provenance.json`, and emits the Lim translation at
[`theorems/lean_replay/subtraction-bridge.lim`](../../../theorems/lean_replay/subtraction-bridge.lim).
Its schema is `lim-lean-subtraction-bridge-fixture-v1`. Private origins are read
with `scripts/lean-export-private-origins.lean`; owner attribution comes from
Lean's environment. The actual `Nat.sub`, `Nat.pred`, and
`Nat.succ_sub_succ_eq_sub` declarations, when present in the exported graph,
are required to belong to `Init.Prelude`. Their genuine induction and
congruence helper declarations and bodies remain in the export and are checked
as part of the pinned corpus; no source-name or kernel-computation shortcut
stands in for the lemma proof.

Reproduce with the pinned Lean and lean4export installations and a built Lim
executable. The producer downloads nothing and verifies the pinned tool
revisions, exporter source hashes, preserved Apache-2.0 licenses, and pinned
`Init.Prelude`/`Init.Core` sources:

```sh
bash scripts/limited-run.sh python3 scripts/regenerate-lean-subtraction-bridge.py \
  --lean-root /path/to/lean-4.33.1-linux \
  --exporter-dir /path/to/pinned-lean4export --lim target/debug/lim
```

If needed, pass `--loader /path/to/ld-linux-x86-64.so.2`. The pinned
reproduction runs under the existing 2 GiB and two-core guard, with each Lean
job limited to one worker. It independently checks every target through Lim's
native CLI before atomically publishing artifacts. `--check` performs the same
reproduction and validation without publishing. The producer records computed
hashes and provenance; this README assumes no artifact hash or declaration
count.

All three targets must have empty axiom and foundation inventories. This is a
small subtraction bridge corpus; it makes no claim to be the full FLT proof or
a complete Lean environment.
