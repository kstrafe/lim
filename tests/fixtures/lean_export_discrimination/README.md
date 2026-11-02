# Generic discrimination fixture

[`Source.lean`](Source.lean) supplies five generic, unbounded proofs under
`DiscriminationSource`: zero is not a successor, successor is injective,
an equality of naturals implies that their Boolean equality test is true,
the Boolean equality test of any natural with itself is true, and equality
preserves that test after mapping through an arbitrary function to naturals.
The source uses no axioms or admitted proofs. The raw export is
`discrimination.ndjson`; the checked Lim translation is
[`theorems/lean_replay/discrimination.lim`](../../../theorems/lean_replay/discrimination.lim).
The schema is `lim-lean-discrimination-fixture-v1`. Original-to-native names
and source/module/license provenance are recorded in `provenance.json`; tests
read native target names from that mapping rather than assuming export ordinals.

The genuine export also includes private `noConfusion_of_Nat.aux` helpers and
`Nat.beq` from `Init.Prelude`, and `Nat.succ.inj` from `Init.Core`. These
are part of the pinned Lean export and are retained as generated, not replaced
with hand-authored declarations.

Reproduce with the pinned Lean and lean4export installations, their toolchain
and the built Lim executable. The script downloads nothing and verifies the
exact Lean 4.33.1 revision and exporter source hashes recorded in the manifest:

```sh
bash scripts/limited-run.sh python3 scripts/regenerate-lean-discrimination.py \
  --lean-root /path/to/lean-4.33.1-linux \
  --exporter-dir /path/to/pinned-lean4export --lim target/debug/lim
```

When required, pass `--loader /path/to/ld-linux-x86-64.so.2`. Private-origin
attribution is queried through `scripts/lean-export-private-origins.lean` so
private helper provenance comes from Lean's environment. The producer applies
the same 2 GiB memory, two-core CPU quota, single-job and ten-minute limits
used for the other pinned export fixtures, checks the
original export and native translation, and records the resulting hashes and
provenance; no hashes or declaration counts are asserted here. Use `--check`
to regenerate and compare without publishing artifacts.

All five targets have empty axiom and foundation inventories. These generic
discrimination results exercise the proof kernel prerequisites; they are not
the full FLT proof or a complete Lean environment.
