# Computed division operands

[`Source.lean`](Source.lean) defines seven closed theorems in
`DivisionCompositionSource`, each proved by reflexivity over actual standard
`Nat.div` and `Nat.pow`. Cases cover `2^6 / 2^3`, computed dividend only,
computed divisor only, both computed operands, equal powers, below-divisor
powers and a computed dividend divided by zero. The large quotient is `2^64`.

The genuine dependency graph is `division-composition.ndjson`, with its exact
native translation at
[`theorems/lean_replay/division-composition.lim`](../../../theorems/lean_replay/division-composition.lim).
`provenance.json` records original identities, exact private-name source
ownership, tool/source/license hashes, native mappings and empty assumption
inventories. Both raw and native targets are checked independently. The
producer downloads nothing and verifies the pinned Lean 4.33.1/exporter
sources and preserved Apache-2.0 notices/licenses before publishing artifacts.

Optional operand normalization uses the existing checked affine rules, with
16,384 additional work units, 2 MiB of transformation payload and 48 additional
depth levels per attempt. It stays inside the enclosing limits, retains charged
work and allocations on decline, and restores the enclosing attempt on every
result. A declined or unrepresentable optional result falls back to ordinary
reduction. Unknown symbols and bad universes remain errors. Full source checking
still rejects malformed erased values and annotations. No new arithmetic
identity, operation-name privilege or proof admission is introduced.

The Euclidean observer still verifies the complete guard/update/increment and
actual fuel. Exact decimal comparisons and subtraction/compaction passes are
charged before execution, rather than charging for every worst-case subtraction
at every digit. Tests compare computed operands with independent expected
values and check quota nesting/restoration, source errors and discarded values.

This corpus and the [literal division corpus](../lean_export_division/README.md)
retain all fifteen cases separately. Their combined export exceeds the existing
256 MiB cumulative replay transformation cap; larger-environment replay remains
open, with no budget increase or skipped declarations. The separate complete
closures do not establish arbitrary course-of-values programs, remainder or
the complete unbounded Fermat proof.

Reproduce under the existing 2 GiB/two-core guard:

```sh
bash scripts/limited-run.sh python3 scripts/regenerate-lean-division-composition.py \
  --lean-root /path/to/lean-4.33.1-linux \
  --exporter-dir /path/to/pinned-lean4export --lim target/debug/lim
```

If necessary, add `--loader /path/to/ld-linux-x86-64.so.2`. Add `--check` to
reproduce and compare artifacts without publishing. Every target is also
rechecked using the native Lim CLI before publication. The shared
`scripts/benchmark-proof-division.py` compares identical-profile compilers and
reports newly accepted proofs separately from successful-check speedups.
