# Checked standard division fixture

[`DivisionSource.lean`](DivisionSource.lean) defines eight closed theorems in
`DivisionSource`, each proved by reflexivity over Lean's actual `Nat.div`.
Cases cover `0/0`, a large dividend divided by zero, below/equal divisor,
`21/3`, `21/5`, and exact/inexact dividends around `2^128` divided by `2^64`.
Numerals are explicit decimal literals; the large quotient is `2^64`.

The producer preserves the complete genuine exported dependency graph,
including the standard fuelled division/history body, as `division.ndjson`.
Its exact native translation is
[`theorems/lean_replay/division.lim`](../../../theorems/lean_replay/division.lim).
`provenance.json` records original identities, source ownership keyed by exact
private names, source/tool/license hashes, original/native mapping and empty
axiom/foundation inventories. Standard division definitions are required to
belong to the pinned `Init.Prelude`, not a replacement fixture implementation.

Lim's Euclidean observation checks the actual guard, predecessor iteration,
recursive field and increment. It requires strictly enough actual fuel to
reach the terminal branch; proof arguments are not accepted as fuel guarantees.
All arguments and annotations are still checked. Exact decimal arithmetic is
charged against existing work and allocation limits before it runs. This is
an additional trusted conversion optimization, tested against separately
expanded history records and changed recurrences. It is not a formal
verification of the checker.

The [composition corpus](../lean_export_division_composition/README.md) additionally
checks operands written as powers. The observer now uses bounded optional
normalization through the existing arithmetic rules and charges the actual
long-division operations before they run. A combined fifteen-target export
exceeds the cumulative replay payload cap, so the corpora independently retain
all cases without raising that limit. This does not establish arbitrary
course-of-values algorithms, remainder, the full mathematical dependency
closure or the complete unbounded FLT proof.

Reproduce with the pinned Lean/exporter installations and a built Lim binary:

```sh
bash scripts/limited-run.sh python3 scripts/regenerate-lean-division.py \
  --lean-root /path/to/lean-4.33.1-linux \
  --exporter-dir /path/to/pinned-lean4export --lim target/debug/lim
```

If necessary, add `--loader /path/to/ld-linux-x86-64.so.2`. The producer downloads
nothing. It verifies Lean 4.33.1, the exporter revision/source, preserved
Apache-2.0 licenses and pinned Prelude/Core source hashes. It independently
checks every raw target and every translated native target before atomically
publishing artifacts. Add `--check` to reproduce and compare without publishing.
Run under the existing 2 GiB/two-core guard, with one Lean worker at a time.

Compare same-profile compilers with the committed benchmark:

```sh
bash scripts/limited-run.sh python3 scripts/benchmark-proof-division.py \
  --before /path/to/previous/lim --after target/debug/lim
```

It alternates 25 measured runs after a warmup, reports wall medians and child
CPU means, and distinguishes newly accepted proofs from speedups. A zero-division
prefix and existing arithmetic/discrimination/subtraction corpora serve as
previously accepted controls. Rejected old division runs are never counted as
successful-check timings.
