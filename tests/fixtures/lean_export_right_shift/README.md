# Pinned right-shift evaluation proofs

Four original Lean proofs are retained across 194 declarations: the small
`13 >>> 3 = 1` case, `n >>> 0 = n` for every natural, a 64-bit shift of
`2^128 + 123`, and the bit-width boundary `13 >>> 4 = 0`. All four use
reflexivity, and both global and target axiom inventories are empty.

The delayed evaluator recognizes the already checked Euclidean history
recurrence, checks the real input and fuel, and reuses a model only for the
same source code and captured dependencies. Projection and application
continuations cannot cross a function or record memoization boundary.
Every original type, value and proof remains subject to source inference.
No operation name authorizes arithmetic.

Raw and native replay use the explicit 1,000,000-work/128-MiB-phase/
1-GiB-total proof profile. The host guard remains 2 GiB and two CPU cores.

```sh
lim --check-lean-export tests/fixtures/lean_export_right_shift/shift-right.ndjson \
  ShiftRightProbe.boundary --proof-work 1000000 \
  --proof-phase-bytes 134217728 --proof-total-bytes 1073741824
lim --check-theorem theorems/lean_replay/shift-right.lim \
  lean-193-ShiftRightProbe-boundary --proof-work 1000000 \
  --proof-phase-bytes 134217728 --proof-total-bytes 1073741824
```

Reproduce all original export, native and provenance bytes with pinned tools:

```sh
bash scripts/limited-run.sh python3 scripts/regenerate-lean-right-shift.py \
  --lean-root /path/to/lean-4.33.1-linux \
  --exporter-dir /path/to/pinned-lean4export --lim target/debug/lim --check
```

Use `--loader /path/to/glibc/lib/ld-linux-x86-64.so.2` where required.
The producer verifies Lean 4.33.1 revision
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6` and exporter revision
`15f6055e299ad5b89345e533cc2192f4cc00f659`, and checks every raw and native
target. The manifest preserves source ownership, hashes, notices and the
Apache-2.0 licenses in `../lean_export/`.

`Stress.lean` preserves the additional unbounded `Nat.shiftRight_eq_div_pow`
proof closure for continued work. It is not part of the accepted corpus:
the general proof currently exceeds work or depth limits in standard helper
lemmas. No unchecked admission or complete FLT verification is claimed.
