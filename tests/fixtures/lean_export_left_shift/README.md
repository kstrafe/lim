# Pinned left-shift proofs

This corpus retains four original Lean proofs across 138 declarations:

- `small`: `Nat.shiftLeft 13 2 = 52`, by reflexivity.
- `zero`: `Nat.shiftLeft n 0 = n` for every natural `n`, by reflexivity.
- `large`: a 65-bit shift of `2^128 + 123`, by reflexivity.
- `general`: `Nat.shiftLeft a b = a * 2^b` for all naturals `a,b`, using the
  actual standard-library `Nat.shiftLeft_eq` proof and its dependency closure.

The export's declaration-wide axiom inventory is `propext`, because the
dependency closure includes it. Target inventories are narrower: `small`,
`zero`, and `large` require no logical assumptions; only `general` requires
`propext`. Raw replay authorizes that axiom only with explicit
`--lean-foundations`; native checking reports the selected theorem's
target-specific basis. No mathematical admission or new primitive shift rule
is introduced.

The evaluator recognizes an identity-base function fold
`F(0,x)=x; F(n+1,x)=F(n,U(x))`, with `U` independent of `n` and `F(n)`. It
rewrites this to scalar iteration of `U` only when the natural count is
computationally known, after checking the complete update syntax and binder
scopes. For left shift, `U(x)=2*x`; existing checked affine arithmetic
evaluates the resulting iteration. An unknown count retains ordinary
conversion: the general theorem is checked using its original induction proof,
not this optimization. Function names do not authorize the rewrite, and
ordinary source inference checks every original source type and proof,
including discarded annotations and values.

The regeneration check replays the full 138-declaration raw export once for
each of the four selected targets, verifies the declaration inventory and
each target's axiom inventory, and checks all four translated native
theorems. Each check uses the same proof budget: 1,000,000 work per phase,
134,217,728 transformation bytes per phase, and 1,073,741,824 transformation
bytes total. These limits are unchanged by the tail optimization.

Lean is pinned to 4.33.1, revision
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`; lean4export is pinned to
`15f6055e299ad5b89345e533cc2192f4cc00f659`, format 3.1.0. The provenance
manifest records every original identity, export line, prefix hash, dependency,
module, source hash, original copyright notice and native name. Preserve its
Apache-2.0 license references in `../lean_export/` with copied artifacts.

```sh
lim --check-lean-export tests/fixtures/lean_export_left_shift/shift-left.ndjson \
  ShiftLeftProbe.general --lean-foundations \
  --proof-work 1000000 --proof-phase-bytes 134217728 --proof-total-bytes 1073741824
lim --check-theorem theorems/lean_replay/shift-left.lim lean-137-ShiftLeftProbe-general \
  --proof-work 1000000 --proof-phase-bytes 134217728 --proof-total-bytes 1073741824
```

These commands show the general theorem, whose target-specific inventory
requires `propext`. Selecting `small`, `zero`, or `large` reports an empty
target inventory, but raw replay still needs `--lean-foundations`: it checks
every declaration, including the general theorem's dependencies. The
regeneration script below checks the full file for each selected target.

To reproduce all raw, native and manifest bytes using the pinned installed tools:

```sh
bash scripts/limited-run.sh python3 scripts/regenerate-lean-left-shift.py \
  --lean-root /path/to/lean-4.33.1-linux \
  --exporter-dir /path/to/pinned-lean4export \
  --lim target/debug/lim --check
```

Use `--loader /path/to/glibc/lib/ld-linux-x86-64.so.2` when required by the
release executable. The host guard remains 2 GiB and two cores; proof budgets
are unchanged. Right-shift and large bitwise evaluation remain open work.
These proofs do not constitute the complete FLT port.
