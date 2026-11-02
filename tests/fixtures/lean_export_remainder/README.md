# Checked standard remainders

[`Source.lean`](Source.lean) defines fourteen targets in `RemainderSource`.
Twelve closed cases cover zero divisors, below/equal divisors, exact/inexact
division, large dividends and computed powers/sums. The large case is
`(2^128 + 123) % 2^64 = 123`. Two further targets quantify over every natural:
`0 % n = 0` and `n % 0 = n`. The latter uses case analysis and explicit
unfolding of the standard definitions; no additional assumption is introduced.

`remainder.ndjson` retains all 216 genuine dependency declarations. Its exact
native translation is
[`theorems/lean_replay/remainder.lim`](../../../theorems/lean_replay/remainder.lim).
`provenance.json` records original identities, exact private-name ownership,
source/tool/license hashes, native mappings and empty assumption inventories.
The original `Nat.mod` and `Nat.modCore` definitions must belong to pinned
`Init.Prelude`. Case analysis also references `Nat.casesAuxOn` from
`Init.Data.Nat.Basic`; its source hash and Apache-2.0 notice are pinned too.
The producer verifies every original/native target independently before
publishing artifacts and never downloads tools or source files.

The Euclidean observer recognizes the exact positive-divisor comparison and
state-minus-divisor update. Remainder requires the below-divisor branch to
return the current state and the positive branch to return the previous field
unchanged; quotient's zero terminal and increment are a different pattern.
Both require actual fuel strictly greater than the quotient. Proof arguments
are not treated as fuel guarantees, and all source terms remain checked.
Tests compare the recurrence with separately materialized history records,
alter each relevant branch/update, and preserve an arbitrary base when fuel
is insufficient.

The guard's validated, context-independent numeral reduction can replace an
exactly matching application argument before exposing subtraction. Full syntax
must match; other expressions keep ordinary normalization, and the full update
shape and count are still checked. This local reuse makes computed divisors
fit the original budgets without an operation-name privilege or theorem cache.
Native and raw mutation tests reject altered proofs and well-typed wrong
operation bodies after their valid dependency prefixes.

The general range theorem `Nat.mod_lt` is not established by these controls.
Its independent genuine export currently exhausts work while checking
`Nat.modCoreGo_lt`. Larger arithmetic/dependency replay and the complete
unbounded Fermat proof remain open.

Reproduce using pinned tools and the existing 2 GiB/two-core guard:

```sh
bash scripts/limited-run.sh python3 scripts/regenerate-lean-remainder.py \
  --lean-root /path/to/lean-4.33.1-linux \
  --exporter-dir /path/to/pinned-lean4export --lim target/debug/lim
```

If necessary, add `--loader /path/to/ld-linux-x86-64.so.2`. Add `--check` to
reproduce and compare without publishing. The producer verifies Lean 4.33.1,
exporter source/revision, preserved licenses and three upstream source hashes.
The benchmark `scripts/benchmark-proof-remainder.py` compares identical-profile
compilers with alternating samples, separates coverage gains from successful-
check speedups, and retains accepted arithmetic/division controls.
