# Pinned single-target GCD self replay

This fixture contains the single target `GcdSelfSource.self`, proved by the
upstream theorem `Nat.gcd_self`. Its checked raw export and native Lim
translation each contain 335 declarations. Provenance uses
`lim-lean-gcd-self-fixture-v1` and records the explicit proof budget used for
successful replay: 1,000,000 work per phase, 134,217,728 transformation
bytes per phase, and 1,073,741,824 transformation bytes total.

The export declares `Quot.sound` and `propext`; the target closure uses both,
along with the pinned `quotient-computation-v1` primitive foundation. Replay
requires explicit axiom authorization, and the constructive budgeted replay
does not authorize these axioms.

This is an unbounded generic self lemma (`Nat.gcd n n = n`), not a proof of
closed GCD computations, the full GCD development, or Fermat's Last Theorem.

The producer script reproduces and checks `gcd-self.ndjson`,
`provenance.json`, and `theorems/lean_replay/gcd-self.lim` using a pinned Lean
4.33.1 toolchain and lean4export revision. Run it with the explicit tool paths
documented in the script's help. `--check` compares every product exactly;
publication replaces changed files atomically after all checks succeed.

Check the two representations independently:

```sh
bash scripts/limited-run.sh target/debug/lim --check-lean-export \
  tests/fixtures/lean_export_gcd_self/gcd-self.ndjson GcdSelfSource.self \
  --lean-foundations --proof-work 1000000 --proof-phase-bytes 134217728 \
  --proof-total-bytes 1073741824
bash scripts/limited-run.sh target/debug/lim --check-theorem \
  theorems/lean_replay/gcd-self.lim lean-334-GcdSelfSource-self \
  --proof-work 1000000 --proof-phase-bytes 134217728 \
  --proof-total-bytes 1073741824
```

The header's budget comment documents this profile; it does not configure the
checker. Raw/native checks deliberately reject the unchanged default work
budget. The fixture producer also checks that a larger budget alone never
authorizes either logical axiom.

Regenerate or check every artifact with the pinned tools:

```sh
bash scripts/limited-run.sh nix develop -c python3 scripts/regenerate-lean-gcd-self.py \
  --lean-root /path/to/lean-4.33.1-linux \
  --exporter-dir /path/to/pinned-lean4export --lim target/debug/lim --check
```

Use `--loader /path/to/ld-linux-x86-64.so.2` where needed on Nix. The
[`provenance.json`](provenance.json) manifest contains each original identity,
export line, prefix hash, native name, canonical owner, source hash and notice,
plus preserved licenses and the selected budget. Keep it with copied proofs.
