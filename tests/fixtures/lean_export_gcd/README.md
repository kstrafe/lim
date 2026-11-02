# Pinned generic GCD theorem replay

This fixture contains three completed targets proved by upstream theorems:
`GcdSource.zeroLeft` (`Nat.gcd_zero_left`), `GcdSource.successor`
(`Nat.gcd_succ`), and `GcdSource.zeroRight` (`Nat.gcd_zero_right`). The raw
export and native Lim translation each contain 284 declarations. Provenance
uses `lim-lean-gcd-fixture-v1`.

The export declares `Quot.sound` and `propext`. The target closures differ:
`zeroLeft` and `successor` use only `Quot.sound`; `zeroRight` uses both
`Quot.sound` and `propext`. All three also use the pinned
`quotient-computation-v1` primitive foundation. Replay requires explicit
authorization and this is not an axiom-free result.

The generic self theorem and closed GCD computation remain open. This corpus
is a dependency milestone, not the complete Fermat's Last Theorem proof.

Check the final target, which also checks every preceding declaration:

```sh
bash scripts/limited-run.sh target/debug/lim --check-lean-export \
  tests/fixtures/lean_export_gcd/gcd.ndjson GcdSource.zeroRight --lean-foundations
bash scripts/limited-run.sh target/debug/lim --check-theorem \
  theorems/lean_replay/gcd.lim lean-283-GcdSource-zeroRight
```

[`provenance.json`](provenance.json) records all three native target names,
per-target logical bases, original declaration identities and export lines,
canonical source/module ownership, source hashes, notices and preserved
licenses. Keep this provenance with copied exports and translations.

Regenerate with the already pinned Lean and exporter tools:

```sh
bash scripts/limited-run.sh nix develop -c python3 scripts/regenerate-lean-gcd.py \
  --lean-root /path/to/lean-4.33.1-linux \
  --exporter-dir /path/to/pinned-lean4export --lim target/debug/lim --check
```

An optional `--loader /path/to/ld-linux-x86-64.so.2` supports the pinned
upstream binary on Nix. Omitting `--check` replaces each changed artifact
atomically after every raw/native check succeeds; identical files are retained.
The producer verifies the Lean revision, exporter source hashes, upstream
sources, licenses, exact declaration mapping, default policy refusal and each
target's precise logical basis. The source is fixed to the three explicit
upstream theorem applications in [`Source.lean`](Source.lean).
