# Pinned constructive closed GCD replay

This fixture exports only `GcdProbe.closed`, the closed equality
`Nat.gcd 84 30 = 6`, proved by `rfl`. The checked closure contains 251
declarations and has no declared axioms, target axioms, or primitive
foundations. Its native target is `lean-250-GcdProbe-closed`.

Raw and native checking use the explicit replay profile of 20,000,000 work per
phase, 1,073,741,824 transformation bytes per phase, and 2,147,483,648
transformation bytes total. The manifest records that profile as audit data;
checking selects its budget from command-line flags. The raw export SHA-256 is
pinned separately from the exact `Source.lean` SHA-256. The measured default
profile (200,000 work, 67,108,864 phase bytes, and 268,435,456 total bytes) also succeeds for
both raw and native checks; the producer verifies these default-budget checks
with an empty logical basis. The producer pins Lean 4.33.1, lean4export,
the exact source text, private declaration origins, six upstream source
records, and the preserved Apache-2.0 license copies. It verifies the raw
receipt, declaration mapping, owner inventory, and both representations before
atomically publishing generated products.

Check either representation with the default budget:

```sh
bash scripts/limited-run.sh target/debug/lim --check-lean-export \
  tests/fixtures/lean_export_gcd_closed/gcd-closed.ndjson GcdProbe.closed
bash scripts/limited-run.sh target/debug/lim --check-theorem \
  theorems/lean_replay/gcd-closed.lim lean-250-GcdProbe-closed
```

This is a closed GCD proof, not the full unbounded Fermat proof.

Regenerate or compare the generated export, native proof, and provenance with
the pinned tool paths:

```sh
bash scripts/limited-run.sh nix develop -c python3 \
  scripts/regenerate-lean-gcd-closed.py \
  --lean-root /path/to/lean-4.33.1-linux \
  --exporter-dir /path/to/pinned-lean4export \
  --lim target/debug/lim --check
```

Use `--loader /path/to/ld-linux-x86-64.so.2` where needed on Nix. Omit
`--check` to atomically replace changed products after all checks pass. The
manifest records declaration identities, export and native mappings, source
ownership and hashes, licenses, logical basis, and the selected budget.
