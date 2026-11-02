# Pinned closed GCD calculation replay

This fixture proves the concrete equality `Nat.gcd 84 30 = 6` as
`GcdCalculationSource.closed`. Its proof applies the checked recurrence lemma
`Nat.gcd_succ` four times, then closes with `Nat.gcd_zero_left`. It records an
actual calculation through intermediate GCD values; the checker validates the
exported proof terms and does not treat theorem names as proof authority.

The export contains 278 declarations. Its declared and target axiom inventory
is exactly `Quot.sound`, and replay also uses the pinned
`quotient-computation-v1` primitive foundation. Thus the result is not
axiom-free. The fixture uses an explicit budget of 1,000,000 work per phase,
134,217,728 transformation bytes per phase, and 1,073,741,824 transformation
bytes total. The unchanged default 200,000 work limit refuses this target.
A larger budget does not authorize axioms: the producer checks both the
no-axiom default replay and the constructive budgeted replay refusals.

This is a closed calculation using checked recurrence lemmas. It is not a
direct `rfl` evaluation, a full development of GCD, or a proof of Fermat's Last
Theorem. Lean 4.33.1, the pinned lean4export revision, six frozen upstream
source records, the private origin reader, and preserved Apache-2.0 license
copies are producer inputs. The producer verifies their versions and hashes,
the exact declaration inventory and ownership, receipt stdout, target and
native checks, and the budget/policy refusals. It atomically publishes the
export, native proof, and provenance manifest only after those checks succeed.

Check the raw target and native target independently with the explicit budget:

```sh
bash scripts/limited-run.sh target/debug/lim --check-lean-export \
  tests/fixtures/lean_export_gcd_calculation/gcd-calculation.ndjson \
  GcdCalculationSource.closed --lean-foundations \
  --proof-work 1000000 --proof-phase-bytes 134217728 \
  --proof-total-bytes 1073741824
bash scripts/limited-run.sh target/debug/lim --check-theorem \
  theorems/lean_replay/gcd-calculation.lim \
  lean-277-GcdCalculationSource-closed \
  --proof-work 1000000 --proof-phase-bytes 134217728 \
  --proof-total-bytes 1073741824
```

Regenerate or compare all products with the pinned tool paths:

```sh
bash scripts/limited-run.sh nix develop -c python3 \
  scripts/regenerate-lean-gcd-calculation.py \
  --lean-root /path/to/lean-4.33.1-linux \
  --exporter-dir /path/to/pinned-lean4export \
  --lim target/debug/lim --check
```

An optional `--loader /path/to/ld-linux-x86-64.so.2` supports the pinned Lean
binary on Nix. Omit `--check` to atomically replace changed products after all
checks pass. The manifest records every original identity and export line,
prefix and native mappings and hashes, source ownership and hashes, licenses,
logical basis, and selected budget. The source text is pinned exactly in
[`Source.lean`](Source.lean).
