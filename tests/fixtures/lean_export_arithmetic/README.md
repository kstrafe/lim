# Standard natural arithmetic fixture

[`Source.lean`](Source.lean) gives five kernel-checked `rfl` computations over
Lean's standard `Nat.add` and `Nat.mul`: large addition, multiplication, a zero
product, the right-zero identity for every natural, and nested multiplication
followed by addition. The source has no imports, axioms, admissions, or
`native_decide`. Lean's module table identifies the standard declarations as
owned by the pinned `Init.Prelude` module.

The raw export is `arithmetic.ndjson`; its checked Lim translation is
[`theorems/lean_replay/arithmetic.lim`](../../../theorems/lean_replay/arithmetic.lim).
The fixture contains 34 checked declarations, with original/native identities,
types, bodies, dependencies, source hashes and license attribution recorded in
[`provenance.json`](provenance.json). Its schema is
`lim-lean-arithmetic-fixture-v1`. The ordinary native file preserves the
course-of-values helpers; guarded first-field and fixed-argument fusion expose
their arithmetic recurrences without replacing bodies by trusted names.

Check the export and a native target without installing Lean:

```sh
lim --check-lean-export tests/fixtures/lean_export_arithmetic/arithmetic.ndjson \
  ArithmeticSource.nested --emit-proof /tmp/arithmetic.lim
lim --check-theorem theorems/lean_replay/arithmetic.lim lean-33-ArithmeticSource-nested
```

All five target inventories are empty. These computations and one generic
right-zero identity are not the full FLT proof or a complete Lean environment.

Regenerate with the already installed pinned Lean and lean4export sources and a
built Lim executable. The script downloads nothing:

```sh
bash scripts/limited-run.sh python3 scripts/regenerate-lean-arithmetic.py \
  --lean-root /path/to/lean-4.33.1-linux \
  --exporter-dir /path/to/pinned-lean4export --lim target/debug/lim
```

Add `--loader /path/to/ld-linux-x86-64.so.2` when an explicit ELF loader is
needed. The producer validates tool, exporter, license, and Prelude pins;
builds the exporter and source in an isolated temporary directory; queries
declaration ownership from Lean's module table; checks the export and empty
axiom/foundation inventories; then translates and audits all five native
targets before publishing artifacts. Use `--check` to rebuild and compare
without publishing. Keep the preserved [Lean](../lean_export/LEAN-LICENSE.txt)
and [exporter](../lean_export/EXPORTER-LICENSE.txt) notices and provenance with
copied artifacts. All replay and native checking still happens locally; a
producer receipt or hash never authorizes unchecked evidence.
