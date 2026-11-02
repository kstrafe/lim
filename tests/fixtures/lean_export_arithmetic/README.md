# Standard natural arithmetic fixture

[`Source.lean`](Source.lean) gives thirty kernel-checked `rfl` proofs over
Lean's standard `Nat.add`, `Nat.mul`, `Nat.pow`, `Nat.sub`, `Nat.ble` and `Nat.beq`: large sums, products,
powers, zero/one bases, generic right-zero and zero-exponent identities,
nested operations, an explicit affine recurrence with a nonzero offset, and
truncated subtraction with large, zero and equal operands, Boolean ordering
and equality, generic zero-left comparison and nested arithmetic operands.
The source has no imports, axioms, admissions, or
`native_decide`. Lean's module table identifies the standard declarations as
owned by the pinned `Init.Prelude` module.

The raw export is `arithmetic.ndjson`; its checked Lim translation is
[`theorems/lean_replay/arithmetic.lim`](../../../theorems/lean_replay/arithmetic.lim).
The fixture contains 78 checked declarations, with original/native identities,
types, bodies, dependencies, source hashes and license attribution recorded in
[`provenance.json`](provenance.json). Its schema is
`lim-lean-arithmetic-fixture-v1`. The ordinary native file preserves the
course-of-values helpers; guarded first-field and fixed-argument fusion expose
their arithmetic recurrences without replacing bodies by trusted names. A
separate structural rule recognizes the exact checked predecessor recursor
and its iteration on the accumulator, using decimal subtraction truncated at
zero. Unknown locals, changed branches and opacity cannot authorize that rule.
Completed finite data observations and nonrecursive case application expose
the matcher histories for Boolean operations. The paired-predecessor rule
checks all zero/successor cases and binder indices, selecting the actual
terminal from the definition without assuming constructor names or order.

Check the export and a native target without installing Lean:

```sh
lim --check-lean-export tests/fixtures/lean_export_arithmetic/arithmetic.ndjson \
  ArithmeticSource.equalZero --emit-proof /tmp/arithmetic.lim
lim --check-theorem theorems/lean_replay/arithmetic.lim lean-39-ArithmeticSource-power
lim --check-theorem theorems/lean_replay/arithmetic.lim lean-45-ArithmeticSource-affineGrowth
lim --check-theorem theorems/lean_replay/arithmetic.lim lean-54-ArithmeticSource-nestedSubtraction
lim --check-theorem theorems/lean_replay/arithmetic.lim lean-63-ArithmeticSource-booleanLess
lim --check-theorem theorems/lean_replay/arithmetic.lim lean-74-ArithmeticSource-equalLarge
```

All thirty target inventories are empty. These computations and generic
identities are not the full FLT proof or a complete Lean environment.
The one-base example locally enables Lean's own literal-evaluation threshold
for its fixed exponent of one million; the affine example gives its explicit
recursor a local Lean recursion-depth allowance. Lim retains every existing
kernel work, depth, allocation and result-size limit during replay.

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
axiom/foundation inventories; then translates and audits all thirty native
targets before publishing artifacts. Use `--check` to rebuild and compare
without publishing. Keep the preserved [Lean](../lean_export/LEAN-LICENSE.txt)
and [exporter](../lean_export/EXPORTER-LICENSE.txt) notices and provenance with
copied artifacts. All replay and native checking still happens locally; a
producer receipt or hash never authorizes unchecked evidence.
