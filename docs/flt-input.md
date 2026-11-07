# Acquiring the pinned full FLT input

This guide concerns the optional elaborated-export replay route. The direct
mathematical source port uses the pinned Lean source and writes proofs in
Lim; it does not require this export. See the [source-port map](flt-source-port.md).

Lim has not verified the complete upstream Fermat's Last Theorem proof. The
producer recipes below are for a separately provisioned external host; none
was run here. Do not run the full producer locally. The local
`scripts/limited-run.sh` guard stays at **2 GiB and 200% CPU**.

The source inspected with `git show` in `/tmp/lim-flt-upstream` is
[anthropics/fermats-last-theorem at
`6e837e75355538c7f80bab5b956861e86c4eacc2`](https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2).
Its [README](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/README.md)
reports a **37.8 GB** export, about **90 GB** of producer memory, and
**1,052,234** declarations accepted by patched nanoda. Those results were not
reproduced here; no actual full-export SHA-256 or public binary download URL
has been established here.

On 2026-11-03 the upstream [releases page](https://github.com/anthropics/fermats-last-theorem/releases)
still listed no published releases. A bounded metadata check also found no
public Actions artifacts. The pinned tree contains no `.github` workflows,
and its [nanoda directory](https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2/verification/nanoda)
contains producer configuration, patches and a script rather than an export.
The configured local export and digest were also absent. This checks those
public and local locations; it does not rule out a privately held or separately
hosted export. No download URL or complete-export digest was established.

| Input component | Exact pin or identity |
| --- | --- |
| FLT source | `6e837e75355538c7f80bab5b956861e86c4eacc2` |
| Exporter source | `leanprover/lean4export`, `15f6055e299ad5b89345e533cc2192f4cc00f659`, tag `v4.33.0` |
| Exporter metadata / NDJSON format | `lean4export` version `3.1.0` / format `3.1.0` |
| Lean runtime | `leanprover/lean4:v4.33.1`, revision `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` |
| Mathlib | `db584cd6d46c92f209a44c0f1c829460d327499d` |
| Imported module | `Theorems.Thm_fermat_last_theorem` |
| Actual global theorem | `fermat_last_theorem` |

The runtime and package pins come from the upstream
[lean-toolchain](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/lean-toolchain)
and [lake-manifest.json](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/lake-manifest.json).
Upstream's
[comparator setup](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/verification/comparator/run.sh)
builds exporter tag `v4.33.0` on Lean 4.33.1. Its
[metadata implementation](https://github.com/leanprover/lean4export/blob/15f6055e299ad5b89345e533cc2192f4cc00f659/Export.lean#L416-L438)
and [NDJSON specification](https://github.com/leanprover/lean4export/blob/15f6055e299ad5b89345e533cc2192f4cc00f659/format_ndjson.md)
use exporter/format version `3.1.0`.

The theorem is declared in
[Theorems/Thm_fermat_last_theorem.lean](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_fermat_last_theorem.lean#L128),
with proof source
[P2M/Sol/S_fermat_last_theorem.lean](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_fermat_last_theorem.lean#L129).
[verification/comparator/Solution.lean](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/verification/comparator/Solution.lean)
imports the theorem module and derives `FLT_for_comparator` and
`FLT_mathlib_for_comparator` from `fermat_last_theorem`.

**Never accept the challenge export as proof input.**
[verification/comparator/Challenge.lean](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/verification/comparator/Challenge.lean)
deliberately uses `sorry` for both comparison statements. Select `Solution` or
the actual theorem module; matching names and types alone are insufficient.

Prefer the original bytes from the upstream artifact holder. The pinned
[verification/nanoda/run.sh](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/verification/nanoda/run.sh#L25-L34)
produces these files, relative to the FLT checkout with its default `WORK`:

```text
.verify-work/nanoda/solution.export
.verify-work/nanoda/solution.export.sha256
.verify-work/nanoda/export.err
```

Request those original files, their exact byte count and provenance from the
artifact holder. If `WORK` was customized, use that location. Validate the full
sidecar digest, rather than a truncated progress-log hash, on the receiving host:

```sh
cd /path/to/received/nanoda
sha256sum --check solution.export.sha256
```

Preserve original bytes and sidecar, including after decompression. Do not
reserialize JSON, renumber IDs, strip declarations or remove bodies.

If the original is unavailable, reproduce it from the pinned compiled products
on the external host: the fully built FLT/Mathlib tree, prepared
`.verify-work/wrapper` with compiled `Solution` and dependency search paths, and
`.verify-work/bin/lean4export`. The comparator setup linked above prepares this
wrapper; its full workflow also performs a large replay. This export-only
recipe assumes the products already exist. Verify their pins before use.

The upstream producer invocation and root order follow, using a separate
output directory to preserve any original artifact. `VMEM_GB=300` belongs
only to this **external-host recipe**, not the local guard:

```sh
set -euo pipefail
FLT_ROOT=/path/to/pinned/fermats-last-theorem
WORK=$FLT_ROOT/.verify-work
W=$WORK/wrapper
EXPBIN=$WORK/bin/lean4export
OUT=$WORK/lim-export
VMEM_GB=300
mkdir -p "$OUT"
(
  cd "$W"
  unset LEAN_PATH
  export LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-4} LEAN_ABORT_ON_PANIC=1
  ulimit -v $((VMEM_GB*1024*1024))
  lake env "$EXPBIN" Solution -- Nat String String.mk Char Quot Quot.mk Quot.lift Quot.ind FLT_for_comparator FLT_mathlib_for_comparator \
    propext Quot.sound Classical.choice Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor Nat.xor \
    Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat List eagerReduce > "$OUT/solution.export" 2> "$OUT/export.err"
)
( cd "$OUT" && sha256sum solution.export > solution.export.sha256 )
```

Retain successful exit status, stderr, complete digest and byte count. Keep a
reproduction distinct from the original unless their full hashes agree.

A focused alternative, using the same external-host setup, exports the actual
theorem's dependency closure:

```sh
(
  cd "$W"
  unset LEAN_PATH
  export LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-4} LEAN_ABORT_ON_PANIC=1
  ulimit -v $((VMEM_GB*1024*1024))
  lake env "$EXPBIN" Theorems.Thm_fermat_last_theorem -- fermat_last_theorem \
    > "$OUT/fermat-last-theorem.export" 2> "$OUT/fermat-last-theorem.err"
)
( cd "$OUT" && sha256sum fermat-last-theorem.export > fermat-last-theorem.export.sha256 )
```

This selects different roots without changing the proof. The pinned
[Main.lean](https://github.com/leanprover/lean4export/blob/15f6055e299ad5b89345e533cc2192f4cc00f659/Main.lean)
imports modules before `--` and selects constants after it; `dumpConstant` in
[Export.lean](https://github.com/leanprover/lean4export/blob/15f6055e299ad5b89345e533cc2192f4cc00f659/Export.lean)
follows type/body dependencies. Preserve full type declarations, definition
values, theorem proofs, opaque initialization bodies, inductives, constructors
and recursor data. Give this alternative its own hash, byte count and root
list; its size is unmeasured here.

From the Lim checkout, the target-aware source inventory command is:

```sh
python3 scripts/audit-lean-export.py FILE --max-input-bytes 68719476736 --target fermat_last_theorem
```

Replace `FILE` with the complete export. For local execution, use the outer guard:

```sh
bash scripts/limited-run.sh python3 scripts/audit-lean-export.py FILE \
  --max-input-bytes 68719476736 --target fermat_last_theorem
```

The inspector has bounded state and an 8 MiB line limit. Its 64 GiB scan bound
does not extend the guard's finite deadline; a refused or interrupted scan is
not a complete inventory.

**Retain the original first metadata header separately** and compare it with
the pins above. The inspector does not return metadata or per-record SHA-256
hashes. It reports the whole-file SHA-256, byte/record/declaration counts,
maximum table IDs and record sizes. In the target-aware output from
[audit-lean-export.py](../scripts/audit-lean-export.py),
`source_inventory.targets.fermat_last_theorem` records the observed name ID and
a scalar declaration summary: kind, line, type/value expression IDs, universe
parameter count and `prefix_sha256`. The prefix hash includes the exact raw
bytes through the declaration, including its newline if present. Check that
the target is present, has theorem kind and has a proof value.

`source_inventory.axioms` summarizes the known declarations `propext`,
`Quot.sound` and `Classical.choice`.
`source_inventory.unrecognized_axioms.count` counts all other axiom
declarations, including `sorryAx`, with bounded name-ID/location examples.
`source_inventory.admissions.sorryAx` separately records that admission when
observed. Reject `sorryAx` evidence; unresolved axiom names remain unknown.

This is **source inventory, not proof checking**. Whole-file/prefix hashes,
metadata, compiler success and comparator/nanoda reports do not supply Lim
proof authority or establish the target's axiom basis. Upstream's
[FinalCheck.lean](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/FinalCheck.lean)
records its expected three-axiom basis.

Keep source/exporter commits, exporter binary hash, `lean --version` and runtime
revision, package pins, exact producer command, output hash/byte count and logs.
Carry upstream
[LICENSE](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/LICENSE),
[NOTICE](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE)
and [ATTRIBUTION.md](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md)
with applicable Lean, exporter, Mathlib and dependency licenses and per-file
attribution, even when NDJSON omits source comments.

Lim's raw replay defaults to **64 MiB** and **4,096 declarations**.
Explicit `LeanExportLimits` / `--export-*` choices can now select larger
cumulative input, name, universe, expression, declaration and dependency
limits, independently of proof transformation budgets. Resident table budgets,
per-record bounds and raw-store scratch capacities remain separate. Native
output has its own explicit `NativeProofLimits`
profile and fresh closed-artifact checker. Raw and native kernel stores now
accept separate explicit scratch capacities while retaining their 128-MiB
default and fixed resident thresholds; full-environment residency and kernel
semantic coverage remain unverified. A checked 4,097-declaration synthetic
replay exercises the selected count path; no full-FLT replay profile is
established here.
The full elaborated export and a trusted acquisition hash are still absent.
See the [input limit reference](lean-export.md#resource-limits-and-unsupported-features).


On 2026-11-04 the upstream [GitHub releases page](https://github.com/anthropics/fermats-last-theorem/releases)
still listed no releases. This checks the release channel only; it does not
prove that no export is available through another service or private storage.
The full elaborated export and acquisition hash remain absent at the local
paths checked by this work. A source checkout or publisher check log cannot
replace that proof input.
