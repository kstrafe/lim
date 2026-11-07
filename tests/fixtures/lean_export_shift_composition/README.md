# Lean shift composition theorem export

`Source.lean` retains the original unbounded theorem
`ShiftCompositionProbe.general`: for all natural numbers `m`, `n`, and `k`,
shifting right by `n + k` equals shifting right by `n` and then by `k`. The
proof is Lean's original `Nat.shiftRight_add` theorem. The variables and
mathematical statement are unbounded; this fixture does not replace the theorem
with finite examples.

The export is pinned to Lean 4.33.1 and lean4export. Its raw NDJSON SHA-256 is
`2b21911f3abd5fd46c4e9ea41937c396dd153fab3e99de09edcfc7657266efbb`, and it
contains 218 declarations. The global and target Lean axiom inventories are
both `propext`; the primitive foundation inventory is empty. The emitted
native replay SHA-256 is
`34c407e714110aa944a9a47f009ec0fdc73c238913ba4a98cf7fb30295162a1a`. The
producer checks the original Apache-2.0 license references, upstream source
hashes, source ownership, declaration identities, and translation mapping.

Replay uses the explicit 20,000,000-work, 1-GiB-per-phase, 4-GiB-total
profile. This is a fixture-specific profile; it does not change Lim's defaults
or the serial host's 2-GiB resource guard. The existing 1,000,000-work profile
has not been accepted for this theorem and remains an open optimization gap.
Raw/native replay, altered-evidence rejection, renaming and forced paging are
covered by the test suite.

Reproduce and verify the raw export, native replay, and provenance with the
pinned tools:

```sh
bash scripts/limited-run.sh python3 scripts/regenerate-lean-shift-composition.py \
  --lean-root /path/to/lean-4.33.1-linux \
  --exporter-dir /path/to/pinned-lean4export \
  --compiled-exporter /path/to/pinned-compiled-exporter \
  --lim target/debug/lim --lean-foundations --check
```

The producer rejects a mismatched raw export, native replay, declaration
count, axiom inventory, source ownership, or native declaration mapping. Its
origin-owner expectation is `Source`, `Init.Core`, `Init.Data.Nat.Basic`,
`Init.Data.Nat.Bitwise.Basic`, `Init.Prelude`, and `Init.SimpLemmas`; the producer obtains and checks the actual
owner of every declaration during regeneration. Use `--loader
/path/to/ld-linux-x86-64.so.2` when the pinned executable requires an explicit
loader.

The optional compiled-exporter directory contains the exact pinned `Export.lean`,
`Main.lean`, `Export.olean`, and `Main.olean` files. Both sources and compiled
products are hash checked; the manifest records compiled input digests. This
avoids rebuilding the exporter in the constrained host. `Source.lean` and the
raw export are regenerated, and every proof is checked independently by Lim.
Omit the option to rebuild the exporter tools from their pinned sources on a
host where that compilation fits the same resource guard. Cached tool products
and the provenance manifest supply no theorem authority.
