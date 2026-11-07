# General natural-number right-shift export

[`Source.lean`](Source.lean) is byte-for-byte the original four-target source
from the verified right-shift probe. It includes the literal `small`, `zero`,
and `large` cases and the unbounded theorem
`ShiftRightProbe.general (a b : Nat) : Nat.shiftRight a b = a / 2 ^ b`, proved
by Lean's `Nat.shiftRight_eq_div_pow`. The corpus preserves the original proof
and numeric literals without rewrites or bounds.

The pinned export contains 489 declarations. Its raw NDJSON SHA-256 is
`7ad6811faecc66bf68855d87ebf7b94faa3b4599f7c3ebfdcaa5576f2d9eaa33`; the
checked native replay SHA-256 is
`a6c613deaa9ccbc2e598711e9864aa5c824d4ec0ba5fe3440578ac16275f5379`. The
global Lean axiom inventory is `propext`; target inventories are empty for
`small`, `zero`, and `large`, and `propext` for `general`. The primitive
foundation inventory is empty.

Replay uses the explicit 20,000,000-work, 1-GiB-per-phase, 4-GiB-total profile.
This fixture-specific profile does not change Lim defaults or caps. The existing
1,000,000-work profile still has an optimization gap for the general target.
No FLT completion is claimed.

The producer verifies the pinned Lean/exporter sources, preserved Apache-2.0
licenses, all declaration identities, exact private source ownership, and the
one-to-one native declaration mapping. It also checks each raw target and each
native theorem independently. Regeneration can reuse the pinned compiled
exporter from the composition probe:

```sh
bash scripts/limited-run.sh python3 scripts/regenerate-lean-right-shift-general.py \
  --lean-root /path/to/lean-4.33.1-linux \
  --exporter-dir /path/to/pinned-lean4export \
  --compiled-exporter /tmp/lim-shift-composition-export-utrczi84 \
  --lim target/debug/lim --check
```

Use `--loader /path/to/ld-linux-x86-64.so.2` if the pinned Lean executable
requires an explicit loader. The origin reader verifies the actual owner set: `Source`, `Init.Core`,
`Init.Data.Nat.Basic`, `Init.Data.Nat.Bitwise.Basic`, `Init.Data.Nat.Div.Basic`,
`Init.Prelude`, `Init.SimpLemmas`, and `Init.WF`. Every upstream source has
an exact content pin and preserved license notice in the manifest.
