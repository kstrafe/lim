# Pinned bitwise forwarding replay

`Source.lean` proves the following equalities using Lean's original `rfl`:

| Operation | Inputs | Result |
| --- | --- | --- |
| `Nat.land` | 13, 11 | 9 |
| `Nat.lor` | 13, 11 | 15 |
| `Nat.xor` | 13, 11 | 6 |

The raw NDJSON contains their complete 385-declaration dependency closure.
`theorems/lean_replay/bitwise.lim` is Lim's checked native translation. These
are closed examples of the evaluator's forwarding path, not an unbounded
bitwise correctness theorem or a proof of FLT.

The source uses Lean 4.33.1 at
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6` and lean4export at
`15f6055e299ad5b89345e533cc2192f4cc00f659`, NDJSON format 3.1.0. The manifest
records every declaration's exact identity, source prefix hash, dependencies,
original module, source hash and native name. Upstream source hashes include
the actual bitwise and division modules. The original copyright notices and
Apache-2.0 license references are retained in the manifest and shared license
files in `../lean_export/`.

The source closure and each target explicitly depend on **`propext`**. Raw
checking requires `--lean-foundations`; the default constructive policy rejects
it. Native checking reports the same foundation. No admission or new logical
axiom is introduced by the evaluator.

```sh
lim --check-lean-export tests/fixtures/lean_export_bitwise/bitwise.ndjson \
  BitwiseProbe.xor_small --lean-foundations \
  --proof-work 1000000 --proof-phase-bytes 134217728 --proof-total-bytes 1073741824
lim --check-theorem theorems/lean_replay/bitwise.lim lean-384-BitwiseProbe-xor_small \
  --proof-work 1000000 --proof-phase-bytes 134217728 --proof-total-bytes 1073741824
```

To reproduce all three artifacts without downloading tools:

```sh
bash scripts/limited-run.sh python3 scripts/regenerate-lean-bitwise.py \
  --lean-root /path/to/lean-4.33.1-linux \
  --exporter-dir /path/to/pinned-lean4export \
  --lim target/debug/lim --check
```

Pass `--loader /path/to/glibc/lib/ld-linux-x86-64.so.2` when the release binary
needs an explicit dynamic loader. The producer compiles the pinned exporter
and fixture, checks all raw/native targets and inventories, and verifies exact
artifact bytes. It runs under the unchanged 2-GiB/two-core serial guard.

`Stress.lean` preserves twelve valid Lean reflexivity cases, including shifts,
zero shift counts, and operands above `u128`. It is separate from the accepted
three-target corpus. To investigate it, copy it to `Source.lean` in a separate
producer workspace, compile that module, then export the `BitwiseProbe` targets
in source order with the same pinned `Main.lean`. Do not overwrite this
fixture's source or artifacts.

The original full stress export has 734,186 bytes and SHA-256
`fadb30c531b31832c9457abc803a841ad9e167dcfb5047c30eaa010b7491cc16`.
With the forwarding fix, the 1M-work profile still refuses at
`BitwiseProbe.shift_right_small`. The existing explicit 20M-work/1-GiB-phase
profile gets through the small shifts but refuses at `BitwiseProbe.and_large`
with its allocation limit. These are remaining evaluator gaps, not failed
mathematical equalities. No test requires future compilers to keep refusing
them, and no limit was raised to make this fixture pass.
