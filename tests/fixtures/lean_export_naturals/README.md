# Genuine compact natural-literal proofs

[`Source.lean`](Source.lean) is an original constructive fixture for Lean
4.33.1 (`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`). The unmodified pinned
lean4export producer (`15f6055e299ad5b89345e533cc2192f4cc00f659`) exports
[`naturals.ndjson`](naturals.ndjson), containing 33 declarations and seven
theorems. These check reflexivity, successor, predecessor, constructor
discrimination, a successor beyond `u128`, and structural addition and
multiplication. There are no axioms, admissions
or native-decision shortcuts. This small corpus is not the Fermat proof.

Lim checks the standard nominal `Nat` family independently. Decimal values
remain compact, with one zero/successor constructor exposed when induction or
conversion needs it. They never wrap or truncate to machine integers. The
literal representation permits at most 4,096 canonical decimal digits; this
limits input size, not mathematical quantification. Constant-increment
recursors with constant natural-valued motives can batch closed literal counts
under the normal kernel work and allocation limits. The last two theorems use
explicit `Nat.rec` definitions; they exercise the same syntax-based native
optimization as ordinary Lim source. The separate
[standard arithmetic corpus](../lean_export_arithmetic/README.md) covers the
different `Nat.brecOn` implementation through guarded observation fusion.

[`provenance.json`](provenance.json) maps every original declaration to its
native identifier, source module, source hash, export line and prefix hash.
It records input/output hashes, producer pins, the original Prelude notice
and links to the preserved [Lean](../lean_export/LEAN-LICENSE.txt) and
[exporter](../lean_export/EXPORTER-LICENSE.txt) licenses. Actual declaration
ownership comes from Lean's module table. Keep this attribution with copied
exports or translations.

The ordinary native translation is
[`theorems/lean_replay/naturals.lim`](../../../theorems/lean_replay/naturals.lim).
All seven targets pass a fresh native check:

```sh
lim --check-lean-export tests/fixtures/lean_export_naturals/naturals.ndjson \
  NaturalSource.structuralMultiplication --emit-proof /tmp/naturals.lim
lim --check-theorem theorems/lean_replay/naturals.lim lean-14-NaturalSource-reflexive
lim --check-theorem theorems/lean_replay/naturals.lim lean-15-NaturalSource-successor
lim --check-theorem theorems/lean_replay/naturals.lim lean-24-NaturalSource-predecessorComputes
lim --check-theorem theorems/lean_replay/naturals.lim lean-26-NaturalSource-constructorDiscriminates
lim --check-theorem theorems/lean_replay/naturals.lim lean-28-NaturalSource-largerSuccessor
lim --check-theorem theorems/lean_replay/naturals.lim lean-30-NaturalSource-structuralAddition
lim --check-theorem theorems/lean_replay/naturals.lim lean-32-NaturalSource-structuralMultiplication
```

Reproduce the raw export, checked native source and complete provenance with
previously downloaded pinned tools and a built compiler:

```sh
bash scripts/limited-run.sh python3 scripts/regenerate-lean-naturals.py \
  --lean-root /path/to/lean-4.33.1-linux \
  --exporter-dir /path/to/pinned-lean4export --lim target/debug/lim --check
```

Add `--loader /path/to/ld-linux-x86-64.so.2` when an explicit ELF loader is
required. The script downloads nothing. It validates source/tool/license
pins, freshly compiles the producer in an isolated `LEAN_PATH`, queries real
declaration origins, replays and translates the export, and checks all seven
native theorem targets. Omit `--check` to publish changed artifacts only after
all checks pass. Cargo consumes and verifies the committed artifacts without
a Lean installation.
