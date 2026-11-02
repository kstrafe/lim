# Genuine string-literal proofs

`Source.lean` contains five original `rfl` proofs using the pinned Lean 4.33.1
and lean4export versions. They cover empty text, ASCII, `é🦀`, embedded NUL,
and a 65-character literal that exercises balanced native expansion. The
378-declaration export and its ordinary native translation both check with
empty declared/target axiom and primitive-foundation inventories.

```sh
lim --check-lean-export tests/fixtures/lean_export_strings/strings.ndjson \
  StringLiteralProbe.balanced --proof-work 1000000 \
  --proof-phase-bytes 134217728 --proof-total-bytes 1073741824
lim --check-theorem theorems/lean_replay/strings.lim \
  lean-377-StringLiteralProbe-balanced --proof-work 1000000 \
  --proof-phase-bytes 134217728 --proof-total-bytes 1073741824
```

The unchanged default work budget refuses an earlier standard-library proof,
`Char.ofNat._proof_2`. The selected profile is recorded in the manifest and
native source; neither the host guard nor defaults are increased automatically.
All literal data becomes ordinary checked calls and lambdas. Unicode is decoded
as scalars, including U+0000, and expanded allocations are bounded. There is no
new native string proof primitive or source-level axiom.

`provenance.json` records input/output hashes, the producer and origin-reader
hashes, all original declaration identities, export lines, prefix hashes,
dependencies and native names. Canonical ownership maps every declaration to
`Init.Prelude` or this original source. Preserve its Prelude notice and the
linked Lean/exporter Apache-2.0 license texts when copying these artifacts.

Reproduce every artifact using already downloaded tools:

```sh
bash scripts/limited-run.sh python3 scripts/regenerate-lean-strings.py \
  --lean-root /path/to/lean-4.33.1-linux --exporter-dir /path/to/lean4export \
  --lim target/debug/lim --check
```

Add `--loader /path/to/ld-linux-x86-64.so.2` when required. The script runs one
Lean worker, checks all five raw and independently translated native targets,
and compares exact bytes without writing in `--check` mode. Cargo uses the
committed artifacts without Lean or network access. Corrupt helper identities,
types, universe arities, proof evidence and literal bounds are tested. An
altered ASCII equality currently exhausts conversion work; it is recorded as
bounded refusal rather than a completed inequality decision.

These fixtures cover a pinned literal-import prerequisite. They are not the
full Lean environment or the unbounded Fermat proof.
