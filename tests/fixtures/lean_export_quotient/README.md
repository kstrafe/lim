# Pinned quotient computation fixture

[`Source.lean`](Source.lean) is an original constructive fixture, compiled with
Lean 4.33.1 at `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` and exported using
unmodified lean4export `15f6055e299ad5b89345e533cc2192f4cc00f659`.
It uses `Quot`, `Quot.mk`, `Quot.lift` and `Quot.ind`, without `Quot.sound`,
`Classical.choice`, `propext`, admissions or native-decision shortcuts.
This is not an export of the Fermat proof.

[`quotient.ndjson`](quotient.ndjson) contains 24 checked declarations and three
theorems: representative computation, a function-valued lift with an additional
argument, and propositional quotient induction. The reader validates the four
pinned primitive signatures against fixed schemas and independently checks
wrappers around native quotient computation primitives. The lift wrapper
derives the bridge from the imported nominal `Eq` to primitive equality by
ordinary checked equality induction. No exported reduction rule is installed.

[`provenance.json`](provenance.json) records the source and tool hashes,
actual defining modules from Lean's environment, original identities and
export-prefix hashes, native identifiers, and artifact sizes and hashes.
Every upstream declaration in this fixture belongs to `Init.Prelude`; its
source hash, copyright notice and pinned upstream URL are retained. The
[Lean license](../lean_export/LEAN-LICENSE.txt) and
[exporter license](../lean_export/EXPORTER-LICENSE.txt) are preserved verbatim.
Keep this attribution with copied fixture or translation files.

The translation is ordinary checked Lim source in
[`theorems/lean_replay/quotient.lim`](../../../theorems/lean_replay/quotient.lim).
The receipt and its header explicitly inventory `quotient-computation-v1` as
a primitive foundation; the axiom inventory remains empty. These computation
primitives do not equate related representatives or expose representatives of
arbitrary quotients. All axiom export records still fail.

```sh
lim --check-lean-export tests/fixtures/lean_export_quotient/quotient.ndjson \
  QuotientSource.inductionReflexive --emit-proof /tmp/quotient.lim
lim --check-theorem theorems/lean_replay/quotient.lim lean-19-QuotientSource-liftComputes
lim --check-theorem theorems/lean_replay/quotient.lim lean-22-QuotientSource-extraArgumentComputes
lim --check-theorem theorems/lean_replay/quotient.lim lean-23-QuotientSource-inductionReflexive
```

Reproduce the producer output, checked translation and provenance together
using previously downloaded pinned tools and a built compiler:

```sh
bash scripts/limited-run.sh python3 scripts/regenerate-lean-quotient.py \
  --lean-root /path/to/lean-4.33.1-linux \
  --exporter-dir /path/to/pinned-lean4export --lim target/debug/lim --check
```

Use `--loader /path/to/ld-linux-x86-64.so.2` when the release executable needs
an explicit ELF loader. The script downloads nothing, checks the producer,
source and license pins, compiles fresh exporter modules in an isolated
`LEAN_PATH`, queries declaration origins, replays and translates the export,
and checks all three native theorem targets. Omitting `--check` publishes only
changed files, after all checks pass. Integrity and adversarial tests also run
with Cargo; Lean is not needed to consume or check the committed artifacts.
