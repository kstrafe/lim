# Native translations of checked Lean proofs

Nine ordinary Lim files translate the small, genuine exports in
[`tests/fixtures/lean_export`](../../tests/fixtures/lean_export/README.md).
They include constructive identity, recursive arithmetic, record projection,
mutual recursion, and nonempty, polymorphic, indexed and dependent nested
containers. They are not the complete Fermat's Last Theorem proof.

The tenth file, [`quotient.lim`](quotient.lim), comes from the separate
[quotient computation fixture](../../tests/fixtures/lean_export_quotient/README.md).
It includes checked quotient construction, lifts and propositional induction,
plus a checked adapter from nominal equality to primitive equality. Its
[provenance manifest](../../tests/fixtures/lean_export_quotient/provenance.json)
records all 24 declarations and three theorem targets, and inventories the
primitive computation foundation separately from its empty axiom inventory.
The fixture guide documents its own pinned-producer regeneration command.

The eleventh file, [`naturals.lim`](naturals.lim), comes from the separate
[compact natural-literal fixture](../../tests/fixtures/lean_export_naturals/README.md).
It checks five large-value theorems across 29 declarations, including successor,
predecessor and constructor discrimination beyond machine-integer widths.
Its own manifest and regeneration script preserve source/module/license
provenance and exact artifact bytes. Imported literals use the inspectable
`#pt-nat-literal` form even for small values; this avoids unary-spine depth
limits while keeping the same checked zero/successor semantics.

Each file records its pinned producer, exact input SHA-256, native theorem
name, and every original declaration's identity, export line and prefix hash.
[`manifest.json`](manifest.json) maps every original declaration to its native
name and records input/output hashes. Its linked upstream
[provenance manifest](../../tests/fixtures/lean_export/real-provenance.json)
contains original module/source ownership, source hashes, notices, and links
to the preserved Lean and exporter licenses. Keep that provenance with copied
translations; the NDJSON stream alone does not carry source licenses.

Names combine a deterministic declaration ordinal and a readable original name.
They are exact identifiers in these files; their recorded mapping distinguishes
names even if sanitization produces the same suffix. Ordinary aliases can
reference the theorem from another Lim source file.

Check the smallest translation without Lean, an exporter, or a native linker:

```sh
lim --check-theorem theorems/lean_replay/identity.lim lean-1-ReplaySource-identityProof
```

All constructors, definitions and recursor wrappers are standard Lim forms.
The parsed declarations are also mapped back to the original identities for
type, body, inductive-signature and opacity correspondence checks. Theorem and
opaque initializers remain explicitly present and checked, while
their values stay hidden from conversion. No replay directive, receipt, source
comment or cached result can bypass the native proof checker. Nested wrappers
use `#pt-nested-induct` with physical type selectors and case ordinals.

Reproduce the original nine files and their mapping manifest using a previously built compiler:

```sh
bash scripts/limited-run.sh python3 scripts/regenerate-lean-source.py --lim target/debug/lim --check
```

Omit `--check` to regenerate stale artifacts. The script checks input hashes,
replays each export, translates and rechecks its complete native source, then
invokes ordinary `--check-theorem` on the resulting file. It verifies every
artifact before publishing changed files. It uses Python's standard library
and Lim; regeneration needs no Lean installation or external libraries.
