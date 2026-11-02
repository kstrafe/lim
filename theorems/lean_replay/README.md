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
It checks seven theorems across 33 declarations, including successor,
predecessor and constructor discrimination beyond machine-integer widths,
plus explicit structural addition and multiplication.
Its own manifest and regeneration script preserve source/module/license
provenance and exact artifact bytes. Imported literals use the inspectable
`#pt-nat-literal` form even for small values; this avoids unary-spine depth
limits while keeping the same checked zero/successor semantics.

The twelfth file, [`foundations.lim`](foundations.lim), translates the separate
[fixed-foundation corpus](../../tests/fixtures/lean_export_foundations/README.md).
Its 34 declarations include checked opaque adapters for the three pinned
logical axioms. The three user theorem targets each use one assumption; all
declared axioms and each target's actual inventory are recorded separately.
Its fixture guide and manifest preserve exact source/module/license provenance
and document opt-in replay and independent ordinary native theorem checks.

The thirteenth file, [`arithmetic.lim`](arithmetic.lim), translates the
[standard arithmetic corpus](../../tests/fixtures/lean_export_arithmetic/README.md).
It keeps the actual pinned `Nat.add`/`Nat.mul`/`Nat.pow`/`Nat.sub`/`Nat.ble`/`Nat.beq` definitions and their
`Nat.brecOn` helpers. Guarded observation fusion exposes their recurrences
without trusting their names or replacing their bodies. Its thirty targets
across 78 declarations check large sums, products, powers, truncated subtraction,
Boolean relations/equality, zeros, equal operands, generic identities, nested
operations and a nonzero-offset affine recurrence;
all have empty logical-assumption inventories and retained source/module/
license provenance. Its fixture guide gives the fresh reproduction command.

The fourteenth file, [`discrimination.lim`](discrimination.lim), translates
the [generic discrimination corpus](../../tests/fixtures/lean_export_discrimination/README.md).
Its five targets include constructor discrimination, successor injectivity,
and the standard equality-to-Boolean bridge with arbitrary naturals and
functions into naturals. The actual private Prelude helper bodies remain
present and checked. All targets have empty axiom and foundation inventories;
the fixture manifest records original identities and source/module/license
provenance, including numeric private-name components.

The fifteenth file, [`subtraction-bridge.lim`](subtraction-bridge.lim), translates
the [generic subtraction bridge](../../tests/fixtures/lean_export_subtraction_bridge/README.md).
Its 60 declarations retain the actual standard induction/congruence proof and
check three unbounded cancellation theorems: one successor on both operands,
two successors, and arbitrary values mapped to naturals. All three targets
have empty assumption inventories and independently checked source/native
correspondence. Its fixture guide documents pinned fresh reproduction.

The sixteenth file, [`division.lim`](division.lim), translates the
[division corpus](../../tests/fixtures/lean_export_division/README.md).
Eight closed targets cover zero divisors, below/equal operands, exact/inexact
division and a quotient beyond machine integers. Original and native checks
retain the standard fuelled body and have empty assumption inventories.
Its fixture guide documents provenance, reproduction and operand restrictions.

The seventeenth file, [`division-composition.lim`](division-composition.lim),
translates the [computed-division corpus](../../tests/fixtures/lean_export_division_composition/README.md).
Fifteen targets combine computed dividends/divisors, equal powers, below/zero-
divisor cases and literal division. The 211-declaration corpus retains the full
standard closure and exact native mapping with empty assumption inventories;
sharing immutable leaves keeps it inside the original replay allocation cap.

The eighteenth file, [`remainder.lim`](remainder.lim), translates the
[remainder corpus](../../tests/fixtures/lean_export_remainder/README.md).
Its 256 declarations check fifteen targets: literal/computed remainders,
unbounded zero controls, and the general positive-divisor remainder bound,
with exact original/native mapping and empty assumptions.
The case-analysis helper's `Init.Data.Nat.Basic` source is independently pinned.
The genuine `Nat.mod_lt` and `Nat.modCoreGo_lt` dependency proofs are checked.

Each corpus records its pinned producer, exact input SHA-256, native theorem
names, and every original declaration's identity, export line and prefix hash.
[`manifest.json`](manifest.json) maps the original nine exports' declarations
and records input/output hashes. The additional corpora have the separate
provenance manifests linked in their fixture guides. The original manifest's
linked upstream
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
