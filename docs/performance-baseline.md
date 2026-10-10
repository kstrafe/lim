# Compiler performance baselines

Run the dependency-free benchmark harness from the Nix development shell:

```sh
nix develop --command cargo bench --bench compiler -- --iterations 20
```

Use the same machine, Nix shell, release profile, and iteration count when
comparing changes. The harness reports lexing, parsing, import/cfg/frontend
processing, semantic checks, checked native assembly emission, cold and warm
generator caches, and internal native linking/publication separately.
It also runs the allocator-backed vector and large aggregate projection
examples, checks their exit values, and reports assembly/binary sizes. Timings
are informational; ordinary correctness tests deliberately have no timing
thresholds. On Linux, the harness prints its process high-water RSS from
`/proc/self/status` when available. The printed peak covers the whole harness,
not a per-phase memory profile.

## Shared typed ownership facts (2026-09-30)

### Classify scoped borrow syntax once (2026-10-01)

Scoped-loan conflict checking now classifies temporary reference expressions
once when constructing its scope table. Previously every access with a live
scope cloned the node's owned syntax and repeated this classification. The
classification and diagnostic traversal order are unchanged.

Sequential warm release measurements, baseline first, include native linking:

| Warm median (ms) | Before | After | Samples |
| --- | ---: | ---: | ---: |
| `async_fn.lim` | 41.37 | 41.27 | 100 |
| 64 functions with 24 reference aliases each | 39.28 | 40.11 | 60 |

Executable bytes were identical. These mixed results do not establish a
wall-clock speedup (0.2% lower async median; 2.1% higher reference median).
The deterministic improvement is removal of repeated syntax cloning and
classification. Both compilers included identical unrelated, uncommitted
local-reference-store changes. All 62 typed-borrow tests and the full enabled
integration suite passed; 743 library tests passed with the known pending
exclusive-holder restoration regression explicitly excluded. Four existing
integration tests remain ignored. That failing regression is not changed or
committed by this optimization.

### Empty scoped-borrow fast path

The scoped-borrow solver now returns empty event facts immediately when no
scoped loans exist, avoiding predecessor construction and fixed-point scans.
The empty-fact regression and all 60 typed-borrow tests pass. All 694 other
library tests pass; the existing uncommitted borrowed-field regression fails
independently. The async, local-waker, native-example, and UI suites pass.

Sixty sequential warm samples per version, with baseline measured first:

| Warm median (ms) | Before | After |
| --- | ---: | ---: |
| `async_fn.lim` | 34.16 | 33.16 |
| `vec_allocator.lim` | 23.63 | 23.81 |

Executables are byte-identical. The observed async reduction is 2.9%, while
the vector measurement regresses 0.8%; these mixed sequential measurements
do not establish a reliable speedup. Both binaries contain the same unrelated
in-progress borrowed-field changes, which are not part of this optimization.

### Allocation-free liveness updates

Backward liveness now computes each bitset word directly into its retained
before/after snapshots, removing two temporary vector allocations per
worklist visit. Successor words are read before updating the current word,
preserving self-loop and back-edge fixed-point behavior. A new regression
checks 130 simultaneously live bindings across three bitset words.

Warm end-to-end CLI measurements used two warmups and 60 samples per
compiler, baseline first, with separate generator-cache warmups:

| Warm median (ms) | Before | After | Reduction |
| --- | ---: | ---: | ---: |
| `async_fn.lim` | 33.51 | 32.23 | 3.8% |
| `vec_allocator.lim` | 23.85 | 23.80 | 0.2% |

Executable bytes were identical for both workloads. These sequential
measurements suggest a small async improvement, not a statistically
established speedup; the vector result is effectively unchanged. The
allocation removal is deterministic regardless of timing noise.

### Move completed dataflow snapshots instead of cloning them

Loan-origin and consumption solvers now publish each completed outgoing
state by moving it, after propagating it to successors. This removes one
deep clone per processed event without changing the stored snapshots or
fixed-point propagation. The complete test suite and formatting checks pass.

Warm end-to-end measurements used the release compiler, two warmups and
100 samples per version, with no concurrent test run:

| Warm median (ms) | Before | After | Binary bytes |
| --- | ---: | ---: | ---: |
| `async_fn.lim` | 32.75 | 32.25 | 11,280 |
| `vec_allocator.lim` | 22.95 | 22.66 | 12,488 |
| `large_reference_projections.lim` | 9.84 | 11.08 | 8,280 |

Every executable was byte-identical. The small async/vector reductions
(1.5%/1.2%) are observations, not established speedups: the small projection
workload was particularly noisy (3.03–15.73 ms before, 2.65–17.46 ms after).
An earlier 60-sample run overlapping tests measured projection medians of
3.40/3.37 ms. The allocation removal is deterministic; the end-to-end timing
benefit needs a quieter, alternating-order benchmark to establish.

### Shared consumption solution

Linear consumption checks and exit diagnostics now share one move-flow
solution per function. Functions with no linear bindings or expressions skip
these linear checks; their type and borrow checks remain unchanged. Tests
compare the shared path's complete diagnostics against independent checks
for valid code, repeated destruction, and missing exit consumption.

Sixty warm samples per compiler alternated order, with two untimed builds
after every compiler switch to warm its generator cache. Compilation includes
internal native linking. The full test suite passed.

| Warm median (ms) | Before | After | Binary bytes |
| --- | ---: | ---: | ---: |
| `async_fn.lim` | 30.31 | 29.97 | 11,280 |
| `vec_allocator.lim` | 21.23 | 22.01 | 12,488 |
| `large_reference_projections.lim` | 3.73 | 3.67 | 8,280 |

All compared executables were byte-identical. These results do not establish
a reliable end-to-end speedup: changes are small, mixed in direction, and
sequential runs varied considerably. A synthetic 128-branch Copy-only
function also showed no reliable improvement (18.86 -> 19.68 ms, forty
sequential samples). This is a reduction in duplicate work, not a demonstrated
wall-clock performance win.

## Shared global scopes and signature-only generator scanning (2026-09-30)

An optimized sampling profile of `examples/async_fn.lim` identified allocation,
freeing, and repeated `HashSet<String>` construction as significant costs.
The lexical scope pass now keeps only local names in its mutable set and
checks the immutable globals separately. Borrow-checker function and branch
contexts share an `Arc<HashSet<String>>` of globals rather than duplicating
them into both returnable-origin and in-scope sets. Local escape and shadowing
rules are unchanged.

Generator capability discovery now normalizes and parses function signatures
only, rather than copying and parsing every ordinary function body. Full body
syntax, types, ownership, and unsafe checks still run in the normal frontend;
external declarations still reject bodies.

Release CLI measurements used 40 warm samples per variant, alternating order
each iteration, on the same machine. Each command compiled its example to a
temporary executable using the internal encoder/linker. All three variants
produced byte-identical binaries and matching exit statuses/stdout/stderr.

| Warm median (ms) | Before | Shared globals | Plus signature-only scan |
| --- | ---: | ---: | ---: |
| `async_fn.lim` | 44.21 | 32.20 | 31.59 |
| `vec_allocator.lim` | 20.04 | 19.61 | 20.65 |
| `large_reference_projections.lim` | 3.55 | 3.36 | 3.69 |

The import-heavy async example improves 28.6% overall; signature scanning
adds a modest 1.9% improvement over shared globals in this sample. The other
workloads show no reliable improvement (and small regressions in this run).
These measurements are informative, not test thresholds or a general speedup
claim. Dedicated regressions cover global references through branches, global
shadowing, local escapes with 512 globals, and deferred function-body checking.

## Borrowed global type maps (2026-09-30)

The type checker now borrows the immutable global type map and keeps a
separate owned map for function locals. Branch, loop, match, and pattern
contexts clone only that local map. Global initializer expressions use the
same lookup view; new pattern bindings are extracted from locals only.
Lookup precedence, visible-name counts, shadowing rejection, and diagnostic
locations remain unchanged.

Forty alternating warm release CLI samples, collected after the full test
suite finished, gave the following medians. Before means the signature-scan
and shared-global-name optimizations were already present.

| Warm median (ms) | Before | Borrowed global types |
| --- | ---: | ---: |
| `async_fn.lim` | 32.10 | 28.37 |
| `vec_allocator.lim` | 19.61 | 19.85 |
| `large_reference_projections.lim` | 4.20 | 4.16 |

The async example improves 11.6%; the other examples show no meaningful
change. Native binaries are byte-identical and runtime outputs/exit values
match. All unit and integration tests pass, with the existing opt-in tests
remaining ignored. Dedicated tests verify shared global storage, independent
branch locals, global initializers, match payloads, and type mismatch rejection.

## Demand-driven async metadata (2026-09-30)

After imports, generators, cfg, and syntax bundles expand, the frontend now
builds async copy/type metadata only if an async invocation remains. Async
metadata scanning also skips forms other than function, enum, alias, and
struct declarations before cloning or normalization. Ordinary declaration
and body validation still runs in the normal frontend.

An isolated run used 80 warm samples per compiler, alternating order, with
byte-identical binaries for all workloads:

| Warm median (ms) | Before | Demand-driven metadata |
| --- | ---: | ---: |
| `vec_allocator.lim` | 20.34 | 19.55 |
| `async_fn.lim` | 27.87 | 28.18 |
| `large_reference_projections.lim` | 10.02 | 9.13 |

The vector example improved 3.9% in this run, consistent with a preceding
40-sample alternating run's 5.1% reduction. No async speedup was measurable.
The small projection timings varied substantially between runs, so the
apparent improvement above is not a reliable speedup claim. This removes
unnecessary frontend work, not a demonstrated improvement on every workload.
The comparison preserves the same unfinished async-loop working-tree changes
in both binaries; those changes are not part of this optimization.

## Borrowed async body normalization (2026-09-30)

Function-level continuation lowering now borrows unchanged bodies. Bodies
that actually require rewriting keep a single owned buffer rather than
deep-copying the rewritten tree again. The complete test suite passes.

Sixty warm samples per compiler produced byte-identical binaries:

| Warm median (ms) | Before | Borrowed bodies |
| --- | ---: | ---: |
| `async_fn.lim` | 28.63 | 29.25 |
| `async_conditional_return.lim` | 15.11 | 12.37 |

These sequential samples had substantial outliers (up to 121 ms), and the
conditional example varied from 7 to 67 ms. They do not establish a reliable
speedup. This change eliminates allocations; it does not claim a measurable
whole-build improvement.

## Move original source trees into diagnostics (2026-09-30)

The frontend now transfers ownership of each original top-level source form
into diagnostic retention instead of deep-copying it. Normalization still
uses its separate tree. Exact diagnostic spans and the full suite pass.

Eight blocks of ten warm builds per compiler, with block order alternating
and two untimed warmups after every compiler switch, gave these results:

| Warm median (ms), 80 samples | Before | Ownership transfer |
| --- | ---: | ---: |
| `async_fn.lim` | 30.21 | 29.10 |
| `vec_allocator.lim` | 21.34 | 21.22 |
| `large_reference_projections.lim` | 7.07 | 8.78 |

An 80-sample sequential async repeat measured 28.91 -> 28.58 ms, a 1.1%
reduction versus 3.7% in the alternating run. The vector workload showed
no meaningful change. A 100-sample projection repeat reversed the apparent
regression (10.64 -> 9.73 ms); this small workload is too unstable for a
speedup or regression claim. Sequential repeats had outliers exceeding two
seconds, so these are modest observational improvements, not timing gates.
All compared executable bytes were identical.

## Historical external-tool production sample (2026-09-25)

Five iterations, Nix release profile, Intel i7-13700KF, Linux 7.2.6 x86-64,
rustc 1.99.0-nightly (89c61a754 2026-07-23), GNU binutils 2.46. The target is
x86_64-sysv. Small/large sources remain 174/9,798 bytes. Peak RSS: 11,684 KiB.

| Phase (mean ms) | Small | Large |
| --- | ---: | ---: |
| Lex | 0.004 | 0.131 |
| Parse (includes lexing) | 0.009 | 0.410 |
| Imports/cfg/frontend | 0.127 | 2.025 |
| Semantic checks | 0.013 | 9.479 |
| Checked native emission | 0.043 | 8.837 |
| Compile end-to-end, without link | 0.186 | 20.592 |
| Production assembly/link/publication | 813.664 | 255.850 |
| Generator cold cache | 0.221 | 5.665 |
| Generator warm cache | 0.148 | 1.421 |

Small/large assembly sizes: 1,743/74,715 B; binary sizes: 13,616/26,936 B.
The checked-program API excludes semantic checking from emission; compile
end-to-end includes lexing, parsing, imports, expansion, validation, and
emission. These historical link timings include `as`, dynamic-linker
discovery, `ld`, and atomic publication; current builds use Lim's internal
encoder and ELF linker. Build timings below also include cache preparation,
inspectable generated source writing, compilation, linking, and one checked
execution. Cold means the generator cache is removed before each build;
it does not flush the OS filesystem cache.

| Workload | Cold build ms | Warm build ms | Assembly B | Binary B | Exit |
| --- | ---: | ---: | ---: | ---: | ---: |
| Reference aggregates | 835.688 | 262.851 | 9,254 | 13,600 | 42 |
| Allocator vector | 823.312 | 811.085 | 50,735 | 19,088 | 4 |
| 64-function branch/call chain | 256.708 | 852.506 | 28,400 | 15,728 | 42 |
| 256 generated aliases | 567.147 | 249.909 | 318 | 13,432 | 42 |

These are noisy wall-clock samples, not speedup claims: the reversed cold/
warm ordering in the call-chain workload demonstrates process scheduling
and wrapper overhead. The old emission number included a second semantic
pass, and the old linker used Clang, so neither is directly comparable.
The old generator benchmark only wrote generated text; compiling that text
exposed an extra list layer, now corrected. A removed semantic pass is
verified by a test counter; its cost on this large workload is represented
by the separate 9.479 ms semantic measurement, not an assumed timing gain.

## Historical Clang sample

Recorded with five iterations on 2026-09-24 in the repository's Nix shell:

- CPU: Intel Core i7-13700KF (13th Gen)
- OS/kernel: x86-64 Linux, kernel 7.2.6
- Rust: rustc 1.99.0-nightly (89c61a754 2026-07-23)
- Linker driver: clang 21.1.8
- Lim target: x86_64-sysv
- Small synthetic source: 174 bytes, 4 leaf functions
- Large synthetic source: 9,798 bytes, 256 leaf functions
- Peak harness RSS: 7,908 KiB

Times below are mean wall time per iteration, rounded to milliseconds where
that precision is useful. Import/cfg frontend processing includes import
loading, cfg expansion, generator expansion, and source normalization. The
generator cache measurements emit 4 aliases (small) or 256 aliases (large).

| Phase | Small | Large |
| --- | ---: | ---: |
| Lex | 0.012 ms | 0.205 ms |
| Parse | 0.030 ms | 0.397 ms |
| Imports/cfg/frontend | 0.512 ms | 1.658 ms |
| Semantic checks | 0.032 ms | 8.850 ms |
| Native assembly emission | 0.133 ms | 17.225 ms |
| Clang linking | 314.869 ms | 989.927 ms |
| Generator cold cache | 0.746 ms | 7.394 ms |
| Generator warm cache | 0.723 ms | 1.553 ms |

| Workload/artifact | Result |
| --- | ---: |
| Small assembly / linked binary | 1,743 B / 15,832 B |
| Large assembly / linked binary | 74,715 B / 29,144 B |
| Large reference projection runtime | exit 42; 0.922 ms |
| Allocator-backed vector runtime | exit 4; 0.525 ms |
| Projection workload assembly / binary | 9,254 B / 15,728 B |
| Vector workload assembly / binary | 50,735 B / 20,960 B |

This is a first baseline, not a statistically stable performance claim. Five
samples are especially weak for sub-millisecond phases. Link timings include
the Nix clang wrapper and system linker startup, which dominates these tiny
inputs. Use longer runs and repeated machine-local measurements for decisions.
## Reproducible artifacts

`tests/reproducible.rs` builds the same imported, generated project in two
independent source roots using fresh CLI processes, both cold and warm. It
compares all cache metadata and inspectable source bytes, assembly, and linked
executables without path filtering. Native results are checked too. Global
emission is sorted by symbol so randomized map order does not affect layout.
This guarantee assumes identical compiler, Nix toolchain, target, and cfg;
it does not promise identical bytes across different linker versions.
Diagnostic paths remain real source paths and are not rewritten for builds.
## Numeric differential regression coverage

`tests/numeric_differential.rs` uses a fixed seed and Rust scalar operations
as an independent oracle for all twelve integer types, including i128/u128.
Bounded native batches compare both global evaluation and emitted operations
against wrap/saturate, bitwise, division/remainder, and shift expectations.
Additional cases exercise casts, invalid shifts, division traps, and float
unordered comparisons. Failures print the seed and a standalone source batch.
These are correctness checks, not timing gates. `saturation_bounds.lim` keeps
minimal regressions for large-bound x86 comparisons and signed 64-bit
multiplication overflow direction.
`wide_shift_count_trap.lim` verifies that a dynamic 128-bit shift count with
nonzero high bits is rejected instead of being truncated to its low word.
`nested_wrapping_constant.lim` checks width normalization between constant
operations, including wrapping negation and bitwise inversion.

## Loan dependency visitation (2026-10-01)

Loan-origin snapshot dependency discovery now reuses a dense visitation table
and two traversal buffers instead of allocating a hash set and stack for each
consumer. A unique event stamp prevents revisiting shared expression nodes;
the transfer rules and snapshot wakeup dependencies are unchanged.

Warm native CLI compilation, 80 samples per compiler, measured median times:

| Example | Before | After |
| --- | ---: | ---: |
| async_fn | 36.16 ms | 35.15 ms |
| vec_allocator | 24.56 ms | 24.82 ms |
| large_reference_projections | 3.80 ms | 4.06 ms |

These sequential measurements used `scripts/benchmark-compile.py` after the
test suite finished. An earlier 60-sample run overlapping integration tests
showed different changes (+0.5%, +2.2%, +7.3% reductions respectively).
The disagreement and large outliers do not establish a reliable end-to-end
speedup. This is an allocation/hash-work reduction, not a demonstrated overall
latency improvement. All three executable comparisons were byte-identical;
709 library tests and all enabled integration tests passed (four existing
ignored tests). Each compiler was warmed separately to populate its cache.

## Shared borrow-check provenance (2026-10-01)

Scope escapes, returned references, live-loan conflicts, and call arguments
now share a lazy, validation-local loan-origin result for each immutable
function body and flow graph. Previously these checks independently solved
the same dataflow problem up to four times. Their ordering, transfer rules,
spans, and diagnostics are unchanged. Results are retained until validation
ends, trading a longer lifetime for fewer analyses; this is not an incremental
cache or a replacement for return-summary analysis.

Reproduce the targeted workload with:

```sh
python3 scripts/benchmark-compile.py --reference-heavy \
  --baseline /path/to/previous/lim --repetitions 100
```

The workload contains 64 functions, each with 24 immutable reference aliases
and a reference-returning helper call. All functions are validated, even
though only one worker is reachable for emission. Sequential warm CLI
measurements on this machine, after the test suite finished:

| Workload | Before median | After median | Change |
| --- | ---: | ---: | ---: |
| Reference-heavy | 44.15 ms | 39.47 ms | 10.6% faster |
| async_fn | 39.02 ms | 38.16 ms | 2.2% faster |
| vec_allocator | 28.66 ms | 27.43 ms | 4.3% faster |
| large_reference_projections | 3.66 ms | 4.91 ms | 34.3% slower |

Each row used 100 measurements per compiler and compared identical executable
bytes. A previous reference-heavy run measured 43.21 versus 40.03 ms (7.4%
faster), although it overlapped another benchmark and is not the primary
measurement. Earlier small-example runs varied substantially, including
37.95 versus 37.98 ms for async and 7.44 versus 3.69 ms for projections.
The small-workload results do not establish a reliable latency improvement;
outliers and background scheduling matter at this scale. No memory reduction
is claimed. The targeted result supports reducing repeated provenance work,
not a claim that every compilation is faster.

Verification: 726 library tests and all enabled integration/native/UI tests
passed, with four existing ignored tests. Formatting, cargo check, and diff
whitespace checks passed. Regression tests cover shared-result reuse and
preserve lazy skipping when live-loan and call checks need no provenance.

## Successor-first liveness scheduling (2026-10-01)

Backward liveness now starts in deterministic DFS postorder rather than hash
set iteration order. Dense visitation and an iterative DFS avoid event-ID
hashing and recursive stack growth. The transfer rules are unchanged. A
test-only work counter verifies exactly one visit per reachable event in an
acyclic 130-binding fixture; forward and randomized schedules need more visits
and produce identical facts. Differential checks also cover loops, branches,
unreachable code, and multi-word bitsets.

Sequential warm CLI measurements, 100 samples per compiler, after tests:

| Workload | Before median | After median | Change |
| --- | ---: | ---: | ---: |
| Reference-heavy | 38.91 ms | 39.30 ms | 1.0% slower |
| async_fn | 43.70 ms | 43.36 ms | 0.8% faster |
| vec_allocator | 32.64 ms | 31.76 ms | 2.7% faster |

Executable bytes were identical in every comparison. An earlier reference
run overlapping a targeted test measured 39.64 versus 38.14 ms. Variability
and a 2-second outlier mean these runs do not establish a reliable overall
latency improvement. The demonstrated win is reduced solver work on acyclic
graphs, not a universal compilation speedup. All 763 library tests and enabled
integration/native/UI tests passed; four existing tests remain ignored.

## Contiguous liveness transfer masks (2026-10-01)

The immutable use/definition masks now occupy two contiguous buffers rather
than two vectors of event rows. For N events and a nonzero binding bitset,
this removes 2N row allocations and 2N vector headers; the bit payload is
unchanged. Zero-binding functions allocate no mask buffers. Queried before
and after snapshots retain their existing representation. Regression checks
cover empty binding sets, multi-word bitsets, branches, loops, and unreachable
events; all 763 library tests and enabled integration/native/UI tests passed.

Sequential warm CLI comparisons against the postorder-only compiler, 100
samples per compiler, after tests:

| Workload | Before median | After median | Change |
| --- | ---: | ---: | ---: |
| Reference-heavy | 39.61 ms | 38.71 ms | 2.3% faster |
| async_fn | 43.31 ms | 43.86 ms | 1.3% slower |
| vec_allocator | 32.19 ms | 32.16 ms | 0.1% faster |

Executable bytes were identical throughout. These small, mixed timing changes
do not demonstrate a general latency improvement. The guaranteed reduction
is temporary allocations and vector-header storage, not peak process RSS.

## Indexed loan snapshot queries (2026-10-01)

Published loan facts now retain the dense expression-to-event index already
built for snapshot dependencies. `value_before` selects candidate evaluation
events from this index instead of scanning every flow event for each result
alternative, including alternatives in loop breaks. The original action and
reachability filters and ascending event order remain unchanged. A differential
regression compares indexed membership/order with exhaustive scans for every
expression in the branch and loop fixtures. Internal recursive solver queries
still scan events; this change does not eliminate those scans.

No additional index construction is introduced, but the previously temporary
index remains allocated for the lifetime of published loan facts. This trades
retained memory for fewer event comparisons, not an allocation-count reduction.
All 777 library tests and enabled integration/native/UI tests pass; four
existing integration tests remain ignored.

Warm end-to-end release compilation, including native linking, with 80 samples
per compiler after tests and three warmups. The first three workloads alternate
before/after order each iteration; reference-heavy uses the existing sequential
benchmark script with two warmups:

| Workload | Before median | After median | Change |
| --- | ---: | ---: | ---: |
| async_fn | 45.21 ms | 45.37 ms | 0.3% slower |
| vec_allocator | 33.40 ms | 33.21 ms | 0.5% faster |
| callee_variant_branch_clear | 3.32 ms | 3.28 ms | 1.3% faster |
| Reference-heavy | 38.03 ms | 38.62 ms | 1.5% slower |

Executable bytes are identical for all workloads. These small, mixed results
do not establish a general wall-clock speedup. The deterministic improvement
is candidate lookup proportional to matching events rather than the entire
control-flow graph for each published snapshot query.

## Scoped-loan work queue and retained scratch sets (2026-10-01)

Scoped-loan propagation now queues only successors whose predecessor outgoing
facts changed, rather than repeatedly sweeping the entire graph. Every node
is seeded initially, preserving the previous treatment of disconnected nodes.
Two reusable scratch sets exchange allocations with changed snapshots instead
of constructing and cloning fresh hash sets on every visit. A differential
test compares every incoming set against the old solver on cyclic joins with
1, 2, 65, and 130 loans, in forward and reversed node order.

The benchmark harness adds `--scoped-heavy`: 64 checked functions containing
24 nested scoped borrows each. Run it with:

```sh
python3 scripts/benchmark-compile.py --scoped-heavy --baseline /path/to/before --repetitions 60
```

Warm end-to-end release compilation, including internal native linking:

| Workload | Before median | After median | Change |
| --- | ---: | ---: | ---: |
| Scoped-heavy | 95.11 ms | 44.00 ms | 53.7% faster |
| async_fn | 46.51 ms | 47.74 ms | 2.7% slower |
| vec_allocator | 35.35 ms | 35.38 ms | 0.1% slower |

Each compiler had two warmups and 60 samples, measured sequentially with
baseline first and no simultaneous build/test work. Executable bytes matched
for all workloads. This establishes a large improvement on the scoped-loan
stress case, not a general compilation speedup. Scratch reuse alone previously
gave mixed results (async 0.8% faster; vector 2.8% slower); changed-successor
scheduling is the key algorithmic improvement.

All 63 borrow-checker tests, 793 library tests, and enabled integration/native/UI
tests pass; four existing integration tests remain ignored. One unrelated
uncommitted async return-variant test is excluded because its fixture uses
unsupported aggregate `#addr-of-mut` syntax. Both measured compilers include
identical pending async-analysis changes; those changes and CHECKLIST.md are
not included in this optimization commit.

## Indexed recursive loan snapshots (2026-10-01)

Recursive branch-result provenance queries now borrow the solver's existing
source-ordered expression-event index rather than scanning the entire graph.
Break events are also indexed by loop result, removing whole-graph scans from
both recursive and published loop-result queries. The index retains one extra
event number per valued break, not a second index. Original action filters,
reachable pre-event snapshots, and result ordering remain unchanged.
A differential regression supplies exhaustive event candidates to the same
recursive transfer and compares complete results on branch, loop, and aggregate
projection examples. All 813 library tests and enabled integrations pass;
four existing integration tests remain ignored.

The benchmark harness adds `--snapshot-heavy`: 64 functions containing 24
branch-result aliases with lexical cleanup each. Warm release CLI samples,
baseline first, two warmups per compiler, and no simultaneous builds/tests:

| Workload | Before median | After median | Samples |
| --- | ---: | ---: | ---: |
| Snapshot-heavy | 320.97 ms | 319.59 ms | 40 |
| async_fn | 48.13 ms | 48.09 ms | 60 |
| vec_allocator | 37.19 ms | 37.24 ms | 60 |

All executable bytes match. The differences (0.4% and 0.1% faster, and 0.1%
slower respectively) do not establish a meaningful wall-clock improvement.
This removes repeated full-graph searches; other work dominates these samples.

## Borrow incoming provenance when loading references (2026-10-01)

Local reference-slot loading now borrows incoming origins instead of taking
ownership. Dereference transfer no longer deep-clones the entire incoming
vector before checking local storage and then parameter storage. Selected
output loans still own their projections, preserving deduplication, shared
access restrictions, and pin metadata. A regression checks 128 repeated inputs
and verifies that mutating an output cannot modify inputs or stored contents.
All 813 library tests and enabled integrations pass, with four preexisting
integration tests ignored.

Warm release CLI measurements include native linking and use 60 samples per
compiler, two warmups, and no concurrent build/test work. Before includes the
indexed recursive snapshot optimization above:

| Workload and measurement order | Before median | After median |
| --- | ---: | ---: |
| async_fn, before first | 49.09 ms | 48.55 ms |
| async_fn, after first | 48.17 ms | 48.99 ms |
| vec_allocator, before first | 37.12 ms | 36.20 ms |
| vec_allocator, after first | 37.54 ms | 36.98 ms |

Executable bytes match in every comparison. Async improves 1.1% in the first
run but regresses 1.7% in the reverse-order repeat. Vector improves 2.5% and
1.5% respectively. Outliers reach multiple seconds; these small differences
do not establish a general speedup. Eliminating the redundant incoming vector
and its nested projection clones is deterministic.

## Move loan vectors and borrow transfer comparisons (2026-10-01)

Matched reference fields now move their loan vectors into flattening rather
than deep-cloning vectors that are immediately replaced. Mutable-loan transfer
compares borrowed strings rather than allocating two strings for each candidate
comparison. Loan ordering, deduplication, and exclusive transfer rules remain
unchanged.

All 813 library tests and 13 targeted nested-reference, reference-release, and
reference-write integration tests pass. Warm release CLI comparisons use 40
samples and verify identical executable bytes. Both compilers include the same
uncommitted async changes, which are excluded from this optimization commit.

| Workload | Before median | After median |
| --- | ---: | ---: |
| async_fn | 49.31 ms | 49.15 ms |
| vec_allocator | 37.26 ms | 37.79 ms |
| vec_allocator, after measured first | 36.84 ms | 44.35 ms |

The async difference is 0.3%; vector results regress 1.4% and 20.4%, with a
410.84 ms outlier in the reverse-order run. These samples do not establish a
wall-clock improvement. The verified benefit is eliminating unnecessary
allocations; further optimization should target larger algorithmic costs.
Repository-wide formatting still reports preexisting pending async edits;
the changed borrow-checker module has been formatted independently.

## Avoid allocations when comparing active loan places (2026-10-01)

Borrow conflict searches now borrow active names rather than eagerly cloning
every candidate. Place overlap streams paired path components rather than
allocating two vectors, including when the first component already differs.
Child-loan searches build their owner prefix once per search, not per candidate.
Linear release collection clones a place only when its operand is linear.

A differential test compares the streaming overlap predicate against the old
collected-prefix implementation for 3,721 pairs, including wildcards, empty
components, unequal depths, and distinct roots. All 824 library tests, 183 async
tests, and enabled integrations pass; four preexisting tests remain ignored.

Warm release CLI comparisons use 40 samples per compiler, two warmups, baseline
first, with no concurrent build or test activity. The baseline is commit
08dac20. Every executable is byte-identical:

| Workload | Before median | After median |
| --- | ---: | ---: |
| Reference-heavy | 38.78 ms | 38.89 ms |
| async_fn | 49.84 ms | 48.97 ms |
| vec_allocator | 37.21 ms | 37.34 ms |

Async is 1.8% faster in this sample; the other workloads are 0.3% slower.
These noisy end-to-end results do not establish a general speedup. The
deterministic benefit is removing candidate-name and path-vector allocations.

## Borrow program declarations instead of cloning them

The borrow checker now gives function and branch contexts an immutable slice
of the input declarations. Previously it deep-cloned every imported item and
function body into an Arc before checking. Rust lifetimes ensure contexts
cannot outlive the program; no ownership rules or generated instructions change.

Baseline: 4ba30f6. Warm release CLI runs, 40 samples per compiler, two warmups,
baseline first, with builds and tests finished:

| Workload | Before median | After median |
| --- | ---: | ---: |
| Reference-heavy | 39.17 ms | 38.76 ms |
| async_fn | 50.37 ms | 50.43 ms |

Executable bytes are identical. The 1.0% reference-heavy reduction and 0.1%
async regression are too small to establish a general timing improvement.
The deterministic benefit is eliminating one whole-program AST copy and its
allocations. All 835 library tests, 183 async tests, and enabled integrations
pass; four preexisting integrations remain ignored.

## Eliminate the duplicate branch-join context copy

Branch merging now borrows the original context for membership checks and
clones it only once to construct the independently owned result. Previously
it copied every loan and provenance table twice. Join equations, labels,
thread state, and independently owned branch mutations are unchanged.

Baseline: ce594b2. Warm release CLI runs, two warmups, no concurrent builds
or tests. Compared executables are byte-identical:

| Workload | Samples per compiler | Before median | After median |
| --- | ---: | ---: | ---: |
| Snapshot-heavy, baseline first | 30 | 321.91 ms | 308.87 ms |
| Snapshot-heavy, optimized first | 40 | 331.33 ms | 322.52 ms |
| async_fn, baseline first | 40 | 50.89 ms | 51.77 ms |
| Reference-heavy, baseline first | 40 | 38.89 ms | 39.44 ms |

The branch-heavy workload improves by 4.1% and 2.7% in opposite measurement
orders. Async and reference-heavy medians regress by 1.7% and 1.4%; large
outliers (up to 2.7 seconds) indicate host scheduling noise, so no universal
speedup is claimed. Removing one complete context copy per branch merge is
deterministic. All 835 library tests, 183 async tests, and enabled integrations
pass; four preexisting integrations remain ignored.

## Index thread worker signatures lazily

The borrow checker now builds one borrowed function index on the first task
declaration, replacing one whole-program scan per task. Programs without tasks
do not build the index. Forward declarations and first-match lookup behavior
are unchanged.

Baseline: fe37783 with the same pending staged ownership changes in both builds.
Warm release CLI, 256 task declarations, 30 samples per compiler, two warmups,
no concurrent builds or tests:

| Measurement order | Before median | After median |
| --- | ---: | ---: |
| Baseline first | 185.72 ms | 183.35 ms |
| Optimized first | 179.21 ms | 184.86 ms |

These mixed results (1.3% faster, then 3.2% slower) do not establish an
end-to-end speedup. Lookup complexity changes from O(tasks × declarations)
to O(declarations + tasks), excluding the unchanged parameter copying.
Executable bytes match. All 847 library tests, 183 async tests, and enabled
integrations pass; four preexisting integrations remain ignored.

The new `--thread-heavy` benchmark also uncovered an order bias: generator
cache maintenance scans every artifact on every lookup. Sharing one synthetic
source directory across different compiler fingerprints grows that directory
for the second compiler (roughly 28–32% slower in the initial measurements).
Synthetic comparison workloads now use separate source/cache directories with
identical contents. Real-file comparisons still share the project's cache.

## Throttle abandoned generator-cache staging scans

Every generated-source and expansion-cache lookup previously traversed the
entire cache directory looking for abandoned staging files. A compilation with
G invocations and C cache artifacts therefore paid O(G × C) housekeeping work
even on warm hits. Cleanup now runs at most once a minute per directory while
its bounded 64-directory history is retained. Eviction permits a fresh scan;
directory history is not retained indefinitely by long-running library users.
Only temporary files older than an hour are removed, unchanged. Full-key,
digest, syntax, and size validation still run on every hit. The coordination
lock is released before traversing the directory or deleting stale files.

Baseline: 9684424, warm release CLI with two warmups and no concurrent builds
or tests. Pending staged ownership edits are identical in both builds.

| Workload / measurement order | Samples | Before median | After median |
| --- | ---: | ---: | ---: |
| 256 tasks, baseline first | 30 | 183.26 ms | 145.11 ms |
| 256 tasks, optimized first | 30 | 183.55 ms | 142.89 ms |
| async_fn, baseline first | 40 | 53.80 ms | 32.53 ms |
| async_fn, optimized first | 40 | 53.55 ms | 30.30 ms |
| Reference-heavy, baseline first | 40 | 38.39 ms | 37.74 ms |

Thread-heavy compilation is 20.8–22.2% faster; the existing async example is
39.5–43.4% faster. Reference-heavy's 1.7% difference is small enough to be
noise. Executable bytes match throughout. Absolute results depend on cache
directory size; these are warm end-to-end measurements, not timing guarantees.
All 848 library tests, 183 async tests, and enabled integrations pass; the four
preexisting ignored integrations remain unchanged. A regression test verifies
throttling, cleanup resumption, and protection of recent temporary files;
the existing concurrent-publication test also passes.

## Bound cache reads on a single open handle

Cache reads no longer perform a separate pathname metadata lookup before
opening the artifact. A limited reader accepts at most 64 MiB and reads only
one additional byte to detect oversize entries. This also bounds allocation
when another process grows the file during the read. Full key, digest, UTF-8,
syntax, and publication validation are unchanged. Oversized files now require
reading the bounded prefix rather than being rejected by metadata alone.

Baseline: 3c22cf1 with identical pending staged ownership edits. Warm release
CLI, two warmups, no concurrent builds or tests:

| Workload / measurement order | Samples | Before median | After median |
| --- | ---: | ---: | ---: |
| 256 tasks, baseline first | 30 | 142.40 ms | 143.48 ms |
| 256 tasks, optimized first | 30 | 142.26 ms | 142.86 ms |
| async_fn, baseline first | 40 | 31.20 ms | 29.73 ms |
| async_fn, optimized first | 40 | 30.44 ms | 30.47 ms |

Executable bytes match throughout. Async's initial 4.7% improvement does not
repeat in reverse order; thread-heavy is 0.4–0.8% slower. These measurements
do not establish a general speedup. The deterministic benefits are one fewer
metadata syscall per read and enforcing the size limit during the read itself.
All 16 focused generator/cache tests pass, including oversized/corrupt entry
rejection and concurrent publication.
All enabled integrations also pass (including 183 async tests); four existing
ignored tests are unchanged. The library suite passes 856 tests and fails the
pre-existing uncommitted staged empty-enum thread-join provenance test.

## Hash generated-source digests without concatenating inputs

The stable hash now accepts borrowed byte slices. Generated-source validation
hashes the key, NUL separator, and source directly instead of allocating and
copying their concatenation. The algorithm, separator, and digest format are
unchanged; no cache schema migration is needed. A regression test checks every
split point, empty segments, embedded NULs, and UTF-8 input against contiguous
hashing. All 17 focused generator/cache tests pass.

Baseline: c798715 with identical pending staged ownership edits. Warm release
CLI, two warmups, no concurrent builds or tests:

| Workload / measurement order | Samples | Before median | After median |
| --- | ---: | ---: | ---: |
| 256 tasks, baseline first | 30 | 141.70 ms | 142.02 ms |
| 256 tasks, optimized first | 30 | 143.00 ms | 142.24 ms |
| async_fn, baseline first | 40 | 30.15 ms | 30.56 ms |
| async_fn, optimized first | 40 | 30.61 ms | 29.83 ms |

Executable bytes match throughout. Task timing ranges from 0.2% slower to
0.5% faster; async ranges from 1.4% slower to 2.5% faster. These mixed results
do not establish a general timing speedup. Removing one key-plus-source-sized
temporary allocation and copy per digest calculation is deterministic.
The library suite passes 857 tests with the same pre-existing uncommitted
staged empty-enum thread-join provenance failure; no additional failure appears.

## Avoid allocation churn while constructing generator fingerprints

Dependency-closure traversal now borrows helper names from the generator call
list and existing fingerprint records. It no longer clones a String for each
queued edge or visited helper. Dependency and helper records are formatted
directly into their destination Strings, avoiding temporary formatted Strings
(including a helper-definition-sized temporary copy for each helper record).
Sorting, deduplication, fingerprint material, and digest inputs are unchanged.
As with any generator implementation edit, the interpreter fingerprint changes
and existing cache entries are invalidated normally.

All 19 focused generator/cache tests pass. The shared-dependency regression
also checks generator-level material and digest bytes against the previous
format, including an unknown helper and repeated dependency paths. No
end-to-end timing improvement has been established for this change. The
separate in-progress ownership-checker migration currently has nine failing
async tests (174 pass); these changes are not included in this optimization.

## Move ordinary declarations through generator expansion

Ordinary top-level forms now move directly into the expansion output instead
of cloning the complete expression and nested source-span trees, comparing
the result, and cloning the spans again. Generator invocations and collection
validation retain their existing path. A regression checks nested spans;
all 20 generator/cache tests and all three UI test harnesses pass.

Baseline: fcd05fd with identical pending ownership-checker edits in both
release builds. Warm CLI, two warmups and 30 samples per compiler, no
concurrent builds/tests during the recorded measurements:

| Workload / measurement order | Before median | After median |
| --- | ---: | ---: |
| Reference-heavy, baseline first | 163.18 ms | 159.27 ms |
| Reference-heavy, optimized first | 169.63 ms | 165.16 ms |
| async_fn, baseline first | 53.35 ms | 53.81 ms |

Reference-heavy improves by 2.4–2.6%; async's 0.9% slowdown is small and
does not establish a general improvement or regression. Executable bytes
are identical for every comparison. The allocation reduction is deterministic.
The much larger pending semantic-analysis migration is outside this commit.

## Use inspectable Lim as the user-generator cache payload

User-generator invocations now write one `.lim/generated/generated-HASH.lim`
file each. Compilation parses that exact file on a cache hit rather than
reading a second copy from a serialized `.cache` artifact. There is no
additional aggregate user-generator output file. Nested invocations remain
visible in their parent's output and cache their own output separately.

Each invocation has one `.lim/cache/generated-HASH.key` metadata file: its
first line is the source-integrity digest and the remainder is the complete
invocation/dependency key. Readers check both before parsing. The metadata
is published after the source, so an interrupted or mixed publication is
not accepted. Full-key comparisons also prevent false hash-collision hits.
Caller comments accumulate `file:line` origins, including duplicate and
nested callers; unchanged headers and metadata are not rewritten. The
separate async capture-analysis cache remains because it stores analysis,
not another copy of generated program code. Older cache artifacts are
ignored, not automatically deleted.

Measurements use release CLI binaries before and after this change on an
Intel Core i7-13700KF, with no concurrent builds or tests. Baseline and new
binary alternate execution order on each iteration, using separate fixture
directories. Times include process startup and native binary emission.
Cold means an absent `.lim` directory, not a cold OS page cache. Reported
values are medians over 20 cold and 100 warm compilations per binary.

| Workload | Cold before | Cold after | Warm before | Warm after |
| --- | ---: | ---: | ---: | ---: |
| custom_generator | 1.607 ms | 1.481 ms | 1.457 ms | 1.403 ms |
| generator_functions | 2.123 ms | 2.231 ms | 1.459 ms | 1.371 ms |
| 256 independent generator invocations | 15.729 ms | 18.404 ms | 9.325 ms | 10.736 ms |
| async_fn | 81.697 ms | 82.104 ms | 65.528 ms | 64.887 ms |

The synthetic fixture declares `(#gn alias (name) \`((#type ,name #u64)))`,
invokes it for `Alias0` through `Alias255`, and returns 42 from main.
The other fixtures are the corresponding files under `examples/`.

Small warm user-generator builds improve by 3.7–6.0% in this final run;
these are machine-specific measurements, not universal guarantees.
Publishing separate readable source and metadata files for each of 256
invocations makes that cold build 17.0% slower, and the warm build is 15.1%
slower in this run. An earlier paired run measured the same fixture at
8.642 -> 12.476 ms cold (+44.4%) and 6.527 -> 6.237 ms warm (-4.4%), so
the larger workload's timings vary substantially. The async differences
are around 1%, not evidence of a meaningful performance change. Executable
exit statuses and stdout/stderr match for all four fixtures. This change
simplifies cache ownership and inspection; it is not an across-the-board
compilation optimization.

An additional warm-only check, alternating binaries for 20 unmeasured
warmups followed by 200 measured builds each, measured the 256-invocation
fixture at 6.072 -> 6.664 ms (+9.7%). Means were 7.151 -> 7.766 ms.
Avoiding cold-cache publication between samples reduces timing variation,
but the extra per-invocation metadata read still has a measurable cost.

## Compilation-local generator lookup and batched provenance

The expansion context now holds a lookup table of already validated
invocations and their source artifacts. An identical invocation skips
cache-key construction, disk reads, parsing, gensym restoration, and nested
re-expansion. Its declarations were already emitted, so it does not need
another AST copy: a retained parent/child invocation graph propagates its
caller location to all affected artifacts in memory. Source artifacts and
caller sets are retained until expansion completes. Each new artifact or
changed header is then published once; unchanged artifacts are not written.
Directory creation is also shared across the publication batch. Builtin
materialization uses a lookup set to avoid repeated reads for the same full
cache key, with the complete caller list available before publication.

The table is expansion-local, not process-global: a later compilation must
read and validate its inputs again. Integrity, full-key comparisons,
gensym ownership checks, and dependency invalidation remain in place.
The new tests count actual source-read attempts and successful publications:
64 calls to a parent and child read each artifact once on a warm run and
publish each artifact once on a cold run, preserving all 64 caller lines.
The warm run performs no provenance writes. A changed generator body in
a subsequent compilation produces new artifacts instead of reusing RAM.

Release CLI measurements compare the previous inspectable-file cache
(`634b02c`) with this change on the same i7-13700KF. Binaries alternate
execution order on every sample. Warm measurements exclude 20 warmups per
binary and use 200 measured compilations (50 for async_fn); cold medians
use 20 compilations with an absent `.lim` directory, not cold OS pages.
No builds or tests were run concurrently with these measurements. Startup
and native executable output are included, and runtime outputs match.

| Workload | Warm before | Warm after | Cold before | Cold after |
| --- | ---: | ---: | ---: | ---: |
| custom_generator | 5.124 ms | 4.653 ms | 4.713 ms | 5.161 ms |
| 256 identical generator calls | 14.905 ms | 2.201 ms | 26.045 ms | 2.202 ms |
| 256 identical nested generator calls | 25.655 ms | 2.266 ms | 40.789 ms | 2.512 ms |
| 256 distinct generator calls | 8.314 ms | 8.184 ms | 18.528 ms | 17.564 ms |
| async_fn | 63.665 ms | 62.725 ms | not measured | not measured |

Repeated-call fixtures use the alias generator from the preceding section.
The repeated fixture calls `(@alias Shared)` 256 times; the distinct one
uses `Alias0` through `Alias255`. The nested fixture additionally declares
`(#gn parent (name) \`((@alias ,name)))` and calls `(@parent Shared)` 256
times. All synthetic fixtures return 42 from main.

Warm repeated calls improve 85.2%, and nested repeated calls improve 91.2%
(about 6.8x and 11.3x faster). Their cold improvements are 91.5% and 93.8%.
Distinct invocations still need one initial source/metadata read each;
the measured warm improvement of 1.6% is small and is not a general
speedup claim. The async change is likewise small. Absolute tiny-program
timings vary across runs, and the custom_generator cold median worsened
9.5% in this run; the reliable result is the eliminated repeated I/O and
publication work, backed by read-count tests and the repeated-call timings.

## Borrow-analysis allocation and traversal work (2026-10-10)

Four separately committed changes retain whole-program semantic validation:

1. Reuse the identical contents-aware provenance solution for return and store
   summaries; retain the distinct legacy store-only transfer.
2. Share reachability, predecessor and call-evaluation indexes within an
   immutable call-result refinement pass, without persistent graph caches.
3. Use dense membership tables for arena IDs in reachability and returned
   provenance traversal. Test membership against an independent hash traversal
   after graph-edge changes, including cyclic and disconnected graphs.
4. Share unchanged loan-state containers with copy-on-write snapshots. Mutating
   access detaches the affected container; identical-container joins avoid
   copying. Tests check branch isolation for bindings, allocation contents,
   parameter contents and global coverage facts, including joins.

The first two changes used 30 sequential warm runs per compiler. Their commit
messages record the individual results, including an effectively unchanged
printing measurement for the first change. Scheduling outliers motivated
alternating execution order and pinning later comparisons to one available
CPU. The dense-ID change's 40 paired samples measured 3.7% and 3.3% reductions
for string_view and string_println respectively.

Final comparisons use preserved release binaries, three warmups per compiler
and 40 measured compilations per compiler/workload. Before/after execution
order alternates each pair, on one CPU, with no concurrent builds or tests.
Measurements include process startup, native linking and executable output
to a temporary directory. Generator caches and OS pages are warm; cold
compilation was not measured. Executable bytes, exit status, stdout and stderr
are identical for every compared workload.

| Cumulative warm median | Before all four | After all four | Reduction |
| --- | ---: | ---: | ---: |
| `examples/string_view.lim` | 108.15 ms | 79.85 ms | 26.2% |
| `examples/string_println.lim` | 106.57 ms | 78.77 ms | 26.1% |
| `examples/async_fn.lim` | 73.38 ms | 63.19 ms | 13.9% |

| Copy-on-write alone | Before fourth change | After fourth change | Reduction |
| --- | ---: | ---: | ---: |
| `examples/string_view.lim` | 98.12 ms | 80.04 ms | 18.4% |
| `examples/string_println.lim` | 97.05 ms | 79.33 ms | 18.3% |

All 1,282 compiler unit tests and 213 async tests pass, along with the native
example manifest, UI diagnostics, UTF-8 oracle tests, String/standard-library
and documentation tests, LSP end-to-end tests, and additional reference,
slice, heap-borrow and pinning regressions. Formatting and all-target checking
also pass. No ownership or borrow-validation gate was removed.

## Shared per-function semantic facts (2026-10-10)

Related return, store, clear and variant summaries now share one provenance
solution and one set of outcome graphs for each compatible transfer mode.
Staged referent effects also reuse the provenance already solved by the caller.
Different contents modes and modified outcome graphs remain independent.
A differential test compares every summary component to independent solves
in both modes. All 1,283 unit tests, 213 async tests, adversarial borrow tests,
native examples and UI diagnostics pass.

Using the same alternating, CPU-pinned, 40-pair warm benchmark protocol above:

| Warm median | Before | After | Reduction |
| --- | ---: | ---: | ---: |
| `string_view` | 82.514 ms | 79.068 ms | 4.2% |
| `string_println` | 81.197 ms | 78.166 ms | 3.7% |
| `async_fn` | 64.970 ms | 63.784 ms | 1.8% |

Executable bytes and runtime results are identical for all three workloads.

## Opt-in semantic stage timings (2026-10-10)

`--timings` now aggregates inclusive semantic substage durations while retaining
the existing outer stages. Nested categories overlap and are not additive.
Disabled collection creates no timestamps or timing events. Unit tests cover
aggregation, nested-session isolation and disabled clocks; command tests cover
successful compilation, type errors and stable text/JSON output.

With timing collection disabled, 40 alternating CPU-pinned warm pairs measured
string_view at 77.835 -> 77.811 ms and async_fn at 66.009 -> 65.781 ms.
These are effectively unchanged, not a speedup claim. Native bytes are identical.
A representative timed string_view check spent 51.240 ms in semantic validation:
30.057 ms in referent contracts, 13.977 ms in provenance, 8.329 ms in referent
consumptions, 7.040 ms in initial summaries and 6.044 ms in contents summaries.
The solver totals are included in their enclosing phases, not additional work.

## Persistent library inference summaries (2026-10-10)

Imported/generated function parameter summaries are cached in
`.lim/cache/semantic/summaries-<hash>.bin`. The versioned, bounded binary
artifact includes exact key material and a payload checksum. Declaration IDs
are stored by name and remapped into the current checked program. Sessions read
once into RAM, publish atomically only after successful validation, and do not
rewrite unchanged warm hits. I/O or decoding failures fall back to inference.

Invalidation is initially conservative: the entire expanded program and all
loaded source dependencies, generator witnesses, cfg, search paths, target,
compiler fingerprint and version participate. Root edits also invalidate the
cache. This saves repeated summary inference, not library validation: every
type, ownership, borrowing, initialized-referent and unsafe gate still runs.

The preceding CPU-pinned, alternating, 40-pair warm protocol measured:

| Warm median | Before cache | After cache | Reduction |
| --- | ---: | ---: | ---: |
| `string_view` | 77.117 ms | 66.696 ms | 13.5% |
| `string_println` | 76.876 ms | 66.300 ms | 13.8% |
| `async_fn` | 62.154 ms | 61.116 ms | 1.7% |

Native bytes, exit status, stdout and stderr are identical. These measurements
use warm generator and summary caches; cold latency was not measured.

All 1,291 unit tests, 213 async tests, native examples, UI diagnostics, String
and standard-library tests, UTF-8 oracles, documentation and LSP end-to-end
tests pass, plus the additional heap/reference/slice/pin borrow regressions.
Cache tests cover both transfer modes, aggregate outcomes and mutable field
stores, transitive and generated dependencies, cfg/root/type changes, target
contexts, name-based ID remapping, damaged/schema-incompatible files, unchanged
file modification times, failed-validation publication, unavailable storage and
concurrent writers. Timing/cache-report tests, formatting and all-target checking
also pass.
