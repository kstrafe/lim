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
