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
