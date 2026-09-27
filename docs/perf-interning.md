# PERF-02 symbol interning measurements

Run from the repository root with:

```sh
nix develop --command cargo bench --bench compiler -- --iterations 10
```

The benchmark reports parsed-AST symbol spelling duplication, a benchmark-only
compilation-local `String` to `u32` interner conversion, generator cache
decisions, and cold/warm builds. The machine used for this sample was an Intel
i7-13700KF running Linux, with rustc 1.99.0-nightly (2026-07-23).

## Parsed AST and interner prototype

The AST estimate walks symbol strings in both the nested `Expr` values and the
parallel span-aware `children` tree. It counts repeated text spellings; it is
not allocator instrumentation. The prototype retains the original AST while
building a benchmark-only mirror with IDs and a local spelling map, so its
timing includes parsing plus conversion and its extra storage is not a
production design measurement.

| Workload | Symbol nodes | Duplicate spellings estimated | Parse only | Parse plus intern conversion |
| --- | ---: | ---: | ---: | ---: |
| 256 generated functions | 3,855 | 3,594 | 261 µs | 571 µs |
| Large reference projections | 1,399 | 1,346 | 87 µs | 144 µs |
| Vector allocator | 1,725 | 1,613 | 135 µs | 225 µs |

Times are per iteration averaged over ten warm iterations. In these samples,
conversion costs more than parsing alone. The 256-function token-only pilot
also measured 88.4 µs for cloned strings and 53.4 µs for local interning over
200 iterations. The token-only result varied across runs and does not erase
the measured post-parse conversion cost. These are prototype comparisons, not
a full compiler A/B.

## Generated syntax and cache

The 256-alias generator fixture estimates 1,536 symbol string instances and
1,278 repeated-spelling allocations across the generated forms. This is
reconstructed from the deterministic fixture expansion (`GeneratedN` type
forms); the serialized syntax cache is private and was not decoded. Cache
diagnostics report two `missing-entry` decisions cold and two `hit` decisions
warm.

The generator phase averaged 5.53 ms cold and 1.58 ms warm. The complete
generator-heavy compile-and-link workload averaged 7.65 ms cold and 3.72 ms
warm. Those timings include the existing compiler pipeline and do not isolate
the cost or benefit of changing its AST representation.

Peak process RSS during the run was 12,896 kB. This is a whole-process high
water mark, not an interner-versus-current memory comparison. The benchmark
does not count allocations or compare two complete compiler implementations;
these results provide evidence against adopting the measured post-parse
interner prototype, while leaving a true front-end A/B unmeasured.
