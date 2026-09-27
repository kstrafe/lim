# PERF-02 symbol interning measurements

Run the benchmark and test suite from the repository root with:

```sh
nix develop --command cargo bench --bench compiler -- --iterations 10
nix develop --command cargo test
```

Measurements below came from the bounded compiler benchmark on an Intel Core
i7-13700KF (13th Gen), Linux x86_64, rustc 1.99.0-nightly (89c61a754,
2026-07-23), release bench profile. The benchmark reports cold/warm generator
and build data as before, plus allocator request counts for parsed syntax.

## Parsed AST A/B

For each source, the current side parses into the production `String` AST. The
interned side parses that same source, then constructs a benchmark-only mirror
with `u32` symbol IDs, a compilation-local `HashMap<String, u32>` retaining each
exact source spelling once, and matching spans and child shape. Allocation
counts for the mirror row start after parsing, so those requests belong to
mirror construction alone. The timing rows compare parse-only with parse plus
mirror construction.

The benchmark executable uses a `std::alloc::System` wrapper. It counts
successful allocator calls and the sizes requested by `alloc` and `realloc`,
and tracks deallocation requests as well. Reported bytes are per-iteration
cumulative allocator traffic, not peak/live heap size; reallocations contribute
the new requested size and the old retired size. The reported `current parse`
allocations are all allocations made by parsing. The mirror row counts only
allocations made while constructing the mirror from an already parsed AST.
This is an exact count of allocator API requests in this single-threaded
benchmark section, not a count of physical allocator pages or retained bytes.

| Workload | Symbol nodes / unique | Current parse calls / bytes | ID mirror calls / bytes | Parse only | Parse + mirror |
| --- | ---: | ---: | ---: | ---: | ---: |
| 256 generated functions | 3,855 / 261 | 10,556 / 1,419,936 | 2,326 / 381,159 | 391 µs | 538 µs |
| Large reference projections | 1,399 / 53 | 2,990 / 226,071 | 1,034 / 104,602 | 113 µs | 175 µs |
| Vector allocator | 1,725 / 112 | 4,027 / 376,099 | 1,245 / 135,617 | 160 µs | 254 µs |

The mirror construction makes additional allocation requests amounting to
about 27%, 46%, and 36% of current parse allocation bytes for these workloads.
This does not demonstrate a memory win: the prototype must duplicate the
already parsed AST to perform the A/B, and its mirror keeps all non-symbol
payloads plus the parallel span-aware child tree. A production interned AST
could replace strings in place and avoid some of this duplication, but that
representation and its end-to-end performance are not measured here. The
measured post-parse conversion is also slower than parsing alone for all three
inputs. No adoption decision or compiler behavior change follows from this
benchmark.

The global allocator counters observe requests across the whole process. The
reported section executes synchronously, without benchmark worker threads;
output and formatting happen after each measured interval. Atomics in the
allocator add some timing overhead, so these timings are directional
single-machine measurements, not timing gates. Existing symbols statistics
count repeated spellings in both `Expr` and `SpannedExpr.children`, where the
AST stores them twice; they are spelling estimates rather than allocations.

## Generated syntax and cache

The 256-alias generator fixture estimates 1,536 symbol string instances and
1,278 repeated-spelling allocations across generated forms. This is
reconstructed from the deterministic fixture expansion (`GeneratedN` type
forms); the serialized syntax cache is private and was not decoded. Cache
diagnostics reported two `missing-entry` decisions cold and two `hit` decisions
warm. In this run, generator phase averages were 8.08 ms cold and 1.97 ms
warm; the complete generator-heavy compile-and-link workload averaged 10.70 ms
cold and 4.48 ms warm. These timings include the existing compiler pipeline
and do not isolate an interning change.

Peak process RSS during the run was 12,956 kB. This is a whole-process high
water mark and does not compare retained memory between representations. The
bounded A/B indicates that this post-parse prototype adds allocation traffic
and conversion time; a front-end representation replacement and downstream
pipeline A/B remain unmeasured.
