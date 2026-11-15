# Bounded compilation and limit diagnostics

Limits are implementation boundaries, not permission to weaken a proof. The
compiler rejects unsupported mandatory analysis rather than choosing a subset
of feasible paths. Supplementary scalar specialization may discard its entire
result and fall back to conservative ordinary checking; it must not return an
incomplete graph as evidence.

Current major bounds:

| Stage | Bound | Failure behavior |
| --- | --- | --- |
| S-expression parser | 256 nested expressions | Source-associated nesting error |
| Imports | 128 active files, 4096 imports, 64 MiB cumulative source | Reject the source/import crossing the limit |
| Generator interpreter | 200,000 evaluation steps; 128 nested expansions | Reject the invocation with expansion context |
| Generator output | 1,000,000 emitted syntax nodes | Reject oversized expansion |
| Generated cache artifact reads | 64 MiB per artifact | Refuse invalid/oversized cache input |
| Borrow call arguments | 1024 alternatives; 128 reference-chain links | Reject rather than omit possible aliases |
| Retained operand loans | 1,000,000 expression/retained-value relations | Reject before retaining an over-budget snapshot; no partial loan proof is accepted |
| Predicate evidence | 4096 facts; 200,000 local analysis steps; 16 KiB per identity; 64 MiB cumulative identity/snapshot work | Reject without accepting partial evidence |
| Constrained types | Depth 64; 1024 expanded fixed-array elements | Reject unsupported expansion; use a whole-collection predicate |
| Async initialization | 16,384 states per emitted function | Reject with state limit, storage width, and a restructuring suggestion |
| Async initialization facts | 16,777,216 retained boolean cells across before/after/identity vectors | Reject before adding an over-budget state; report width and configured state limit |

The fact-storage bound is separate from state count. A wide frame can exhaust
fact storage with relatively few states. Equal retry states reuse existing
facts; merely visiting a loop again does not consume another state budget.
The storage bound is not a claim about total compiler RSS: source trees, typed
graphs, native emission, allocator overhead, and temporary vectors also use RAM.

The async errors explicitly state that no partial proof was used. Reducing live
storage or separating independent suspension histories into concrete functions
can reduce analysis work. Raising a limit without understanding the state space
is not a substitute for a sound proof.

## Reproducible pathological benchmark

The ignored unit benchmark constructs nondeterministic initialization histories
at two storage widths. It asserts that bounded rejection occurs, and prints
elapsed time, the state/fact budgets, and the diagnostic. It does not compare
timings against a flaky CI threshold or accept a partial result.

```sh
bash scripts/limited-run.sh nix develop -c \
  env CARGO_PROFILE_TEST_DEBUG=0 CARGO_INCREMENTAL=0 \
  cargo test --lib pathological_specialization_reports_bounded_work \
  -- --ignored --nocapture --test-threads=1
```

For end-to-end release compilation use `scripts/benchmark-compile.py` with its
reference/scoped/snapshot/async workload switches and a retained baseline. Use
`--timings` on a compile or `--check` command to inspect stage contributions.
Record build profile, target, corpus, and cold/warm cache state with results.

`tests/seeded_safety.rs` also contains the ignored
`pathological_reference_programs_report_cold_and_warm_check_codegen_times`
benchmark. It compiles actual balanced 8/32/128-target reference-selection
programs, reports first/cached passes, and asserts identical assembly. It measures
the in-process frontend and assembly generation, not process startup or linking:

```sh
bash scripts/limited-run.sh nix develop -c \
  env CARGO_PROFILE_TEST_DEBUG=0 CARGO_INCREMENTAL=0 \
  cargo test --test seeded_safety pathological_reference_programs \
  -- --ignored --nocapture --test-threads=1
```

One local debug-profile run under the resource limits below produced:

| Reference targets | Cold pass | Two warm passes |
| --- | --- | --- |
| 8 | 5.30 ms | 4.20 / 4.23 ms |
| 32 | 15.54 ms | 14.85 / 14.55 ms |
| 128 | 69.41 ms | 65.33 / 65.55 ms |

The initialization-history model rejected at 128 states in 0.30 ms for 16 fact
columns and 23.53 ms for 4096 columns. These are diagnostic workload samples,
not release performance claims or a before/after speedup measurement. Re-run
the retained benchmarks on the same profile and host when comparing changes.

Development commands should run through `scripts/limited-run.sh`. Its current
aggregate scope enforces 2 GiB RAM, no swap, two CPU equivalents, a process limit,
a ten-minute timeout, one Cargo build job, and serial Rust tests. These external
limits protect the host independently of the compiler's internal proof budgets.
