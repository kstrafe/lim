# Lim4 ownership interaction campaign findings

Base: `09837cf1f4f051b65d218abaa5dc4ea78838600f`.
Branch: `lim4/adversarial-tests`.

## Result

No compiler bug established by this bounded campaign. The dedicated integration
file `tests/ownership_interaction_campaign.rs` contains 28 deterministic cases:
16 valid controls and 12 intended rejections. Both campaign tests pass; Cargo
also runs three existing support-module process tests (five tests total).
No production compiler, LSP, website, or existing test files were changed.
Evaluation order is outside this campaign.

## Corpus and independent expectations

Eighteen cases cross handwritten/generated imported helpers, three returned
aggregate layouts (struct, tuple, one-element array), and three loan actions.
A file alias calls the helper. A local alias extracts the returned reference,
then the aggregate is forgotten. Mutation of the referent must still reject;
mutation of a distinct local must accept; releasing the extracted alias must
permit mutation. These expectations follow the reference-lifetime contract,
not agreement between compiler modes.

Ten cases cross handwritten/generated imported identity helpers with explicitly
linear scalar-bearing structs. Consuming the transferred owner once accepts;
consuming it twice or leaving it unconsumed rejects. A field reference read after
owner transfer rejects as access to a consumed linear referent; releasing that
reference before transfer accepts. The rejection class for these cases is
`Linear`; ordinary live aggregate-reference mutation uses `Borrow`.

Each case compiles twice with an initially empty, privately owned scratch cache.
Accepted cases require identical cold/warm assembly and actual semantic-summary
cache hits on the warm run. Rejected cases require identical complete diagnostics
on repeated attempts. Each of the six aggregate overlap cases additionally
warms a valid sibling source in the same cache and checks that the violating
source still produces the same diagnostic. Changing root source can invalidate
summaries: this last check does not claim an invalid root itself reuses a summary.
All 16 accepted controls link and execute independently, require exit code 42,
and require empty stdout/stderr. The native expected value is literal and does
not come from another compiler path.

## Validation

Final focused command (through the unchanged shared serial resource guard):

```sh
bash scripts/limited-run.sh nix develop -c env CARGO_PROFILE_TEST_DEBUG=0 CARGO_INCREMENTAL=0 cargo test --test ownership_interaction_campaign -- --test-threads=1 --nocapture
```

Final result: 5 passed, 0 failed, 0 ignored; campaign runtime 0.32 seconds.
The guard applies a 2 GiB command-tree memory ceiling, no swap, 200% CPU quota,
128 tasks and ten-minute timeout. Native controls additionally use the existing
process-group runner with five-second timeout and 4096-byte per-stream output
limit. Corpus size is fixed; no random search or unbounded retries are included.
Build output stayed in this worktree's own `target` directory. Scratch source,
cache, generated artifacts and binaries are removed by `support::Scratch`.

The initial harness attempts used unsupported alias-to-local syntax and omitted
the explicit `#linear` marker on the resource fixture; those were harness errors,
not compiler findings. A subsequent over-specific `Borrow` class expectation for
the post-transfer field read was corrected to `Linear`: rejection was already
present. No failing acceptance expectation was hidden or marked ignored.

The new Rust file was formatted with Nix-provided `rustfmt`; scoped formatting
and `git diff --check` are checked before commit.

## Limits

This is regression evidence, not a soundness proof. It covers shallow aggregate
layouts, one imported helper hop, shared reference aliases and explicit linear
consumption. It does not cover all enum/heap/slice/pin/async combinations, dynamic
indices, arbitrary generators, actual destructor counters, unsafe programmer
promises, other targets, or the full repository suite. Generated helpers are
ordinary user `#gn` expansion, not the standard-library async/allocator recipes.
No bug reproducer is attached because every final expectation passed.
