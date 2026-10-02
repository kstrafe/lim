# Soundness audit coverage

This is a maintained adversarial regression index, not a formal proof of the
compiler. Each invariant below points to a test that attempts to violate it.
The complete suite is run with `cargo test --all-targets`; executable
destruction and allocation cases are in the binary integration tests.

| Boundary | Adversarial evidence |
| --- | --- |
| Raw pointers require `#unsafe`; mutability, pointee type, null handling, and checked pointer offsets are validated | `checks_raw_pointers_and_unsafe_blocks` |
| A reference produced from a raw pointer inherits the explicit anchor's provenance | `soundness_audit_tracks_raw_pointer_borrows_through_returned_tuples`, plus raw-pointer reference escape checks in `checks_raw_pointers_and_unsafe_blocks` |
| Loans survive returns through tuple aggregates and remain live when carried in enum payloads into `#match` | `soundness_audit_tracks_raw_pointer_borrows_through_returned_tuples`, `soundness_audit_keeps_enum_payload_borrows_live_across_match`, `dropping_reference_aggregate_releases_each_field_loan` |
| Nested aggregate projections and reference provenance are checked through local/global references and large indirect layouts | `projects_large_fields_through_references_into_indirect_storage`, `copies_large_aggregate_dereferences_through_indirect_storage`, `nested_multiword_aggregates` binary example, `ref_array_field` native regression |
| Structural `Send`/`Sync` derivation rejects raw pointers; an unsafe override is the explicit boundary for a programmer promise and is used by spawn validation. Generated `@cell` uses atomic storage and is `Send + Sync` | `derives_send_and_sync_and_accepts_explicit_unsafe_overrides`, `thread_spawn_generator_requires_send_worker_inputs_and_output` |
| Spawn allocation/creation failures select distinct variants; failed join returns the still-owned task handle and does not free its packet | `thread_allocation_failure_selects_explicit_spawn_error_variant`, `thread_creation_failure_selects_explicit_spawn_error_variant`, `thread_join_failure_selects_error_variant_without_freeing_task` |
| Captured loans remain live while a task is outstanding and transfer with the task handle through a failed-join error branch | thread-task loan checks in `borrowcheck.rs`, including failed-join/error-binding coverage |
| Generated destruction consumes nested owned fields exactly once across moves and returns; allocator failure preserves the vector for explicit destruction | `explicit_aggregate_destruction_runs_once_after_moves_and_returns`, `allocator_backed_vector_grows_and_destroys_elements`, `allocator_backed_vector_reports_allocation_failure_without_losing_vector` |

Compiler-enforced properties include structural Send/Sync derivation,
thread-handle ownership, captured-loan transfer, and the explicit unsafe
boundaries. Unsafe pointer operations and `#unsafe-impl #send/#sync` remain
programmer promises: the compiler checks their syntactic and type-level
preconditions, but cannot establish that an external address is valid or that
an override is truthful. The tests demonstrate both sides of this boundary:
raw pointers are rejected structurally, while an explicit unsafe
override allows the opted-in type to satisfy the property. Thread runtime tests
cover allocation, creation, and join failures; a failed join preserves the
task packet and returns its handle rather than silently destroying it. These
tests are regression evidence, not a formal proof of the compiler.
# Ownership place identity

The linear checker uses opaque, uniquely renamed binding identities and typed
projection components. Dots in local or field names do not denote projections.
Unknown array indices conservatively overlap every element; a dynamic write
does not prove that a previously moved element has been restored. Existing
borrow loans use a separate internal separator, not dots, for overlap checks.

## Bounded native test processes

The native example and malformed-input suites use a shared Linux runner.
It drains stdout and stderr concurrently, retains at most one MiB per stream,
and terminates the child's separate process group on timeout, excess output,
or parent exit. This closes pipes held by ordinary descendants as well as
reaping the immediate child. Test programs must not escape that process group;
this is a regression-test resource guard, not a hostile-program sandbox.
Scratch directories are exclusively created and removed only by their owner.

## Interprocedural reference-store checking

Production prepares contents-aware callee contracts before solving live loans.
References written into caller-owned storage therefore retain their pointees'
loans after the call and cannot hide a block-local escape. Dropping the call's
temporary destination reference does not release the loan held by its container.

`production_callee_reference_store_retains_the_callers_rhs_loan` rejects mutation
of a callee-stored referent and checks its exact mutation and loan-origin spans.
`production_callee_store_into_outer_storage_cannot_hide_a_block_local_escape`
covers scope escape and the causal origin span. Both have executable compiler
UI fixtures. Forwarded, conditional, computed and pinned store regressions also
require production mutation rejection. The contents solver intersects
physical-write guarantees across normal
returns and summarizes final contents rather than all intermediate writes.
`staged_store_contracts_distinguish_all_return_paths_and_final_contents` checks
sequential replacement, branches, loops, early returns, and forwarding;
`staged_final_store_contents_account_for_overlapping_and_uncertain_writes`
covers whole/field overlap and ambiguous/dynamic targets.
`staged_callee_clearing_preserves_loans_in_the_returned_old_value` prevents
post-write snapshots from releasing references returned from entry storage.
These facts do not prove linear ownership restoration.

`typed_contents_borrow_checks_preserve_checked_pinned_async_frames` verifies
the contents-aware production contracts on all three pinned self-reference
examples. `staged_store_unions_do_not_claim_ready_path_self_reference_clearing`
keeps the naive may-store-only solver's false Ready-path conflicts explicit;
plain unions must not replace result-conditioned clearing. The full async
integration suite separately exercises Pending, Ready and cancellation.
Production borrowing now uses typed places, live loans and these contents-aware
contracts without a syntax-based acceptance fallback. The old lexical model is
test-only differential evidence. `typed_unread_holders_retain_loans_until_use_release_or_scope_exit`
covers unused direct references, reference-bearing structs and slices, branch
cleanup and scope exit. `typed_fresh_aggregate_borrows_are_checked_before_binding`
rejects conflicting fresh struct/tuple/array/enum operands before the result is
bound and accepts disjoint owners. The pinned-copy holder matrix independently
checks that releasing a loaded copy does not authorize destruction of its
original holder's parent handle; UI fixtures check both new primary spans.
`typed_aggregate_operand_snapshots_survive_later_handle_reassignment` checks
that replacing a shared source handle in a later operand cannot hide the loan
already copied into the first operand, with exact conflict/origin spans and
disjoint-owner and symbolic-slot controls. Slice metadata reads remain subject
to suspended-parent permission in `tests/slice_reborrow.rs`.
This coverage is not a proof of all ownership or arbitrary-body async lowering.
