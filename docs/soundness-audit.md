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
| Nested aggregate projections and reference provenance are checked through local/global references and large indirect layouts | `projects_large_fields_through_references_into_indirect_storage`, `copies_large_aggregate_dereferences_through_indirect_storage`, `nested_multiword_aggregates` binary example |
| Structural `Send`/`Sync` derivation rejects raw pointers and `Cell` sharing; an unsafe override is the explicit boundary for a programmer promise and is used by spawn validation | `derives_send_and_sync_and_accepts_explicit_unsafe_overrides`, `thread_spawn_generator_requires_send_worker_inputs_and_output` |
| Spawn allocation/creation failures select distinct variants; failed join returns the still-owned task handle and does not free its packet | `thread_allocation_failure_selects_explicit_spawn_error_variant`, `thread_creation_failure_selects_explicit_spawn_error_variant`, `thread_join_failure_selects_error_variant_without_freeing_task` |
| Captured loans remain live while a task is outstanding and transfer with the task handle through a failed-join error branch | thread-task loan checks in `borrowcheck.rs`, including failed-join/error-binding coverage |
| Generated destruction consumes nested owned fields exactly once across moves and returns; allocator failure preserves the vector for explicit destruction | `explicit_aggregate_destruction_runs_once_after_moves_and_returns`, `allocator_backed_vector_grows_and_destroys_elements`, `allocator_backed_vector_reports_allocation_failure_without_losing_vector` |

Compiler-enforced properties include structural auto-trait derivation,
thread-handle ownership, captured-loan transfer, and the explicit unsafe
boundaries. Unsafe pointer operations and `#unsafe-impl #send/#sync` remain
programmer promises: the compiler checks their syntactic and type-level
preconditions, but cannot establish that an external address is valid or that
an override is truthful. The tests demonstrate both sides of this boundary:
raw pointers and `Cell` are rejected structurally, while an explicit unsafe
override allows the opted-in type to satisfy the trait. Thread runtime tests
cover allocation, creation, and join failures; a failed join preserves the
task packet and returns its handle rather than silently destroying it. These
tests are regression evidence, not a formal proof of the compiler.
