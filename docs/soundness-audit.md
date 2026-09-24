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
| Structural `Send`/`Sync` derivation rejects raw pointers and `Cell` sharing; unsafe overrides are explicit, checked for duplicates/targets, and used by spawn validation | `derives_send_and_sync_and_accepts_explicit_unsafe_overrides`, `thread_spawn_generator_requires_send_worker_inputs_and_output` |
| Generated destruction consumes nested owned fields exactly once across moves and returns | `explicit_aggregate_destruction_runs_once_after_moves_and_returns`, `allocator_backed_vector_grows_and_destroys_elements`, `allocator_backed_vector_reports_allocation_failure_without_losing_vector` |

Unsafe pointer operations and `#unsafe-impl #send/#sync` remain author
promises: the compiler validates their syntactic and type-level preconditions,
but cannot establish that an external address is valid or that an unsafe
override is truthful. Fallible thread results are intentionally excluded from
this audit's passing claim until task ownership is carried through their error
branches; that behavior remains a separate unchecked checklist item.
