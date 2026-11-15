# Explicit effect migration

An omitted `#effects` field permits no effects. Validation always checks
functions, direct calls, implicit clone calls, and retained async source
witnesses. There is no legacy-source exemption or migration-on-load mode.
Authorization neither proves predicate facts nor preserves them across writes.
The existing memory summaries, borrow checks, and unsafe rules still apply.

```lim
#effects = (#io-input (#read-global counter));
#effects = (#io-output (#write-global counter));
#effects = (#io #global-access);
#effects = ((#effects-of public-operation));
```

`#io` covers input and output permissions. `#global-access` covers reads and
writes of all globals; a specific write grant also covers reads of that global.
Read-only never covers writes, and input-only never covers output. Unknown IO
still requires the broad `#io` grant even if both narrow tokens were listed.
Ordinary immutable runtime globals need read permissions; immutable `#const`
data without references, ownership handles, or atomics does not.

Calls check the callee's declared interface, including unused declared grants.
Callers are never widened automatically. A forwarding wrapper should name its
effectful callees explicitly:

```lim
#fn print-text {
  #params = ((text (#ref String)));
  #returns = #i64;
  #effects = ((#effects-of std-print));
  #body = ((#return (#call std-print ((text text)))));
}
```

An explicit callback group can contain repeated names, nested groups, or empty
groups: `(#effects-of ((poll) (start-next) ()))`. It is a union of the written
function declarations, not an inference from their bodies. Composition
generators use this form to emit callback sets and optional continuations.
The original single-function form remains valid.

## Real input-only and output-only byte IO

Two fixed-operation primitives perform real Linux IO on the native x86-64 and
AArch64 backends:

```lim
// descriptor: #i64; result: (#tuple #i64 #u8)
(#io-input-byte descriptor)
// descriptor: #i64; byte: #u8; result: #i64
(#io-output-byte descriptor byte)
```

Input returns the read count or negative errno and a byte. The byte is zero on
EOF/error; inspect the count before treating it as input. Output returns the
write count or negative errno. Operands evaluate once in written order. Each
primitive passes the kernel a private one-byte temporary, never a caller's
pointer or reference. They therefore require only `#io-input` or `#io-output`,
plus any ordinary effects of evaluating their operands. Source cannot select
another syscall number or enlarge the buffer. Backend lowering selects read/
write as 0/1 on x86-64 and 63/64 on AArch64.

`#std` exports `std-read-one-char` (input-only, with EINTR retry) and
`std-write-one-char` (output-only, taking `value #u8`). The primitive's valid
descriptor and scalar value operations are memory-safe; this adds no exemption
to the unsafe requirements of existing raw APIs. WebAssembly still rejects
native IO primitives. Predicate purity and conservative evidence invalidation
remain checked by the existing contract summaries; an output permission does
not promise evidence stability.

## Library and template review

Classify each function's direct operations first. Keep pure functions without
annotations. Give known atomic global operations a specific global grant;
for example the system allocator's lock/unlock functions declare only
`(#write-global systemAllocatorLock)`. Forwarding wrappers use `#effects-of`.

The current checker conservatively requires `#io #global-access` for assembly,
raw/word memory primitives, and foreign or unmodelled boundaries. This includes
assembly that happens to be a pointer cast and raw heap accesses that happen
to stay local. An annotation cannot assert that such an operation is input-only
or output-only. Narrow primitive classification requires a separate audited
compiler change; this migration does not guess from syscall numbers or strings
of assembly. Existing pinned shared-handle spellings retain their current
checker classification as well.

`std-write-all` in `library/stdio.lim` and `File::read-raw`/the file write
boundary still call an arbitrary syscall primitive. These bulk/raw APIs remain
broad. Narrowing them still requires audited typed buffer operations and their
memory footprints: input writes the destination; output reads the source.
Numeric syscall classification alone is insufficient because ordinary typed
checking does not retain the backend target. Unknown and dynamic syscalls stay
broad. `std-read-line` also inherits the broad effects of String allocation;
the new input-only guarantee applies to `std-read-one-char`, not all readers.

`#effects-of` includes private global effects through a visible function, but
does not create a name, pointer, borrow, or visibility grant for that memory.
Direct annotations remain subject to normal alias and library access rules.
Do not import a private static merely to make a wrapper's annotation readable.

Quoted `#fn`/`#unsafe-fn` templates need a signature clause immediately after
the return type: `(#effects (...))`. It is removed before executable statements
are parsed. A generated factory has its own interface; it need not inherit
effects that occur only when its deferred body is polled. Generated raw storage
helpers declare their own broad boundary, and dispatchers explicitly include
the written interfaces of selected helper templates. Authored async bodies
retain their own written permissions and are checked as source witnesses.

## Bounded offline workflow for remaining fixtures

`scripts/migrate-effects.py` is an offline structural planning tool, not part of
the compiler. It uses only the Python standard library and the existing record
migration tokenizer. Bounds are 128 explicit `.lim` paths, 2 MiB per source,
16 MiB combined, 300,000 tokens per source, 10,000 functions combined, and a
structural nesting limit of 200. Run it under the repository's process limits.

1. Classify a fixture before extracting its Lim source. Separate complete
   positive programs, intentional negative programs, fragments, and generated
   syntax. Never rewrite arbitrary Rust strings or expected diagnostic text.
2. Pass complete source plus library context to the helper, without `--write`.
   Save/review the JSON plan. It lists direct structural effects, written
   interfaces, callee inclusions, generator fragments, and parameter mutations.
   Automated insertion supports explicit record `key = value;` sections and
   grouped positional template trees. Colon/indentation body sections stop with
   a manual-classification error. Surface named applications are review markers;
   use the same declaration edits against the original spelling after review.
3. Review generator fragments manually. The helper does not interpret unquotes,
   execute generator functions, resolve types, infer clone dispatch, or perform
   full reference-origin analysis. Unknown callback names stay explicit
   `#effects-of` references. Review globals forwarded through mutable or atomic
   reference parameters against the checked read/write summaries. Generated
   APIs such as `CellU64::set` can be pure despite appearing in the unknown
   callee list; inspect their emitted interfaces before adding a redundant
   declaration. Review async factories separately from their deferred bodies.
4. Apply `--write` only to the classified `.lim` inputs. Existing declarations
   are preserved, even when insufficient; their missing permissions require a
   review. Pure functions receive no declaration. The helper makes insertions
   only and preserves existing function bodies and comments.
5. Copy only reviewed declaration edits back to the selected fixture. Preserve
   its negative-test trigger and expected diagnostic. For privacy fixtures,
   prefer a visible callee's effects to a private-memory annotation.
6. Have the coordinator run the effect acceptance target and selected migrated
   fixture targets through serialized guarded validation. Treat diagnostics as
   missing declarations or modeling gaps; do not disable mandatory checking.
   Repeat cached-source cases as part of that validation.

The generated-source format key is bumped for these explicit signatures so
cached artifacts containing old unannotated runtime functions are rebuilt.
The key change does not grant permissions, bypass checks, or disable caching.

## Built-in coverage and remaining integration targets

Built-in vector allocator and sort source templates reside in
`src/lib.rs` (`generated_vec_allocator_source` and
`generated_vec_sort_source_parts`) and are migrated in this followup. The
allocator-template functions declaring broad boundaries are
`{name}::reserve-fields`, `push`, `get`, `get-mut`, `set`, `pop`, and `free`.
`{name}::reserve` includes `(#effects-of {name}::reserve-fields)`.
`{vector}::sort` has a broad clause; explicit allocator, destructor, and
comparator inclusions document the selected callbacks.
`new`, `new-with-storage`, `len`, and `capacity` remain pure.

Native thread task spawn/join interfaces are opaque compiler interfaces rather
than ordinary `Item::Function` records. Calls currently require broad IO/global
permissions. They cannot be named by `#effects-of` until they have an explicit
effect interface; use the broad grants at those call sites. Worker bodies still
need their own declarations, including generated executor callback inclusions.

Existing examples and general Rust fixture strings are not changed by this
migration. Call sites of effectful library and generated functions need their
own explicit declarations. The helper's generator-fragment and parameter-write
reports are review obligations, not a claim that compiler validation has passed.
`docs/effects-tutorial.patch` contains reviewed declaration edits against main's
`examples/tutorial_hello.lim` and the Hello World executable fence in
`docs/tutorial.md`. Apply it after integrating the new tutorial, then regenerate
the handbook under the coordinator's validation guard. `docs/playground.html` and
`scripts/check-browser*.mjs` remain with the printing worker until its handoff.
Predicate-prerequisite inheritance is a separate task.
