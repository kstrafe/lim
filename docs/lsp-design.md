# LSP source navigation design

Go-to-definition is a language feature, not a collection of spelling searches.
Every identifier occurrence has a source role. Builtin keywords, literals,
wildcards, cfg values, and literal generator inputs have no user declaration.

## Resolution model

`src/lsp_navigation.rs` is the shared source-role resolver. Its lexical scopes
retain declaration spans and explicitly declared types. A use of a parameter,
local, destructured binding, match payload, loop variable, or label resolves in
that scope. Initializers cannot see their new binding; failure branches cannot
see success bindings; nested blocks, arms and loops do not export bindings.
No-shadowing does not remove the need for scope: separate functions can reuse
parameter names, and unrelated structs can reuse field names.

Fields resolve through the receiver's declared type, aliases, reference/pointer
wrappers, function signatures and projections. Named call labels resolve to the
selected function's parameters. Struct-literal labels resolve to that struct's
fields. Tuple/array indices remain literals, not identifiers. `$` puns navigate
as the value use, since their label and value share the same source token.
Enum constructor and pattern names resolve to variant declaration spans; this
includes cases, conditional patterns, payload operations and fieldless values.
Borrowed `#let-else-ref`, `#let-else-ref-mut`, `#let-else-pin` and
`#let-else-pin-mut` retain the same variant/binding roles as their case modes.
Their reference annotation describes the input, not the payload. Success
bindings enter only the following statements; `#else` bindings are confined to
the diverging fallback. Input expressions precede either binding scope.

Types navigate in all explicit type positions, including bindings, function
signatures, aggregate fields, layout queries, casts, raw operations and typed
constructors. Generator parameters, for-each binders and `#gn-call` helpers have
their own lexical roles. Quoted syntax is data; only active unquotes evaluate
generator expressions. `#syntax-splice` and short `#await` protocol references
resolve to syntax-bundle declarations. Explicit function syntax passed into a
generator retains its source-level parameter/local/type roles; arbitrary macro
arguments do not become references merely because they resemble names.

`src/editor.rs` selects the entry, cfg, target, module paths and unsaved overlays.
Raw active source trees retain generator declarations and lexical function
inputs; the expanded program supplies generated declarations and concrete type
information. Ordinary lexical navigation remains available when unrelated
generation or type checking fails. Each compilation context is independent;
results are deduplicated by exact source location, never merged by spelling.
Unknown or ambiguous declarations fail closed instead of choosing an arbitrary
global with a matching name. This resolver is not a rename/workspace index or
an incremental compilation cache.

Original source IDs, byte spans, UTF-16 positions and cfg exclusion must be
preserved. Generated targets use the existing checked `editor-*.lim` snapshot
publication path, including generated distributed-enum contributions. A request
must not overwrite edited snapshots or create a generated target from an
invalid expansion. Ordinary checking remains source/cache-write-free.

## New syntax acceptance checklist

Every syntax addition or change must include all of the following:

- Identify declarations, lexical binders, value uses, type uses, field/argument
  labels, variant names, generator-time uses and deliberately literal tokens.
- Implement these roles in the shared resolver. Do not add another ad hoc
  lookup for one expression when the role is common to other forms.
- Specify scope, declaration order, initializer visibility and branch/loop
  lifetime. Distinguish runtime expressions from templates and literal inputs.
- Add positive and negative LSP tests with exact target ranges. Include names
  reused in different scopes/types, out-of-scope uses, unsaved buffers and
  unrelated errors. For generated/imported syntax include provenance, external
  prefixes, cfg and multiple entry points as applicable.
- Preserve read-only diagnostics, generated publication safeguards and UTF-16
  source mapping; update formatter/highlighting/documentation as appropriate.
- Update this design, the local implementation checklist, the user-facing LSP
  feature description and the independent `src/lsp_syntax_policy.rs` review
  inventory. Its test rejects new parser keywords and builtin-reference entries
  without navigation review, including specialized forms and metadata keywords.

The inventory is intentionally independent of the parser. It is a review gate,
not a proof that every possible program or future change of argument shape is
covered. New forms and changed forms still require semantic regression tests.
