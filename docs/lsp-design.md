# LSP source navigation design

Go-to-definition is a language feature, not a collection of spelling searches.
Every identifier occurrence has a source role. Builtin keywords, literals,
wildcards, cfg values, and literal generator inputs have no user declaration.

Identifier conventions do not replace declaration lookup: `Type::FunctionGroup::function`
is one function name and `Enum.Variant` is one variant name. The new scalar
operations such as `#u64::add-wrap` are builtin tokens and have no definition.
`#gn-variant` uses the existing generator-expression roles: its evaluated
arguments resolve lexical syntax parameters, while quoted symbols and string
suffixes are literal data. Navigation tests cover these positive and negative
roles as well as explicit enum literals and variant patterns.

## Resolution model

Directory libraries use the nearest enclosing `lib.lim` as their boundary.
`#export` operands navigate to declaration or variant tokens; the keyword has
no definition. External prefixes form complete identifiers (`prefix@Name`),
not namespace syntax. `#generate` opens the generated artifact, while its
generator-name operand navigates to the generator declaration. Literal inputs
remain data. New syntax must preserve compiler visibility checks in diagnostics
and cover these roles in navigation tests, including unsaved library roots.

Compilation contexts may omit `cfg` entries. Builtin configuration keys are
derived from that context's target; an omitted target defaults to the host,
matching the compiler CLI. Explicit cfg entries override individual defaults.
Each context derives its own defaults without inheriting another context's
custom flags.

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
In `(#enum-literal Variant payload)`, `Variant` resolves only to an enum
variant declaration, never a local, function or type with that spelling.
The optional payload is an ordinary expression in the current scope; it
introduces no binding. The owning enum supplies the expression's declared
type for chained field/payload navigation, including imported and generated
declarations. Construction syntax is not accepted as a pattern.
Optional-reference projection results use ordinary `#let-else` variant and
binding roles. The generated enum's payload reference type determines member
navigation, including all four ordinary/pinned, shared/exclusive modes. Success
bindings enter only the following statements; failure locals are confined to
the diverging `#else` body. Input expressions precede either binding scope.
`#generate #enum-project` arguments remain literal generator inputs; its emitted helper
and optional variants use ordinary generated-definition navigation.
The compact `(#let-else variant-pattern value (#else statements...))` has no
type operand or failure binder. Its variant supplies the declared payload
type; navigate the value as an expression and every `#else` child as a
statement in a separate scope, without exposing the success binding there.

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

`#call-graph` is a zero-argument builtin, not a user-defined symbol. Navigation
on its keyword has no target. Its caller-context parameters and stack buffers
are compiler-owned implementation details and do not introduce source bindings
or change navigation of the surrounding user function's declarations.
