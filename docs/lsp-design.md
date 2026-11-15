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

Direct `path.lim::name` references and `#alias` operands resolve through canonical
file/declaration identities, not spelling searches. Alias uses and both alias
operands navigate to the final original declaration, including facade aliases,
same-named definitions in different files, and generated definitions. `#alias`,
`=`, and `#unstable` have no definition target. The explicit bypass affects only
the selected declaration's visibility, never the navigation identity or struct
representation access. File-reference paths resolve against their authored
source, including unsaved overlays and generator definition/caller contexts.
Source navigation consults the final file scope for names introduced during
generation, including enum variants used in `#let-else` patterns.
New resolution forms require positive and negative end-to-end tests.

Directory libraries use the nearest enclosing `lib.lim` as their boundary.
`#export` operands navigate to declaration tokens; individual enum variants are
not export operands. Exporting an enum makes its construction and pattern
variant references navigable without separate variant exports. The keyword has
no definition. File paths select declarations; aliases retain their original identity. `#generate` opens the generated artifact, while its
generator-name operand navigates to the generator declaration. Literal inputs
remain data. New syntax must preserve compiler visibility checks in diagnostics
and cover these roles in navigation tests, including unsaved library roots.
Canonical paths identify one source file. Alias chains and symlinks resolve to
the same declaration; different dependency files can carry identical spellings.
Project-root `project::` paths use the selected principal entry context, including
multi-entry `lim.lsp` configurations.
Generated-file access is distinct from declaration ownership. Validated
`#generated-context` headers describe definition and invocation module instances;
they never change which declaration a fully qualified identifier denotes.
Source `@name` qualification must navigate to the resolved global declaration,
including inside generator templates and literal arguments, without treating it
as a same-spelled local or generator parameter. Generated private references
must navigate to the original library definition. Add navigation coverage when
introducing or changing qualification, generated headers, and argument syntax.

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

Delimited bindings such as `#let value : Type = initializer;` retain the
reader's nested `(Type = initializer)` source tree. Resolve the type inside
that specification as a type, and the initializer as an expression evaluated
before the new binding enters scope. The `:` and `=` delimiters have no
definition target. Navigation, hover, and initializer signature help must also
handle `#let-mut`, compound types, and multiline specifications while retaining
the exact authored spans. The checked binding representation remains the same
as for canonical positional generator syntax.

Fields resolve through the receiver's declared type, aliases, reference/pointer
wrappers, function signatures and projections. Named call labels resolve to the
selected function's parameters. Struct-literal labels resolve to that struct's
fields. Tuple/array indices remain literals, not identifiers. `$` and bare record
puns navigate as the value use, since their label and value share a source token.
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

## Hover and signature help

Hover and signature help share the source-role resolver and declaration metadata
used by definition navigation. They must preserve canonical alias and generated
identities, lexical scope and owner-type selection. A matching spelling alone
does not provide information. Hover ranges select the authored token in UTF-16;
explicit binding, parameter and field types retain their source notation.
Function information includes named parameters, return types and the declaration's
`#requires`, `#ensures` and `#preserves` contracts without checking or changing their
meaning. When checked metadata is available, it separately displays computed
predicate prerequisites in evaluation order, with substituted arguments and
numbered source-origin edges. Canonical declaration spans identify the contract
through aliases and private library names; shared prerequisites are shown once.
Display limits bound large dependency graphs and report omitted information.
Information queries do not publish generated source or write buffers.
When an unfinished named call prevents normal expansion from completing,
display-only queries can reuse the existing declaration planner before call
normalization, retaining generated signatures and canonical file scopes. This
metadata is not a validation result and cannot publish navigation snapshots.
Deferred async expansions may remain unavailable until the buffer is complete.

Signature help selects the innermost runtime call containing the cursor. Explicit
`#call`/`#unsafe-call` and surface named calls use the same callee roles. Select the
active parameter by the current argument's name, including reordered arguments
and `$` puns; an unknown label must not select a parameter by ordinal position.
Direct positional scalar intrinsic calls use the compiler's parameter order;
source operators lowered from infix notation do not become signature-help calls.
Clients advertising `signatureInformation.noActiveParameterSupport` receive
`activeParameter: null` for unknown labels; older clients receive no index and
may apply their protocol default. Responses follow the
[LSP signature-help schema](https://github.com/microsoft/language-server-protocol/blob/gh-pages/_specifications/lsp/3.18/language/signatureHelp.md).
Strings, comments, quoted templates and literal generator inputs are not calls.
Independent compilation contexts contribute distinct signatures and hover blocks;
identical information is deduplicated, and failed entries do not erase valid ones.
Hover content and signature contract documentation honor each client's supported
markup formats and default to plaintext when no preference is advertised.

Editor-only suffix recovery may complete unfinished delimiters or argument values
so a call being typed can resolve against existing compiler metadata. Recovery
preserves every authored byte offset, is bounded, never rewrites the document,
and does not accept malformed syntax in the middle of a buffer. Compiler parsing,
type checking and evaluation order remain unchanged. End-to-end stdio tests must
cover surface call spellings, incomplete edits, aliases/generated declarations,
negative source roles and Unicode/UTF-16 positions.

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
  unrelated errors. For generated and cross-file syntax include provenance,
  direct paths, aliases, `@` qualification, relative and project-root paths,
  cfg and multiple entry points as applicable. Test malformed metadata at both
  its own token and neighboring reference roles so malformed forms stay inert.
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


## Predicate contract navigation

### Surface notation source roles

The surface reader preserves the original spans while lowering records, implicit
calls, semicolon groups, infix brackets and indentation lists. Function names,
parameter binders, type operands and body references retain their canonical
roles. Literal record keys become argument labels or declaration sections in
their consuming form; argument labels navigate to the callee's parameters.
Section markers, arithmetic mode markers, infix operators and punctuation have
no user declaration target. Newlines and dedents introduce no bindings.
For `key:` indentation entries, the trailing colon is excluded from the key's
source range; `key:`, `key :` and `key =:` retain the same canonical roles.
Statement-header colons group indented children without changing their roles:
body collections normalize like explicitly parenthesized collections. Loop
binders cover the loop body, and dedented forms retain the enclosing scope.
The colon is punctuation, including when attached to a numeric bound.
Inline colons introduce ordinary nested lists at any expression position.
They do not bind names or require a list-head position. Source ranges begin
at the written colon, while contained callees, labels and operands retain
their own exact ranges. Named calls with ordinary pair lists resolve their
callee and labels in expression context; quoted and generator data remain data.
Marker-free calls with braces or `((name value))` arguments normalize through
the same call roles: the callee resolves to its function and labels to its
parameters. The compiler's synthetic call marker has no authored source range.
Infix headers never cross ordinary calls or argument records. This local syntax
context introduces no name-resolution or proof inference. Navigation tests
cover exact positive and negative ranges in declaration records and layout.

Contract errors use E4400 and the ordinary source ranges and related locations.
JSON diagnostics classify them as `contract`; theorem outcome metadata has
been removed with the symbolic engine.

`#requires`, `#ensures`, `#preserves`, `#assume`, `#if-valid` and `#old` traverse
ordinary function/value/field references. `#result` has the enclosing function's
return type and no declaration target. Contract keywords never resolve to a
same-spelled user function.

`#index-proven` has the same array-reference and index value roles as `#index`.
The keyword has no definition target. Its element type supports subsequent
field/member navigation, and both operands retain their lexical scopes.
Typed comparisons in contracts traverse ordinary value operands.

Callable scalar intrinsics keep the `#call` argument roles: operand expressions
retain lexical scope, while the intrinsic callee and its generated parameter
labels have no user-source declaration target. Their generated return types
are available to value navigation. `#generate #array` has literal named inputs;
its keyword opens the generated source, and uses of the emitted alias and
accessors navigate to exact declarations in that source. No new lexical scope
is introduced by the invocation.

`#where` binds its value name only inside its predicates. Its base type uses
ordinary type navigation. The binder does not escape into sibling types or the
surrounding lexical scope. Malformed forms retain no speculative bindings.

### Single positional parameter roles

A plain `#params` type is a type position, including imported names and nested
reference/array types. Bare `#arg` resolves to that parameter type section and
hover reports its explicit type. Its scope is only the enclosing positional
function. Positional applications resolve their callee through the normal
file/alias/generated declaration identity; the whole operand is a value, never
a named-argument label. Hover and signature help show the plain parameter type
and identify its one active operand. These roles, formatter roundtrips and
keyword highlighting must accompany future changes to this syntax.
