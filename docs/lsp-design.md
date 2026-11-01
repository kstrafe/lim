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
Project-root `//` paths use the selected principal entry context, including
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


## Proof source roles

`(#theorem name proposition)` declares a procedural theorem name at the name
token. The proposition starts a fresh lexical scope. `#theorem`,
`#math-definition`, and `#math-inductive` are the declaration forms; `#proof`
is solely an evidence clause in a structured theorem. Spelling prefixes do not
grant builtin or navigation behavior. Proof-operation and clause keywords are
metadata with no definition.
This includes the boolean connectives (`#proof-and`, `#proof-or`, `#proof-not`,
`#proof-implies`) and effect tags (`#proof-allocation`, `#proof-io`,
`#proof-global-write`, `#proof-unsafe`, `#proof-external`, `#proof-asm`,
`#proof-mutation`). Neovim highlights the theorem declaration and the exact
proof keyword inventory, including effect tags, at every nesting depth.

Function operands of `#proof-calls-directly`, `#proof-calls-transitively`,
`#proof-calls-before`, `#proof-calls-when`, `#proof-no-effects`,
`#proof-only-unsafe`, `#proof-stack-at-most`, and `#proof-contract` resolve through
the canonical function declaration table. `#proof-sorted` uses that same role
for its comparator. Local values and non-function declarations cannot substitute
for these operands. Aliases and file references retain their original function
identity, and generated names use the final file scope through `scoped_name`.
Targets are the actual source declarations, including generated snapshots.
Unprefixed entries in the `#proof-only-unsafe` allowlist are trusted function
boundaries and use the same canonical function role, including aliases and
generated declarations; they never resolve to lexical values. Hash-prefixed
builtin entries in that list have no definition. The boolean observation in
`#proof-calls-when`, effect tags in `#proof-no-effects`, and stack ABI string and
limit remain metadata; their contents do not undergo global spelling lookup.

`(#proof-requires-validation entry (#parameter-of validate user)
(#parameter-of perform user))` has distinct function and parameter-reference
roles. Each descriptor must be a three-item list headed by the exact
`#parameter-of` marker. The `entry` operand and each descriptor's function
operand at index 1 navigate through the canonical function declaration table
to their actual definitions. Aliases, file references, and generated function
names preserve the same identity rules as other proof function operands.

The parameter operand at index 2 navigates only to the existing parameter token
of the selected function: `(#parameter-of validate user)` selects `validate`'s
`user` parameter, while `(#parameter-of perform user)` selects `perform`'s. These
need not be the same source span or have matching spellings. Neither token is
a local binding or an expression in the theorem's or entry function's scope.
An unknown parameter or unresolved descriptor function has no definition;
there is no fallback to a same-spelled caller parameter, local, global, or an
unrelated function's parameter. Descriptor lists introduce no lexical bindings.

Both `#proof-requires-validation` and `#parameter-of`, along with descriptor
list structure, are metadata, not runtime calls or values. Function and parameter
leaves retain the explicit roles above; clicking a marker or delimiter has no
definition. Bare legacy `(function parameter)` lists, unprefixed
`(parameter-of function parameter)` lists, and malformed selectors have no
navigation targets or spelling fallback, including through `@` qualification.
An ordinary function or parameter named `parameter-of` retains its usual role;
its unprefixed spelling is distinct from the descriptor marker. Semantic
checking separately enforces reference or pinned-reference parameters, equal
resolved referent types, and a Boolean validator. Navigation while editing
must not substitute a different role when these requirements fail.

Navigation regression coverage must distinguish the two parameter spans,
include reused names in the caller and globals, and reject missing parameters,
unresolved functions, legacy lists, and malformed descriptors without spelling
fallback. Selecting a parameter must not make it visible to sibling propositions.
The exact `#proof-requires-validation` token is highlighted as `limProof` at
all nesting depths; bare names are identifiers and unknown suffixed spellings
remain generic keywords.

`(#proof-for-all (: x Type : y Type) proposition)` gives each name its own binder
span and explicit type. Its bindings are visible only in its proposition;
nested quantifiers retain outer bindings and sibling propositions cannot see
inner bindings. Navigation retains these nested scopes while editing even though
the semantic checker rejects nested quantified claims and requires combined
`#proof-for-all` binders. Type operands use ordinary type navigation.
`#proof-contract` predicates instead bind the selected function's declared
parameter names to their actual parameter tokens and types. Contract result
projections retain the function's declared return type.

Each `(Function label invariant rank)` entry of `#proof-with-invariants`
selects that function and reconstructs its lexical scope at the label. The
label resolves within that function, never by global spelling. Invariant and
rank expressions use the actual parameter/local binding spans and declared
types at that point, including enclosing block and loop bindings. Later locals,
locals from completed blocks, and bindings in unrelated functions are excluded.
Missing or ambiguous labels fail closed. Entry scopes do not escape into the
wrapped proposition or other entries. Scope reconstruction uses declaration
order rather than the proof cursor offset, so imported functions work too.

Operands of `#proof-eq`, `#proof-old`, `#proof-result`, `#proof-permutation`, and
the array operand of `#proof-sorted` use the ordinary runtime expression walker.
`#proof-no-overflow` treats its typed operation token as metadata and walks its
value operands; `#proof-loop-limit` treats its bound as metadata and walks its
proposition. Runtime roles continue through all these wrappers: fields resolve
through receiver types, named call arguments resolve to the selected function's
parameters, labels stay lexical, and neither fields nor argument labels fall
back to same-spelled globals. `#proof-old` preserves its operand's type for
member navigation.

`tests/proof_navigation.rs` covers exact declaration ranges, all canonical
keywords, positive function/value/type references, scope isolation, runtime
member/argument roles, metadata collisions, aliases, generated declarations,
and unsaved proof buffers. `src/lsp_syntax_policy.rs` independently inventories
all proof forms; the Neovim syntax tests also reject partial keyword matches.

## Kernel proof source roles

Mathematical definitions and datatypes are direct declarations:
`(#math-definition name (universes...) TYPE VALUE)` and
`(#math-inductive name (universes...) ((parameter Type)...) SORT
((constructor ((field Type)...))...))`, with an indexed form that inserts
`(#indices (#parameter name Type)...)` before `SORT` and gives each constructor
an output index list after its fields. Their names navigate to their own source
tokens. Universe parameters scope over the remaining declaration operands.
Datatype parameters are sequential kernel term bindings. In indexed declarations,
index binder types see datatype parameters and earlier indices, the sort sees all
indices, and constructor fields see datatype parameters plus earlier fields.
Declared index binders are deliberately unavailable in constructor field types.
Constructor output indices see all constructor fields. Each constructor gets a
separate sequential field scope; fields never escape into another constructor.
Constructor names navigate to their declaration tokens in either form.

A mutual family places `(#mutual FAMILY...)` after its parameter list and
before the optional `#indices` clause. Every member remains a top-level
`#math-inductive`; the ordered family list is shared by all members. In
mutual induction, `#pt-recur FAMILY (indices...)` resolves its family as a
declaration role and its indices as terms. `#pt-mutual-induct` uses explicit
indices and ordered `(FAMILY MOTIVE (BRANCHES...))` bundles; family keys are
metadata and motives, branches, and subject use ordinary term scopes.

A mathematical theorem uses shared explicit binders:

```lim
(#theorem reflexive
  (#universes u)
  (#parameters (#parameter A (#pt-type u)) (#parameter x A))
  (#statement (#pt-eq A x x))
  (#proof (#pt-refl A x)))
```

`#universes`, `#parameters`, `#parameter`, `#statement`, and `#proof` are clause
metadata with no definition. A parameter's type is navigated before its name
enters scope, using earlier parameters and the universe scope. The statement
and evidence share that one parameter scope: both occurrences of `x` above
navigate to the same `#parameter x` token, rather than duplicated synthetic
Pi/lambda binders. Mathematical theorems and procedural shorthand theorems share
the global theorem declaration role; their operand roles remain distinct.
The private `proof-definition`, `proof-theorem`, and `proof-inductive` AST
wrappers used by the checker are not registered as public source syntax.

Kernel types are proof terms, not runtime `Type` expressions. Term bindings and
universe parameters have separate lexical namespaces, with no fallback from a
bare name to a runtime declaration or global proof. Inner `#pt-pi`, `#pt-lambda`,
and single-binder `#pt-sigma` forms retain their existing `((name Type)...)`
binder syntax. Each binder's type sees earlier binders; all binders scope over
the body. Navigation supports nested shadowing during editing, including terms
that the semantic checker rejects. A definition's declared type and value have
independent term scopes; neither scope escapes the declaration.

`(#pt-let (#parameter NAME TYPE) VALUE BODY)` requires exactly three operands
after its head and a three-child `#parameter` binder. The binder name follows
the kernel identifier rule: it starts with a Unicode alphabetic character or
`_`, and contains no `:`, `/`, `.`, or `@`; `_` is a valid mathematical name.
`TYPE` and `VALUE` use the incoming term scope; the
name enters scope only in `BODY`, where it shadows an outer term binding or a
same-spelled universe without changing universe lookup. Its declaration token
navigates to itself. The `#parameter` metadata token and malformed let shapes
have no navigation fallback. Explicit `#pt-use` references inside the body
continue to select globals. File resolution preserves these same type, value,
and body boundaries through aliases and generated source.

Universe occurrences navigate in `#pt-type`, `#pt-sort`, explicit level argument
lists, and nested `#pt-level-succ`, `#pt-level-max`, and `#pt-level-imax`
expressions. `(#pt-sort LEVEL)` names the sort directly: sort 0 is Prop and sort
`(#pt-level-succ u)` is Type u. `(#pt-level-imax LEFT RIGHT)` is universe-level
arithmetic metadata with exactly two operands: its value is 0 when RIGHT is 0,
otherwise the maximum of LEFT and RIGHT. Both written operands retain universe
navigation even when arithmetic makes one irrelevant. A malformed imax list
or a sort with the wrong operand count has no navigation target.

Integer levels and level/sort keywords have no definition. Term binders cannot
capture universe occurrences, universes are not implicit term bindings, and
same-spelled globals or aliases never supply a universe reference. File-access
resolution leaves `#pt-sort` and `#pt-level-imax` operands untouched, just as it
does for `#pt-type` and the other level operators. This preserves universe names
in imported proofs and generated definition/invocation contexts; it does not
change explicit global proof-reference roles.

`(#pt-use declaration (levels...))` explicitly selects any mathematical
`#math-definition`, `#math-inductive`, or structured `#theorem` declaration.
`#pt-program` and `#pt-certificate` select procedural shorthand theorems.
These roles ignore same-spelled lexical bindings and reject runtime functions
and types. They preserve canonical declaration identity through aliases,
imports and the final file scope for generated names. Explicit level arguments
always occupy a list, including the empty list.

`#pt-construct` and `#pt-induct` select a `#math-inductive` declaration. Mutual
declarations also support `#pt-recur` and bundled `#pt-mutual-induct`; their
family names resolve to declaration tokens while indices and bundle terms
retain term roles. Explicit
levels use the universe scope; parameter values use the current term scope.
Indexed `#pt-induct` adds an index expression list after the parameter list;
those expressions, the shifted motive, branches and subject use the current term
scope. `(#pt-self-at (index-expr...))` gives its index expressions ordinary
kernel term roles. The `#indices` and `#pt-self-at` tokens are metadata and have
no definition.
A construction's label resolves only to a unique constructor of that datatype,
never an unrelated global or another datatype's same-spelled constructor.
Field values, induction motives, branch terms and subjects use the current term
scope. Lists of parameter values, field values and branches are containers, so
their first element is a term rather than a keyword or implicit call head.

Recursive function fields use the same sequential `#pt-pi` scope rules as
ordinary kernel functions. Each nested domain can refer to earlier arguments;
`#pt-self-at` indices in recursive field types can refer to datatype
parameters, earlier constructor fields, and in-scope function arguments.
Datatype indices are not in scope in constructor fields or constructor result
indices. A field is not in scope in its own type. Function argument names
remain local to that recursive field: they do not enter constructor result
indices or later field types. Constructor-label navigation continues to select
the constructor declaration. Tests cover these roles and the negative scope
boundaries in `tests/kernel_navigation.rs`.

An optional `#mutual` clause precedes any `#indices` clause. Every member in
that header is a global inductive reference, never a term binder. Header
layout validation shifts index, sort and constructor positions together, so
constructor label lookups still select the correct family and source range.
`#pt-recur` treats its first operand as a global family and its second as a
container of index terms. `#pt-mutual-induct` separates universe metadata,
parameter values, the explicit index clause, a list of family/motive/branch
bundles and the subject. Bundle keys are global references; motives and branch
lists use the current lexical term scope without leaking their binders into
siblings. Missing clauses, malformed containers and invalid group metadata
have no runtime or global-spelling fallback. Generated member lookups use
the checked expanded declarations. Exact ranges, aliases and malformed roles
are covered in `tests/kernel_navigation.rs` and
`tests/kernel_mutual_resolution.rs`.

`(#pt-project FAMILY INDEX SUBJECT)` selects a `#math-inductive` family and a
zero-based field ordinal. The ordinal is an explicit untyped nonnegative
integer carried as metadata; it has no navigation target. The family navigates
to its inductive declaration and the subject uses ordinary kernel term roles,
including local binders. Family references support direct paths, `@` names,
aliases, imports and generated declarations. The ordinal never resolves to a
same-spelled global or local. Malformed arity or ordinal forms remain inert,
including the family and subject roles. The navigation tests cover these
positive and negative roles in `tests/kernel_projection_navigation.rs`.

`#pt-app`, `#pt-eq`, `#pt-refl`, `#pt-eq-elim`, `#pt-pair`, `#pt-first`,
`#pt-second`, `#pt-succ` and `#pt-nat-induct` navigate every term operand with
these same kernel roles. `#pt-numeral` carries integer metadata. All kernel
keywords, including atomic `#pt-prop`, `#pt-nat`, `#pt-zero`, `#pt-false` and
`#pt-self`, have no definition. Unknown or malformed terms never fall back to
the runtime walker or global spelling lookup. The general `@name` prepass does
not bypass explicit kernel-reference roles.

`tests/kernel_navigation.rs` reuses the proof navigation protocol harness for
exact ranges on shared theorem parameters, dependent term types, universes,
constructor fields and labels, aliases, imports and generated declarations.
It also covers clause metadata, shadowing, isolated scopes, missing or ambiguous
constructors and wrong declaration kinds. `tests/proof_navigation.rs` covers
procedural shorthand theorems and their runtime operand roles.
