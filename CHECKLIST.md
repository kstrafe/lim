# Lim implementation checklist

This is the working roadmap for the language. Checked items are implemented
and covered by the current test suite. Cross items off as they are completed;
the checklist is committed alongside the implementation it tracks.

## Typed representation migration

- [x] **IR-02c: Resolve concrete declaration and member identities.** Assign
  deterministic program-local IDs to globals and aggregate types. Identify
  fields and enum variants by owner ID and declaration index; resolve aliases
  and references before selecting members. Retain these identities in reads,
  writes, constructors, and patterns, including enum alternatives, and use
  them when reconstructing backend input. Preserve existing source spans and
  keep syntax labels separate from values. Test same-named fields on different
  owners, global/local shadowing, imported spans, declaration-order stability,
  and native projection/mutation behavior. Specialization remains open below.

- [x] **IR-02b: Declare scoped binding identities and assignment roots.**
  Allocate local IDs at parameter, let, destructuring, let-else, and match
  pattern declarations, including unused bindings. Resolve uses and local
  assignment roots to these IDs; distinguish global assignment roots. Preserve
  block, loop, match-arm, and let-else success/failure scopes. Discard the
  temporary source-address index after lowering. Retain syntax labels as
  syntax rather than discovering locals from their first use. Member identities
  are covered by IR-02c; full specialization remains in IR-02 below.

- [x] **IR-02a: Retain typed body arenas on the normal compilation path.**
  Record checked expression types without another semantic pass; preserve
  source spans, numeric modes, function IDs, local IDs, and structured control
  flow. Reconstruct instruction-selector input from these arenas and carry
  expression types across unsafe erasure. Expose a deterministic library debug
  dump. Test contextual literals, reordered arguments, mutation/control-flow
  round trips, native examples, and numeric differential behavior. IR-02/03
  below remain open for complete removal of legacy lowering paths.

- [x] **IR-01: Retain resolved declarations after validation.** Preserve
  checked function signatures, struct fields, enum payloads, and global types
  in `CheckedProgram`; have native emission consume them. Assign deterministic
  program-local function IDs and retain declaration spans. Share recursive
  alias resolution across validation and remaining AST lowering, including
  every nested type constructor, with no unresolved-field fallback. Acceptance:
  single validation per compilation, stable IDs and assembly across fresh
  parses, recursive-alias diagnostics unchanged, executable nested-alias test.

- [x] **IR-02: Lower checked expressions and bindings to stable identities.**
  Retain operand/result types, binding IDs, function IDs on calls, and exact
  source spans. Numeric nodes must explicitly encode operation, width,
  signedness, and wrapping/saturation behavior. Preserve named-argument source
  order metadata separately from declaration-order operands. IDs must survive
  unsafe erasure and specialization without depending on allocation addresses.
  Acceptance: shadowing, dotted names, reordered calls, contextual literals,
  generated/imported spans, and all numeric modes have focused lowering tests.

- [x] **IR-02i: Derive emission order and pattern bindings from typed IDs.**
  Walk typed instructions and nodes to build the checked emission sequence,
  including unsafe erasure and structured control flow. Resolve pattern
  declarations through typed child IDs instead of an expression-address index;
  discard that temporary index from the body builder. Type and span capture
  still use source-address maps, and the backend overlay remains a bridge until
  the rest of IR-02/03 is migrated. Cover deterministic node order across fresh
  parses and retain native examples and diagnostic tests.

- [x] **IR-02j: Read match scrutinee types from checked nodes.** Lower the
  scrutinee first, then use its retained node type to resolve match-pattern
  identities. Do not look it up again by syntax address. Keep pattern binding
  and native match regressions; the broader checker-to-IR type/span maps remain
  part of open IR-02 work.

- [x] **IR-02k: Key retained expression types by source span.** Collect the
  expression-to-span association before semantic checking and store checked
  types under source spans. Use stable span lookup for unambiguous nodes, with
  an address fallback when span lookup is unavailable or ambiguous after
  transformed/imported syntax maps multiple AST nodes to one span. Preserve
  contextual aggregate ownership, generated/imported code, cfg, and
  loop-lowering behavior across the complete library suite. The backend's
  address-keyed emission overlay is still open in IR-02/03.

- [x] **IR-02l: Key checked types by deterministic expression IDs.** Assign
  dense program-local IDs with a source-order walk before semantic checking and
  retain expression types by those IDs. Keep the AST-address-to-ID map only as
  a temporary lookup adapter; spans remain independent diagnostic metadata.
  Verify dense IDs and stable corresponding nodes across fresh parses, then run
  the complete library and native integration suites.

- [x] **IR-02m: Retain local binding IDs in the emission bridge.** Carry each
  resolved local `BindingId` alongside its checked type under the expression's
  stable ID. Preserve the temporary address adapter for the legacy emitter;
  verify local identity survives the bridge while keeping shadowing tests.

- [x] **IR-02: Verify generated declaration nodes retain source spans.** Add a
  focused generated-function lowering regression that resolves a typed node's
  source ID back to generated source text and checks its exact literal span.
  Imported source and declaration-span tests cover the same IR path for modules.

- [x] **IR-02d: Retain named-call written order separately from operands.**
  Checked call nodes keep arguments in parameter declaration order and record
  the source-order permutation when all argument spans are available. This
  preserves the written order for diagnostics without changing the language's
  declaration-order evaluation rule. Reordered and contextual-literal call
  tests cover both orderings. The address-indexed emission bridge and the
  remaining IR-02 criteria are still open.

- [x] **IR-02e: Encode numeric operations as typed opcodes.** Replace the
  free-form operation string in checked numeric nodes with a closed opcode
  enum. Retain the exact scalar operand type for width and signedness, plus
  the explicit overflow mode. Round-trip every supported operator spelling
  and reject unknown names; retain native numeric differential coverage.
  Direct typed emission and the address-free bridge remain part of IR-02/03.

- [x] **IR-02f: Reject same-length emission shape drift.** The temporary
  syntax-shaped backend bridge now checks each paired node's expression kind
  and exact literal value after unsafe erasure, not only the total node count.
  A regression swaps equally shaped operands and requires an internal error
  instead of silently attaching checked metadata to the wrong expression.
  Replacing the remaining address-keyed bridge is still required by IR-02.

- [x] **IR-02g: Reject same-shaped symbol drift in the emission bridge.**
  Verify a reconstructed symbol still names its checked binding or resolved
  declaration before associating type metadata, including when the overall
  node count and expression kinds are unchanged. Test a substituted local
  name; preserve native imports and generated-code examples. The bridge
  itself remains temporary and address-keyed until IR-02 is complete.

- [x] **IR-02h: Reject same-shaped form-head drift in the emission bridge.**
  Compare the reconstructed form head to the retained builtin, typed numeric
  spelling, or checked callee name before associating metadata. A changed
  operator or borrow mode with unchanged operands must fail internally.
  Cover a swapped numeric opcode and preserve native generated/imported cases.
  Direct typed emission still remains the IR-02/03 endpoint.

- [x] **IR-02a: Preserve checked metadata when erasing unsafe wrappers.**
  Verify the body's stable node sequence and retained numeric type/operation
  metadata still associate with backend syntax after `#unsafe` wrappers are
  erased. This covers the existing order-based bridge; replacing that bridge's
  temporary address index remains part of IR-02.

- [x] **IR-03a: Distinguish checked syntax nodes from backend-synthesized
  expressions.** Carry a set of every checked expression into the emission
  overlay, including syntax nodes without runtime types. Do not reconstruct a
  type from syntax for those checked nodes; reserve the legacy fallback for
  expressions introduced after body lowering. Test overlay membership and
  preserve if-let/while-let plus generated Vec codegen.

- [x] **IR-03b: Drive numeric operator selection from retained metadata.**
  Carry each checked numeric node's operand type, operation, and overflow mode
  into emission, and use those values directly instead of reparsing the dotted
  operator spelling. Preserve native results for wrapping, saturating, signed,
  unsigned, wide, floating-point, and comparison operations.

- [x] **IR-03c: Resolve checked call ABIs by function identity.** Carry
  `FunctionId` through the emission overlay and select the call signature by
  that ID, not by looking up the reconstructed callee spelling. Keep the
  source-level symbol for assembly naming and diagnostics; synthesized legacy
  calls without an IR identity retain their compatibility lookup.

- [x] **IR-03d: Reject missing checked numeric metadata in emission.** A
  checked numeric expression must retain its opcode, operand type, and overflow
  mode; it cannot silently fall back to reparsing its source spelling. Preserve
  the compatibility fallback only for backend-synthesized expressions that
  were never checked as syntax nodes. Test both paths and retain the native
  numeric differential suite.

- [x] **IR-03e: Select direct checked-call symbols by function identity.**
  Keep the canonical source symbol in the resolved ABI; direct scalar calls
  now use the same `FunctionId` for both ABI layout and call target, even if
  reconstructed syntax carries a different spelling. Backend-synthesized
  calls keep the name lookup. Aggregate-specialized call paths are covered by
  IR-03f and IR-03g.

- [x] **IR-03f: Resolve aggregate-call targets by checked identity.** Pass the
  original checked expression through indirect-return and aggregate-temporary
  call paths so their ABI and emitted symbol come from `FunctionId`. Avoid
  cloning nested call syntax, which loses the emission overlay association.
  Existing indirect-return native examples, numeric differential tests, and
  reproducibility tests continue to pass. The dispatch guards are covered by
  IR-03g; backend-synthesized calls retain the name lookup.

- [x] **IR-03g: Dispatch aggregate returns by checked identity.** Resolve
  indirect-return guards against the retained `FunctionId`, including nested
  match, index, and projection paths. Keep the name lookup for syntax that the
  backend synthesized after validation. A regression uses mismatched syntax
  spelling and checked identity to verify the guard selects the checked ABI.

- [x] **IR-03h: Require retained types for checked scalar call operands.**
  Before native call lowering, verify each checked primitive, reference, or
  pointer argument has retained type metadata agreeing with the resolved ABI.
  Missing or mismatched checked metadata is an internal error; synthesized
  calls retain their compatibility path. Cover missing metadata, missing type,
  and a retained type in unit tests, plus native call examples.

- [x] **IR-03i: Verify checked scalar call results against their ABI.**
  Native emission requires the retained result type of a checked scalar call
  to agree with the resolved function return type. Missing or mismatched
  metadata is an internal error; aggregate returns are covered by IR-03n. Cover
  missing, mismatched, and valid result metadata in unit tests.

- [x] **IR-03j: Require function identity for checked direct calls.**
  A checked call to a declared function must retain its `FunctionId`; losing
  it is an internal error instead of a name-based ABI fallback. Builtin forms
  and backend-synthesized calls continue using their respective paths. Test
  missing and present identity, and run native examples.

- [x] **IR-03k: Verify checked numeric results against typed opcodes.**
  Before native instruction selection, require a retained result type matching
  the opcode's scalar type or `bool` for comparisons and logical operations.
  Reject missing or mismatched checked metadata; synthesized expressions
  remain on the compatibility path. Test arithmetic, comparison, and integer
  bitwise-not cases, then run numeric differential and native examples.

- [x] **IR-03l: Verify retained numeric operand types.** Require every
  checked numeric operand to retain a type matching the typed opcode before
  native emission; logical `&&`/`||` currently take `bool` operands even with
  an integer source qualifier. Missing or mismatched metadata is an internal
  error. Cover synthesized bypass, missing/type mismatch, valid arithmetic,
  and logical operands without changing accepted source syntax.

- [x] **IR-03m: Enforce checked identity on aggregate-call paths.** The
  indirect-return dispatch guard and aggregate destination call now reject a
  checked function call whose `FunctionId` was lost, matching ordinary scalar
  emission. Backend-synthesized calls continue using name lookup. Extend the
  mismatched-spelling identity regression to cover missing metadata.

- [x] **IR-03n: Verify aggregate call results against the resolved ABI.**
  Generalize the retained return-type check to all checked calls, including
  indirect-return calls emitted directly into aggregate storage. Reject
  missing or mismatched aggregate result metadata before writing destination
  words. Cover aggregate agreement and mismatch in unit tests and run native
  examples; synthesized calls retain their compatibility path.

- [x] **IR-03o: Store checked emission metadata by stable expression ID.**
  Make deterministic `ExpressionId`s the authoritative keys for retained
  backend types, numeric opcodes, and callees. Keep the AST-address association
  only as a temporary adapter for legacy codegen, and isolate backend-created
  expressions in a separate compatibility map. Verify every checked adapter
  resolves to exactly one retained ID and preserve native call/numeric tests.

- [x] **IR-03p: Require retained source types for casts.** Remove the native
  emitter's implicit `i64` fallback when a cast operand has no checked type;
  report an internal error instead. Explicit casts are source-only forms, so
  no backend-synthesized compatibility case is needed. Keep numeric cast
  differential and native compilation coverage passing.

- [x] **IR-03q: Require retained types for explicit ownership operations.**
  Require checked operand types for `#clone`, `#drop`, and `#forget` instead
  of silently treating missing clone metadata as a plain read or missing
  destruction metadata as `unit`. Preserve native linearity, custom clone,
  and destruction examples.

- [x] **IR-03r: Require retained operand types for floating-point emission.**
  Remove implicit `f64` selection from floating arithmetic and comparisons.
  Require the checked first operand to retain an `f32` or `f64` type before
  selecting scalar SSE instructions. Preserve the numeric differential suite
  and native floating examples.

- [x] **IR-03s: Use retained expression types for float classification.**
  Remove the separate syntax-recursive float-type walker and classify floats
  through the shared expression type path, which reads checked metadata by
  stable ID before its synthesized-expression fallback. Preserve f32/f64,
  branch, call, and aggregate native cases.

- [x] **IR-03t: Select signedness from resolved operand types.** Remove the
  syntax-recursive unsigned-expression heuristic. Native integer instruction
  selection now uses the resolved expression type; checked numeric operands
  are already required to retain that type, while synthesized expressions
  keep the centralized type fallback. Preserve division, shifts, saturation,
  and numeric differential tests.

- [x] **IR-03u: Pass numeric operand types directly to instruction selection.**
  Carry the checked opcode's `Type` into unary, binary, shift, division, and
  saturating arithmetic lowering instead of converting it to an identifier
  and reparsing it. Retain spelling-based compatibility only when the backend
  handles a synthesized expression with no checked opcode. Preserve numeric
  differential and native example coverage.

- [x] **IR-03v: Reject numeric expressions with missing operand types.** Require
  an explicit resolved scalar type before selecting unary and binary numeric
  instructions. Preserve boolean bitwise operations as their own valid scalar
  case, and keep float, wide-integer, division, saturation, and shift paths
  covered by existing native and differential tests.

- [x] **IR-03w: Pass checked types into wide-integer lowering.** Select signed
  versus unsigned 128-bit division, shifts, and saturation from the retained
  operand `Type`, rather than re-querying the AST expression. Preserve the
  wide-integer differential and native example coverage.

- [x] **IR-03x: Select comparison instructions from checked operand types.**
  Carry the resolved type into scalar, floating, and 128-bit comparisons;
  remove the now-redundant syntax-based float and unsigned classification
  helpers. Preserve native comparison and numeric differential tests.

- [x] **IR-03y: Avoid formatting checked numeric types as identifiers.** Keep
  the retained `NumericOperation`'s `Type` and opcode together through
  instruction dispatch; do not stringify the scalar qualifier only to reparse
  it. Textual qualifier parsing remains only for synthesized legacy forms.
  Preserve compilation and numeric differential coverage.

- [x] **IR-03z: Preserve checked argument identities through clone helpers.**
  Emit generated `Type-clone` helpers directly from the original operand slice
  and resolve the helper by `FunctionId`, rather than cloning its AST into a
  synthetic call. This keeps nested operand metadata available for ABI checks.
  Preserve native allocator, Cell, local-waker, and explicit-clone examples.

- [x] **IR-02n: Resolve scalar local reads by `BindingId`.** Carry binding
  names in identity order only as a temporary storage-allocation bridge, then
  read scalar and wide local slots from the symbol's checked `BindingId` and
  retained type. Keep aggregate lowering on the existing bridge until it is
  migrated. Cover nested distinct bindings and dotted local identifiers.

- [x] **IR-02o: Resolve local scalar writes by `BindingId`.** Bridge each
  legacy statement destination name to its unique checked binding, then select
  scalar/wide type and storage through that ID for initialization and
  assignment. Preserve aggregate assignment on the bridge until its place
  lowering is migrated; cover dotted mutable locals and wide values.

- [x] **IR-02p: Resolve destructuring destinations by `BindingId`.** Use the
  checked pattern symbol's binding identity for slot writes and large-value
  destructuring reads. Reject checked pattern symbols that have lost identity;
  retain spelling lookup only for synthesized syntax. Cover tuple, struct,
  array, nested, and let-else patterns.

- [x] **IR-02q: Resolve match-arm destinations by `BindingId`.** Retain binding
  identities when aggregate and enum pattern lowering collects arm bindings;
  use those IDs for stack destinations in ordinary, nested, large-value, and
  let-else match paths. Preserve source names for diagnostics only.

- [x] **IR-02r: Resolve local aggregate match sources by identity.** Use the
  checked scrutinee symbol's binding identity to select local slots for tuple,
  array, and struct match lowering, including large aggregates. Keep globals
  and synthesized expressions on their own paths.

- [x] **IR-02s: Resolve large aggregate call arguments by identity.** Use a
  checked local symbol's `BindingId` to select indirect-call argument storage;
  keep global and synthesized aggregate values on their existing paths. Cover
  large tuple, struct, and enum arguments, including nested calls.

- [x] **IR-02t: Resolve oversized aggregate copies by identity.** Use checked
  `BindingId`s when copying large local values directly into destination slots
  or projecting oversized aggregate fields. Preserve global and synthesized
  expression paths; cover nested tuple, array, and struct values.

- [x] **IR-02u: Resolve aggregate local destinations by identity.** Select
  struct, enum, tuple, and array storage for initialization and assignment via
  the checked destination binding, not the spelling-keyed compatibility map.
  Keep source-expression resolution independent and test aggregate mutations.

- [x] **IR-02v: Resolve aggregate copy sources by identity.** Use checked
  symbol identities when copying local structs, enums, tuples, and arrays, and
  when writing aggregate locals into indirect return storage. Keep global and
  synthesized expression handling on their existing paths.

- [x] **IR-02w: Resolve indirect aggregate sources by identity.** In generic
  indirect-value emission, select local source slots by checked `BindingId`
  rather than spelling, preserving global and synthesized fallbacks. Cover
  large aggregate returns through nested branches and blocks.

- [x] **IR-02x: Resolve checked local reads through unique identities.** When
  transformed checked syntax lacks a direct `BindingId` association, resolve
  the unique binding from the checked binding registry; fail if no unique
  binding exists. Keep spelling-keyed stack fallback only for synthesized
  syntax.

- [x] **IR-02y: Resolve slice initialization destinations by identity.** Select
  local slice slots through their checked binding IDs, retaining name fallback
  only for synthesized declarations. Preserve slice construction and mutable
  slice reborrow behavior in native tests.

- [x] **IR-02z: Resolve tuple and array indirect returns by identity.** Use a
  checked local's `BindingId` when copying tuple or array values into caller
  return storage, retaining global and synthesized paths. Cover nested wide
  elements and direct aggregate return cases.

- [x] **IR-02aa: Resolve borrowed local addresses by identity.** Use the
  checked place symbol's `BindingId` to locate the base slot for shared and
  mutable borrows; retain static and synthesized place handling. Cover scalar
  and aggregate borrows, including projected field reborrows.

- [x] **IR-02ab: Resolve direct slice reads by identity.** Use checked binding
  metadata for tuple-backed slice locals in length and indexing fast paths;
  keep non-local and synthesized expressions on the existing evaluation path.
  Cover immutable and mutable slices with native tests.

- [x] **IR-02ad: Resolve remaining slice value paths by identity.** Use checked
  local identities in range, mutable-split, and slice argument emission paths;
  preserve ordinary expression handling for non-local values. Cover immutable
  and mutable slice operations and function calls.

- [x] **IR-02ac: Resolve oversized array-element sources by identity.** When
  copying a large indexed element directly into aggregate storage, select its
  local array base through the checked `BindingId`. Preserve globals and
  synthesized array expressions; add a large-element indexing regression.

- [x] **IR-02ae: Resolve local array indexing by identity.** Read the base,
  length, and element layout from the checked local binding rather than the
  spelling-keyed storage map. Keep global arrays and computed array expressions
  separate, and verify bounds checks plus scalar/aggregate element reads.

- [x] **IR-02af: Resolve enum match scrutinees by identity.** Select local enum
  discriminant and payload storage through the checked scrutinee `BindingId`;
  keep global and computed enum values on their own paths. Cover nested matches
  and large payloads.

- [x] **IR-02ag: Resolve enum argument storage by identity.** Read local
  payload-enum discriminants and payload slots through checked binding IDs
  when lowering by-value arguments; preserve global and constructed enum paths.
  Cover ordinary and large payload enums.

- [x] **IR-02ah: Resolve array-assignment storage by binding identity.** Route
  `#set-index` target storage and element type through the checked local
  binding map rather than the syntax-name maps. Preserve bounds checks,
  aggregate element layout, and static/global paths. Exercise scalar and
  multiword array mutation in native examples.

- [x] **IR-02ai: Resolve projected aggregate writes by binding identity.**
  Use checked local storage and type lookups for tuple, struct-field, and enum
  payload assignments instead of syntax-name maps. Preserve checked member
  declarations and native layouts; exercise each write form in native tests.

- [x] **IR-02aj: Resolve by-value aggregate returns by binding identity.**
  Load local tuple, array, struct, and payload-enum return values through
  checked binding storage. Keep global and constructed return paths distinct;
  cover scalar-sized and multiword layouts in native execution tests.

- [x] **IR-02ak: Resolve local tuple and struct projections by identity.**
  Use the checked source expression's binding ID for local `#get` storage and
  derive owner types from retained expression metadata. Preserve global,
  referenced, and constructed projection paths; test scalar and multiword
  field reads.

- [x] **IR-02al: Resolve aggregate call arguments by binding identity.**
  Push local array, tuple, and struct arguments from storage selected by the
  checked value expression's binding ID. Preserve global and constructed
  values, argument evaluation order, and ABI word order; test narrow and
  multiword argument layouts.

- [x] **IR-03: Emit typed scalar expressions and calls.** Route backend
  emission through IR-02, then extend to aggregates and control flow. Remove
  corresponding AST type reconstruction as each path migrates; do not silently
  fall back when a migrated node lacks type information. Acceptance: numeric
  differential tests, every native example, reproducibility, and benchmark
  smoke tests pass with unchanged source syntax and one validation pass.

- [x] **IR-03ad: Emit checked scalar literals from retained IR values.** Store
  literal payloads in expression metadata and consume them for integer, float,
  character, and string emission. Checked literal nodes without a retained
  payload or with a mismatched literal kind must fail internally; synthesized
  backend expressions may retain their narrow syntax fallback. Test the
  metadata contract and preserve the full native-example suite. The full
  serial test suite passes.

- [x] **IR-03ae: Emit boolean constants from checked IR values.** Retain
  `true`/`false` as checked constant payloads instead of relying on the
  name-based symbol special case. Reject a lost or mismatched boolean value and
  preserve native examples and typed-constant metadata tests. The full serial
  test suite passes.

- [x] **IR-03aa: Keep syntax type reconstruction off checked nodes.** When a
  source expression has a stable typed identity but its retained type is
  missing, do not infer a replacement from its surface syntax. Keep the
  narrow reconstruction path for backend-synthesized expressions only; test
  checked-versus-synthesized identity and run all native examples.

- [x] **IR-03ab: Reject missing types on checked local symbol reads.** Do not
  recover a checked binding's scalar/storage classification from the legacy
  name-keyed type table when its retained node type is missing. Keep that
  compatibility lookup only for synthesized nodes; test both paths and retain
  numeric and native-example coverage.

- [x] **IR-03ac: Reject missing metadata on checked scalar expressions.** In
  native expression dispatch, distinguish backend-synthesized AST from checked
  source nodes. A checked node without its emission record must fail internally
  instead of falling through to syntax-based operator or call resolution;
  preserve the narrow synthesized-node path and test both cases.

- [x] **IR-03af: Pass static aggregates by checked identity.** Use `GlobalId`
  when pushing global arrays, tuples, structs, and payload enums as call
  arguments. Preserve local storage and evaluation order; cover direct and
  indirect ABI layouts in native linking tests.

- [x] **IR-02am: Keep function specialization before the checked boundary.**
  Reject generic function/type declarations even for programmatically built
  `Program` values, matching the source grammar's concrete-only rule. Remove
  post-validation function monomorphization and ABI reconstruction from native
  emission; generated concrete functions remain ordinary checked declarations.
  Test the checked API rejection and preserve generated-function/native tests.

- [x] **IR-02an: Never recover typed local identity by spelling.** If a
  checked local symbol has retained a type but lost its binding ID, fail
  internally before consulting the legacy local-name map. Keep name-based
  lookup for inline-assembly operands and backend-synthesized syntax that has
  no language binding; test both paths and native local/aggregate emission.

- [x] **IR-02ao: Keep checked unsafe nodes in the emission bridge.** Reconstruct
  function bodies without erasing `#unsafe` wrappers, associate their stable
  checked IDs in the ordinary postorder walk, and let the backend erase their
  runtime effect at expression emission. Keep compile-time global-initializer
  normalization separate; verify wrapper identity and unchanged native output.

- [x] **IR-02ap: Key retained expression spans by stable IDs.** Store checked
  expression spans under their deterministic `ExpressionId` rather than AST
  addresses. Keep statement spans separate until statements have stable IDs;
  use only a temporary address adapter while legacy AST binding-span extraction
  remains. Verify imported/generated source slices and preserve exact compiler
  diagnostics across the full suite. The complete serial test suite passes.

- [x] **IR-02aq: Assign stable statement identities and retain them in IR.**
  Traverse function bodies in deterministic source order, including nested
  blocks, loops, and labeled statements. Key checked statement spans by
  `StatementId`, carry IDs on typed instructions, and expose them in the typed
  IR dump. Keep an address adapter only while matching legacy AST statements;
  test density, repeat-parse stability, nested coverage, and exact spans. The
  complete serial test suite passes.

- [x] **IR-02ar: Lower expressions using a stable-ID traversal stream.**
  Precompute each function's deterministic expression-ID order, then have the
  typed body builder consume IDs and retrieve types/spans directly by ID rather
  than resolving every AST node through a pointer map. Assert complete
  consumption and preserve node order, contextual typing, generated/imported
  spans, and emission-bridge shape checks. The full serial test suite passes.

- [x] **IR-02as: Preserve resolved declaration IDs in emission metadata.**
  Carry resolved field, variant, aggregate, and global declaration identities
  across the checked-body emission bridge instead of retaining only names.
  Verify a field projection keeps its exact declaration ID under its stable
  expression ID.

- [x] **IR-02at: Select named struct fields by checked declaration identity.**
  Use the retained field owner and index for native `#get` lowering across
  locals, globals, references, constructors, and aggregate results. Validate
  owner/name consistency and reserve spelling lookup for synthesized syntax.
  Test retained owner metadata and native aggregate access.

- [x] **IR-02au: Read checked globals by declaration identity.** Retain each
  global's source name under its `GlobalId` in the emission bridge and select
  native global storage from that ID for checked symbol reads. Reject missing
  global identity rather than silently falling back to spelling; keep the
  narrow fallback for synthesized syntax.

- [x] **IR-02av: Preserve expression spans in emission metadata.** Carry each
  checked node's exact source span alongside its `ExpressionId` through the
  backend bridge. Use retained locations in internal member-identity errors
  and verify a field selector maps back to its exact source token.

- [x] **IR-02aw: Emit unit enum variants by checked identity.** Resolve a
  checked unit-variant value through its `VariantId` and owner enum instead of
  scanning all enum declarations by spelling. Preserve name lookup only for
  synthesized syntax; verify stable owner metadata and native enum examples.

- [x] **IR-02ax: Lower direct enum match arms by checked identity.** Resolve
  unit and payload variant labels through the pattern's `VariantId`, use the
  retained discriminant and payload types, and verify that the variant owner
  matches the scrutinee enum. Keep or-pattern expansion as a separate lowering
  path; preserve every native example and constructor/match identity coverage.

- [x] **IR-02ay: Lower enum or-pattern alternatives by checked identity.**
  Resolve each unit or payload alternative through its own `VariantId`, use
  its retained discriminant and payload types, and reject owner mismatches.
  Preserve generated scope bindings and verify all native enum/or-pattern
  examples.

- [x] **IR-02az: Project enum payloads by checked variant identity.** Resolve
  `#get-payload` selectors through their `VariantId` in both scalar and
  oversized aggregate projection paths. Validate the owner enum and use the
  retained discriminant and payload layout; preserve all native examples.

- [x] **IR-02ba: Lower enum let-else patterns by checked identity.** Resolve
  direct, fieldless-or, and payload-or let-else alternatives through their
  `VariantId`, checking each owner against the matched enum. Preserve payload
  binding layout and validate the complete native-example corpus.

- [x] **IR-02bb: Borrow enum payloads by checked variant identity.** Resolve
  the `#borrow` projection's variant through its `VariantId` and validate
  its owner against the referenced enum before selecting the payload offset.
  Preserve native payload-borrow and projection behavior.

- [x] **IR-02bc: Store enum locals by checked variant identity.** Resolve unit
  and payload enum initializers through their head node's `VariantId`; verify
  the owner enum and consume its discriminant and payload types. Preserve
  generic-expression fallback only when the constructor is not a variant.
  Validate all native examples.

- [x] **IR-02bd: Emit enum constructors by checked variant identity.** Resolve
  constructor heads through `VariantId` and consume its owner, discriminant,
  and payload types directly. Keep the enum's maximum payload layout for
  register padding, without re-finding the selected variant by spelling.
  Validate all native examples.

- [x] **IR-02be: Return large enum constructors by checked identity.** Write
  indirect enum results using the constructor head's `VariantId`, owner,
  discriminant, and payload fields. Reject owner drift while retaining local
  and global enum-copy paths; validate all native examples and aggregate
  linking.

- [x] **IR-02bf: Store large enum arguments by checked identity.** Resolve
  large payload-enum argument constructors through the head's `VariantId`,
  verify the owner enum, and store the retained discriminant and field layout.
  Preserve aggregate/thread native coverage.

- [x] **IR-02bg: Store unit enum values in aggregate slots by identity.**
  Resolve checked unit variants through `VariantId` when writing indirect
  aggregate storage, validate the owning enum, and zero the remaining payload
  words. Preserve native enum and aggregate examples.

- [x] **IR-02bh: Lower indirect enum values by checked identity.** Use
  `VariantId` for unit and payload values written into indirect aggregate
  storage, including payload type recovery for `#get-payload`. Validate the
  owner enum and preserve enum/aggregate native execution.

- [x] **IR-02bi: Project global structs by checked global identity.** Resolve
  the base of a global `#get` through its `GlobalId` before selecting field
  storage; preserve local and synthesized fallbacks. Validate field identity
  and all native examples.

- [x] **IR-02bj: Project global tuples by checked global identity.** Resolve a
  tuple-valued global base through its retained `GlobalId` before loading
  tuple words. Preserve local tuple slots and validate static aggregate and
  full native examples.

- [x] **IR-02bk: Index global arrays by checked global identity.** Resolve a
  checked global array base through its retained `GlobalId` before selecting
  static storage. Preserve local and computed array paths, bounds checks, and
  scalar/multiword element loading; validate global array native examples.

- [x] **IR-02bl: Return global structs by checked global identity.** Resolve
  global struct sources through their retained `GlobalId` before copying into
  indirect return storage. Preserve local and constructed values; exercise
  large static struct returns and nested aggregate layouts.

- [x] **IR-02bm: Return global tuples by checked global identity.** Resolve
  tuple sources by `GlobalId` for both register and indirect returns. Preserve
  tuple locals and constructors; cover nested and multiword static tuples.

- [x] **IR-02bn: Copy global aggregates by checked identity.** Resolve global
  aggregate sources through `GlobalId` before copying their words into
  indirect aggregate destinations. Preserve locals, dereferences, and
  constructors; cover nested static aggregate values.

- [x] **IR-02bo: Return global enums by checked identity.** Resolve global
  enum values through `GlobalId` in both direct and indirect return paths.
  Preserve local enum layouts and constructor lowering; cover static enums
  with unit and multiword payload variants.

- [x] **IR-02bp: Return global arrays by checked identity.** Resolve static
  array sources through `GlobalId` for register and indirect returns. Preserve
  local arrays and literal constructors; cover scalar, nested, and multiword
  array elements.

- [x] **IR-02bq: Initialize aggregate temporaries from checked globals.** Use
  `GlobalId` when copying a global aggregate into temporary/local slots.
  Preserve local, dereference, projection, and constructor sources; validate
  static aggregate copies across native examples.

- [x] **IR-02br: Return register-sized global structs by checked identity.**
  Resolve static struct sources through `GlobalId` before loading return
  registers. Preserve local struct and constructor paths; cover mixed scalar,
  float, and nested-field layouts.

- [x] **IR-02bs: Match static aggregates by checked identity.** Resolve static
  enum and aggregate scrutinees through `GlobalId` before staging their data
  for pattern matching. Preserve local and computed scrutinees; cover payload
  enums and nested/multiword aggregate patterns.

- [x] **IR-02bt: Project large global aggregates by checked identity.** Use
  `GlobalId` to select static sources in oversized array-index and struct/tuple
  field projections. Preserve local and computed sources; validate large
  nested projections and bounds behavior.

- [x] **IR-02bu: Borrow and copy reference fields by checked identity.** Use
  retained `FieldId` metadata for projected field borrows and oversized
  reference-field copies instead of re-resolving the selector by spelling.
  Preserve synthesized lowering; test reference reborrows and large fields.

- [x] **IR-02bv: Select oversized struct projections by checked identity.**
  Use retained `FieldId` metadata when computing the source offset for a
  large projected struct field copied into slots. Preserve tuple indexing and
  synthesized syntax; validate large static and local projections.

- [x] **IR-04: Migrate ownership analyses to shared typed control flow.**
  Use stable binding/place identities and explicit branches, joins, loops,
  returns, and unreachable paths. Retain loan and consumption origin spans.
  Acceptance: existing borrow/linearity tests and exact UI spans remain valid;
  add branch/loop aliasing and aggregate-reference propagation regressions.
  Checked referent/place transfer must ultimately replace the remaining
  syntax-side reborrow handling.

- [x] **IR-04a: Resolve legacy reborrow parents from typed places.** For the
  compatibility borrow checker used during normal compilation, associate each
  borrow expression with its typed flow `Place` and recover projected parent
  bindings from stable checked IDs. Keep syntax projection recovery only for
  standalone legacy checks; test mutable field reborrows, disjoint siblings,
  mutable slices, and failure when checked body/flow metadata is absent.

- [x] **IR-04b: Check reads of Copy projections after linear moves.** Typed
  consumption checks must reject reading a Copy field or element after its
  linear owner was consumed, and format diagnostics from checked binding and
  projection identities. Keep syntax diagnostics authoritative until typed
  transfer and exit diagnostics match their coverage and source precision.

- [x] **IR-04c: Make typed flow authoritative for linear errors.** Evaluate
  typed release, consumption, and exit obligations first. Use the syntax
  checker only as a diagnostic refinement when it identifies the same checked
  binding/projection, or as a fallback for a construct not yet modeled in
  typed flow. Preserve precise spans and test branch, loop, and aggregate cases.
  Refinement requires overlapping checked-place subjects or the same primary
  source span. The full serial test suite passes.

- [x] **IR-04cw: Preserve direct-borrow operator spans in typed diagnostics.**
  Map two-argument `#borrow` and `#borrow-mut` loan origins to the operator
  token, just as scoped borrows already do. Test the exact source slice so
  future typed-flow diagnostics underline the offending operation, not its
  surrounding form.

- [x] **IR-04: Permit bounded mutable-slice element reborrows.** Track a
  `#slice-mut-idx` child loan while its parent slice is suspended, restore the
  parent after explicit release, and reject parent use or overlapping shared
  borrows. Add acceptance and rejection regressions.

- [x] **IR-04: Retain split-slice origins through tuple patterns.** A checked
  `#slice-mut-split` now carries its source loan into both tuple positions so
  each destructured half retains its referent and original borrow span.
  Complete disjoint-range transfer remains part of IR-04.

- [x] **IR-04: Check reference-bearing aggregate call arguments.** Include
  bound aggregate origins, not only direct reference bindings, when comparing
  checked call arguments. Treat the aggregate's stored loans as coexisting and
  retain exact borrow spans in conflict diagnostics. Correlated alternatives
  across conditional aggregate values remain for the full ownership transfer.

- [x] **IR-04: Preserve aggregate storage paths through projected call values.**
  Carry the checked field, tuple, payload, or index path with each aggregate
  loan and select matching origins when a call receives a projected value.
  Preserve remaining nested paths and add a conflicting projected-reference
  regression.

- [x] **IR-04: Verify loop-local loan cleanup at typed loop headers.** Check
  that a reference created and explicitly released within each iteration has
  no origin at the loop condition or back edge, and that an outer mutable loan
  remains live across the same fixed point. Both loops pass borrow checking.
  This covers loop-state propagation; full ownership transfer remains open.

- [x] **IR-04: Classify contextual aggregate constructor operands on typed flow.**
  Use the checked array/tuple arity to distinguish a contextual first value
  from an explicit type operand. Track that first value as a linear transfer
  and include it in aggregate loan provenance. Regression tests reject a
  later release of the transferred value. The syntax-side ownership checker
  still needs complete migration for accepting every valid contextual move.

- [x] **IR-04: Accept bare contextual aggregate moves in legacy ownership.**
  A bare first operand of `#array` or `#tuple` cannot be an explicit type
  expression, so consume it in the syntax-side checker. Test accepted
  single transfers and rejected later reuse. List-valued contextual operands
  are handled in the following checked-metadata bridge.

- [x] **IR-04: Classify list-valued contextual constructor moves.** Reuse
  checked expression types and constructor arity in the transitional linear
  checker, avoiding a syntax guess when the first value is itself a list.
  Test both accepted transfers and rejected reuse for arrays and tuples.
  This address-indexed bridge must disappear when IR-04 is complete.

- [x] **IR-04: Verify contextual aggregate loan slots.** Extend typed-flow
  provenance tests to contextual tuple and array constructors and confirm
  positional destructuring retains separate first and second borrow origins.

- [x] **IR-04: Preserve tuple loan slots during call-expression analysis.**
  Attach tuple storage paths to loans created by tuple constructors in the
  call-argument provenance walker. Transfer only matching paths through
  block-local destructuring and projected values. Test a conflicting extracted
  borrow and independent sibling references without changing ownership flow.
  Array, struct, and enum transfer parity remains under the broader IR-04 item.

- [x] **IR-04: Preserve array loan slots during call-expression analysis.**
  Transfer indexed borrow paths through array constructors and destructuring
  before comparing call arguments. Reject a mutable borrow that aliases an
  extracted element while accepting a sibling element borrowed from another
  owner. Keep dynamic-index overlap conservative.

- [x] **IR-04: Preserve provenance through reference-returning call arguments.**
  Resolve the possible referent origins of a checked reference- or
  slice-returning call from its arguments, including aggregate-held references,
  before comparing that result with sibling call arguments. Retain the original
  borrow span and reject overlapping mutable access without rejecting disjoint
  referents.

- [x] **IR-04: Preserve struct-field loan paths in call analysis.** Attach
  declaration-identity field slots to checked struct-constructor borrows and
  distribute only matching paths through struct patterns. Reject a conflicting
  extracted field borrow while allowing a disjoint sibling field.

- [x] **IR-04: Preserve enum-payload loan paths in call analysis.** Attach
  variant and payload-index identities to enum-constructor borrows, then
  transfer matching loans through `#let-else` and match patterns. Reject a
  conflicting payload borrow and accept a disjoint referent.

- [x] **IR-04: Preserve nested aggregate loan paths through patterns.** Keep
  every field/payload/index segment while recursively constructing aggregates
  and destructuring nested patterns. Reject overlapping extracted references
  and accept an independent referent after a multi-level projection.

- [x] **IR-04: Propagate direct loop-break borrow results into call analysis.**
  Collect reachable value-carrying `#break`/`#break-to` exits for a loop
  expression, without mistaking nested-loop exits for the outer result. Retain
  borrow spans and reject conflicting call arguments while accepting disjoint
  referents.

- [x] **IR-04: Cover labeled loop-break reference results.** Exercise the
  `#label`/`#break-to` path through the same checked loan transfer and verify
  its borrow origin is reported when a sibling mutable argument overlaps.

- [x] **IR-04: Find loop-break results nested in branch expressions.** Walk
  checked `#if`, `#match`, and block expressions inside loop bodies so a
  value-carrying break in a branch retains its borrow origin. Do not mistake
  inner-loop exits for outer-loop results.

- [x] **IR-04: Propagate loans through explicit array-of construction.**
  Treat `#array-of` as an aggregate value with an explicit type operand and
  indexed reference slots, not as an opaque expression. Test that positional
  destructuring recovers each distinct borrow origin. Broader enforcement of
  indirect aggregate loans remains part of IR-04.

- [x] **IR-04: Propagate repeated shared-reference origins.** Preserve a
  wildcard index origin for nonempty `#array-repeat` values so any concrete
  projection or destructured element retains the borrow. Empty repeats retain
  no loan. Test both cases, including the wildcard/concrete slot transfer.

- [x] **IR-04: Keep one-slot repeat provenance precise.** Record index zero
  rather than a wildcard for length-one repeats, so releasing that only
  element clears its typed loan origin. The legacy borrow pass still rejects
  some later owner accesses; the following bridge covers tracked projections.

- [x] **IR-04: Retire exactly tracked projected reference loans.** The
  transitional borrow pass now recognizes static typed-literal indices and
  releases only field loans still held by the aggregate; unknown projections
  remain conservative. Keep empty loan records so a later aggregate drop
  cannot accidentally end a copied alias's loan. Cover one-element mutable
  repeats, multiple shared fields, aliases, and a native owner write. Full
  structural identity and path-sensitive release handling remain in IR-04.

- [x] **IR-04: See array constructor borrows at call boundaries.** Include
  `#array-of` and `#array-repeat` in typed call-argument borrow collection,
  preserving the originating borrow's span when a later mutable argument
  conflicts. Test both forms with exact second-argument diagnostics.

- [x] **IR-04: Do not retain a zero-length repeated borrow.** The value
  operand is evaluated, but a zero-element array stores no reference. Match
  typed call-argument checking to aggregate loan transfer and accept a later
  mutable argument borrowing the same owner. Keep nonempty repeats checked.

- [x] **IR-04: Invalidate explicitly released reference places.** Closing
  a reference loan with `#drop` or `#forget` must not leave its handle usable
  afterward. Track explicit releases of reference-bearing Copy places in the
  transitional linear pass, including projections and clones, while retaining
  Rust-like reuse of plain Copy scalars. Cover the stale-reference regression
  and keep ordinary linear assignment/replacement behavior intact.

- [x] **IR-04: Retain typed provenance across reference-returning calls.**
  Conservatively union loan origins reachable through checked call arguments
  when the result is a direct reference or slice. Clear argument aggregate
  storage paths for a direct reference result and keep original borrow spans.
  Test direct and aggregate arguments. Precise interprocedural summaries and
  alias-sensitive returns remain in the full IR-04 migration.

- [x] **IR-04: Carry slice borrow provenance through derived views.** Preserve
  the original array borrow and mutability through slice creation, range, and
  element-reference expressions. Test immutable range/index chains and a
  mutable indexed write. Bound mutable element reborrows remain in IR-04.

- [x] **IR-04a: Represent expression branches and match arms explicitly.**
  Lower `if`, `match`, and each match arm to dedicated typed-body node kinds;
  retain condition/scrutinee/result node IDs and the pattern binding identities
  scoped to each arm. Round-trip syntax unchanged and test branch node kinds,
  binding identity, and arm scopes. Ownership passes have not yet migrated.

- [x] **IR-04b: Preserve reference releases across block and branch joins.**
  A block now propagates consumption of pre-existing references while keeping
  its new bindings scoped. Branch joins merge only loans active on at least one
  path, retaining their origin diagnostics, and merge aggregate reference
  provenance instead of taking the first branch. Tests cover release on both
  branches, release on one branch, and aggregate-held references; a native
  example exercises the accepted path. The full typed-CFG ownership migration
  remains open in IR-04.

- [x] **IR-04c: Reject references escaping block-local owners.** Track names
  visible at each borrow-checking scope, compute block-result provenance through
  local aliases and destructuring, and reject out-of-scope owners retained by
  bindings or passed to reference-valued function parameters, including type
  aliases of references. Preserve scalar
  block results and references to outer owners. Add a source-underlined UI
  regression and positive/negative borrow tests. This is a transitional AST
  check; stable place identities and complete ownership CFG remain in IR-04.

- [x] **IR-04d: Propagate aggregate reference origins through match arms.**
  Collect all reference-bearing field origins of a matched aggregate, bind
  them conservatively to arm payload names for arm checking and match-result
  provenance, including direct enum and struct constructors, and reject
  returns that would expose a local owner's reference.
  Cover the rejected enum-payload escape with an exact UI span and a safe
  parameter-backed return with a native example. This remains an AST-side
  safeguard until match arms use typed binding/place identities in IR-04.

- [x] **IR-04e: Retain shared typed control flow before ownership checks.**
  Lower checked bodies before linear and borrow analysis, then build a stable,
  address-free flow graph with edges for expression branches and matches,
  short-circuit operators, loops, labeled breaks/continues, returns, and
  divergence. Expose the graph in the typed-IR debug dump. As a first consumer,
  run definite-binding analysis over `BindingId` at joins and loop fixed points;
  a reachable read or assignment must be bound on every incoming path. Tests
  cover branch edges, labels, and divergent paths. Full move/loan analysis on
  this graph remains open in IR-04.

- [x] **IR-04f: Model ordered match and guard fallthrough in typed flow.**
  Dispatch patterns in source order, branch to the next arm when a pattern or
  guard fails, and bind an arm's payloads only on its successful edge. Keep
  exhaustive failure diverging rather than falling through to following code.
  Test guarded fallthrough and stable binding scopes. Move and loan transfer
  functions on this graph remain open in IR-04.

- [x] **IR-04g: Retain binding liveness on typed control flow.** Compute
  backward may-liveness of stable `BindingId`s at each graph node, including
  guarded match fallthrough and loop back edges. Distinguish whole-local
  replacement, which kills the old value, from projected writes, which still
  need the aggregate. Keep liveness in checked declarations and expose it in
  the debug IR dump. Tests cover guarded bindings, assignments, and loops.
  This identifies future reads, not ownership cleanup or loan lifetimes;
  those remain open in IR-04 and ASYNC-01.

- [x] **IR-04h: Resolve typed place identities for reads and writes.** Build
  local/global-rooted paths from checked nodes and assignment projections,
  using owner-qualified field/variant IDs and structural tuple/array indices.
  Distinguish dotted binding names from field paths and dynamic indices from
  concrete elements. Flow assignments now retain these paths; liveness and
  definite-binding checks consume their roots. Test named-owner collisions,
  array writes, enum payloads, and punctuation. Move/loan overlap analysis on
  these places remains open in IR-04.

- [x] **IR-04i: Reject overlapping direct call-argument borrows.** Compare
  resolved places for bare `#borrow` and `#borrow-mut` arguments passed to the
  same call. Two shared borrows may coexist; a mutable borrow cannot overlap
  another argument's borrow. Parent/child paths and dynamic indices overlap,
  while distinct field IDs do not. Report the second borrow's exact span and
  label the first; cover shared/shared, mutable/shared, disjoint fields, and a
  source-underlined UI error. Borrows hidden inside aggregate expressions or
  retained in bindings still need full typed loan analysis in IR-04.

- [x] **IR-04j: Track call-argument borrows through pure value construction.**
  Preserve direct borrow origins through struct and tuple constructors and
  expression-valued conditionals, comparing only borrows on the same execution
  path. Reject overlapping mutable loans across argument values with exact
  source spans, while permitting disjoint fields and branches. Binding aliases,
  borrow-returning calls, and general flow-sensitive loans remain in IR-04.

- [x] **IR-04k: Retain local block-result borrow origins.** Follow immutable
  binding IDs through value-producing blocks when checking call arguments;
  invalidate a bound origin after assignment rather than reusing stale data.
  Cover nested array/enum constructors and match arms, with exact borrow-site
  labels for a block alias. Mutable bindings are partially covered by IR-04l;
  control-flow-joined bindings and borrow-returning calls still require the
  full IR-04 loan transfer.

- [x] **IR-04l: Preserve initial origins of mutable block bindings.** Extend
  the value-block call check to `#let-mut` bindings, while continuing to
  invalidate an origin after assignment. Check both overlapping and disjoint
  call arguments. Replacing a reference-bearing binding is prohibited by the
  language, so this does not add reference reassignment or loop dataflow.

- [x] **IR-04m: Deduplicate equivalent typed borrow paths.** Identify path
  states by their resolved places and mutability, retaining the first source
  origin for diagnostics. Apply the path budget to unique states rather than
  the raw Cartesian product, so repeated branches do not reject valid code.
  Still reject genuinely excessive distinct paths with a bounded diagnostic.

- [x] **IR-04n: Retain value origins on typed ownership transfers.** Bind,
  assignment, and pattern flow actions now carry the checked `NodeId` of the
  value supplying them, including match scrutinees and destructuring sources.
  Verify these IDs and their exact spans in focused tests. This supplies the
  origin needed by later move/loan transfer without reconstructing syntax or
  inferring it from predecessor graph shape.

- [x] **IR-04o: Represent direct borrows as typed flow events.** Carry the
  borrowed resolved place, shared/mutable mode, and checked source node on
  graph actions for direct `#borrow` and `#borrow-mut`. Preserve liveness and
  definite-binding behavior, and test exact source spans. Indirect referent
  provenance and live-loan transfer still remain in IR-04.

- [x] **IR-04p: Compute direct loan origins on typed flow.** Add a forward
  may-analysis that retains direct borrow places and source spans through
  bindings, simple aliases, and conditional results; union origins at joins
  and clear a dropped binding without clearing its aliases. Expose the states
  in the typed-IR debug dump. This is observational groundwork, not yet an
  enforcing replacement for the lexical borrow checker; aggregate values are
  covered by IR-04q, while indirect referents, scopes, and full transfer remain
  in IR-04.

- [x] **IR-04q: Retain aggregate-held loan origins in typed flow.** Walk
  checked struct, enum, tuple, and array constructors, syntax field groups,
  and value-block results when computing a binding's direct origins. Test
  exact source borrow spans inside struct fields and enum payloads. Individual
  destructuring slots are covered by IR-04r; indirect referents remain in IR-04.

- [x] **IR-04r: Map aggregate loan origins through destructuring.** Tag each
  direct origin with its owner-qualified field, tuple, array, or variant-payload
  storage path. Transfer only matching origins to pattern bindings, preserving
  exact source spans. Test reordered named struct construction, tuple and array
  positions, and distinct enum variants so payloads never cross match arms.
  Alias-aware indirect referents and enforcing loan conflicts remain in IR-04.

- [x] **IR-04s: Verify branch-join loan release.** Exercise the shared typed
  flow with a direct reference dropped on both paths and on only one path.
  Require the forward loan state to be empty at the first join and retained at
  the second. Scope exits are covered by IR-04t; indirect origins and
  enforcement remain in IR-04.

- [x] **IR-04t: End typed loan state at lexical scope exits.** Retain explicit
  scope-exit actions for value blocks, match arms and guard failure, loop
  bodies, and for-loop initializer scopes. Route break, continue, and return
  through cleanup for the scopes they leave. Clear binding-held direct origins
  at those actions; test block fallthrough, break, continue, and for-range
  scope boundaries. Indirect provenance and enforcing conflict checks remain.

- [x] **IR-04u: Resolve simple reference aliases at call arguments.** Seed the
  typed call-borrow preflight from flow-state bindings with one known direct
  reference origin. Reject an overlapping mutable argument using the original
  borrow as a secondary source label; allow a disjoint owner. Skip origin
  dataflow for functions without calls or reference bindings. Multi-origin
  aliases, aggregate symbols, and indirect referents remain in IR-04.

- [x] **IR-04v: Model projected replacement in typed loan state.** On a
  statically known local field, tuple slot, payload, or array element write,
  remove origins stored under that slot and prefix new value origins with the
  projection. Keep old origins for dynamic indices, whose target is uncertain.
  Unit-test static replacement, disjoint-slot preservation, and dynamic-index
  conservatism. The language currently rejects replacing reference-containing
  fields, so this is a flow-transfer invariant, not a new source capability.

- [x] **IR-04w: Propagate stored borrow origins through aggregate reads.**
  Reading a checked `#get`, `#get-payload`, or `#index` projection now selects
  the matching direct origins from its aggregate value and removes the storage
  slot prefix. Dynamic indexes conservatively select any indexed origin.
  Verify a reference field read retains its original borrow span. Indirect
  referents and full loan enforcement remain in IR-04.

- [x] **IR-04x: Check joined reference origins at call arguments.** Convert
  every direct origin of a reference binding at a typed-flow join into a
  bounded call-argument alternative instead of ignoring multi-origin aliases.
  A conflict in any alternative is rejected; disjoint arguments remain valid.
  Test two joined origins and the conflict/disjoint cases. Correlated branch
  alternatives and indirect referents still need the complete IR-04 analysis.

- [x] **IR-04y: Resolve projected call borrows through known references.**
  For a direct `#borrow` of a `#get`, `#get-payload`, or `#index` place rooted
  in a reference binding, append its checked projection to each known direct
  referent origin before comparing call arguments. Keep unknown origins on the
  conservative compatibility path. Test a reference-to-struct field projecting
  to the original owner's place and an overlapping mutable argument. Longer
  known chains are covered by IR-04z; full enforcement remains in IR-04.

- [x] **IR-04z: Follow bounded chains of known reference origins.** Resolve
  projected call borrows through successive reference bindings until they
  reach a concrete owner place, preserving owner-qualified projection order.
  Reject excessive alternatives, detect cycles without recursing forever, and
  retain the conservative fallback for an unknown origin. Test a nested
  reference-to-struct chain and a synthetic cycle. Full typed loan enforcement
  remains open in IR-04.

- [x] **IR-04aa: Represent direct local releases in typed flow.** Lower
  `#drop` and `#forget` of a local to checked release actions with binding and
  expression IDs. The observational loan transfer clears only that binding,
  preserving live aliases; tests cover both forms. Projected releases and
  full ownership enforcement remain in IR-04.

- [x] **IR-04ab: Track projected releases by checked place.** Extend release
  actions to resolved local field, payload, tuple, and array places. Clear only
  origins stored below the selected projection; preserve unrelated fields and
  conservatively retain dynamic-index alternatives. Test sequential release
  of two aggregate-held references. Indirect release and full conflict checks
  remain in IR-04.

- [x] **IR-04ac: Retain explicit clones as checked flow actions.** Record the
  resolved place and exact expression ID for `#clone` rather than treating it
  as an undifferentiated evaluation. Verify action metadata and test a field
  clone with its source span; computed operands and ownership enforcement
  remain in IR-04.

- [x] **IR-04ad: Retain checked values on return edges.** Carry the result
  node ID on each typed return action and verify it refers to a checked value.
  Preserve evaluation-before-cleanup order and test the exact source span of
  the returned binding. Actual move/loan transfer still remains in IR-04.

- [x] **IR-04ae: Retain checked values on break edges.** Carry and verify the
  optional loop-result node ID on typed `#break` actions. Test the value break
  in the native loop-result example; move/loan transfer remains in IR-04.

- [x] **IR-04af: Transfer control values before lexical cleanup.** Order
  return and break edges as value evaluation, transfer action, then scope-exit
  actions. Check return cleanup reaches function exit, and test a live loan at
  a value break plus a nested return's cleanup edge. This keeps origin state
  visible to future ownership transfer; actual enforcement remains in IR-04.

- [x] **IR-04ag: Model the function root local scope.** Lower top-level
  instructions through the same scope builder as nested blocks, so local
  bindings clear after return transfer or fallthrough. Test that a returned
  dereference sees its live loan at transfer and that the root cleanup clears
  it before function exit. Parameters remain separately seeded at entry;
  full ownership enforcement remains in IR-04.

- [x] **IR-04ah: Preserve referent identity in stored projected borrows.**
  Resolve known reference-binding chains when recording a direct borrow of a
  projected field, retaining the original owner and owner-qualified path in
  typed loan state. Keep unknown parameters and cyclic paths conservative.
  Test a two-link reference chain and exact borrow metadata. This extends the
  observational transfer; complete enforcing ownership remains in IR-04.

- [x] **IR-04ai: Retain explicit consumption on typed flow.** Propagate
  checked places and all release spans for `#drop`/`#forget` through branch joins;
  clear them on rebinding, definite replacement, and lexical scope exit.
  Expose this observational state in the typed-IR dump and test single- and
  dual-origin branch joins plus root cleanup. Moves through expressions and
  calls, conflict enforcement, and exactly-once exit checks remain in IR-04.

- [x] **IR-04aj: Distinguish definite from possible explicit release.** Add a
  backward-edge-safe must-analysis over checked places, intersecting reachable
  predecessor states and killing facts on rebinding, replacement, and scope
  exit. Test one-sided and two-sided branch releases plus a zero-iteration
  loop. Retain all possible origin spans separately for future diagnostics.
  This does not yet classify Copy versus linear values or transfer implicit
  moves, so the existing checker remains the enforcing path.

- [x] **IR-04ak: Enforce overlapping explicit linear releases by place ID.**
  Share the existing structural linear-type classifier with typed flow and
  reject a `#drop`/`#forget` of a linear parent after releasing a child, or
  other overlapping checked places. Keep Copy-valued field releases harmless
  and preserve source-underlined diagnostics with the first release labeled.
  The syntax checker still handles implicit moves and exit obligations; full
  typed ownership enforcement remains in IR-04.

- [x] **IR-04al: Complete structural owners through their linear fields.**
  At return and lexical exit, treat an implicitly linear struct, tuple, or
  array as consumed when each linear component has been consumed; keep a
  `#linear` owner's own explicit obligation. Permit rebinding after complete
  field consumption and clear stale child moves on replacement. Use the same
  type metadata in nested blocks, and stop counting repeated Copy field reads
  or releases as moves while still rejecting access after the owner moves.
  Test missing fields, both fields, explicit `#linear`, rebinding, blocks,
  tuple/array completion, and source-underlined Copy-after-owner errors.
  Resolve known match payload types so Copy payloads are not treated as
  linear, and isolate binding metadata per function. This is still an
  AST-side rule; typed-flow migration and general branch-equivalence handling
  remain in IR-04.

- [x] **IR-04am: Join equivalent complete ownership paths.** Treat a whole
  move and complete fieldwise consumption as the same discharged obligation
  at `#if` and `#match` joins, while rejecting a whole move against incomplete
  fields. Preserve the stricter root obligation of an explicitly `#linear`
  type. Cover accepted joins, both rejection cases, and a native example.
  This is transitional syntax-side equivalence; stable-place move transfer
  and general ownership joins remain in IR-04.

- [x] **IR-04an: Enforce direct loans held by live reference bindings.** At
  each typed borrow event, compare its checked place with direct origins of
  reference bindings live at that point. Reject overlapping access when either
  loan is mutable, preserving the new borrow and origin source spans; leave
  reborrows through references to the separate alias-aware path. Test allowed
  disjoint places and a conflicting checked-place event. Aggregate-held loans,
  indirect referents, moves, and full ownership transfer remain in IR-04.

- [x] **IR-04ao: Enforce direct loans stored in live aggregates.** Include
  stored reference origins at typed borrow events, using the referent's checked
  place rather than its storage slot. Count explicit `#drop`/`#forget` as a
  liveness use so the aggregate stays live until destruction. Test a struct
  holding a mutable reference, disjoint access, and a conflicting event with
  both exact spans. Indirect referents and complete move transfer remain open.

- [x] **IR-04ap: Reject typed writes through live direct loans.** At checked
  assignment events, compare the written place against origins held by live
  bindings. Preserve the write and loan sites in diagnostics, and allow writes
  to disjoint places. Test a shared reference followed by a checked-place
  write conflict. Indirect referents and complete move transfer remain open.

- [x] **IR-04aq: Reject explicit destruction of a live borrowed place.**
  Compare `#drop`/`#forget` release places with direct loan origins held by
  future-live bindings. Report both the destruction and original borrow sites;
  allow disjoint releases. Keep implicit moves and indirect referents in IR-04.

- [x] **IR-04ar: Reject cloning through a live mutable loan.** Include typed
  clone events in binding liveness and compare their checked source places
  against origins held by live bindings. Keep shared-loan reads valid and
  report the clone and original mutable-borrow spans. Implicit read/move
  classification remains in IR-04.

- [x] **IR-04as: Reject symbol reads through live mutable loans.** Compare
  checked symbol-read binding IDs with direct origins held by live bindings;
  preserve the read and borrow source spans. Keep shared-loan reads valid and
  leave implicit move classification and projected/indirect reads to IR-04.

- [x] **IR-04at: Check the final place for projected reads.** Avoid treating
  intermediate base evaluation in a checked field/index/payload projection as
  a whole-base read. Compare the complete projected place when available,
  and keep borrow, clone, and release operands with their dedicated event.
  Test a disjoint field access through a reference; indirect referent
  resolution and implicit move classification remain in IR-04.

- [x] **IR-04au: Retain checked read places on typed flow.** Convert place
  evaluations to explicit read actions with the checked value and place IDs,
  marking intermediate projection/borrow/clone/release bases separately from
  value reads. Use those actions for direct-loan checks, liveness, and definite
  binding verification. Test field distinctions and exact role metadata;
  implicit move classification remains in IR-04.

- [x] **IR-04av: Track direct linear transfers on typed flow.** Classify
  checked value reads used directly by bind, assignment, pattern, return, or
  break as consuming when their type is linear; retain their source spans and
  explicit linear releases through joins, replacement, and scope exit. Reject
  a later overlapping read or release, while keeping Copy/reference reads and
  borrowing builtins such as mutable-slice indexing non-consuming. Test a
  transfer followed by destruction with both exact sites. Nested expressions,
  calls, and complete exit obligations remain in IR-04.

- [x] **IR-04aw: Follow value-branch results in typed move transfer.** Trace
  direct transfer roots through `#if`, `#match` arms, value blocks, labels,
  and erased unsafe wrappers, classifying only their selected result reads as
  moves. Preserve alternative source spans across joins; test conditional,
  match, and block results. Calls and other nested expressions remain in IR-04.

- [x] **IR-04ax: Track direct linear call arguments as moves.** Use resolved
  ordinary-call IDs and source argument nodes to classify direct linear
  arguments, including value-branch results, as transfers. Keep Copy and
  reference arguments non-consuming and leave builtin operand modes outside
  this rule. Test an explicit linear resource passed by value and a Copy
  argument in the same body. Other nested expressions remain in IR-04.

- [x] **IR-04ay: Track linear values placed into aggregates.** Classify
  checked tuple, array, and enum payload operands as transfers, including
  struct-literal fields normalized to their aggregate declaration form.
  Preserve their exact value-site spans and reject later overlapping use;
  test each constructor family with an explicit linear field. Non-constructor
  builtin operand modes remain in IR-04.

- [x] **IR-04az: Retain the consuming mode of mutable-slice splitting.**
  Treat the source of `#slice-mut-split` as a linear transfer in typed flow,
  while leaving `#slice-mut-idx` and `#slice-mut-len` as borrowing reads.
  Verify the split move and non-consuming index in one checked body. Other
  builtin operand modes remain to be migrated in IR-04.

- [x] **LINEAR-ARRAY-01: Reject repetition of non-Copy ownership.** A
  repeated array element must be duplicable unless the array has exactly one
  slot. Reject zero- or multi-slot repetition of explicit/structural linear
  values and mutable references, including references nested in structs,
  enums, tuples, and arrays. Preserve Copy scalars and shared references;
  test exact source-underlined diagnostics.

- [x] **IR-04ba: Classify value-mode builtin operands on typed flow.** Treat
  nested checked builtin arguments as transfers by default while exempting
  borrows, clones, destruction operands, place projections, and other
  borrowing forms. Ensure a one-slot `#array-repeat` transfers its linear
  source, and fix syntax-side contextual repeat analysis so a later use is
  rejected. Keep unresolved builtin access modes in IR-04.

- [x] **IR-04bb: Check return escapes from typed loan origins.** Run a
  source-located return check over checked values and retained place/loan
  origins before the transitional borrow pass. This handles direct values,
  aliases, aggregates, and reference-returning calls; keep the AST-side escape
  check active because typed match-result provenance still needs branch-local
  pattern state. A regression exposed that limitation, so the legacy check is
  deliberately not bypassed.

- [x] **IR-04bc: Evaluate conditional return values at their typed flow sites.**
  For `#if`, `#match`, and labeled results, inspect each result expression at
  its own flow event so arm-local pattern bindings and aliases remain available
  before cleanup. Reject an enum payload reference escaping through a returned
  match, and verify the return span plus original borrow label. Loop-break
  result provenance and complete typed escape enforcement remain in IR-04.

- [x] **IR-04bd: Tie loop-expression breaks to their result identity.** Retain
  the checked loop node on each corresponding break edge, and inspect break
  values at their pre-cleanup flow events when checking a returned loop result.
  Validate that the target is a checked loop node; test a local borrow escaping
  through `(#return (#loop (#break ...)))` with both source labels. Statement
  loops and other typed ownership transfers remain in IR-04.

- [x] **IR-04be: Check block results before their lexical cleanup.** Resolve a
  block's final evaluated expression through typed instructions and inspect its
  loan origins at that expression's flow event, before block-local bindings are
  cleared. Reject an alias to an outer local escaping via a returned block and
  verify both source locations. Non-final side effects remain flow-ordered.

- [x] **IR-04bf: Align match-escape UI diagnostics with typed return spans.**
  Update the UI expectation from the match expression to the complete explicit
  `#return` statement now selected by typed-flow checking; retain the secondary
  label at the originating borrow and verify the exact underline width.

- [x] **IR-04bg: Preserve branch-local origins inside returned aggregates.**
  When a tuple, array, enum, or struct result contains a conditional expression,
  recursively evaluate that child at its branch-specific flow event before
  attaching its aggregate storage path. Reject a returned struct containing a
  match-bound reference to a local owner and assert both diagnostic locations.
- [x] **IR-04bh: Preserve branch-local origins in repeated arrays.** Resolve
  the element value of `#array-repeat` at its own flow event and attach the
  exact or dynamic array slot according to the checked length. Reject a repeated
  match-bound local reference in a returned array with both source locations.

- [x] **IR-04bi: Preserve branch-local origins through reference-returning calls.**
  Evaluate each reference-valued call argument with its own branch flow state,
  then lift the origin out of aggregate storage exactly as for direct calls.
  Reject an arm-bound local reference returned through an identity function
  and verify the return and original borrow spans.

- [x] **IR-04bj: Project fields from branch-produced aggregates.** Derive the
  checked field, tuple, payload, or index segment even when the aggregate base
  is itself a conditional result rather than a place. Select the matching
  retained loan slot and reject a match-produced wrapper field escaping its
  local referent.

- [x] **IR-04bk: Propagate loop-result loans inside aggregates.** Resolve
  break values using the loop expression's checked identity even when the loop
  is nested in a tuple, array, enum, or struct constructor. Inspect each break
  before cleanup and reject a wrapper containing a borrow of a local owner.

- [x] **IR-04bl: Preserve match-bound origins through slice constructors.**
  Resolve source origins through `#slice-of`, range/index views, and mutable
  split projections using the arm-local flow state. Reject a slice returned
  from a reference-to-array pattern that borrows a local array owner.

- [x] **IR-04bm: Preserve arm-local origins in explicit array literals.**
  Evaluate each `#array-of` element at its own typed flow event and retain its
  checked array index while collecting conditional reference origins. Reject
  an explicitly constructed returned array containing a match-bound local
  reference and retain both error locations.

- [x] **IR-04bn: Use typed origins for direct reference and slice returns.**
  In normal compilation, bypass the AST return-escape rule only when the
  declared result is a direct reference or slice type already checked against
  typed loan origins. Keep the AST rule for standalone borrow-checker callers
  and named aggregate results whose generated provenance is not yet complete.
  Borrow/linearity regressions include generated allocator-backed vectors and
  mutable-reference-bearing structs to guard that boundary.

- [x] **IR-04bo: Reject mixed local/parameter origins at typed branch joins.**
  Join every `#if` result alternative by its flow-site loan origins; a valid
  parameter-backed branch cannot mask a branch that returns a local borrow.
  Verify the return underline and local-origin secondary label.

- [x] **IR-04bp: Keep the standalone legacy return checker test-only.** Limit
  the old syntax-oriented entry point to unit tests while the normal compiler
  uses the typed path for direct reference/slice returns and retains a scoped
  fallback for unsupported named aggregate results. This removes a production
  dead-code warning without dropping compatibility coverage.

- [x] **IR-04bq: Resolve aliases to direct reference return types.** Extend
  the typed-return selection through acyclic type aliases to references and
  slices, without treating arbitrary reference-bearing structs as covered.
  Reject a local borrow returned under a reference alias with exact source
  locations; named aggregate fallback remains active.

- [x] **IR-04br: Preserve generator invocation provenance in typed borrow errors.**
  When typed return-origin analysis rejects code from a generator, keep the
  generated return span primary and attach the source invocation as a secondary
  label. Verify generated and caller source IDs and exact source fragments.

- [x] **IR-04bs: Carry raw-pointer borrow anchors into typed return origins.**
  Treat `#ptr-borrow` and `#ptr-borrow-mut` as lifetime-reborrows from their
  checked anchor, not as origin-free pointer expressions. Reject a local anchor
  returned through an aliased raw pointer with the return and anchor spans.

- [x] **IR-04bt: Seed reference-parameter origins in typed flow.** Retain an
  abstract `Parameter` place root for each reference parameter at function
  entry, distinct from the local slot holding that reference. Carry it through
  local aliases, and preserve mutability for mutable-reference parameters.
  Verify shared-reference aliasing, mutable-reference reads, and that caller
  origins remain distinct from local owners; local-return rejection remains
  enforced by typed escape checks.

- [x] **IR-04bu: Summarize parameter loans across aggregate-returning calls.**
  Compute return-origin summaries over the acyclic checked call graph and
  preserve the returned aggregate's loan slots across helper chains. Keep
  empty summaries distinct from unavailable external bodies. Verify both a
  two-helper accepted local use and a local borrow rejected when the returned
  aggregate escapes, with the typed diagnostic identifying the local owner.

- [x] **IR-04bv: Select typed escape checking for summarized aggregate returns.**
  Bypass the syntax-side return escape check when every reference-bearing
  aggregate call in a function has a checked body summary. Retain the legacy
  safeguard for opaque external aggregate-returning calls. Verify that a local
  borrow escaping through internal helper chains is rejected by typed flow.

- [x] **IR-04bw: Compute definite consumption on typed control flow.** Add a
  must-analysis alongside may-consumption, intersecting ownership facts at
  branch joins and converging across loop back edges. Verify that a value
  consumed in both branches is definite, while removing either branch's
  transfer makes the join non-definite. Complementary zero-iteration behavior
  is covered by IR-04cc.

- [x] **IR-04bx: Differentially verify whole-value return obligations.** Use
  active typed binding IDs and must-consumption facts to check linear values at
  returns, including explicit `#linear` values, atomics, opaque named values,
  and the aggregate leaves covered by IR-04by. Keep the syntax checker
  authoritative for now; assert agreement on accepted programs and verify
  mixed-branch transfer rejection.

- [x] **IR-04by: Check typed partial aggregate consumption at returns.** Expand
  return obligations into linear struct/tuple/array leaves and resolve those
  paths to typed field/index identities. A consumed ancestor satisfies its
  descendants; consuming every linear field is accepted, while leaving one
  field unconsumed is rejected.

- [x] **IR-04bz: Transfer enum payload obligations through typed match arms.**
  Retain payload alternatives as stable variant/index places and mark the
  scrutinee payload transfer on a successful arm, leaving the arm's bindings
  with their own consumption obligations. Test an owned enum payload and
  rejection when its arm binding is not consumed.

- [x] **IR-04ca: Preserve typed linear-exit source and branch origins.** If a
  synthetic cleanup/return node lacks a useful source span, fall back to the
  binding's typed declaration event. When a must-obligation fails after a
  partial path transfer, label that exact transfer as the path-specific origin.
  Verify the declaration hunk and related transfer in the branch-join test.

- [x] **IR-04cc: Preserve zero-iteration paths in loop must-analysis.** Add a
  loop whose body alone consumes an owned value and prove that the fallthrough
  edge keeps the value non-definitely-consumed after the loop.

- [x] **IR-04cd: Rebase projected accesses through live references.** Resolve
  checked field/index suffixes through stored reference origins before testing
  loan conflicts. Suspend only the parent binding during a reborrow, so access
  through that parent conflicts with the child loan while disjoint fields stay
  usable. Test overlapping nested projection and disjoint sibling projection.

- [x] **IR-04ce: Avoid a duplicate direct-place must-analysis.** Keep generic
  consumption origins as a may-analysis and run definite ownership dataflow
  only for the linear-leaf exit obligations that consume it. Remove the unused
  second pass and verify branch and loop behavior on the obligation analysis.

- [x] **IR-04cf: Select typed live-loan diagnostics before AST fallback.** Run
  checked-place live-access and call-argument conflict checks before the
  transitional syntax borrow checker, retaining generated invocation spans.
  Keep the syntax pass afterward for reborrow/alias cases not yet transferred.

- [x] **IR-04cg: Represent lexical borrow bodies in typed control flow.** Lower
  three-operand `#borrow` and `#borrow-mut` forms to explicit begin/end loan
  events around their body. Run overlap checks over CFG paths, including
  nested borrows and branches; insert cleanup events for returns and loop
  exits that leave the region. Ensure the loan ends before later accesses,
  preserve keyword-sized diagnostic spans, and verify typed diagnostics run
  before the syntax fallback.

- [x] **IR-04ch: Rebase lexical projected reborrows to referent places.** When
  a scoped borrow targets a field through a stored reference, resolve its
  referent place at the start event and carry all joined origins through the
  scope. Permit disjoint sibling accesses while rejecting a nested borrow of
  the same projection; do not mistake an equal-place nested borrow for a
  strict child reborrow.

- [x] **IR-04ci: Verify lexical loan cleanup on early return.** Allow typed
  return paths to pass through explicit borrow-scope end events, and test a
  return nested in a block inside `#borrow-mut` to ensure cleanup precedes the
  function exit.

- [x] **IR-04cj: Verify lexical loans across loop back edges.** A scoped loan
  created in a loop body must be ended before the next iteration, while a
  break or continue that exits the scope must also release it. Test that a
  post-loop mutable borrow succeeds after per-iteration shared scopes.

- [x] **IR-04ck: Rebase typed dereference reads to their referents.** Retain
  dereference as a structural place projection and resolve it through the
  reference's checked loan origins before overlap analysis. Verify a dereference
  read resolves to the original binding without conflating the reference handle
  with its referent. Typed writes are tracked separately in IR-04cl.

- [x] **IR-04cl: Check direct dereference writes on typed flow.** Lower
  `#deref-set` through a checked reference or field place to a distinct typed
  write event, then rebase it to the referent for loan overlap checks. Preserve
  borrows of sibling fields and reject writes while a child borrow is live.

- [x] **IR-04cm: Retain mutable split-slice halves in typed places.** Give
  each split half a distinct place projection, preserve that projection when
  destructuring the split tuple, and append element indices when resolving
  `#slice-mut-idx` and `#deref-set` through each half. Verify distinct halves
  remain disjoint in typed loan checking while each retains the original array
  loan.

- [x] **IR-04cn: Preserve nested split-slice partition paths.** Repeatedly split
  one mutable half, then prove writes through both child halves and the
  untouched sibling resolve to three non-overlapping referents. Keep each
  nested origin tied to the original array loan and pass typed live-loan
  checking.

- [x] **IR-04co: Retain exact local binding spans in typed ownership state.**
  Associate each top-level local `BindingId` with the source identifier span,
  rather than the complete `#let` statement. Use that span for typed linear
  exit diagnostics and verify the source slice is the binding name.

- [x] **IR-04cp: Retain parameter identifier spans in typed ownership state.**
  Associate each parameter `BindingId` with its declared identifier span from
  the function signature, and verify the span through checked-body lowering.

- [x] **IR-04cq: Retain nested local spans in typed ownership state.** Traverse
  nested blocks, branches, loops, and initializer expressions in the same order
  as typed-body lowering, preserving local identifier spans even after
  alpha-renaming. Verify nested block and branch bindings independently.

- [x] **SAFE-01: Resolve static access by identity, not spelling.** Exclude
  function parameter names from each function's static access set; local and
  pattern declarations that shadow statics are alpha-renamed before checking.
  Genuine static reads/borrows still require `#unsafe` and retain exact spans,
  including imported locations and generated-code plus invocation provenance.
  A later full typed-IR ownership migration can replace this transitional
  scoped-name handling with direct resolved-identity checks.

## Collections and initial async facilities

Next steps: finish IR-02, IR-03, and IR-04 in the typed representation
section; then implement ASYNC-02, ASYNC-01, and ASYNC-03 below.

- [x] **COL-01: Freeze keyed syntax collections before generation.** Collect
  active imported contributions, sort by key, deduplicate identical entries,
  reject conflicts/unknown collections, and prohibit generated registration.
  Frozen collection snapshots are included in invocation/cache identity. Keep
  helpers pure and add `#gn-length` for lists.
- [x] **COL-02: Generate static registries and concrete error enums.** Provide
  user-defined generators in `library/collections.lim`, with inspectable cached
  output, inline payloads, static arrays, and native examples across imports.
  Correct slice indexing/ranges/splitting to preserve ascending static or
  raw-backed layout as well as descending tagged stack layout. Preserve the
  address and direction when reading/writing multiword referents. Cover
  references crossing function calls and multiword slice elements with native
  regression tests.
- [x] **COL-03: Distribute syntax explicitly at invocation sites.** Replace
  generator parameter collection annotations with the direct argument form
  `(#syntax-distribute Collection)`, so bare symbols stay literal. Rename
  declarations from `#generator` to `#gn` without a compatibility mode.
  Migrate generators, examples, docs, and UI tests; verify sorting, import
  prefixing, diagnostics, and cache identity for resolved lists.
- [x] **TASK-01: Add explicit linear task states and bounded cooperative
  execution.** `#linear` opts concrete structs/enums out of structural Copy.
  Task generators emit linear states and concrete Pending/Ready results; the
  executor owns a fixed heterogeneous set of slots and uses direct polling.
- [x] **TASK-02: Add explicit awaiting-state composition and cancellation.**
  `@async` builds named child-task states with `#await` and named continuations;
  `@task-cancel` requires exhaustive, consuming cleanup handlers. Test borrow
  escape, outstanding borrows, duplicate use, missing cleanup cases, and actual
  cleanup side effects. Fix native unit-valued returns skipping evaluation.
- [x] **TASK-03: Run fixed executors on explicit OS workers.** Compose the
  executor generator with existing thread spawn/join support, retaining
  structural Send/Sync checks, mandatory joins, and explicit spawn errors.
  This is thread-owned execution, not a migrating worker-pool scheduler.
- [x] **ASYNC-02a: Generate a concrete bounded ready queue.** Add an
  inspectable user generator with literal capacity inputs and explicit names
  for every generated declaration. Enqueue/dequeue return concrete Full/Empty
  result enums, with native tests for FIFO order, wraparound, exhaustion,
  zero capacity, and independent instantiations. This stores task IDs only;
  generational wake handles, non-busy waiting, OS registration, and safe
  cancellation remain in ASYNC-02.
- [x] **ASYNC-02b: Keep ready-queue state linear.** Mark each generated
  queue type `#linear` so implicit copies cannot duplicate scheduler state.
  Require explicit consumption or destruction of each queue owner. Test a
  native queue run and a rejected use after move; explicit cloning remains a
  separate user decision under the language's normal linearity rules.
- [x] **ASYNC-02c: Add a concrete generational token protocol.** Provide a
  four-slot linear table and Copyable slot/generation tokens. Explicit
  registration, validity, and retirement operations reject out-of-range,
  busy, stale, and exhausted slots; retirement saturates generation to avoid
  wraparound reuse. Cover re-registration, stale rejection, exhaustion, and
  borrowing a linear queue field through an owner reference in native tests.
  This is not an unforgeable safe wake authority while
  fields and constructors remain public.
- [x] **ASYNC-02d: Make wake authority opaque.** Add module-private fields or
  compiler-owned opaque handles before task scheduling relies on token/table
  invariants. Prevent safe callers from forging tokens, replacing generation
  arrays, or cloning live authority. Preserve explicit inspectable operations
  where possible, and test cross-module rejection and stale-handle behavior.
- [x] **ASYNC-02e: Generate borrowed local wake adapters.** Add a user-defined
  `@local-waker` producing a linear handle that borrows one concrete executor,
  owns arbitrary concrete metadata, and calls named notify/clone/destroy
  functions directly. Keep it !Send/!Sync via an unused raw-pointer marker;
  test wake, clone, destruction, borrow escape, thread-transfer rejection,
  generated-code inspection, and invalid generator arguments. This is not
  unforgeable wake authority while generated fields remain public.
- [ ] **ASYNC-01: Suspend arbitrary ordinary function bodies.** Complete the
  typed ownership/control-flow migration, then calculate live values and loans
  at suspension points. Define source syntax, borrowing across suspension, and
  immovable storage before accepting self-referential frames. Preserve exact
  source diagnostics and explicit cleanup for each suspended state.
- [x] **ASYNC-01a: Define pinning as a checked place guarantee.** Add explicit
  pinned types and pinned references without generic traits. Establish stable
  stack and allocator-backed places before creating internal references;
  prohibit safe moves, replacement, copies, or owner destruction while pinned
  references exist. Distinguish pinning the referent from pinning a handle,
  and test move, reborrow, field projection, and scope-exit diagnostics.
- [x] **ASYNC-01a1: Represent pinned-reference types distinctly.** Add an
  internal typed representation that preserves pointee and mutability and
  remains distinct from ordinary references through type-source serialization,
  alias resolution, reference containment, and thread-property analysis. This
  is compiler groundwork only; the surface syntax and pinning guarantees remain
  unsupported until ASYNC-01a is complete.
- [x] **ASYNC-01a2: Pin stack places with tracked references.** Add distinct
  `#pin-ref` / `#pin-ref-mut` types and `#pin-borrow` / `#pin-borrow-mut`
  operations. Carry pin provenance through field reborrows, aggregate storage,
  and reference-returning calls. While the loan is live, reject referent copies,
  moves, writes through other aliases, and whole-referent replacement; dropping
  the pin releases the place. Verify native reads through direct and projected
  pins, a native function return, exact UI diagnostics, and focused
  move/copy/reborrow/lifetime cases. Allocator-owned pin handles and
  self-reference initialization remain open under ASYNC-01a/01c.
- [x] **ASYNC-01a3: Prove stack-pin owner scope and destruction.** Reject a
  pinned reference (including one nested in an aggregate) escaping the
  function that owns its stack place. Reject explicit destruction of a pinned
  owner until every derived pin is ended, then allow destruction. Cover direct
  and projected pins, function returns, and scope-exit diagnostics; allocator-
  backed pin handles remain a separate requirement.
- [x] **ASYNC-01a4: Anchor pinned borrows into stable raw storage.** Add
  explicit unsafe shared and exclusive pointer-to-pinned-reference forms that
  require an existing pinned lifetime anchor. Propagate the anchor's tracked
  loan and pinned provenance so allocator-backed owners can expose their
  stable pointee without converting it to an ordinary reference. Verify native
  reads, rejection of conflicting owner writes, anchor escape rejection, and
  unsafe-context diagnostics. This is a primitive for a future
  allocator-backed pin owner, not itself a safe allocation abstraction.
- [x] **ASYNC-01a5: Generate allocator-owned pinned boxes.** Add a user-defined
  `@pin-box` specialization that owns one initialized allocation, borrows its
  concrete allocator, exposes only pinned shared/mutable pointee borrows from
  a pinned box handle, and explicitly destroys then deallocates the value.
  Allocation failure must return both the allocator error and the original
  value. Test native round trips, handle movement/destruction exclusion while
  pinned, generated-code inspection, and allocation failure ownership.
- [x] **ASYNC-01b: Lower async functions to concrete poll state machines.**
  Extend the initial `@async-fn` lowering beyond sequential immutable `#let`
  bindings. Support control-flow joins, mutable locals, and expression-level
  `#await` with typed liveness and loan capture, rather than an explicit
  capture list. Preserve source-level spans through lowering and support
  explicit cancellation of every generated state.
- [x] **ASYNC-01b1: Forward local wake context through explicit async stages.**
  Generate a concrete waker-aware poll function for `@async-wake` task
  composition. Child polls receive the same borrowed local waker, without
  function pointers or hidden clones. Exercise Pending, wake notification,
  Ready, and explicit handle destruction in a native example; retain a test
  that rejects a pending task that illegally retains an executor borrow.
- [x] **ASYNC-01b2: Lower sequential async functions with explicit captures.**
  Add built-in inspectable `@async-fn` over a `#fn` form. Accept one or more
  top-level immutable `#let` bindings whose initializer is `#await`; each
  suspension declares its concrete child task, poll and result variants,
  and the values to retain. Emit a linear state enum, start function, poll
  result, and acyclic stage helpers into the hashed generated-code cache.
  Verify immediate Ready, multiple Pending/resume cycles, empty captures,
  omitted capture and escaping-reference rejection, and manual cancellation.
- [x] **ASYNC-01b3: Carry mutable locals through sequential suspension.**
  Preserve mutable parameter and `#let-mut` metadata in generated helpers,
  allow explicit assignments to captured mutable locals between await stages,
  and keep captures explicit. A native Pending/resume regression mutates the
  retained value and checks the Ready result; existing async tests still pass.
- [x] **ASYNC-01b4: Lower a direct await in the explicit return expression.**
  Treat `(#return (#await ...))` as the final concrete state-machine stage,
  preserving explicit captures and the declared return type. Exercise a native
  Pending/resume cycle and inspect the generated helper; nested awaits within
  other expressions remain unsupported.
- [x] **ASYNC-01b5: Preserve branch forms between sequential await stages.**
  Carry `#if`, `#match`, and `#block` forms without nested awaits into the
  appropriate start or resume helper. Require values used by later stages to
  remain in explicit capture lists; verify a mutable branch update between two
  awaits in a native Pending/resume regression. Branches containing suspension
  and other loop state across suspension remain open.
- [x] **ASYNC-01b6: Verify match-stage state mutation.** Extend the native
  two-await regression with scalar `#match` arms that update captured mutable
  state in a resume helper; retain the `#if` case and check the final Ready
  value to exercise the branch join.
- [x] **ASYNC-01b7: Diagnose suspension nested in control flow.** Reject
  `#await` inside `#if`, `#match`, or `#block` with a targeted generator error
  instead of a generic unsupported-binding message; test the diagnostic text.
- [x] **ASYNC-01b8: Infer values live across sequential suspension points.**
  Remove user-maintained capture lists from `#await`; determine the concrete
  bindings referenced by the continuation, skipping constructor/type/field and
  named-argument labels. Preserve declaration order and mutability in generated
  frame fields. Verify that used values survive Pending/resume, unused linear
  values must be consumed before suspension, and same-spelled parameter/field
  labels do not cause false captures. This syntax-level pass remains a
  restricted precursor to full CFG liveness in ASYNC-01b.
- [x] **ASYNC-01b9: Extract typed awaits from eager value expressions.** Allow
  nested `#await` in value-producing forms by requiring its result type
  explicitly, then lower awaits left-to-right into ordinary concrete stages.
  Preserve call/constructor argument evaluation order. Conditional branch
  selection is handled separately in ASYNC-01b10.
- [x] **ASYNC-01b10: Await after conditional child-task selection.** Lower
  `#if` and `#match` expressions whose every arm awaits through the same
  explicitly typed child/pending/ready/poll protocol by selecting the concrete
  child first and suspending once. Diagnose partial or incompatible protocols;
  branch-specific poll protocols and immediate non-await arms remain open.
- [x] **ASYNC-01b11: Preserve external borrows across suspension.** Infer a
  live reference parameter into the generated frame, retain its caller loan
  across Pending/resume, and reject mutation of the referent while suspended
  or a returned task borrowing a local owner. This does not permit self-refs
  or prove precise loan release at every Ready/cancellation join.
- [x] **ASYNC-01b12: Preserve exclusive external borrows across suspension.**
  Capture a live `#ref-mut` in the generated frame, allow mutation through it
  after resume, and reject direct access to its owner while Pending. Treat
  moving/matching an aggregate parameter containing mutable references as
  transferring handles, not reading through the referents. Precise loan
  release at Ready remains open.
- [x] **ASYNC-01b13: End captured loans at Ready and cancellation.** Release
  external shared/exclusive loans once the generated frame is consumed by a
  Ready transition or explicit cancellation; preserve them on every Pending
  path. Verify owner access stays rejected while Pending, becomes legal after
  Ready/cancellation, and remains rejected if any returned value retains the
  reference.
- [x] **ASYNC-01b14: Join an awaited branch with an immediate value.** Permit
  an `#if` or `#match` expression whose suspending arms use one shared child
  poll protocol and whose other arms produce the explicitly typed result
  directly. Generate an inspectable concrete choice task/poll adapter that
  turns immediate arms into Ready without polling a child. Verify both branch
  paths natively; keep the generated choice task linear so capture transfer
  and explicit cancellation retain their existing ownership checks.
- [x] **ASYNC-01b14a: Verify captures and cancellation through a branch join.**
  Capture an external reference needed after a conditional await, reject owner
  mutation while the generated choice task is Pending, and prove explicit
  cancellation releases the loan before owner mutation. Run the immediate
  branch natively and inspect the generated frame for the captured reference.
- [x] **ASYNC-01b15: Join branch-specific child poll protocols.** Permit
  conditional await branches to use different concrete child types, pending
  and ready variants, and poll functions when their result type agrees. Emit a
  concrete tagged choice task with per-branch polling and preserve each child
  across Pending/resume. Reject branches with incompatible result types; test
  distinct protocols natively across both Pending/resume and immediate Ready.
- [x] **ASYNC-01b16: Lower awaits in terminal binding blocks of branches.**
  Recognize a branch block consisting of one immutable binding initialized by
  `#await` and yielding that binding. Preserve the binding's explicit result
  type while lowering the branch through the existing concrete choice task;
  verify an awaited branch natively alongside an immediate branch. Arbitrary
  post-await block continuations and other loop suspension remain open.
- [x] **ASYNC-01b17: Preserve branch-local setup before suspension.** Allow
  non-suspending statements before the terminal await binding, keeping them
  inside the selected branch's task-construction block. Verify a branch-local
  value initializes the child task and survives through native polling without
  becoming an unnecessary frame capture.
- [x] **ASYNC-01b18: Prevent loop-await hoisting from changing semantics.**
  Lower supported `#while`, `#for-range`, `#for`, and terminal-transfer
  `#loop` awaits as loop-carried suspension state; diagnose remaining
  unsupported control flow before expression lowering can hoist awaits.
  Diagnostics underline `#await`.
- [x] **ASYNC-01b19: Resume a direct child await inside a `#while` loop.**
  Support a loop condition and body with one direct `#let`/`#let-mut` await per
  iteration, capturing the loop-carried values and child task in a concrete
  generated state. A Pending poll must resume that same iteration; Ready runs
  the continuation and proceeds to the next iteration. Reject awaits in the
  condition, multiple awaits per iteration, unsupported local bindings or
  control transfers around the await. Verify multiple `#while` iterations and
  Pending/resume natively; range-loop coverage is tracked separately below.
- [x] **ASYNC-01b20: Preserve safe per-iteration setup before loop awaits.**
  Allow ordinary `#let` and `#let-mut` setup before the loop's direct await.
  These locals remain scoped to the current iteration and may initialize the
  child task, but must not be referenced by the post-await continuation because
  they are not retained across suspension. Reject shadowing and verify both a
  native child initialized from a loop-local value and a diagnostic when that
  local is used after suspension.
- [x] **ASYNC-01b21: Lower awaited `#for-range` loops without hoisting.**
  Convert a half-open integer range with one direct child await per iteration
  into a resumable task that retains its counter while Pending and increments
  only after Ready. Preserve the range start/end and per-iteration binding
  semantics; test a Pending first iteration followed by a Ready later
  iteration natively. Direct awaits in loop conditions remain unsupported.
- [x] **ASYNC-01b22: Lower awaited `#for` loops with existing counters.**
  Preserve initializer execution, condition, and step ordering for `#for`
  loops. Execute the step only after the awaited child is Ready and retain the
  counter across Pending. Local initializer binding scope is tracked in b23.
- [x] **ASYNC-01b23: Preserve `#for` initializer binding scope.**
  Support a local `#let`/`#let-mut` in the `#for` initializer by assigning it
  a fresh internal name and rewriting only its value references in the loop
  condition, step, and body. Keep type names, field labels, call names, and
  named-argument keys untouched. Reject collisions with visible source names
  and verify native Pending/resume across multiple iterations.
- [x] **ASYNC-01b24: Resume awaited `#loop` bodies through terminal transfers.**
  Lower a `#loop` containing one direct child await per iteration and a terminal
  `#break`/`#continue`, including terminal `#if` branches, into explicit done
  state. Resume the same iteration after Pending, execute its continuation, and
  stop or repeat only after the terminal transfer. Keep value-bearing breaks,
  nonterminal transfers, and more complex branch control flow rejected; verify
  a Pending/resume sequence that repeats once and then exits natively.
- [x] **ASYNC-01b25: Return mutable scalar captures after awaited loops.**
  If a mutable Copy scalar is changed by the loop and used by the continuation,
  include it in the generated Ready payload and restore it after `#await`.
  Verify a loop increments a captured counter over Pending and Ready iterations
  and the caller observes the final value.
- [x] **ASYNC-01b26: Return linear captures after awaited loops.** Carry a
  mutated live-after `#linear` value in the generated Ready payload, move it
  back into a fresh continuation binding, and let the existing linear checker
  enforce complete consumption of the output aggregate. Keep an explicit
  internal run-state enum so captured ownership is transferred consistently
  between active iterations, Pending, and Ready without exposing extra poll
  protocol variants. Verify Pending followed by multiple immediately-Ready
  iterations natively, consume the returned value explicitly, and explicitly
  cancel a Pending task that owns a linear capture.
- [x] **ASYNC-01b27: Return unchanged live-after captures from awaited loops.**
  Include every captured binding still used after the loop in the generated
  Ready payload, not only captures assigned in the loop. Preserve immutable
  bindings as immutable and transfer unchanged linear aggregates exactly once.
  Test an immutable linear value used by the loop condition and after Ready,
  including its explicit consumption in the continuation; inspect the concrete
  output payload to ensure both the mutated and unchanged owners are returned.
- [x] **ASYNC-01b28: Suspend in a direct `#while` condition.** Lower a boolean
  condition that is exactly one `#await` into a resumable child poll before
  each loop-body decision. Preserve while semantics so Ready(false) skips the
  body, and re-evaluate by polling a fresh child on the next iteration after
  Ready(true). Keep compound awaited conditions, a second suspension in the
  body, and loop transfers from the body rejected until their control-flow
  joins are represented explicitly. Verify Pending, repeated Ready(true)
  iterations, and final Ready(false) natively while carrying a mutable counter.
- [x] **ASYNC-01b29: Preserve mutable loop captures across condition awaits.**
  Carry a mutable value into each condition child, preserve it through Pending,
  update it in the body only after Ready(true), and return it after the false
  condition. Exercise oversized generated state and poll enums through
  indirect ABI storage in a native example.
- [x] **ASYNC-01b30: Preserve external pinned loans through pinned async frames.**
  Capture a caller-owned `#pin-ref` across Pending/resume, reject mutation of
  its owner while the frame retains the loan, and verify the reference is read
  after resume. Explicitly destroy the completed frame before reusing its owner;
  this does not permit a reference into the async frame itself.
- [x] **ASYNC-01b31: Suspend in a mutable assignment value.** Lower a typed
  `#await` nested in a `#set` right-hand side into an explicit result binding,
  retain the target's mutable value across Pending, and assign in the resume
  helper before returning. Verify Pending/resume natively and inspect both the
  generated frame capture and mutable resume parameter.
- [x] **ASYNC-01b32: Suspend in a projected assignment value.** Lower a typed
  `#await` nested in `#set-index` into the resume helper while retaining the
  mutable array across Pending. Verify the indexed write and subsequent read
  natively, and inspect the generated continuation assignment.
- [x] **ASYNC-01b33: Await before conditional branch selection.** Suspend on a
  typed boolean `#await` in an `#if` condition, resume, and only then select the
  branch. Verify the Pending/resume path natively and inspect that the generated
  continuation branches on the awaited result.
- [x] **ASYNC-01b34: Await before match-arm selection.** Suspend on a typed
  `#await` used as a `#match` scrutinee, then select an arm from the resumed
  result. Verify the Pending/resume path natively, including payload binding,
  and inspect that matching occurs in the generated continuation.
- [x] **ASYNC-01b35: Resume through a value-producing block.** Lower a block
  containing one typed awaited binding followed by a value expression that
  uses the binding. Preserve the post-await expression in the continuation,
  including value-position rewriting, and verify Pending/resume natively.
- [x] **ASYNC-01b36: Capture block-local setup across suspension.** Allow simple
  local binding setup before an awaited binding in a value-producing block.
  Hygienically lift those bindings into generated stages, infer whether they
  must survive Pending, and verify both task initialization and continuation
  use across resume.
- [x] **ASYNC-01b37: Lower sequential awaits within one block.** Preserve the
  remainder of a value-producing block as the continuation after each await,
  so multiple awaited bindings resume in source order. Verify two consecutive
  Pending/resume stages natively and inspect the generated state transitions.
- [x] **ASYNC-01b38: Resume awaited block mutations in order.** Support direct
  typed awaits in block-local `#set`/projected assignment values. Keep the
  mutable target live in the frame, execute the write only after Ready, and
  verify Pending/resume plus the generated mutable continuation parameter.
- [x] **ASYNC-01b39: Preserve explicit await types in branch blocks.** Lower a
  terminal binding block in an `#if`/`#match` arm when its `#await` includes an
  explicit result type. Normalize the protocol without dropping the type and
  verify branch-local setup and native Ready behavior.
- [x] **ASYNC-01b40: Preserve mutable awaited block bindings.** When a
  `#let-mut` is initialized by `#await` inside a value-producing block, keep
  its mutable status in the generated continuation and frame. Verify mutation
  after Pending/resume natively and inspect the generated mutable parameter.
- [x] **ASYNC-01b41: Cancel every generated async frame state explicitly.**
  Compose `@task-cancel` with an `@async-fn` frame containing a retained capture
  and child task. Require an exhaustive handler for the start and pending states,
  and verify cancellation consumes both the capture and child owner natively.
- [x] **ASYNC-01b42: Preserve terminal loop control in awaited while bodies.**
  Allow terminal `#break`, `#continue`, and complete `#if` branches containing
  them in a `#while` whose condition awaits. Preserve body guarding for
  Ready(false), and reject nonterminal or unsupported transfers. Verify a
  native loop that continues once and then breaks.
- [x] **ASYNC-01b43: Preserve boolean short-circuiting around awaits.** Lower
  awaited right operands of `#bool.&&` and `#bool.||` through explicit branch
  selection so an unselected child task is neither created nor polled. Verify
  a skipped poll with a native side effect.
- [x] **ASYNC-01b44: Preserve match guards around awaited arms.** Lower an
  awaited guarded `#case` through conditional-task selection without evaluating
  its child unless both the pattern and `#when` guard match. Verify a rejected
  guard leaves a poll side effect untouched.
- [x] **ASYNC-01b45: Preserve `#if-let` selection around awaits.** Lower an
  awaited branch through an equivalent `#match`, so the success or fallback
  expression is evaluated only after the typed pattern selects it. Verify
  skipped and selected branches natively.
- [x] **ASYNC-01b46: Suspend in a `#while-let` scrutinee.** For one direct,
  explicitly typed `#await`, poll a fresh child each iteration, run the body
  only for matching results, and terminate on the first non-match. Preserve
  captured mutable state across Pending/resume and test multiple iterations.
- [x] **ASYNC-01b47: Await an existing-counter `#for` condition.** Accept one
  direct boolean `#await` in the loop condition; keep initializer execution
  once, run the body only on Ready(true), and run the step after the body but
  not after Ready(false). Test Pending/resume and multiple iterations.
- [x] **ASYNC-01b48: Preserve `#for` step order with terminal transfers.** In
  an awaited condition loop, run the step before `#continue`, skip it on
  `#break`, and keep it on normal/continuing `#if` branches. Verify Pending,
  continue, break, and final counter natively.
- [x] **ASYNC-01b49: Preserve terminal transfers in awaited `#while-let`.**
  Rewrite body `#break`, `#continue`, and terminal `#if` transfers into the
  generated stop state, so control remains in the loop across Pending/resume.
  Verify both transfers with matching and non-matching awaited results.
- [x] **ASYNC-01b50: Suspend in a `#for` step.** Lower one direct typed await in
  the step after a non-suspending loop body and condition. Preserve body-before-
  step ordering through Pending/resume, then recheck the condition only after
  the awaited step is Ready. Verify an iteration-sensitive child task suspends
  once and the loop completes with the expected result.
- [x] **ASYNC-01b51: Assign an awaited result in a `#for` step.** Lower a direct
  `#set target (#await ...)` into a typed temporary followed by the assignment
  only after Ready. Resolve the target's explicit type from the checked async
  binding environment; reject unknown targets and non-direct await values.
  Verify the step sees body-updated state and transfers the awaited value across
  Pending/resume before the next condition check.
- [x] **ASYNC-01b52: Suspend in a `#for` initializer.** Lower a direct explicitly
  typed await in a `#let` or `#let-mut` initializer before evaluating the loop
  condition, exactly once. Preserve initializer binding scope and liveness when
  the loop body or condition also suspends; test native initialization order,
  Pending/resume, and diagnostics for unsupported initializer forms. Verified
  native initialization before both synchronous and suspending loop conditions
  and bodies.
- [x] **ASYNC-01b53: Extract nested awaits from `#for` initializers.** Permit
  nested typed awaits in initializer expressions by extracting them in source
  order into generated stages before the loop. Preserve short-circuit and
  conditional evaluation; reject await forms lacking explicit result types.
  Verify native Pending/resume and left-to-right evaluation with multiple
  initializer awaits; untyped nested awaits receive the explicit-result-type
  diagnostic.
- [x] **ASYNC-01b54: Preserve conditional initializer evaluation.** Verify a
  non-selected `#if` initializer branch containing an await does not poll its
  child; the immediate branch must complete on the first poll. This keeps
  generated initializer lowering from eagerly evaluating a conditional await.
- [x] **ASYNC-01b55: Suspend conditionally in a `#for` condition.** Compose
  conditional `#if` branches that either await the same child protocol or
  immediately produce a boolean into one per-iteration child task. Evaluate the
  branch selector each iteration, never hoist its await, and preserve loop
  step ordering. Verify native Pending/resume and that an immediate branch does
  not poll the child.
- [x] **ASYNC-01b56: Suspend conditionally in a `#while` condition.** Compose
  an awaited branch and an immediate boolean branch into one per-iteration
  child task. Re-evaluate the selector after each Ready(true), preserve
  Pending/resume and body ordering, and verify the immediate branch does not
  poll its child.
- [x] **ASYNC-01b57: Suspend inside a `#for` step assignment expression.**
  Extract a typed nested await from the assignment's right-hand side, retain
  the per-iteration task across Pending, and assign the computed value only
  after Ready. Verify native ordering, Pending/resume, and that the next
  condition observes the completed assignment.
- [x] **ASYNC-01b58: Suspend conditionally in a `#while-let` scrutinee.**
  Compose branches that await the same typed result protocol or immediately
  produce a matching result value. Re-evaluate the branch selector per
  iteration and verify Pending/resume, pattern termination, and that the
  immediate branch never polls the child.
- [x] **ASYNC-01b59: Await a task produced by an earlier await.** Extract a
  typed await nested inside a top-level await's task expression into a prior
  concrete stage. Preserve dependency order, generated task ownership, and
  Pending/resume for the outer child; verify the generated source contains no
  nested `#await` expression.
- [x] **ASYNC-01b60: Sequence nested task construction in a `#for` initializer.**
  Extract a typed await from the initializer await's task expression before
  polling the outer child. Run initialization exactly once before the loop,
  preserve Pending/resume, and verify an immediate loop condition is evaluated
  only after the outer initializer resolves.
- [x] **ASYNC-01b61: Await `#for-range` bounds before entering the range.**
  Extract typed awaits from the start and end expressions in source order,
  evaluate each bound once, and do not begin iterations until both complete.
  Verify multiple Pending/resume stages and the resulting range boundaries;
  body suspension remains independent.
- [x] **ASYNC-01b62: Compose awaited `#for-range` bounds with body suspension.**
  Carry extracted bound values and types into the range-body state machine.
  Finish each bound exactly once before polling per-iteration body tasks, and
  verify Pending/resume across both phases plus correct range iteration.
- [x] **ASYNC-01b63: Select a conditional await in a loop-body binding.**
  Allow a `#let`/`#let-mut` in `#while`, `#for`, or `#for-range` bodies to
  choose between a typed await and an immediate value. Preserve branch
  selection across Pending/resume and emit one inspectable choice task.
- [x] **ASYNC-01b64: Sequence adjacent awaits within one loop iteration.**
  Compose consecutive typed await bindings into nested concrete sequence
  tasks, where each Ready value may construct the next child. Preserve each
  Pending state and execute the loop suffix only after the final child is
  Ready.
- [x] **ASYNC-01b65: Compose awaited `#while` conditions with body suspension.**
  Poll the condition child first; on Ready(false), skip the body task entirely,
  and on Ready(true), construct and poll one direct body-await binding. Retain
  either child across Pending, preserve the binding result and terminal
  `#break`/`#continue`, and verify both suspension stages plus false-condition
  short-circuiting natively. Outer-local references in the two task
  constructors remain unsupported and must be carried explicitly in a later
  async-capture step; ASYNC-01 remains open.
- [x] **ASYNC-01b66: Carry Copy locals into composed awaited body tasks.**
  Preserve scalar, shared-reference, raw-pointer, tuple, and array Copy values
  needed to construct the body child across condition and body Pending states.
  Keep the value available to the source continuation, and diagnose linear or
  otherwise non-Copy captures with the offending local name instead of
  producing malformed generated code. Named aggregate Copy proofs and
  mutable-value/linear captures remain open under ASYNC-01.
- [x] **ASYNC-01b67: Compose conditional awaits in an awaited `#while` body.**
  Reuse the concrete choice-task protocol when the one body binding selects
  between a child `#await` and an immediate value. Evaluate that selection
  only after the awaited condition is Ready(true), retain the selected child
  across Pending, and preserve the ordinary body continuation. Verify native
  child resumption and retain the Ready(false) body-skip regression; broader
  body control-flow joins remain open under ASYNC-01.
- [x] **ASYNC-01b68: Suspend a `#while-let` body after a matching scrutinee.**
  Poll the scrutinee child first, skip body construction when its pattern does
  not match, and otherwise retain the scrutinee plus the body child across
  Pending. Restore pattern bindings and body-await results before the original
  continuation; verify direct and conditional body awaits, as well as an
  unmatched value that must not poll the body task.
- [x] **ASYNC-01b69: Preserve expressions between loop-body awaits.**
  Compose the first two direct loop-body awaits even when separated by
  nonbinding, noncontrol, nonsuspending expressions. Run those expressions
  exactly once after the first child becomes Ready and before constructing the
  second child; allow them to use the first result, and reject inaccessible
  outer or per-iteration locals explicitly. Verify that the first result feeds
  both an intervening check and the second task.
- [x] **ASYNC-01b70: Preserve match-based terminal transfers in awaited `#loop`.**
  Rewrite `#break` in terminal match arms to the loop's carried done state,
  while preserving `#continue` and ordinary arm completion as another
  iteration. Reject nonterminal or labeled transfers. Verify a native
  Pending/resume loop whose match selects both continuation and termination.
- [x] **ASYNC-01b71: Preserve match transfers in awaited `#for` bodies.**
  Apply the explicit step exactly once after ordinary or continuing match arms,
  and skip it for breaking arms. Reject transfers in guards and preserve
  terminality diagnostics. Verify native resume behavior where different arms
  select continue and break around an awaited condition.
- [x] **ASYNC-01b72: Preserve match transfers in awaited `#while` and `#while-let`.**
  Lower terminal match-arm breaks and continues through the loop's stopped
  state, without changing scrutinee binding or body-await ordering. Reject
  nonterminal and guarded transfers. Verify a native awaited-condition loop
  and an awaited-scrutinee body that exits through a match arm.
- [x] **ASYNC-01b73: Preserve side effects before awaits in value blocks.**
  Allow nonbinding, nonsuspending block-prefix expressions before a direct
  awaited binding. Keep them in source order and execute them exactly once
  before constructing the child task; preserve binding-renaming and liveness
  for later continuation code. Reject prefix control transfers and suspension.
  Verify a mutable prefix side effect remains single-execution across Pending.
- [x] **ASYNC-01b74: Normalize mutable await-result blocks in conditional arms.**
  Treat a `#block` that binds a direct await with `#let-mut` and yields that
  binding as the same result expression as an immutable binding, retaining
  branch selection and task-construction order. Verify both `#if` and `#match`
  arm selection, including that an unselected arm is never polled.
- [x] **ASYNC-01b75: Resume branch-local continuations after conditional awaits.**
  Accept an `#if` or `#match` arm block with one direct typed await binding and
  a nonsuspending continuation that uses only that binding. Generate an
  inspectable concrete adapter task that polls the selected child, preserves
  Pending, and evaluates the continuation exactly once on Ready. Keep immediate
  and unselected branches unchanged; diagnose unsupported outer captures.
- [x] **ASYNC-01b76: Carry branch-local values through continuation adapters.**
  Capture prefix bindings used after the await in the adapter task state,
  restoring their original mutability in the Ready continuation and retaining
  them across Pending. Keep prefix evaluation inside selected-branch task
  construction; allow linear captures when ownership transfers into the task.
  Verify a branch-local value remains usable after multiple polls.
- [x] **ASYNC-01b77: Support multiple awaits in one selected branch block.**
  Lower branch-local await bindings through the regular concrete async state
  machine, preserving prefix-local ownership, ordered task construction, and
  the final branch continuation. Keep branch selection lazy and never poll an
  unselected branch. Verify two child Pending/resume stages inside both `#if`
  and `#match` branches.
- [x] **ASYNC-01b78: Suspend inside branch value expressions.**
  Lower nested typed awaits in an `#if`/`#match` arm's ordinary value
  expression into a concrete branch task, preserving left-to-right evaluation
  and selection. Initially require the expression result to match the awaited
  value type and reject uncaptured outer locals explicitly. Verify native
  Pending/resume for `#if` and `#match`, plus an unselected immediate arm.
- [x] **ASYNC-01b79: Compose awaited `#for` conditions with body suspension.**
  Poll the condition task before constructing the body task, skip the body when
  the condition is false, and preserve the explicit step and terminal `#break`
  behavior. Verify native Pending/resume across condition and body tasks,
  including that a false condition never polls the body.
- [x] **ASYNC-01b80: Compose awaited `#for` steps with body suspension.**
  Sequence the body's selected await before an awaited step assignment, retain
  each pending child independently, and commit the step result only after its
  child is Ready. Verify native Pending/resume across both stages and that the
  next condition observes the completed step assignment.
- [x] **ASYNC-01b81: Compose awaited `#for` conditions with awaited steps.**
  Resolve the condition before running the ordinary body, then poll the step
  task and apply its assignment only when Ready. Re-evaluate the condition
  after the update. This covers loops with a non-suspending body; the
  condition/body/step combination is tracked separately below.
- [x] **ASYNC-01b82: Compose awaited `#for` condition, body, and step.**
  Run the condition first, then lower the entire selected iteration body and
  awaited step into one concrete child task. Return updated mutable,
  Copy loop-carried values only after the step is Ready, and recheck the
  condition afterward. Verify native Pending/resume across all three phases
  and preserve body-before-step ordering.
- [x] **ASYNC-01b83: Preserve terminal transfers in three-phase awaited `#for`.**
  Carry terminal body `#break`/`#continue` through the condition/body/step
  adapter. A continue must await and apply the step before rechecking the
  condition; a break must skip the step and exit after the body is Ready.
  Preserve updated loop-carried values and verify both paths natively.
- [x] **ASYNC-01b84: Transfer external borrows through three-phase awaited `#for`.**
  Move each shared, mutable, or pinned reference through exactly one live task
  state; do not duplicate it in nested condition/body/step frames. Preserve the
  borrower's provenance through every Pending result, and release or return the
  loan on Ready/cancellation. Verify shared, exclusive, and pinned references
  through condition/body/step suspension, reject owner mutation while Pending,
  permit it after Ready, and release the loan when a Pending frame is cancelled.
- [x] **ASYNC-01b84a: Retain shared captures through three-phase awaited `#for`.**
  Transfer borrow provenance when a by-value explicitly linear aggregate
  contains references, and use the pre-move provenance when destructuring its
  returned enum payload. Verify a shared capture survives condition/body/step
  suspension, owner mutation is rejected while Pending, and owner access is
  accepted after Ready.
- [x] **ASYNC-01b84b: Treat enum payload loans as path alternatives.** When a
  value can hold references in different enum variants, check each variant's
  loans as a separate execution path while still combining references stored
  together in one variant. Preserve nested variant choices and verify that
  exclusive states do not create false mutable-alias errors.
- [x] **ASYNC-01b85: Suspend on the success path after awaited `#let-else`.**
  Lower the matching continuation as a concrete async child while retaining
  pattern bindings and outer captures. Select it only after a match, keep the
  mismatch arm's awaited return independent, and preserve Pending/resume for
  either child. Verify a captured value and pattern payload through native
  execution, alongside a mismatch child that also suspends.
- [x] **ASYNC-01b86: Track loans through awaited `#let-else` success children.**
  Retain an exclusive external reference in the selected success child across
  Pending, reject owner access while suspended, and release the loan when Ready
  so the caller can access the owner again. Verify the mismatch path remains
  independent and test both rejected and accepted accesses.
- [x] **ASYNC-01b87: Prove named aggregate captures in composed loop tasks.**
  Resolve named capture copyability from the project’s structural ownership
  metadata, carry a non-linear struct through condition/body Pending states,
  and reject an explicitly linear version with the capture name. Include the
  resulting capability set in generated-source cache identity.
- [x] **ASYNC-01b88: Suspend multiple awaits in an awaited `#while` body.**
  Lower the full multi-statement body into a concrete nested async child so its
  locals survive each Pending state and awaits resume in source order. Construct
  the child only after the awaited condition is true; verify two native
  Pending/resume transitions followed by a false condition that skips the body.
- [x] **ASYNC-01b89: Relay terminal loop transfers from multi-await bodies.**
  Carry a body-completion status from the nested async child so terminal
  `#continue` resumes the condition and terminal `#break` exits the loop.
  Preserve transfers inside nested loops and reject labeled or nonterminal
  outer-loop transfers; verify both cases after multiple Pending transitions.
- [x] **ASYNC-01b90: Join conditional loop transfers after body suspension.**
  Lower terminal `#if`, `#match`, and `#block` branches containing `#break` or
  `#continue` into the child frame's explicit stop status. Preserve branch
  effects and treat nontransferring branches as continuation; verify both `#if`
  outcomes, a `#match` arm, and native resumption through multiple Pending states.
- [x] **ASYNC-01b91: Retain typed captures in nested loop-body tasks.**
  Pass structurally Copy named aggregates into the nested async body frame in
  source parameter order, use their fields across multiple awaits and a
  conditional await, and preserve them for the outer continuation. Reject an
  explicitly linear version with the offending capture name.
- [x] **ASYNC-01c: Permit self-references only in pinned async frames.**
  First give generated frames a stationary polling/cancellation lifecycle;
  then initialize owned fields before pinning and establish internal
  references with field-sensitive loans. Reject escaping references and
  incompatible projections. Require cancellation to end internal loans before
  consuming their referents; test movement, cancellation, and storage lifetime.
  Completed by ASYNC-01c1 through ASYNC-01c2r: pinned frames now support
  immutable and exclusive self-references into promoted owners and enum
  payloads, with state-preserving poll transitions and explicit cancellation.
- [x] **ASYNC-01c1: Keep async frames stationary across polling.** Add an
  opt-in pinned-frame representation whose poll and cancellation operations
  borrow the frame in place rather than consuming and returning it by value.
  Do not permit self-references yet. Keep state transitions and cancellation
  explicit, reject moving, replacing, or destroying the pinned owner while its
  handle is live, and verify Pending/resume, cancellation, movement, and escape.
  `@async-fn-pinned` now returns a pinned `Frame` struct shell containing a
  distinct `Frame-state` field. Poll and cancellation project a pinned
  reference to that field; their unsafe move-out/write-back transitions no
  longer move the shell or its other fields. Keep internal self-references
  unsupported until ASYNC-01c2 adds stable owned fields and loan cleanup.
- [x] **ASYNC-01c1a: Add checked unsafe access to pinned frame storage.** Add
  `#pin-read` and `#pin-write` for generated in-place state transitions.
  Require `#unsafe`, support aggregate values in native codegen, preserve
  existing borrow conflicts, and test stack-backed aggregate reads/writes,
  unsafe diagnostics, and writes conflicting with a live projected reference.
- [x] **ASYNC-01c2: Form checked immutable references into pinned async frames.** After
  the stationary lifecycle is established, allow internal references only
  after their owned referents are initialized and pinned. Track field-sensitive
  loans through every state transition; reject moves, replacement, incompatible
  projections, return, and cancellation that could invalidate a live internal
  reference. Mutable projections are a separate extension under ASYNC-01c2r.
- [x] **ASYNC-01c2a: Initialize pinned self-reference fields in place.** Add a
  checked operation that can install a reference into a reference-valued field
  through a mutable pinned struct reference without replacing the containing
  object. Preserve field-sensitive loan identity so a reference to one field
  may be stored into a disjoint reference field, while overlapping writes,
  moving the referent, and owner destruction remain rejected. Exercise a
  native self-reference setup and a conflicting-projection diagnostic. This
  is only the borrow-checking primitive; async frame lowering must still emit
  stable slots and end internal loans during cancellation.
- [x] **ASYNC-01c2b: Update pinned Copy control fields independently.** Permit
  in-place writes to scalar/fieldless-enum fields and shared-reference fields
  through a mutable pinned struct reference. Preserve field-sensitive loans so
  a state tag can change while another field is borrowed, but a write to the
  borrowed referent itself is rejected. Verify native state changes and both
  disjoint/overlapping borrow cases. This is groundwork only; linear slot
  transitions still need explicit Empty/Full state and move-out operations.
- [x] **ASYNC-01c2c: Generate stable linear Empty/Full slots.** Add a concrete
  `@pin-slot` generator with a linear slot enum and an explicitly unsafe
  move-out operation that replaces the value with Empty at the same pinned
  address. Keep the unsafe generated code inspectable; verify a native Full to
  Empty transition and reject taking the slot while it is borrowed. This is a
  storage primitive only; async-frame lowering must still use slots and order
  internal-reference cleanup before taking their referents.
- [x] **ASYNC-01c2d: Keep disjoint self-references live across slot moves.**
  Place a generated linear slot beside an owned referent and a self-reference
  in a pinned struct. Move a value out of the slot while the reference into
  the sibling referent remains live; prove the reference still reads the same
  value, then clear it before consuming the owner. Preserve the separate
  rejection of taking the slot through an overlapping live borrow.
- [x] **ASYNC-01c2e: Borrow pinned enum payloads in place.** Permit
  borrowing through a pinned enum reference, preserving the variant payload's
  checked place identity and pinned provenance. Verify a
  native self-reference into a generated slot payload and reject moving that
  slot while the payload loan remains live.
- [x] **ASYNC-01c2f: Separate pinned payload borrows from value projection.**
  Add `#pin-get-payload` and `#pin-get-payload-mut` as explicit shared and
  exclusive in-place borrows. Keep `#get-payload` value-only so pinned storage
  cannot appear to be safely extracted by value. Check the active variant at
  runtime, track payload loans in typed flow, and document both forms.
- [x] **ASYNC-01c2g: Reject stack pins captured by pinned async frames.** Add a
  regression proving `@async-fn-pinned` cannot convert a reference to a local
  stack pin into an internal self-reference merely by capturing it across
  `#await`. Preserve the source-local lifetime diagnostic until generated
  stable slots and frame-internal loan cleanup are implemented.
- [x] **ASYNC-01c2h: Refill pinned linear slots without moving their address.**
  Extend `@pin-slot` with a safe try-insert operation that writes into an Empty
  slot in place and returns the unconsumed value when the slot is Full. Keep
  the move-out operation explicitly unsafe, and verify both insertion paths
  natively so generated async frames can reuse stable storage across states.
- [x] **ASYNC-01c2i: Retain a parameter-backed self-reference across Pending.**
  For a top-level immutable `#pin-ref` binding initialized by `#pin-borrow` of
  an owned function parameter, hoist the owner to a stable sibling frame field
  and form the reference only after pinning. Require that the owner is used
  only to initialize this reference; carry the reference through the suspended
  state, preserve the field-sensitive owner loan, and require cancellation
  cleanup to end the state scope before the owner can be mutated or destroyed.
  Verify native Pending/resume and cancellation, generated frame layout, and a
  rejected owner mutation before cleanup. Body-local owners and other
  self-reference shapes remain open under ASYNC-01c2.
- [x] **ASYNC-01c2j: Borrow one field of a parameter-backed owner.** Allow the
  pinned async self-reference initializer to use one direct `#get` projection
  from an owned struct parameter, while keeping the whole owner in stable frame
  storage. Resolve the generated field address through the pinned frame and
  preserve the field-sensitive loan. Verify native Pending/resume and reject
  owner replacement before cleanup. Body-local owners remain unsupported.
- [x] **ASYNC-01c2k: Borrow through nested inline owner fields.** Extend the
  pinned async self-reference projection path to traverse multiple inline
  struct fields without crossing a reference or pointer boundary. Accumulate
  the correct frame-relative layout offset, retain field-sensitive overlap
  checks, and verify nested-field Pending/resume, cancellation, and owner
  mutation rejection in the native example.
- [x] **ASYNC-01c2l: Promote a first-statement local owner into the pinned frame.**
  Move an immutable body-local owner into the stable frame before returning it,
  then form its internal reference only after pinning. Require the owner to be
  the first function statement; reject unsupported shapes explicitly. Verify
  native Pending/resume, generated layout, and diagnostics for late owners.
  ASYNC-01c2m extends initializer inputs.
- [x] **ASYNC-01c2m: Initialize promoted local owners from parameters.** Allow
  the first-statement local owner initializer to read ordinary function
  parameters before moving the value into the frame. Preserve linear moves and
  explicit Copy semantics when a parameter is also live after suspension.
  Verify a parameter-fed nested owner in the native example and retain the
  late-owner rejection.
- [x] **ASYNC-01c2n: Isolate mutable self-reference forwarding controls.** Add
  passing controls for forwarding an exclusive pinned reference alongside a
  shared waker and for moving pinned frame state while borrowing a disjoint
  owner field in ordinary code. These show the remaining mutable self-reference
  failure is in generated poll-state transfer; they do not complete ASYNC-01c2.
- [x] **ASYNC-01c2o: Retain multiple disjoint self-references across Pending.**
  Allow a pinned async frame to form immutable references to two disjoint fields
  of the same promoted owner, retain both in its suspended state, and end both
  loans on completion or cancellation. Verify native results, reject mutable
  borrows of either projected field while pending, and permit owner mutation
  after cancellation cleanup.
- [x] **ASYNC-01c2p: Retain a self-reference into a pinned enum payload.**
  Recognize a `#pin-get-payload` initializer whose enum owner is a promoted
  frame field. Preserve the payload's exact place through temporary
  `#pin-borrow` expressions, emit checked in-place payload access on each poll,
  and retain that reference across Pending. Verify native execution and reject
  a conflicting mutable borrow of the enum owner until the task is resumed.
- [x] **ASYNC-01c2q: Borrow a struct field inside a pinned enum payload.**
  Preserve `#pin-get-payload` as the checked root when `#pin-borrow` projects
  one of its inline struct fields. Retain the exact nested field reference in a
  pinned async frame across Pending, verify native reads after resume, and
  reject a mutable borrow of the containing enum while the loan is live.
- [x] **ASYNC-01c2r: Retain exclusive self-references across async suspension.**
  Create each `#pin-borrow-mut` only in the frame's initial state, then transfer
  that exclusive reference through generated state and helper calls without
  reborrowing or aliasing it on resume. Preserve field-sensitive access so
  disjoint state transitions remain legal while overlapping owner access,
  replacement, and movement remain rejected. End the loan on Ready or explicit
  cancellation. Verified native mutation after Pending/resume and cancellation
  followed by owner mutation, plus diagnostics for duplicate exclusive borrows
  and overlapping owner access. The legacy borrow checker uses typed return
  summaries for exclusive results to avoid treating unrelated shared inputs
  (such as the waker) as mutable-reference origins.
- [x] **ASYNC-01d: Connect polling to wake registration.** Integrate local
  wakers with generational tokens and the ready queue, prevent lost wakes
  between registration and Pending, and make stale wakes and duplicate queue
  entries harmless. Reject forged authority until module privacy or opaque
  compiler-owned handles are available.
- [x] **ASYNC-01e: Remove the fixed async suspension-count limit.** Preserve
  unique generated stage names and frame states for functions with more than
  32 sequential awaits. Verify a 33-stage function builds and runs natively.
- [x] **ASYNC-01f: Preserve the originating statement for async lowering errors.**
  Map an error from a later await-bearing statement to that statement's source
  span instead of underlining the first await in the function. Preserve the
  exact await token span when the lowering can identify it.
- [x] **ASYNC-01g: Preserve short-circuiting in awaited loop conditions.**
  Lower awaited right operands of `#bool.&&` and `#bool.||` as branch-selected
  child tasks in `#while` and `#for` conditions. Do not poll the child when
  short-circuiting selects the immediate boolean result; test native behavior.
- [x] **ASYNC-01h: Derive sequential async frame captures from typed CFG liveness.**
  Build a typed, ownership-independent probe of generated resume helpers, use
  stable binding IDs to select values live after each suspension, then regenerate
  the final frame. Keep mutable slots needed for post-resume writes and leave
  nested helper/loop lowering to the full CFG migration.
- [x] **ASYNC-02: Add non-busy waiting and safe asynchronous I/O.** Define a
  bounded ready queue and explicit wake handles (no callbacks), readiness or
  completion registration, and OS-operation ownership. Cancellation must not
  release buffers until completion/cancellation is acknowledged. Test stale
  wake handles, lost wakeups, capacity exhaustion, shutdown, and cancellation.
  The Linux x86_64 implementation covers one-shot and mixed readiness,
  owned descriptor operations, native-AIO completion routing, wake-before-wait,
  and explicit scheduler cancellation. These APIs remain concrete and bounded;
  a portable cross-platform reactor is outside this milestone.
- [x] **ASYNC-02a: Own one-shot timer readiness without retained buffers.**
  Add a concrete Linux timerfd operation with an opaque linear owner, a
  bounded registered wake, blocking kernel wait, explicit poll and cancellation,
  and cleanup of fd and scratch mapping. Verify one-shot completion and
  cancellation before completion in a native example. Runtime-sized bounded
  timer waits are covered by ASYNC-02f, mixed readiness by ASYNC-02h, and
  scheduler shutdown by ASYNC-03b.
- [x] **ASYNC-02b: Return recoverable timer setup errors.** Lower block-valued
  large aggregate branches through indirect result storage, then return a
  concrete success/error enum from timer creation. Clean up each acquired
  resource on syscall failure and report invalid duration without a trap.
  Cover the invalid-duration path and successful ownership transfer natively.
- [x] **ASYNC-02c: Wait on two owned timers without busy polling.** Borrow two
  distinct opaque timer owners, use one blocking Linux poll call, and validate
  each wake token independently. Reject aliasing the same owner in both slots;
  cover whichever timer fires first, eventual completion of both, and cleanup
  in a native example. Runtime-sized timer registration is covered by
  ASYNC-02f; other readiness sources are covered by ASYNC-02g and ASYNC-02h.
- [x] **ASYNC-02d: Keep native-AIO buffers owned through completion or cancel.**
  Add opaque linear AIO context, pending-operation, and completed-operation
  types. Each submitted read or readiness request owns its mmap containing the
  `iocb`, event record, and read buffer, and shares an immutable borrow of its
  single-thread-only context. Provide blocking `min=1` waiting and cancellation
  that keeps the owner intact until the terminal event is acknowledged; return
  the pending owner on every unacknowledged error. Verify byte contents,
  cancellable eventfd readiness, and native cleanup. Multi-request routing is
  tracked separately in ASYNC-02e.
- [x] **ASYNC-02e: Route concurrent native-AIO completion events.** Put each
  request's owned event-buffer address in `aio_data`. When a blocking wait for
  one request receives another's event, copy the complete record into that
  request's still-owned mapping and continue waiting. Its later wait must
  consume the saved event without another syscall. Route asynchronous cancel
  acknowledgements through the same path. The native regression completes B
  before A, waits for A first, then verifies B's routed result; multiple
  outstanding operations share a !Send/!Sync context safely. Scheduler wake
  integration is covered by ASYNC-03a.
- [x] **ASYNC-02f: Wait over a bounded runtime slice of timer owners.** Accept
  one to four shared borrows of opaque timer owners, reject duplicate owners,
  populate poll records in scratch storage, and perform one blocking poll.
  Notify each ready token independently and return a bit mask of ready slots;
  reject invalid poll events without exposing descriptors or transferring
  ownership. Verify a three-timer native wait and duplicate-owner rejection.
  General readiness sources are covered by ASYNC-02g and ASYNC-02h;
  scheduler shutdown is covered by ASYNC-03b.
- [x] **ASYNC-02g: Add a cancellable, borrowed one-byte readiness read.** Add a
  concrete Linux operation that retains an exclusive destination borrow, uses
  the bounded wake queue, blocks in `poll` rather than spinning, and performs
  the read only after readiness is notified. The kernel never retains the
  destination pointer across Pending or cancellation; destruction retires the
  wake token and releases the borrow. Verify echoed input, EOF, and cancellation
  while the input stream remains open, including mutation after destruction.
  General descriptor ownership is covered by ASYNC-02i, multi-source
  registration by ASYNC-02h, and scheduler shutdown by ASYNC-03b.
- [x] **ASYNC-02h: Share one bounded wait across mixed readiness sources.** Add
  an opaque borrowed source view that adapts concrete timers and byte-read
  tasks without exposing their descriptors or wake tokens. Wait on one to four
  sources with a single blocking poll, notify every ready source independently,
  and reject invalid capacity before touching the kernel. Test a timer and a
  pipe read in the same set, including either source becoming ready first, plus
  capacity rejection. Descriptor ownership is covered by ASYNC-02i and
  scheduler shutdown by ASYNC-03b.
- [x] **ASYNC-02i: Make readiness operations own their descriptors.** Duplicate
  each caller descriptor into an opaque linear operation owner with
  close-on-exec semantics. Close it exactly once on explicit destruction, and
  close it on every later setup failure before returning its setup or cleanup
  error.
  Verify the operation still completes after the caller closes its descriptor,
  invalid-descriptor errors, and cancellation cleanup.
- [x] **ASYNC-02j: Require nonblocking descriptors for readiness reads.** Make
  the read operation reject blocking fds instead of risking a blocking read
  after a readiness race. Provide a distinctly named opt-in that changes the
  open-file-description status flags, return `EAGAIN` as Pending, and document
  that aliases observe the flag change. Test rejection, opt-in, and a competing
  read consuming readiness without stalling the event loop.
- [x] **ASYNC-02k: Consume queued wakes before blocking.** Before entering
  `poll`, take any wake bits already published to the bounded local queue and
  return those ready slots immediately. This preserves a wake issued by a task
  before it returned Pending, instead of sleeping despite the recorded wake.
  Verify an indefinite wait with a disabled descriptor returns from the queued
  wake alone, and that the token is consumed and retired exactly once.
- [x] **ASYNC-03: Add a simple, bounded single-threaded task scheduler.**
  Run ready tasks cooperatively on one OS thread, using the wake handles and
  non-busy waiting from ASYNC-02. Make queue capacity, fairness, wake ordering,
  shutdown, and cancellation behavior explicit. Test multiple tasks sharing
  one event loop, including repeated wakes, exhausted capacity, and idle
  waiting. Keep task ownership on that thread; task migration and worker-pool
  scheduling are outside this milestone.
  - [x] **ASYNC-03a: Poll a fixed homogeneous task set from wake masks.** Add
    `@wake-executor` for one through four statically named tasks sharing
    concrete task, poll, result, and waker types. Poll each once initially,
    then poll only Pending tasks selected by a blocking wait callback's ready
    mask. Validate consecutive unique slots, use direct calls (no function
    pointers), retain completed results, and verify duplicate wake coalescing
    and native completion.
  - [x] **ASYNC-03b: Define scheduler shutdown and cancellation.** Provide an
    explicit wait-error/shutdown result and per-task cancellation handlers;
    ensure pending waker handles, task states, and OS operations are consumed
    in a documented order. Test cancellation while idle and while multiple
    tasks remain Pending. `@wake-executor` now returns a concrete Complete or
    Stopped outcome, stops polling after a wait stop/error, and invokes each
    slot's cancellation function in descriptor order, including already-Ready
    states. Native coverage cancels two Pending timer-backed tasks and one
    completed task while idle.
  - [x] **ASYNC-03c: Verify scheduling fairness and bounded wake behavior.**
    Test multiple simultaneous ready tasks, wake bursts and coalescing,
    capacity exhaustion, repeated idle waits, and prove no task is polled while
    its bit is absent. Define the wait callback's zero-mask and invalid-bit
    behavior. Coverage includes three fixed slots with successive masks that
    wake two tasks together and leave the third untouched until its bit is
    returned; capacity and slot validation; duplicate wake coalescing; and
    repeated waits before completion. The callback contract explicitly states
    that zero and non-pending bits are ignored, so a mask with no pending bit
    can make no progress.

## Test reliability

- [x] **BACKEND-ABI-01: Pass oversized enums through indirect storage.** Keep
  enum layout size independent of the six-register direct-return limit, and
  route large enum parameters/returns through the existing indirect aggregate
  ABI. Verify a native function returning an enum with a nine-word tagged
  array payload, pass it as an indirect argument, then match and read its last
  element.
- [x] **BACKEND-ABI-02: Store large enum match results directly to slots.**
  Lower assignments whose right-hand side is a match by dispatching each arm
  into the destination enum's existing stack storage, rather than trying to
  materialize an oversized enum in return registers. Preserve guards,
  discriminants, and payload move semantics. Route nested indirect aggregate
  calls through temporary slots into the correct return-storage offset.
  Verify large enum matches and generated async run-state enums natively.

- [x] **BACKEND-REF-01: Preserve the base of multiword reference fields.**
  Load projected aggregate words through a dedicated scratch register so the
  first value word cannot overwrite the address for later words. Cover a
  three-word array field read through a struct reference with a native
  regression, and retain the bounded ready-queue example as a second user.

- [x] **TEST-01: Avoid flaky numeric differential process timeouts.** The
  native oracle launches many short-lived programs, so a 3-second per-process
  deadline could expire from host scheduling pressure after the all-example
  suite. Increase the bounded deadline to 10 seconds; keep the seeded oracle
  and signal/result assertions unchanged.

## Earlier completed foundation

- [x] S-expression lexer and parser with comments, strings, characters, and
  numeric literals.
- [x] Nix development shell with the Rust toolchain.
- [x] Explicit `#`-prefixed builtin syntax; legacy unprefixed forms rejected.
- [x] Explicit typed bindings, free-standing functions, and explicit returns.
- [x] Require named function arguments using `#call` and `(: name value ...)`; reject
  positional calls and validate argument labels at compile time.
- [x] Builtin scalar types through 128-bit integers, floats, `bool`, `char`,
  unit, and never.
- [x] Explicitly qualified arithmetic, comparison, shift, cast, and overflow
  operations.
- [x] Structs, enums, tuples, arrays, aliases, destructuring, and keyed
  struct construction.
- [x] Linear values with structural plain-old-data `Copy`, explicit `#clone`,
  explicit `#forget`, and consume-before-scope/return checks.
- [x] Recursion rejection and finite call-graph checking.
- [x] Native x86-64 assembly generation and direct `as`/`ld` binary linking.
- [x] Internal and external imports with cycle detection and deduplication.
- [x] `@` generated declarations, user generators, `#gn-*` operations,
  quasiquote/unquote, generator limits, and generator error reporting.
- [x] Generated-code caching keyed by generator code, dependencies, and
  literal invocation inputs.
- [x] Raw pointers, `#unsafe`, unsafe statics, and pointer access checks.
- [x] Structural `Send`/`Sync`, unsafe overrides, and generated thread
  spawn/join operations.
- [x] Compile-time `#cfg-*` forms, automatic platform keys, and
  `--collect-cfgs`.
- [x] Lexical borrow checking with reference provenance, control-flow joins,
  loop handling, mutable references in aggregates, field-sensitive struct
  places, derived-field suspension, and explicit `#drop`/`#forget` loan release.
- [x] Audit public documentation and checklist claims against implemented
  behavior; replace the obsolete README generic examples and update the build
  instructions to describe direct `as`/`ld` linking and concrete generators.

## Next implementation work

### Borrowing and references

- [x] Extend place-sensitive borrowing to nested tuple fields and array
  elements, including dynamic array indices that conservatively conflict with
  every element. Tuple and array projections now work through references.
- [x] Add borrowable enum-payload projections with explicit
  `#get-payload reference Variant index` syntax and place-sensitive conflict
  checking.
- [x] Define and implement reference projection rules for nested aggregates,
  including references stored inside tuple and struct aggregates and nested
  reference chains.
- [x] Add borrow-checker diagnostics with stable `E4100`, function/statement
  context, exact source underlines for borrow operators and conflicting
  borrow/read/write accesses, and preserved generator/source context where
  available.
- [x] Add regression tests for the supported projection and control-flow
  combinations, including nested tuples, static/dynamic arrays, branch-local
  projections, and multiple derived field loans.
- [x] Remove stale comments that described references as not being first-class
  values.
- [x] Add unsafe raw-pointer-to-reference operations whose explicit reference
  anchor feeds inferred lifetime provenance into the borrow checker.

### Values, memory, and aggregates

- [x] Specify the dynamic allocation ABI and allocator ownership model in
  `docs/allocator.md`.
- [x] Define the concrete allocator-borrowing `@vec` representation and the
  explicit `@vec-sort` invocation contract.
- [x] Implement usable allocator-backed vectors: construction, checked
  reserve/growth, push, indexed read/write, pop, and explicit destruction.
  Allocation and capacity failures must be represented with generated
  `Result` types, including zero-sized element behavior.
- [x] Implement `#ptr-offset` for raw pointers, with a `usize` element index,
  explicit `#unsafe` boundaries, zero-sized pointee handling, and checked
  byte-offset/address overflow.
- [x] Add typed `#ptr-null` construction so allocator-backed collections can
  represent an empty, zero-capacity storage state without an uninitialized
  pointer.
- [x] Add non-consuming `#ptr-is-null` so allocator wrappers can report
  allocation failure without losing the returned pointer value.
- [x] Implement `@vec-sort` using its literal comparator function name, with
  compile-time signature validation and no runtime function-pointer values.
- [x] Define allocation failure, deallocation, destruction, and current leak
  behavior in `docs/allocator.md`.
- [x] Add aggregate `#deref`/`#deref-set` support for aggregates that fit the
  native value registers; larger aggregate ABI support remains a separate item.
- [x] Remove backend restrictions on large aggregate returns, arguments, and
  reference projections by routing them through indirect aggregate storage.
- [x] Finish large aggregate lowering for nested multiword fields and payloads
  across returns, globals, reference projections, patterns, and native ABI
  boundaries; several backend branches still report scalar-field-only limits.
- [x] Specify and implement field-wise destruction for reference-containing
  aggregates.
- [x] Define and test deterministic explicit destruction for owned resources
  and generated collections: user/generated destroy functions consume values,
  including after moves/returns and field-wise aggregate destruction; no
  implicit destructor calls are inserted, and `-free` consumes a vector.

### Generators and monomorphization

- [x] Reject angle-bracket generic declarations and applications. Concrete
  specialization is generator-driven, and generic examples use concrete names.
- [x] Add generator dependency tracking for imported files and compiler
  configuration values, not only generator definitions and nested generators.
- [x] Make generated-file cache entries durable across compiler-version and
  target changes by including both values in the cache key namespace.
- [x] Improve generator diagnostics so failures identify the generator,
  invocation, argument position, and generated source location.
- [x] Add capability-aware generators without hidden typeclass/interface
  requirements; `#capability` declarations are checked against explicit
  generator parameter requirements before evaluation.

### Backend, platform, and interoperation

- [x] Add an explicit target description for the native x86-64 System V ABI;
  unsupported target names are rejected rather than silently treated as host.
- [x] Implement the native x86-64 assembler/linker path; normal compilation
  invokes `as` and `ld` directly, without requiring Clang.
- [x] Define constrained FFI declarations: `#extern-fn` uses the target C ABI,
  accepts directly passed scalar signatures only, and requires `#unsafe` at
  every call site.
- [x] Add generated native thread creation/join behavior with structural
  `Send` checks, captured-borrow tracking, and explicit runtime failure paths.
- [x] Replace thread null/zero failure sentinels with explicit fallible
  spawn/join results. Preserve task ownership and borrow state on failed join,
  and make it possible to distinguish a valid zero result from runtime failure.
  Spawn reports allocation versus creation errors; join failure returns its
  still-owned handle and native error code. Runtime tests cover both direct and
  indirect result layouts and injected spawn/join failures.
- [x] Add compile-and-run coverage for the binary pipeline under the Nix
  development shell.

### Language completeness and tooling

- [x] Add public structured diagnostics with stable phase/category codes,
  optional source spans, and notes while retaining the existing string APIs.
- [x] Add a parser-backed formatter and syntax-aware pretty-printer, exposed
  through `format_source` and `--format INPUT [OUTPUT]`.
- [x] Preserve semicolon comments and source annotations in formatted output
  (commented files are currently preserved verbatim); keep parser-backed
  canonical formatting idempotent for generator templates and generated
  declarations.
- [x] Add `--check-examples [DIRECTORY]`, which checks all `.lim` examples and
  reports failures by source file, including generated examples.
- [x] Add dependency-free `lim.project` metadata with a project name and
  manifest-relative module paths; these are loaded by the binary CLI, alongside
  the explicit `CompileConfig::add_module_path` and `--module-path` APIs.
- [x] Extend project metadata with a versioned schema, explicit source root and
  output directory, target/link settings, and validation for duplicate or
  nonexistent module roots.
- [x] Document the core grammar and builtin semantics, including ownership,
  `#unsafe`, thread, generator, cfg, and explicit arithmetic forms.
- [x] Closures, function pointers, methods, traits, and user interfaces are
  documented as permanent non-goals; named free-standing functions and
  generators provide the explicit alternatives.

### Newly identified runtime and language gaps

- [x] Add end-to-end tests that compile and execute generated vector operations
  with a real allocator, covering growth, allocation failure, element
  destruction, and allocator-borrow lifetime enforcement.
- [x] Make FFI linking configurable for external libraries and object files;
  `#extern-fn` remains restricted to scalar signatures, while binary compilation
  accepts repeated `--link-lib` and `--link-object` arguments in deterministic
  object-before-library order after the built-in C and pthread libraries.
- [x] Specify reusable C layout metadata for external aggregates: explicit
  `#repr-c`, declaration-order fields, natural alignment/padding, tagged-union
  enum layout, `#size-of`/`#align-of`/`#offset-of`, and explicit `#abi-c` on
  external functions. By-value aggregate FFI remains rejected until Lim's
  runtime aggregate representation can match C's ABI.
- [x] Define a recoverable compilation/linking diagnostic API end to end.
  `compile_source_to_assembly`, generated-source materialization, and
  `link_native_binary` return structured diagnostics with stable phase codes;
  the CLI uses those APIs for normal binary and assembly builds while legacy
  string-returning APIs remain available.
- [x] Add Rust-style CLI diagnostic rendering with source excerpts and
  underlines for errors that carry or expose a source location.
- [x] Carry source spans from parsed expressions into type, ownership, borrow,
  unsafe, generator, and codegen errors. Type mismatches now select
  identifiable incompatible operands (including normalized typed literals)
  for local and top-level initializers, and borrow escapes identify the local
  referent. Each analysis maps a failure to the offending token or projection
  when identifiable, otherwise to the smallest retained value expression or
  declaration span. Unknown types in expressions and declarations, and
  representative borrow, linearity,
  unsafe, generator, and codegen diagnostics now have exact-range assertions.
  Named-call and struct-literal lowering also identifies unknown, duplicate,
  and omitted arguments/fields at their source forms. Duplicate declarations,
  unsafe-impl targets, and specialization-time validation now underline the
  relevant name where that name is available in the original form. C-enum
  discriminant, thread-task worker/result, and task-in-aggregate diagnostics
  now identify their invalid source token/type as well. Thread-task handles in
  function signatures and type aliases also underline the task type token.
  Missing-import and import-cycle failures underline the path string, while
  unknown cfg keys underline the referenced key token.
  `Send` failures on thread workers now underline the offending parameter type,
  not the unrelated worker return type, even when an earlier local has the
  same name as the unknown type. Unsafe external calls underline the callee
  in `#call` syntax, and raw-pointer safety errors underline their builtin.
  Diagnostic hunks expand tabs at
  four-column stops before positioning underlines; common wide and combining
  Unicode characters are included in display-column calculations, and lexer
  columns count Unicode scalars to match the renderer.
  Non-constant global initializers now highlight a nested `#call` that makes
  the initializer invalid instead of the larger enclosing constant expression.
  Imported and generated-source parser errors retain their original lexer or
  parser spans instead of reconstructing one-character spans from locations;
  this covers quoted tokens with whitespace and escaped quotes. UI
  diagnostics now also assert exact token alignment for unknown identifiers,
  recursion, and codegen errors, including underline widths. Repeated linear
  field moves underline the repeated `#get` projection, and repeated
  array-element moves underline the
  repeated `#index`, instead of the enclosing `#let` statement. CLI tests
  assert full unterminated-string spans and zero-width end-of-file parse spans.
  Every UI fixture is required to declare a precise fragment or a custom
  alignment assertion.
  Mismatched `#if` branch values underline the incompatible branch, excluding
  the condition expression from type-hint matching. Mismatched `#match` arms
  similarly exclude the scrutinee and patterns from arm-value selection.
  Named-call type mismatches carry the parameter name through type checking
  and underline that argument's value, even if an earlier argument has the
  same type. Struct-literal field mismatches identify the responsible named
  field value rather than a same-typed value from an earlier field. Enum
  constructor payload mismatches carry the payload index and underline the
  corresponding constructor argument.
  Explicit `#return` type mismatches also underline the incompatible returned
  expression, covered by a UI test. Tuple and array construction diagnostics
  retain the mismatching element index and underline that element rather than
  another value with the same inferred type; extra constructor values and
  missing-element constructor heads are also pinpointed, including nested
  tuple constructors. Borrow conflicts distinguish an
  accessed binding from a same-named struct field selector, call callee, or
  named-argument label.
  The UI diagnostic suite requires every fixture to assert a precise source
  fragment and underline width, or a custom exact-alignment check; new
  diagnostics must add coverage under the same rule.
  Unknown named types in local `#let` annotations underline the annotation,
  including when type checking represents the failure as an expected-type
  mismatch. Immutable assignments now underline the assigned binding instead
  of the entire assignment form. Named-type mismatches in destructuring lets
  underline the declared type rather than an identically named pattern
  constructor. Mutable-borrow-through-immutable-reference errors underline
  the owner argument. Invalid operands to `index`, `slice-of`, `slice-len`,
  `get`, `get-payload`, and `deref-set` also receive argument-level spans with
  UI coverage. Invalid conditions, array indices, and out-of-range shift counts
  also select their offending operand. Generator capability checks now pinpoint
  missing, mismatched, and duplicate operation names, including the later
  duplicate occurrence;
  duplicate capability/type pairs and generator declarations point at their
  repeated identifier. Generator-function recursion diagnostics underline the
  recursive `#gn-call` target, and duplicate generator parameters underline
  the repeated parameter. Builtin arity errors underline the operator
  identifier, including its full typed spelling; unresolved calls underline
  the function name. Non-exhaustive match diagnostics underline the `#match`
  head. Invalid array/struct assignment targets underline
  the named target instead of the full statement. Missing struct fields and
  enum payload variants underline the missing member name, and invalid enum
  match arms underline the variant pattern rather than treating it as an
  operator symbol. Unknown enum variants in `#let-else` patterns also underline
  the pattern token. Repeated boolean, enum, and wildcard match patterns
  underline the later duplicate. Out-of-range and repeated integer match
  patterns underline the corresponding literal token. Range-pattern errors
  underline the invalid range or its upper bound when the bounds are reversed;
  duplicate character patterns underline the later character literal. Enum
  match payload-arity errors underline the affected variant pattern.
- [x] Specify generator capability contracts beyond name membership: bind each
  capability/type pair to concrete free-standing operation signatures, validate
  function existence and exact signatures before expansion, and include a
  deterministic capability-contract hash in generated-code cache keys.
- [x] Add a soundness-focused audit and adversarial regression suite for
  unsafe pointer operations, reference provenance through aggregate/control
  flow forms, `Send`/`Sync` overrides, and generated destruction paths;
  `docs/soundness-audit.md` maps each invariant to its regression evidence and
  records the limits of unsafe promises.

## Remaining hardening and platform work

These items close known gaps between the implementation, its safety claims,
and the documented behavior. They are not prerequisites for the current
single-target experimental compiler, but should be completed before treating
these areas as stable.

### Safety audit and ownership

- [x] Re-audit thread spawn/join failure paths, including task-handle
  ownership and captured borrows on every success and error branch. Reconcile
  the checklist claims, regression tests, and `docs/soundness-audit.md`; add
  adversarial tests for any uncovered paths.
- [x] Extend the soundness audit with explicit invariants and adversarial
  tests for unsafe `Send`/`Sync` overrides, raw-pointer-derived references,
  and unsafe destruction/allocator interactions. Clearly distinguish
  compiler-enforced guarantees from programmer promises.

### Diagnostics and generated source

- [x] Add CLI UI regression fixtures for lexical/parser errors, imports and
  cycles, cfg and type/named-call errors, struct literals, borrow, linearity,
  top-level type mismatches, unsafe, recursion, duplicate
  parameters, fields, local/cross-enum variants, types, and recursive aliases;
  thread ownership and thread-safety; generator invocation,
  capability-contract and #gn-fn recursion failures; and codegen failures.
  Assert diagnostic categories, source lines,
  underlines, and key token alignment, including imported files and nested
  expressions.
- [x] Ensure source-level compilation errors carry a source location and
  underline the responsible Lim statement, declaration, or expression across
  parsing, imports/cfg, generators, type/ownership/borrow/unsafe checking, and
  code generation. CLI UI coverage exercises representative failures in each
  phase. Some diagnostics use a containing statement/declaration span where
  the exact inner token is not retained; exact-span coverage remains tracked
  separately above.
- [x] Add diagnostic regression tests for nested expressions and imported
  generated source locations, asserting the exact highlighted source range.

### Native ABI and targets

- [x] **NATIVE-01: Encode Lim's x86-64 instructions in a dedicated module.**
  Add a dependency-free instruction encoder under `src/` with typed operands,
  registers, memory addressing, widths, labels, and relocations. Keep frontend
  parsing and semantic analysis out of this module. Cover the instructions
  emitted by the current backend, including integer, floating-point, atomic,
  and thread/syscall paths. Reject unsupported `#asm` instructions with a
  precise diagnostic rather than producing incorrect bytes. Compare encoded
  instructions and executable behavior with the existing toolchain during
  migration.
  The dedicated encoder handles integer/control-flow, SSE and x87 scalar
  arithmetic, static constants, indexed memory, repeated numeric labels,
  atomic operations, and generated thread assembly. All 318 examples now
  compile with `PATH` restricted to an empty directory; the full exact-outcome
  manifest passes. Focused byte-level and unsupported-assembly tests exist;
  The complete example manifest and full test suite pass under the internal
  encoder, including hand-written inline assembly and unsupported-form
  diagnostics.
- [x] **NATIVE-02: Write self-contained Linux x86-64 ELF binaries directly.**
  Lay out code, read-only data, writable data, entry stub, load segments, and
  permissions in the compiler. Resolve local/global labels and PC-relative
  relocations, check displacement and size overflow, and publish the executable
  atomically. Retain `--emit-asm` for inspection. Test ELF headers, section and
  segment permissions, reproducible bytes, and the native example suite.
  Compiler and object-file constants now occupy a separate non-executable,
  non-writable PT_LOAD; code remains RX and mutable data RW. Static and dynamic
  segment tests, object relocations, the full example manifest, and the full
  test suite pass.
- [x] **NATIVE-03: Remove `as` and `nm` from normal compilation.** Use the
  encoder's symbol definitions and unresolved references directly to decide
  whether a program needs foreign linkage. Preserve detection of foreign
  references from `#asm`, including references without `.extern` directives.
  Keep symbol diagnostics and source locations when resolution fails.
  Compiler-owned definitions/relocations and a checked ELF64 object reader
  replace tool-driven symbol inspection. Neither tool is invoked in the
  compilation path, including foreign-linking and inline-assembly cases.
- [x] **NATIVE-04: Link foreign objects and libraries without `ld` or `cc`.**
  Read supported ELF relocatable objects and their symbols/relocations;
  resolve library dependencies and emit the dynamic ELF metadata required by
  the supported Linux target. Specify the dynamic loader path as target
  configuration, not by executing a C compiler. Preserve `--link-object`,
  `--link-lib`, and referenced foreign functions; test mixed Lim/foreign
  objects, missing symbols/libraries, rollback on failure, and runtime output.
  The internal linker handles text/rodata/data/BSS, supported ELF64 RELA
  relocations, libc and explicit shared libraries, and eager GOT resolution.
  Runtime, missing-library, mixed-object, PIC GOT, and rollback tests pass.
  Direct unresolved PC32 references to sized shared-library data use COPY
  relocations. Writable-section R_X86_64_64 references use dynamic relocations;
  PC-relative call, GOT, and COPY references work from writable sections.
  Undefined weak object symbols resolve to zero when no object defines them.
  TLS, text relocations requiring loader writes, and unsupported ELF forms
  remain explicit errors rather than silently producing invalid binaries.
- [x] **NATIVE-05: Remove external build tool invocations and dependencies.**
  The compiler, benchmark, and default tests no longer invoke `as`, `nm`,
  `ld`, or `cc`; ELF object fixtures are built in Rust, the Nix shell no longer
  lists clang/lld, and all examples build with an empty PATH.
- [x] Make `#repr-c` layout guarantees match actual Lim storage and the C ABI,
  or narrow the feature and its documentation so layout-query results cannot
  be mistaken for permission to pass or reinterpret Lim aggregates as C
  values.
- [x] Implement and test by-value C aggregate arguments and returns, including
  structs and enums, or explicitly keep them unsupported until the internal
  representation and target ABI agree.
- [x] Define the supported target policy and add a target/ABI test matrix.
  Unsupported targets must continue to fail explicitly; add a backend and
  linker path for each newly supported target.

## Next development priorities (September 2026 audit)

These are follow-ups beyond the completed baseline, not claims that every
limitation below is a soundness bug. Implementation must retain explicit
types, ownership and destruction, concrete generators, and free-standing
functions; no implicit dispatch, runtime recursion, or external Rust crates.
Each item requires documentation and regression coverage before being checked.

### Priority 1: semantic consistency and safety guarantees

- [x] Specify and enforce evaluation order for named calls and aggregate
  construction. `normalize_call_expr` in `src/lib.rs` currently rearranges
  argument expressions into parameter declaration order. Decide explicitly
  whether evaluation follows source order or declaration order; if source
  order, stage values before ABI argument placement. Apply the same documented
  rule to struct field initializers. Test reordered arguments/fields with
  observable side effects, traps, moves, and conflicting borrows; ensure
  borrow checking and native execution use the same order.
- [x] Support destructuring aggregates that retain references.
  `Statement::Destructure` and `Statement::LetElse` in `src/borrowcheck.rs`
  currently reject these values wholesale. Transfer field-specific origins,
  loans, and mutable-reference ownership to pattern bindings, including
  nested structs, tuples, and enum payloads. Accept returned wrappers whose
  referents remain alive; reject escaped locals, duplicated mutable loans,
  and parent access during a derived mutable borrow. Cover both let-else
  branches and explicit consumption of remaining linear fields.
- [x] Remove register-count limits from otherwise legal aggregate projections.
  `src/codegen.rs` still rejects large fields projected through references and
  large enum payload projections. Reuse indirect aggregate destinations rather
  than requiring every projected value to fit `VALUE_REGISTERS`. Test nested
  aggregates above the register threshold, zero-sized and mixed scalar fields,
  local/global referents, and inactive enum variants. Preserve the distinction
  between copying a Copy value and illegally moving a linear value out of a
  reference; these tests must execute natively, not only pass type checking.
- [x] Report a conservative stack bound in bytes, not only call depth.
  The backend documentation currently connects finite call depth to a static
  stack requirement. Account for frames, expression temporaries, outgoing
  arguments, indirect aggregate storage, alignment, and generated helpers
  along each call path. Add a stack-usage report with the limiting call chain
  for main and thread entry points. Mark external-call usage unknown unless
  an explicit trusted bound is supplied; do not claim no overflow merely
  because recursion is forbidden. Test nested large calls, repeated loops
  without stack growth, checked size arithmetic, and thread stack budgets.
  - [x] State accurately that finite call depth alone does not prove a byte
    bound or prevent stack overflow, especially across external calls.

### Priority 2: trustworthy generated artifacts and diagnostics

- [x] Detect syntactically valid modifications to cached generated source.
  `cached_generated_source` in `src/generator.rs` verifies the input key and
  parses the `.lim` file, but does not verify its original output contents.
  Store and validate an output digest/length for both inspectable source and
  cached expansions; define whether edits cause regeneration or a diagnostic.
  Test valid edited source, truncation, missing metadata, and stale artifacts.
  Preserve full-key collision checks. Document that checksums detect damage,
  not an attacker who can rewrite both the cache and its metadata.
- [x] Make cache publication robust across concurrent compilers and interrupted
  writes. Current inspectable artifacts publish source and key separately and
  use process-ID temporary filenames. Use unique per-write staging and a
  coherent validated publication protocol, including concurrent library calls
  in one process. Test simultaneous same-key and different-key invocations,
  interruption between publication steps, and cleanup of abandoned temporary
  files; readers must never accept a mismatched source/metadata pair.
- [x] Automatically fingerprint generator implementation changes in cache keys.
  Builtin materialization in `src/lib.rs` currently includes package version
  and a manually maintained `builtin-materializer` revision. Add a deterministic
  implementation/build fingerprint that changes when expansion semantics or
  reachable generator helpers change, even without a package version bump.
  Use the effective compilation target/configuration rather than assuming host
  settings. Test builtin and user-generator hits, helper-only changes, cfg
  changes, and identical reproducible builds without timestamps or local paths.
- [x] Carry diagnostic identity and exact spans through semantic lowering.
  Replace message-text/name-based span recovery in `src/lib.rs` incrementally
  with node IDs, structured error variants, and retained source ranges.
  Preserve expansion provenance so errors can label both the generated code
  and invocation, plus a borrow origin where relevant. Add exact-range UI
  assertions for repeated identifiers, shadowing, reordered named arguments,
  nested `#case` patterns, imports, and cache hits; changing message wording
  must not change the highlighted token.
  - [x] Resolve duplicate named-call parameter spans from retained syntax
    structure instead of recovering the parameter name from diagnostic text.
  - [x] Verify semantic errors from generated declarations retain the
    invocation span identically on cold expansion and cache hit.
  - [x] Assert exact UI source ranges for a shadowed-name type error, a
    reordered named-argument mismatch, a nested enum `#case` pattern mismatch,
    imported-source errors, and a generated semantic error on a cache hit.
  - [x] Replace `"source span …"` and `"conflicting span …"` string metadata
    with structured semantic errors carrying a stable diagnostic category,
    source ID, and byte range from type checking through CLI rendering. The
    checker compatibility API now returns message text only; spans and borrow
    origins stay in structured fields, with regression assertions that neither
    marker appears in its message.
  - [x] Carry function-body and top-level-initializer type-error ranges as
    `Span` data to the CLI diagnostic constructor; retain the string-returning
    checker API as a compatibility wrapper. Unit and UI tests assert exact
    source excerpts and verify these errors need no span text in the message.
  - [x] Carry unsafe-checker source locations as structured spans into the CLI
    diagnostic path; the unsafe-static UI case and semantic unit test pin the
    accessed static without serializing its range into the error message.
  - [x] Carry linear-checker source locations as structured spans into the CLI
    diagnostic path; the existing linearity diagnostic coverage pins the local
    ownership violation without serializing the range into its message.
  - [x] Preserve borrow conflicts and their origin as structured primary and
    secondary spans through CLI rendering; tests assert both exact source
    tokens and distinct rendered hunks without span-marker text.
  - [x] Carry a structured semantic diagnostic category into CLI construction;
    `analysis_diagnostic` consumes that category directly instead of
    classifying errors by searching message text.
  - [x] Stop decoding serialized span markers in `analysis_diagnostic`; the
    CLI now consumes checker-provided spans or retained syntax provenance.
    Imported-source and generated-code UI tests pin their rendered locations.
  - [x] Assign the borrow category at the `#borrow-mut` immutable-reference
    rejection site using an internal diagnostic identity tag; unit and UI tests
    verify the structured category and rendered E4100 without exposing the tag.
  - [x] Resolve duplicate-parameter diagnostics at parameter validation time
    from the retained function declaration tree, and remove the corresponding
    message-parsing branch from `unlocated_analysis_span`; the UI test asserts
    that the second duplicate name is underlined.
  - [x] Resolve duplicate struct-field and enum-variant spans while validating
    declarations, including variants duplicated across enums, and remove their
    diagnostic-message span-recovery branches. UI fixtures pin the second
    declaration occurrence.
  - [x] Carry the recursive call edge's source span from call-graph cycle
    detection, and remove cycle parsing/call-name span recovery from
    `unlocated_analysis_span`; the recursive-call UI assertion pins the callee.
  - [x] Locate out-of-range `#repr-c` enum discriminants during declaration
    validation and remove the corresponding message-parsing span fallback;
    the UI fixture checks the offending discriminant.
  - [x] Locate missing thread-worker names at `#thread-task` validation time
    and remove the dedicated error-message recovery branch; the UI test pins
    the worker identifier.
  - [x] Validate recursive type aliases in source declaration order, retain
    the alias target span at detection, and remove the alias-recursion message
    parsing branch; the UI case checks the target identifier.
  - [x] Locate unresolved types in thread-worker parameters/returns from their
    signature syntax and remove the unknown-type message fallback; the UI case
    checks the exact identifier.
  - [x] Locate thread-worker `Send` failures and reference-containing return
    failures directly at the parameter or return type, and remove their
    dedicated message-based span recovery; UI tests pin the offending type.
  - [x] Carry inconsistent function calling-convention diagnostics from
    declaration validation with the function-name span; a unit regression
    verifies the exact token arrives through the structured checker API.
  - [x] Carry duplicate/invalid unsafe auto-trait implementation diagnostics
    from type validation with the implementation's type-name span, and remove
    their message-based fallback; tests pin the repeated implementation name.
  - [x] Carry thread-task-handle rejection spans from aggregate, alias, global,
    and function validation; remove those dedicated message-recovery branches
    and retain generated-invocation provenance. UI coverage remains green.
  - [x] Remove message-text/name-based fallback span selection from
    `analysis_diagnostic` and delete `unlocated_analysis_span`; duplicate
    type/global declarations now supply their second-occurrence name spans
    directly, and generated diagnostics keep invocation provenance. Full tests
    pass with diagnostics using only structured spans.
  - [x] Preserve user-generator expansion source and invocation provenance;
    cold and cache-hit UI tests independently check both rendered ranges.
  - [x] Preserve builtin-generated declaration source and invocation
    provenance; UI tests assert exact ranges on cold and cached compilations.
  - [x] Select the generator invocation span structurally when generated
    function body syntax has no retained source nodes. The cached
    generated-error UI test asserts the invocation hunk on cold and warm
    compilations.

### Priority 3: collection ergonomics without implicit behavior

- [x] Add explicit ranged immutable subslices. `docs/language.md` currently
  documents immutable slices without ranged slicing. Choose a constructor
  distinct from the slice type, specify half-open bounds and failure behavior,
  and retain the original referent's lifetime through nested slices and
  function returns. Test empty and end-boundary ranges, reversed/out-of-bounds
  ranges, overflow, zero-sized elements, and attempted escape from a local.
- [x] Add mutable slices and an explicit disjoint-split operation. Specify
  exclusive reborrowing, parent suspension, and linear handling of mutable
  views before implementing syntax. A checked split must establish disjoint
  regions without callbacks, implicit copying, or lifetime annotations.
  Test writes through each half, prohibited overlapping views and parent
  access, nested reborrows, zero-sized elements, and return provenance.
  - [x] Fix the surface contract: `#slice-mut T` is the mutable-view type,
    `#slice-mut-of` creates one only from a mutable array reference,
    `#slice-mut-idx` yields an exclusive element reference, and
    `#slice-mut-split view at` consumes the view and returns a pair of
    disjoint mutable views. Bounds are checked at runtime; the parent view is
    unavailable after reborrow/split until the derived view is consumed.
- [x] Establish a safe synchronization foundation for shared allocators and
  other interior-mutable state. Send/Sync classification alone is not a
  synchronization operation. Specify a small explicit atomic API, supported
  scalar widths/alignment, memory-order arguments, and invalid-order errors;
  provide concrete generated wrappers if appropriate. Keep unsafe override
  obligations explicit. Test cross-thread publication and counter updates,
  reject invalid orderings, and document which target guarantees are relied
  upon; stress tests alone are not a memory-model proof.
  - [x] Fix the API contract: `(#atomic T)` wraps supported integer scalars;
    `#atomic-init` initializes one; `#atomic-load`, `#atomic-store`, and
    `#atomic-fetch-add` take an explicit shared reference plus an explicit
    `#memory-*` order. Load/store order restrictions follow Rust's rules;
    atomics are Send+Sync only when their scalar width is supported.
  - [x] Implement checked load/store/fetch-add operations with operation-specific
    memory-order validation and x86-64 lowering; exercise signed and unsigned
    widths and ensure oversized atomics are rejected.
  - [x] Run two native workers against one shared atomic counter, join both,
    and verify the combined update; test rejected load/store orderings in the
    compiler and document the supported x86-64 memory-model mapping.

### Priority 4: tooling and implementation quality

- [x] Format commented source instead of returning the entire file unchanged.
  `format_source` in `src/lib.rs` retains source spans for line comments and
  attaches them to surrounding syntax while formatting declarations, calls,
  `#case` arms, and
  generator quasiquotes without dropping or moving comments to the wrong
  form. Test leading/trailing comments, strings with semicolons, empty lists,
  and formatting idempotence; parsed semantics must remain unchanged.
  - [x] Distinguish actual line comments from semicolons inside string literals
    before deciding whether comment-preserving formatting is required.
- [x] Bound recursive parser nesting and return a source-spanned parse error
  before the Rust call stack can be exhausted. Test the nesting limit at and
  beyond its boundary with generated inputs.
- [x] Add a dependency-free compiler robustness suite with explicit resource
  budgets. Audit import traversal, generator expansion size, aggregate layout
  arithmetic, and diagnostic rendering beyond existing limits. Exercise seeded
  generated inputs and malformed/truncated files in bounded subprocesses.
  Require deterministic diagnostics instead of panics, hangs, or partially
  published outputs; keep minimal reproducers for every discovered failure.
  - [x] Reject aggregate storage/value word-count overflow instead of
    saturating or wrapping layout arithmetic; cover arrays and nested layouts.
  - [x] Bound recursive import depth, import count (including differently
    prefixed repeats), and cumulative source bytes; report the import site.
  - [x] Bound diagnostic excerpts and underline construction for very long
    source lines while preserving source-column alignment.
  - [x] Exercise seeded malformed/truncated inputs in timeout-bounded compiler
    subprocesses; require deterministic diagnostics and no partial assembly.
  - [x] Include failing generator invocations in the bounded subprocess seeds,
    and reject truncated, forged-length, and oversized cache artifacts without
    panicking or trusting partially published generated source.
- [x] Establish reproducible compile-time and generated-code performance
  baselines before optimizing the compiler. Measure lex/parse, import/cfg,
  generation (cold and warm cache), semantic checks, native emission, and
  linking separately on small and large generated projects. Record time,
  peak memory where available, and artifact sizes with toolchain/machine
  details. Include runtime collection and aggregate workloads with checked
  outputs; use results to prioritize work without flaky timing assertions in
  ordinary correctness tests.
- [x] Add a dependency-free regression test that parses every fenced Lim
  example in the language reference and fully compiles every complete example
  containing `main`. Fix stale examples found by the test and describe
  aggregate pointer exposure consistently with the explicit raw-pointer API.
- [x] Audit the remaining language reference against the compiler for canonical
  type-versus-constructor forms, named calls, `#case`, aggregate limits, stack
  bounds, and deliberate negative examples. Compile complete positive examples
  through the backend, and pair each documented rejection with a UI fixture
  asserting its intended diagnostic; document any example that is only a
  syntax fragment or depends on a stated backend limitation.
  - [x] Add exact-span UI rejection fixtures for type names in constructor
    position, positional calls, generic declarations, and angle-bracket calls.
  - [x] Compile every complete fenced positive program through assembly
    generation; the dependency-free `tests/language_docs.rs` harness does so.
  - [x] Pin the documented `#case`, aggregate-overflow, and stack-bound
    rejection/limitation behavior with UI or report tests and cross-reference
    those fixtures in the reference.

## Follow-up audit (2026-09-25)

These items come from inspecting the current implementation and its tests.
Earlier diagnostic work made the checker-to-renderer boundary structured;
message parsing still occurs inside some passes and at other phase boundaries.
Existing passing tests do not establish the stronger guarantees below. Keep
explicit types, explicit destruction, concrete generators, and free-standing
functions. Each item should have its own implementation commit, documentation,
and acceptance coverage.

### Correctness and reliable verification

- [x] **STACK-01: Analyze the actual emitted control-flow graph.**
  `src/stack_usage.rs::parse_functions` skips lines beginning with `.` before
  recognizing labels, including emitted `.L...:` labels. Instruction analysis
  also retains only the last terminator in a block. Recognize local labels,
  split blocks after conditional/unconditional branches and returns, and
  model epilogues and stack adjustments explicitly. Unsupported writes to RSP
  must produce an unknown-bound result or a diagnostic, never a guessed bound.
  Acceptance: analyze real compiler output for asymmetric branches, nested
  loops, early returns, and calls with large temporary arguments. Independently
  verify expected byte bounds, reject positive-growth cycles, and retain
  unknown external-call bounds. Include a regression using `.L` labels rather
  than only hand-written labels that avoid the parser issue.

- [x] **TEST-01: Give every executable example an expected outcome.**
  `scripts/native-sweep.sh` currently counts every exit below 128 as successful
  and every exit at or above 128 as a trap without checking expectations. Add
  a dependency-free expectation manifest distinguishing runnable examples,
  support modules, expected compilation errors, and intentional runtime traps.
  Compile through the production binary linker and assert exact exit status,
  stdout/stderr where relevant, and the expected signal for trap cases.
  Acceptance: an unexpected segfault, wrong numeric result, linker failure,
  timeout, or missing expectation fails the sweep; intentional trap examples
  pass only with their declared outcome. Keep compiler/linker stderr available
  on failure and use uniquely created temporary directories.

- [x] **DIAG-01: Select declaration errors by occurrence and source order.**
  Declaration span maps are keyed by names, and
  `task_type_in_declaration_span` searches `HashMap` task keys. These are
  insufficient to guarantee the responsible occurrence when several names
  repeat or several invalid task types appear. Retain declaration/member IDs
  or direct syntax references at validation sites; choose errors in documented
  source order, independent of hash iteration. Keep generated invocation labels.
  Acceptance: three duplicate declarations underline the second declaration;
  mixed Send/Sync annotations underline the actual invalid annotation; fields
  with multiple task types and same-named selectors identify the rejected type
  occurrence. Repeat tests in fresh processes, through imports, and on cache
  hits to verify deterministic primary and secondary spans.

### Compiler architecture and diagnostics

- [x] **DIAG-02: Remove message parsing inside semantic error producers.**
  `src/typecheck.rs::precise_type_error_span` still extracts tuple indices,
  payload positions, field names, and other details from English messages.
  `BORROW_ERROR_MARKER` also embeds diagnostic identity in a string. Replace
  these with structured error variants carrying operand/node identity and a
  category at the failure site; preserve that identity through named-argument
  reordering and aggregate lowering. Acceptance: eliminate these string
  protocols, and verify that changing the rendered wording leaves exact source
  ranges unchanged for repeated operands, shadowing, nested constructors,
  reordered calls, and mutable-borrow failures. Preserve existing UI coverage.

- [x] **DIAG-03: Extend structured errors across cfg, generation, and codegen.**
  `generator_diagnostic`, `codegen_diagnostic`, and source-error helpers in
  `src/lib.rs` still parse or create `source span`/`source file` strings;
  `src/codegen.rs` also serializes spans into messages. Carry source IDs,
  primary/secondary ranges, and phase/category data directly across those
  boundaries. Use string-returning compatibility wrappers only at public API
  edges. Acceptance: remove metadata serialization and quoted-name recovery
  from these paths; test imported paths containing spaces/colons, nested
  generated failures, cfg errors, and nonconstant initializers. Diagnostic text
  resembling metadata must remain ordinary text and must never select a file
  or location. Cold and cached expansions must report equivalent provenance.

- [x] **COMP-01: Validate once and pass a checked program into emission.**
  `compile_source_to_assembly` runs semantic checks, then
  `generate_assembly_for_target` calls `check_types` again. Introduce an internal
  checked-program boundary so emission can reuse resolved types, validated
  calls, and source identities. Retain validation for public APIs that accept
  unchecked programs, and prevent mutation from invalidating the checked state.
  Acceptance: instrument tests to show one semantic pass per normal compile,
  keep public unchecked entry points rejecting invalid programs, and compare
  native output and diagnostics before/after. Measure effects on large projects
  rather than assuming a speedup.

- [x] **PERF-01: Benchmark the production compiler and linker accurately.**
  `benches/compiler.rs` links using Clang while production uses `as`/`ld`, and
  its assembly-emission measurement includes another semantic check. Benchmark
  the production APIs with clearly separated and end-to-end timings; describe
  any phases that deliberately include earlier work. Add call-chain, branch,
  reference-aggregate, and generator-heavy workloads beyond independent leaf
  functions. Acceptance: record a new machine/toolchain-qualified baseline for
  cold/warm runs, compare against the old sample with its limitations stated,
  and check runtime outputs and artifact sizes without timing gates in ordinary
  tests. Keep Nix and dependency-free Rust tooling.

- [x] **PERF-02: Measure compile-local symbol interning before adopting it.**
  Count duplicate identifier allocations and AST/generator symbol clones on
  representative cold/warm builds. Prototype a compilation-local interner
  using only the standard library; compare wall time, allocations or peak
  memory, and cache behavior against the current `String` AST. If beneficial,
  use stable symbol IDs or shared immutable strings at the front-end boundary,
  preserving source spelling and diagnostics. Avoid a process-global interner
  that retains symbols between compilations; keep the simpler representation
  if benchmarks show no material win.
  On an i7-13700KF with Rust 1.99.0-nightly, the 256-function fixture's
  current parse averaged 386.6 µs over 20 iterations; building the post-parse
  interned mirror averaged 536.3 µs and raised total requested allocation
  traffic from 1.42 MB/10,556 calls to 1.80 MB/12,882 calls per iteration.
  The large-reference and allocator fixtures showed the same direction. Keep
  the String AST: the prototype adds work and allocations, so there is no
  measured win to justify changing production representation. This does not
  rule out a future in-place parser prototype if profiling points to identifier
  cloning. Because the pool is not integrated into generation, cold/warm cache
  decisions are unchanged (both workloads miss cold and hit warm).

- [x] **PERF-02a: Pilot a standard-library symbol pool in benchmarks.** Add a
  compilation-local `Arc<str>`/ID pool alongside the existing String-clone
  workload, without changing compiler behavior or cache keys. On the
  i7-13700KF, 200 iterations of the 256-function token workload averaged
  about 56.9 µs for pooling versus 52.6 µs for cloning; the four-function
  workload averaged 1.48 µs versus 0.79 µs. This microbenchmark does not
  measure a fully interned AST, so PERF-02 remains open. Preserve the current
  representation until a broader A/B build shows a material improvement.

- [x] **PERF-02b: Measure AST symbol duplication and cached generator work.**
  Extend the compiler benchmark to count spellings in the parsed AST and
  deterministic generated-syntax fixture, report cold/warm cache decisions,
  and time a benchmark-only post-parse local interner. Document machine and
  toolchain details, plus why this does not yet constitute a full front-end
  A/B or memory-allocation comparison.

- [x] **PERF-02c: Count allocation traffic for the local-ID prototype.** Use
  a standard-library allocator wrapper in the benchmark to compare current
  parse requests with constructing a span-preserving ID mirror after parsing.
  Record requested bytes and allocation calls on representative sources,
  together with wall times and cache behavior. The mirror duplicates the AST,
  so retain PERF-02 until an in-place front-end replacement and downstream
  build A/B can establish a material benefit.

- [x] **PERF-02d: Benchmark a compile-local interned syntax-tree prototype.**
  Preserve syntax shape and spans in a benchmark-only AST with `u32` symbol
  IDs and a per-compilation spelling pool. On an i7-13700KF with Rust 1.99.0
  nightly, 30 warm release iterations measured current parse versus parse
  plus conversion at 271/640 µs (256 generated functions), 87/143 µs
  (large reference projections), and 135/221 µs (allocator example).
  Duplicate symbol allocation estimates were 768, 105, and 251 respectively.
  This post-parse design loses; retain the simpler String representation as
  recorded in the PERF-02 decision above.

### Build outputs and developer tooling

- [x] **BUILD-01: Publish final outputs only after successful compilation.**
  The CLI writes assembly directly to its destination, and `link_native_binary`
  passes the requested output path directly to `ld`. Stage output in a uniquely
  created file in the destination directory and rename it after success; clean
  up owned temporary files on failure. Reject input/output collisions before
  overwriting source, including canonical path aliases. Apply the same policy
  to explicit formatter output. Acceptance: failed assembly/linking and write
  failures preserve an existing artifact byte-for-byte, concurrent builds never
  expose partial output, executable permissions survive publication, and source
  files cannot be accidentally replaced by build artifacts.

- [x] **DOC-01: Make executable documentation coverage explicit.**
  `tests/language_docs.rs` checks one document and uses the substring
  `(#fn main` to decide whether a fence is a complete program. Define explicit
  fence metadata or a fixture index for runnable programs, checked libraries,
  fragments with a prelude, and intended errors. Cover README, language,
  allocator, and soundness documentation as applicable. Acceptance: multiline
  function declarations and comments containing `main` are classified correctly;
  positive examples compile through the backend, selected programs run with
  expected results, and negative examples assert their intended diagnostic.

- [x] **DOC-01b: Keep custom Lim fences warning-free in rustdoc.** The crate
  includes the language reference as its documentation, and its `run=N`,
  `library`, `fragment=NAME`, and `error=CODE` fence tags are validated by
  `tests/language_docs.rs` rather than rustdoc. Explicitly allow rustdoc's
  unsupported-attribute warning without weakening the project-specific fence
  validation.

- [x] **TOOL-01: Offer structured diagnostic output for editors and LLMs.**
  Add an opt-in JSON diagnostic mode with a versioned schema, stable category,
  message, source path, byte range, primary/secondary labels, and expansion
  provenance. Specify the relationship between byte offsets and display columns.
  Implement correct JSON escaping without external libraries. Acceptance:
  lexical through linker failures use the schema, Unicode and quoted paths
  remain valid, imported/generated spans are retained, and human prose or raw
  subprocess stderr does not corrupt the diagnostic stream. Preserve the
  existing human-readable mode.

### Explicit concurrency and language terminology

- [x] **SYNC-01: Add atomic compare-exchange and exchange.**
  The current atomic API has load/store/fetch-add, but no operation that can
  conditionally claim shared state for an allocator or lock. Specify explicit
  strong/weak compare-exchange forms, expected/desired values, separate success
  and failure orders, and an explicit success/observed-value result. Add exchange
  with an explicit order. Acceptance: reject invalid ordering combinations,
  type-check every supported integer width, test successful/failed comparisons
  and observed values, and run competing workers that safely claim shared state.
  Document the generated x86 instructions, ordering guarantees, and fairness
  limitations; do not introduce callbacks, methods, or implicit dispatch.

- [x] **LANG-01: Use Send/Sync annotation terminology consistently.**
  `AutoTrait`, `UnsafeAutoTraitImpl`, diagnostics, and the soundness document
  still borrow trait terminology despite traits being a documented non-goal.
  Rename internal concepts and user-facing wording to Send/Sync properties and
  unsafe annotations while preserving the established `#unsafe-impl` syntax.
  Acceptance: errors and documentation describe exactly the unsafe promise and
  structural derivation rules, without suggesting user-defined traits exist;
  existing Send/Sync behavior and diagnostic locations remain covered.

## Next audit: ownership identity and runtime consistency

These follow-ups are based on the implementation after the completed audit
above. They distinguish observed implementation gaps from additional validation
work; they are not claims that every risk has a demonstrated failing program.
Keep the existing language constraints and implement each item with its own
commit, documentation, and focused regression coverage.

### Priority 1: ownership and canonical calls

- [x] **OWN-02: Represent ownership places structurally, not as identifiers
  joined with punctuation.** `src/linearcheck.rs::place_key`, `place_root`, and
  `has_move_conflict` encode projections using dots/brackets and string-prefix
  comparisons. A dot is legal inside an ordinary identifier, so a local named
  `a.b` must not become indistinguishable from field `b` of local `a`. Introduce
  binding IDs and typed projection components for fields, tuple positions,
  enum payloads, constant indices, and unknown indices. Use binding identity
  across shadowing and scope exit; format paths only when rendering errors.
  Audit borrow-checker conversions for the same ambiguity without discarding
  its existing disjoint-loan handling. Acceptance: distinguish dotted locals
  and dotted field names from projections, reject actual double moves, allow
  independent moves, preserve conservative dynamic-index conflicts, and cover
  shadowing, reinitialization, cloning, and partial aggregate consumption.

- [x] **CALL-01: Apply named-call syntax to generated thread entry points.**
  `normalize_function_calls` excludes `Item::ThreadTask` from its signature
  table, while `examples/atomic_claim.lim` still invokes spawn/join positionally.
  Include generated spawn/join signatures in canonical call normalization,
  using the inspectable generated declarations as the contract. Require
  `#call` with named argument lists at user call sites, without changing `#case` patterns
  or turning enum constructors into functions. Acceptance: migrate every
  affected example and documentation fence; test reordered worker arguments,
  missing/duplicate/unknown names, unsafe obligations where applicable,
  imports, and cold/warm generator caches. Native tests must retain explicit
  spawn failure, successful join, and failed-join handle ownership behavior.

- [x] **DIAG-04: Remove diagnostic-message parsing from ownership and unsafe
  analysis.** `precise_unsafe_span` in `src/unsafecheck.rs`, borrow diagnostic
  recovery in `src/borrowcheck.rs`, and location selection in
  `src/linearcheck.rs` still extract names or error kinds from English text.
  Return structured violations with the actual failing node, binding/loan ID,
  and relevant origin or prior-use node. Carry those identities through
  lowering; do not replace text parsing with a first-matching-name search.
  Acceptance: wording replacement leaves primary/secondary ranges unchanged;
  repeated unsafe operations inside/outside unsafe blocks, shadowed locals,
  dotted names, reordered arguments, nested branches, and imported/generated
  code all underline the responsible occurrence. Cold and cached expansions
  must retain equivalent provenance and borrow-origin labels.

### Priority 2: numeric consistency

- [x] **CONST-01: Support typed floating-point constant and static values.**
  Audit correction: float globals already had a separate evaluator; the
  integer evaluator's rejection did not mean they were unsupported. Use typed constant
  values that preserve f32/f64 bit patterns rather than passing floats through
  integer numeric conversion. Specify which pure expressions may initialize
  globals and how width rounding and exceptional values behave; runtime
  effects must remain forbidden. Acceptance: execute scalar and aggregate
  initializers containing floats, references to earlier constants, negative
  zero, and explicitly supported arithmetic. Check f32 rounding and compare
  equivalent constant/runtime expressions. Reject cycles and nonconstant
  operations with exact source spans; static access must still require unsafe.

- [x] **NUM-01: Add differential numeric backend tests across widths.**
  The exact-outcome sweep recently exposed a typed-float comparison lowering
  bug; a collection of hand-picked examples is not comprehensive numeric
  coverage. Build a dependency-free, deterministic test generator with a
  small independent Rust oracle for documented integer operations. Compare
  native outputs, constant evaluation where supported, and expected traps.
  Cover every supported width, signedness, wrap/saturate mode, casts, shift
  boundaries, division/remainder boundaries, and 128-bit lowering. Add float
  comparison cases for unordered values, infinities, signed zero, and rounding
  using explicitly documented semantics rather than assuming bitwise equality
  for all NaNs. Acceptance: bounded batches run in the Nix shell, failures
  print a seed and standalone Lim reproducer, and the oracle does not reuse
  compiler evaluation/lowering helpers. Preserve each discovered bug as a
  small permanent fixture with an exact outcome.

### Priority 3: bounded tooling and inspectability

- [x] **TEST-02: Bound subprocess output and clean up subprocess trees.**
  `tests/robustness.rs` polls a child before draining piped output, which can
  turn a large diagnostic into a pipe-capacity timeout. The native example
  harness redirects output to files but has no output-size budget and kills
  only its direct child on timeout. Share a dependency-free test runner with
  bounded capture, timeout diagnostics, uniquely owned scratch directories,
  and process-group cleanup on the supported Linux host. Never target the
  test runner's own process group. Acceptance: exercise noisy stdout/stderr,
  output-limit failures, a spawned descendant that would otherwise survive,
  and timeout cleanup; retain useful truncated diagnostics without hangs or
  unbounded disk/memory use. Replace predictable temporary-directory removal
  in robustness tests with exclusive creation and owned cleanup.

- [x] **CACHE-01: Explain generator cache decisions without inspecting
  private metadata manually.** The CLI uses `.lim/cache` but does not expose
  why an invocation hit, missed, or regenerated a damaged artifact. Add an
  opt-in report identifying the invocation, artifact path, key, and decision:
  missing entry, changed input/dependency context, incompatible implementation,
  or failed integrity validation where that distinction is available. Keep
  sufficient versioned metadata for reported comparisons; do not invent a
  specific miss reason when no previous entry can be identified. Include
  builtin and user generators plus reachable `#gn-fn` dependencies. Acceptance:
  tests distinguish unchanged builds, helper/input/cfg changes, and damaged
  source; enabling reporting must not alter keys or generated code. Define a
  machine-readable report channel that does not corrupt JSON diagnostics or
  emitted assembly, and document that cache digests are not authentication.

- [x] **BUILD-02: Verify reproducible outputs across fresh processes and
  relocated workspaces.** Existing cache identity and publication tests do
  not by themselves prove whole-build reproducibility. Build a representative
  imported/generated project in two independently created source roots with
  identical contents, using one pinned Nix toolchain and target. Compare
  normalized cache metadata, inspectable generated sources, assembly, and
  native binaries on cold and warm runs. Specify any intentionally variable
  path/provenance fields separately rather than filtering arbitrary byte
  differences. Acceptance: output ordering cannot depend on hash-map iteration,
  temporary paths, process IDs, or cache warmth; comparisons run in fresh
  compiler processes and failures identify the differing artifact. Keep real
  source paths available in diagnostics, and scope the guarantee to identical
  compiler/toolchain/configuration rather than different linker versions.

## Follow-up from 2026-09-25 design notes

- [x] **GEN-API-01: Make generator parameter declarations unmistakable.**
  The current `(name annotation)` form declares one parameter; it is not a
  destructuring pattern. Clarify this distinction in grammar/reference examples
  and gather usage feedback before changing syntax. If a syntax change is
  justified, keep parameter names and annotations explicit, do not add implicit
  destructuring, and provide focused parser diagnostics for malformed
  declarations. Acceptance: docs show ordinary literal parameters and
  collection/capability annotations; parser tests establish the exact AST and
  reject pattern-like forms rather than silently destructuring them.
  The grammar now spells out each declaration form; parser tests distinguish
  one annotated parameter from two bare parameters and underline nested-list
  patterns. Syntax remains unchanged pending actual usage feedback.

- [x] **GEN-API-02: Reject shadowing in generator iteration bindings.**
  A `#gn-for-each` binding cannot reuse a generator parameter or an enclosing
  iteration binding. Independent sibling expansions may reuse a name because
  their lexical scopes do not overlap. Test parameter and nested-loop
  collisions, alongside the language-wide no-shadowing rule.

- [x] **GEN-API-03: Document generator binding scope.** Explain that loop
  bindings cannot shadow parameters or enclosing iterations, while sibling
  iteration forms have independent scopes. Keep the reference and its tests in
  sync with the interpreter's binding rules.

- [x] **SYS-01: Establish a target-specific syscall boundary for Lim libraries.**
  Establish an explicitly unsafe, typed primitive for the supported target,
  including register arguments, clobbers, errno representation, and source
  diagnostics. Build Lim wrappers above it, selected by target/configuration
  rather than presenting OS syscall numbers as portable APIs. Preserve FFI for
  external libraries, but make core OS services implementable without libc
  calls. Acceptance: syscall-backed APIs pass output and return-value tests;
  invalid pointers remain explicitly unsafe; unsupported targets fail clearly;
  assembly and ABI tests verify argument registers, return/error handling, and
  clobbers. A Lim standard library owns policy and safe wrappers while the
  compiler owns the minimal architecture-specific boundary. Subitems SYS-01a-af
  establish the Linux x86-64 boundary, catalog, and initial tested wrapper
  families. Call-site unsafe enforcement is complete, with 278 catalog
  syscalls referenced by the current library and observed in passing programs.
  This satisfies the supported-target boundary and the requested most-syscalls
  baseline (278/386 catalog entries). Remaining syscall families, deeper
  behavioral coverage, and additional operating systems remain follow-up work.

- [x] **SYS-01a: Add unsafe inline assembly and direct Linux syscalls.**
  `#asm` binds typed scalar/pointer values to explicit x86-64 registers and
  returns a declared scalar from `rax`; it preserves callee-saved GPRs and is
  restricted to `#unsafe`. `#linux-syscall` directly emits the Linux x86-64
  `syscall` instruction with the six kernel argument registers and returns raw
  negative errno values. Automatically expose `#os`, `#arch`, and `#target` cfg
  values. Acceptance: unsafe/arity/type tests and generated assembly tests pass.

- [x] **SYS-01b: Add initial Linux syscall library and executable tests.**
  `library/linux_x86_64.lim` provides byte IO and process, descriptor, memory,
  clock, sleep, and randomness helpers without FFI. Executable Lim tests assert
  exact piped output and kernel results, including error paths and pointer
  buffer behavior. Broader safe wrappers and per-syscall behavioral tests
  remain part of SYS-01.

- [x] **SYS-01c: Add the native x86-64 Linux syscall number catalog.**
  `library/linux_x86_64_syscall_numbers.lim` contains all 386 `common` and
  native `64` ABI entries from the pinned Linux syscall table; x32 entries are
  excluded. The Lim integration test checks count, ordering, unique names, and
  representative recent IDs. Importing the Linux syscall library compiles and
  type-checks the complete catalog.

- [x] **SYS-01d: Exercise syscall buffers and pipe IO at runtime.**
  Lim tests use mmap-backed buffers with `uname`, `getrandom`, `openat`,
  `readlinkat`, and `getcwd`; they verify narrow raw-pointer accesses at page
  boundaries. A `pipe2` test transfers and validates a payload using direct
  `read`/`write` syscalls, then closes descriptors and unmaps memory.

- [x] **SYS-01e: Test common descriptor syscall error paths.**
  The executable syscall test checks `EBADF` from `fstat`, `ioctl`, `fcntl`,
  `flock`, `fdatasync`, `fchdir`, `fchmod`, `fchown`, `getdents64`, `fallocate`,
  and `dup2` when given invalid descriptors; no valid file is modified.

- [x] **SYS-01f: Verify process credential output buffers.**
  Runtime checks call `getresuid` and `getresgid` with three mmap-backed
  pointers each, compare real/effective IDs to their scalar queries, and verify
  `getgroups(0, null)` succeeds with a nonnegative count. Single-byte read/write
  wrappers retry `EINTR`, and the echo example returns failure on IO errors.

- [x] **SYS-01g: Test Linux virtual-memory management calls.**
  Mapped pages are read-protected and restored with `mprotect`, passed through
  `madvise`, expanded with `mremap`, checked for preserved contents, and
  unmapped at the expanded length. Narrow-pointer boundary checks remain part
  of the same executable test.

- [x] **SYS-01h: Test eventfd counter IO.**
  An `eventfd2` descriptor is created, receives an eight-byte counter write,
  returns the expected counter through an eight-byte read, then is closed and
  its mapped buffer unmapped.

- [x] **SYS-01i: Test process and resource query syscalls.**
  A standalone Lim example verifies FIFO priority bounds, null-output `getcpu`,
  a signal-zero `tgkill` probe, `getrlimit(RLIMIT_NOFILE)` output ordering, and
  `sysinfo` uptime through mmap-backed output storage.

- [x] **SYS-01j: Test anonymous file descriptor syscalls.**
  A Lim example creates a memfd, verifies close-on-exec, writes and reads its
  payload, checks `fstat` size, truncates and verifies the new size, syncs it,
  and closes/unmaps all resources without creating a persistent file.

- [x] **SYS-01k: Add and exercise file-descriptor wrapper functions.**
  Add target-selected Lim wrappers for `openat`, `read`, `write`, `pread64`,
  `pwrite64`, `fstat`, `fcntl`, `fdatasync`, `memfd_create`, and `unlinkat`.
  Route pipe, `/dev/null`, and memfd examples through these wrappers and assert
  exact byte counts, payloads, metadata, descriptor flags, and `EFAULT`/`EBADF`
  results. These raw-pointer wrappers document their caller obligations, and
  examples mark calls as `#unsafe`; SYS-01n now enforces these contracts at
  call sites with `#unsafe-fn` declarations.

- [x] **SYS-01l: Exercise local Linux socket syscalls.**
  Use an `AF_UNIX` socket pair to check socket creation, `sendto`/`recvfrom`
  payloads, `getsockopt`/`setsockopt`, local/peer address lengths, write-side
  shutdown and EOF, invalid-descriptor errno, and complete descriptor/mapping
  cleanup. Assert all results by compiling and running a Lim example; no
  external network or persistent filesystem state is involved.

- [x] **SYS-01m: Exercise epoll readiness and eventfd notification.**
  Register an eventfd with epoll, send and receive its counter, verify the
  packed event mask/data bytes, check that readiness clears after consumption,
  and close/unmap all kernel resources. The Lim program's result is asserted by
  the native integration suite.

- [x] **SYS-01o: Verify successful file-descriptor control operations.**
  Extend the anonymous memfd run to test sequential advice, exclusive lock and
  unlock, mode and owner updates, allocation, and `dup2(fd, fd)`. Assert kernel
  success and the resulting expanded/truncated file sizes. Route these calls
  through target-selected Lim wrappers rather than libc.

- [x] **SYS-01p: Exercise Linux wall-clock and process-time syscalls.**
  Add target-selected wrappers and runtime assertions for `clock_getres`,
  `clock_nanosleep`, `gettimeofday`, `time`, and `times`. Check timestamp and
  resolution ranges, output fields, zero-duration sleep, and mmap cleanup.

- [x] **SYS-01q: Exercise Linux zero-copy pipe transfer syscalls.**
  Use an anonymous file and three pipes to test `sendfile`, `tee`, and `splice`.
  Verify exact payloads, input offsets, tee's non-consuming behavior, and
  descriptor/mapping cleanup in a Lim executable.

- [x] **SYS-01r: Exercise private futex wait and wake results.**
  Add a target-gated wrapper and use a mapped futex word to assert deterministic
  `EAGAIN` on a mismatched wait value, zero wakes when there are no waiters, and
  unchanged word contents. Run and assert the Lim binary's result.

- [x] **SYS-01s: Exercise successful Linux directory-descriptor queries.**
  Enumerate the current directory with `getdents64`, reset and reread its
  position, use `fchdir` on that directory, and verify `getcwd` produces an
  absolute path. Assert records, results, and cleanup through a compiled Lim
  example without creating or deleting files.

- [x] **SYS-01t: Exercise Linux process resource and usage syscalls.**
  Verify `getrusage`, lower and restore the child program's soft `RLIMIT_NOFILE`
  with `getrlimit`/`setrlimit`, query the restored limit through `prlimit64`,
  and change/restore `umask`. Assert output fields and return codes from Lim.

- [x] **SYS-01u: Exercise Linux real-time signal state syscalls.**
  Verify signal-action and signal-mask installation, queries, and restoration,
  plus pending-mask querying, without delivering a signal.

- [x] **SYS-01v: Exercise Linux POSIX timer syscalls.**
  Create a `SIGEV_NONE` monotonic timer, arm and query a future expiration,
  delete it, and verify querying its deleted ID fails as expected. Keep the
  test independent of signal delivery and wall-clock output.

- [x] **SYS-01w: Exercise Linux descriptor-based extended attributes.**
  On a fresh memfd, set an attribute, enumerate the name, verify its payload,
  remove it, and assert the kernel's missing-attribute result afterward.

- [x] **SYS-01x: Exercise Linux interval timer syscalls.**
  Snapshot the process interval timer, arm and query a future expiration,
  restore the prior timer state, and verify every timeval field was restored.

- [x] **SYS-01y: Exercise Linux inotify event delivery.**
  Watch a private scratch directory, create and remove one file, validate both
  inotify records, remove the watch, and clean up all descriptors and paths.

- [x] **SYS-01z: Exercise Linux fork and wait4 process lifecycle.**
  Fork a child that exits with a known status, reap it with `wait4`, and verify
  the PID and encoded exit status from the Lim program.

- [x] **SYS-01aa: Exercise Linux scheduler affinity syscalls.**
  Query the process's allowed-CPU mask, set that same mask back, yield, and
  query again. Verify return sizes and that the complete supported mask buffer
  remains identical.

- [x] **SYS-01ab: Exercise Linux copy_file_range.**
  Copy a byte payload between two anonymous files using explicit offsets,
  validate offset updates and exact destination bytes, and close all resources.

- [x] **SYS-01ac: Exercise Linux scheduler query syscalls.**
  Query the current scheduler and parameters, validate policy priority bounds,
  verify invalid-policy error handling, and check the current nice value.

- [x] **SYS-01ad: Exercise Linux renameat2 semantics.**
  Verify `RENAME_NOREPLACE` rejects an existing destination, then rename
  successfully and check old/new path results with resource cleanup.

- [x] **SYS-01ae: Exercise Linux statx metadata queries.**
  Query an anonymous file through `AT_EMPTY_PATH`, verify the returned mask
  includes `STATX_SIZE`, and assert its reported length matches written data.

- [x] **SYS-01af: Exercise Linux openat2 path resolution.**
  Open a scratch file with `RESOLVE_BENEATH`, verify a missing path result and
  reject an unknown resolve flag, then remove the file and clean resources.

- [x] **SYS-01n: Enforce unsafe syscall-wrapper contracts at call sites.**
  Add an unsafe-function declaration/call model (or equivalent) so functions
  that accept raw pointers or expose kernel memory effects require an explicit
  `#unsafe` at every call site. Migrate low-level Linux wrappers and prove safe
  calls are rejected while explicitly unsafe calls compile; preserve imported
  function identity and diagnostics. The `#unsafe-fn` contract and io_uring
  migration are implemented and tested, including implicit-call safeguards.
  At migration, 196 raw-pointer/hidden-memory/process-state wrappers required unsafe
  calls in native and fallback branches; 81 safe APIs retain their signatures.
  Examples and raw-pointer example helpers use explicit caller contracts.
  Regression tests reject safe calls to every unsafe wrapper in both cfg
  branches (392 negative probes) at the exact callee, compile their explicit
  unsafe counterparts, and guard raw-pointer and scalar-hidden obligations.
  All 52 I/O tests passed after migration; the native manifest sweep also
  passed all 319 entries. Caller obligations are documented by category in
  docs/syscall-coverage.md; unsafe declarations do not prove their fulfillment.

- [x] **SYS-01ag: Verify blocked robust-futex owner-death wakeup.**
  Gate owner exit on observing a child sleeping directly on the shared robust
  futex. Require a successful wait return and OWNER_DIED/WAITERS with cleared
  TID, reap both children, and verify exact stdout. The I/O test repeats eight
  times; an additional 100-run Lim stress check passed. Readable procfs wait
  symbols are required and unsupported hosts are not counted as passing.

- [x] **SYS-01ah: Investigate robust-futex cleanup after requeue.**
  CMP_REQUEUE onto an owned robust word intermittently produced timeout despite
  the owner-death bits being set on kernel 7.2.6. An independent C probe also
  reproduces the failure, including with confirmed sleeping waiters. Preserve
  direct-wait coverage, isolate the requeue/exit interaction, and add a reliable
  blocked-requeue regression before claiming that path works. See
  docs/syscall-coverage.md for the reproducer sequence and evidence limitations.
  A pipe-gated test now requires a blocked waiter, moves exactly one waiter
  from staging to the registered robust word, and only then releases the owner.
  The waiter must return successfully with OWNER_DIED/WAITERS and cleared TID.
  The existing direct-wait path remains. The Lim example passed 1,000 repeated
  runs and the independent C sequence passed 2,000 on this host. This validates
  the exercised path, not the root cause of earlier intermittent failures.

- [x] **SYS-01ai: Add direct memory sealing and secret-memory wrappers.**
  Match the kernel flag widths (`usize` for mseal, `u32` for memfd_secret),
  preserve cfg fallback signatures, and verify real protected-memory behavior.
  Examples check sealing rejection and preserved bytes, shared secret mappings,
  rejected process_vm_readv access, descriptor/mapping lifetimes, and exact
  stdout. Kernel support and locked-memory requirements are explicit.

- [x] **SYS-01aj: Remove unnecessary C runtime dependencies from syscall binaries.**
  Inspect assembled undefined references with nm. Objects without references
  or requested libraries link statically without libc/pthread or an interpreter.
  Regression tests inspect ELF metadata and execute a program importing the
  Linux library; foreign declarations/calls, inline assembly, explicit libraries,
  and supplied object references are covered separately. Runtime selection is
  conservative for references resolved between supplied objects. All 318 native
  examples pass after the change, including generated threads and foreign calls.

- [x] **SYS-01ak: Add direct io_uring calls and real ring I/O.**
  Add setup/enter/register with matching cfg fallbacks. Exercise kernel offsets,
  single/separate mappings, explicit x86-64 publication fences, slot reuse,
  registered-file lifetime after ordinary close, read/write completions and
  error CQEs. Check exact stdout and require kernel support rather than skipping.

- [x] **SYS-01al: Preserve main's process exit status with workers present.**
  Startup used raw thread exit, allowing io_uring worker termination to replace
  the process status. Switch only the entry stub to exit_group; keep explicit
  linux-exit thread-local. Pin the behavior with both io_uring and a raw-clone
  regression whose worker remains alive when main returns.

- [x] **SYS-01am: Exercise alternate-stack handlers and rt_sigsuspend.**
  Add the unsafe raw-mask suspend wrapper with matching cfg fallback. Install
  a real x86-64 SA_SIGINFO/SA_ONSTACK handler and SA_RESTORER trampoline using
  assembly labels, not libc or ordinary Lim callback functions. Check actual
  entry RSP bounds, SS_ONSTACK, active-stack disable rejection, signal/sender
  metadata, handler mask, and stdout written by the handler. Deliver once
  unblocked and once via pending-signal/sigsuspend; require -EINTR and mask
  restoration, plus invalid-size and invalid-pointer errors. Restore and check
  the original action/stack/mask before releasing memory. Eight repeated runs
  require H/H/S output; broken-stack, broken-restorer, and fake-suspend-result
  variants must fail before the second handler output.
  The 54-test I/O suite passes. The new wrapper brings the library to 274
  distinct catalog numbers, with 197 unsafe and 81 safe wrapper declarations.
  All 320 native manifest entries passed on retry. The first sweep timed out
  on the existing never.lim trap; isolated recheck and full retry passed.

- [x] **SYS-01an: Add futex2 vector/single waits and direct wakeups.**
  Implement futex_waitv, futex_wait, and futex_wake with their native ABI
  widths, unsafe declarations, caller contracts, and matching cfg fallbacks.
  Exercise both indices of a shared two-entry vector plus a single-word wait
  from isolated children. Retry empty wakes until exactly one dequeue succeeds,
  require correct wait results and exit status, and check queues are empty
  afterward. Test absolute monotonic/realtime timeouts, second-entry mismatch
  cleanup, invalid counts/flags/record fields, bad addresses, invalid clocks
  and timespecs, and oversized values/masks. Eight repeated runs require
  A/B/C stdout within bounded process-group deadlines. All 55 I/O tests pass.
  Library breadth is 277 catalog syscalls, with 200 unsafe and 81 safe wrappers.
  All 321 native manifest entries, 400 unsafe-call probes, six coverage checks,
  four documentation tests, and seven native-linker tests also pass.

- [x] **SYS-01ao: Exercise ordinary futex2 requeue on a live waiter.**
  Add the unsafe requeue wrapper with matching cfg fallback. Move a shared
  single-word waiter without waking it, then prove the source is empty and
  the destination retains the original wake mask. A live value mismatch must
  not move it back. Release it only through a matching destination wake, check
  its return/exit status and the final empty queues, and require A/B/C/D stdout.
  Test invalid flags, null records, destination reserved fields, empty queues,
  and mismatched values. A mutation that wakes instead of moving must fail even
  though it returns the same count. All 56 I/O tests and 402 unsafe-call probes
  pass, as do all 321 native examples, six coverage checks, four documentation
  tests, and seven native-linker tests. This does not close SYS-01ah's
  robust-owner-death cleanup investigation.

- [x] **SYS-01ap: Audit runtime syscall coverage against implemented numbers.**
  Trace the executable Linux corpus and compare the observed syscall numbers
  to the library's referenced catalog entries. Include forked children, paired
  exec fixtures, and stdin-driven echo; preserve per-example exit/output checks
  and process-group timeouts. Keep instrumentation failures explicit, and do
  not count compiler/linker/trace-launcher calls as target-program execution.
  Investigate any missing number with its wrapper/call-site mapping. Record
  runtime evidence separately from structural coverage and deeper behavior
  assertions; an observed syscall alone does not prove its semantics.
  `tests/syscall_execution.rs` observed all 278 implemented numbers across 54
  passing programs, checking static ELF linkage and exact runtime outcomes.
  The ignored audit must be explicitly run with `--ignored --nocapture`;
  ordinary test runs exercise its trace-parser regression only. The Linux
  devshell includes strace, and the coverage document records reproduction
  instructions and the distinction between reachability and behavior.

- [x] **SYS-01aq: Remove generated-thread FFI from the standard-library path.**
  `library/tasks.lim` exposes `@threaded-executor`, so its former backend's
  malloc/free/pthread_create/pthread_join calls violated the no-FFI objective
  even though syscall-wrapper binaries were static. Use direct Linux calls for
  allocation, guarded stacks, clone entry, clear-child-TID/futex joining, and
  cleanup. Preserve Send/Sync, linear handles, captured-reference lifetimes,
  aggregate argument/result ABI, retryable join errors, and spawn-failure
  ownership semantics. Calculate worker stack requirements rather than silently
  assuming a fixed stack fits. Define and test the foreign-code/TLS boundary;
  raw threads must not call libc with shared parent TLS. Test actual concurrent
  execution, immediate exit/join races, repeated spawn/join cleanup, failures,
  nested workers, and large frames. Inspect the standard-library executor ELF
  for absence of interpreter/dynamic dependencies and trace its kernel calls.
  All eight kernel-thread tests pass, including the two explicit ptrace audits.
  They verify guard faults, calculated large stacks, aggregate and nested-worker
  ABI, multi-page packets, concurrent progress, zero worker FS base, exact
  stdout, static executor linkage, spawn cleanup, interrupted joins, and retrying a returned error
  handle. The new FFI diagnostic has an exact-underlining UI test. Legacy
  failure tests now simulate native negative returns rather than C stubs.

- [x] **SYS-01ar: Prove byte-I/O interruption and hard-error behavior.**
  Inject EINTR independently into read/write and require exact binary echo;
  inject EBADF and require failure without output. The new test reproduced
  syscall(-4)/ENOSYS after interruption. Preserve the syscall number outside
  RAX and restore it on every retry. The opt-in syscall execution audit now
  exercises these cases as well as all 278 implemented syscall numbers.

- [x] **SYS-01as: Remove unstable queue-membership assumptions from futex2 tests.**
  An untraced stress failure and core dump located the source wake probe after
  requeue. A spurious kernel wake can restart the original wait; do not probe
  its source destructively and assume it must stay empty. Retry moves as needed
  and require an actual masked destination wake of one, then verify the child
  and final empty queues. Preserve the wake-instead-of-move negative test.
  The corrected executable passed 1,000 consecutive untraced runs and both
  normal/mutation regressions. SYS-01ah remains a separate investigation.

- [x] **SEM-01: Reject lexical binding shadowing.** Parameters, locals,
  destructured names, and match bindings may not hide a visible parameter,
  outer local, or global. Keep non-overlapping sibling scopes independent.
  Validate original `@async-fn` bodies before suspension splitting can discard
  dead bindings; report a nested branch's newly introduced identifier with an
  exact source underline. Unit,
  declaration-identity, and compiler UI tests cover local, nested, pattern,
  parameter/global, repeated same-scope, and async-generated bindings.

- [x] **IR-04cr: Check local-reference scope escapes on typed flow.** Add a
  must-analysis of bindings definitely in scope at each CFG point, then inspect
  checked loan origins when references are bound or destructured. Reject a
  transfer whose local referent has exited on any incoming path. Route normal
  compilation through this typed diagnostic before the syntax checker and stop
  the syntax fallback from repeating local-binding scope checks. Preserve
  standalone legacy checking, exact value/origin spans, and cover both direct
  and destructured block-reference escapes plus valid in-scope references.

- [x] **IR-04cs: Check call-argument referents at the typed call event.** Use
  checked argument borrow origins and bindings definitely in scope when the
  callee is invoked. Reject a temporary block reference whose owner was already
  exited, while accepting borrows from locals that remain live through the
  call. Remove the corresponding syntax-side call-argument scope check on the
  normal compiler path; retain exact argument and borrow-origin spans.

- [x] **IR-04ct: Enforce typed linear exit obligations.** Promote the typed
  definite-consumption analysis from a debug-only differential assertion to a
  validation error with its retained declaration/transfer spans. Keep legacy
  checking for ownership paths not yet represented in typed flow; cover
  missing and complete fieldwise consumption at return and scope exit.

- [x] **IR-04cu: Run typed linear analysis before the diagnostic fallback.**
  Check typed releases, consumptions, and exit obligations before legacy
  ownership analysis. Use typed errors when the syntax checker misses a case;
  when both catch it, preserve the legacy checker's more specific message and
  underline. Verify exact UI spans and accepted branch, loop, and aggregate
  ownership cases.

- [x] **IR-04cv: Preserve match-result loans and reject moves of borrowed owners.**
  Resolve value origins for branch and match expressions at their actual CFG
  predecessor events, including references nested in opaque structs and enum
  payloads. Treat a linear by-value transfer as an owner move when checking
  live loans, so calls cannot consume an owner while a result still borrows it.
  Cover enum payload extraction, by-value calls, and pending AIO context use.

- [x] **IR-04cw: Transfer nested mutable loans through moved match results.**
  When a linear match consumes a reference-bearing enum, transfer its actual
  referent loans to the selected payload/result instead of retaining a loan
  against the consumed wrapper. Preserve the transfer across by-value calls
  that return reference-bearing aggregates. Keep ordinary aggregate field
  reborrows distinct. Cover safe one-request native AIO submission, completion,
  cancellation, and rejection of a second outstanding operation.
