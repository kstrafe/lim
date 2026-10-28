# Lim semantic contracts

This document records the intended guarantees of the implemented language. It
does not claim a formal soundness proof or that all implementation bugs have
been eliminated. Unsupported operations and exhausted mandatory proof budgets
must reject a program rather than silently discard a possible execution path.
The [language reference](language.md) specifies syntax; these contracts make
cross-feature behavior explicit. Changes to them require regression tests.

## Names, generation, and libraries

Identifiers are flat. `.` and `::` are spelling conventions, not dynamic lookup
or namespaces. External imports deterministically transform identifiers using
their complete accumulated `@` prefix. Different instances have different
identifiers and private access contexts, even for the same physical source.

Source `@name` qualification resolves in the context where it is written before
generator interpretation. It cannot capture an interpreter parameter or runtime
local. Handwritten forward declarations and exported generated names have
pre-expansion declaration/export contracts; unknown names are not implicit
locals. Literal strings and unmarked syntax remain data.

Generated declarations belong to the invocation library. Compiler-validated
`#generated-context` headers record definition and invocation module instances.
Generated code can access those two instances, not every dependency or ancestor
generator. A privileged generator is responsible for any executable syntax it
constructs from literal inputs. Qualification and privacy are distinct from
type, borrow, linearity, and unsafe checks. Cache reuse must preserve the same
permissions and semantics; a self-issued header grants no access.

## Evaluation and control flow

Function argument expressions execute in parameter declaration order, not label
order at the call site. Struct field initializers execute in field declaration
order, not source label order. Array and tuple elements execute left to right.
Each supplied expression is evaluated once; names do not imply deferred work.

`#if` evaluates only its selected branch. Boolean `and` and `or` short circuit.
`#match` evaluates its scrutinee once and executes one matching arm. Patterns
must provide the required exhaustive coverage. A failed `#let-else` must exit
the current continuation; no following statement can use an absent binding.
Functions return explicitly. Returning `()` is explicit too.

Runtime calls are statically known. Recursion, indirect function calls, and
closures are not part of the language. This restriction supports whole-program
checking and bounded native stack analysis; it is not a promise that unsafe
inline assembly cannot violate stack invariants.

## Values, ownership, and references

Declared types and operation types are explicit. Linear owners must be consumed
on every reachable function exit, including failure paths. There is no hidden
destructor invocation. Cloning, moving, cancellation, and destruction are
different operations. Copy values and references do not require consumption;
Copy eligibility is structural, not permission to duplicate owning storage.
`#forget` consumes a value without invoking a destructor; explicit leaks are
possible and must not be confused with automatic resource reclamation.

A derived reference retains the identity and lifetime of its referent. Returning
it, storing it in an aggregate, passing it through a function, or taking a
subslice must not detach that obligation. Exclusive access forbids conflicting
live accesses; disjoint checked projections may be borrowed independently.
Raw-pointer conversion does not make invalid memory, unchecked bounds, or an
expired owner safe. Unsafe code must uphold validity, alignment, initialization,
aliasing, and lifetime requirements of the operations it uses.

Pinning protects storage identity, not merely the lifetime of one reference
token. Forgetting a pin reference does not authorize relocating stationary
storage. Owning heap wrappers may move their pointer handle without moving the
pointee; their APIs must not expose a safe route to relocate pinned contents.

## Arithmetic, bounds, and failure

Integer widths and signedness are part of the type. Wrapping and saturating
operations have distinct explicit spellings. Their results must agree in
constant evaluation and native execution. Division by zero, invalid shift
counts, and failed safe indexing are traps, not successful arbitrary results.
Traps do not unwind or implicitly destroy linear owners.

Floating-point operations follow the supported target's documented scalar
operation semantics, including unordered NaN comparisons and signed zero.
This is not a guarantee of identical NaN payloads or bit-identical results across
all targets, nor does it give the compiler permission to assume NaNs absent.
Numeric casts use the specific conversion rules in the language reference;
pointer casts do not prove safety.

## Suspension and cancellation

Async generators emit inspectable ordinary Lim declarations. The original
source witnesses and the emitted program must both pass their required checks.
Unsafe pointer storage in an emitted pinned frame is justified by checked source
origins, physical layout, initialization, and cancellation ordering—not by a
borrow-checker exemption for an async name.

Pending preserves exactly the state needed for resumption and exposed cleanup.
Cancellation is explicit; dependent children must be retired before their
referents are destroyed. Repeated terminal cleanup must not repeat destruction.
Current supported recipes and remaining direct allocation limitations are
listed in [the graph production documentation](async-graph-production.md).

## Support and verification scope

Linux x86-64 System V is the primary native target. AArch64 remains experimental
and rejects unsupported operations; emulator execution does not establish real
hardware memory-order correctness. FFI expansion is out of scope for this work.
Private mutable globals and allocator instances must not be merged merely
because their initial data or associated machine code looks identical.

Executable contracts live in `tests/evaluation_contract.rs`,
`tests/seeded_safety.rs`, `tests/numeric_differential.rs`,
`tests/borrow_adversarial.rs`, `tests/generator_context_matrix.rs`, and the async
anchor/cancellation suites. Seeded corpora are bounded and reproducible. They
are evidence, not exhaustive coverage of all possible programs.
