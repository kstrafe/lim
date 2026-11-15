# Meet Lim {#introduction}

Lim is an experimental, compiled **Lisp with explicit, strong static types**
and a **human-readable target for generated code**. Write it by hand, ask a
language model to produce it, or build your own generator: the result stays
ordinary source you can follow, test, and change. This page explains the design,
walks through examples, and keeps the full reference close at hand.

## Read what runs {#language}

**Explicitness is the guiding principle.** Declarations and behavior are written
out in source. Local variable declarations include a type instead of asking the
compiler to infer one. A function returns through an explicit return statement;
its final expression never silently becomes its return value. Arithmetic
operations state the types they operate on and, where relevant, how overflow is
handled. Ordinary function calls name their arguments, so you can see which
parameter receives each value at the call site. Builtin operations and special
forms can also have positional operands.

Note: the **`#` prefix is reserved for language keywords, builtin types and
operators**, such as `#fn`, `#u64` and `#return`. User declarations cannot use
that prefix. Adding a future builtin `#feature` therefore leaves your `feature`
name available. Language keywords and user declarations keep distinct spellings
as the builtin vocabulary grows.

A small surface notation makes handwritten code lighter: records, indentation, colon grouping and infix
expressions reduce parentheses, verbosity and visual noise. This syntax sugar
lowers to the same explicit parenthesized trees that code generators manipulate.

```lisp run=42
#fn add {
  #params = { left = #u64; right = #u64; };
  #returns = #u64;
  #body: #return [#u64 #wrap; left + right];
}

#fn main {
  #params = {};
  #returns = #u64;
  #body: #return add { left = 40; right = 2; };
}
```

The result is the process exit status, 42. Braces contain named pairs; the
colon groups the rest of its line; brackets contain typed infix arithmetic.
The [tutorial](tutorial.md) develops these rules step by step.

## Generate concrete code at compile time {#compile-time-generation}

Code generation is built into Lim. Pure compile-time generators produce
concrete, specialized types and their APIs: an optional value for a particular
element type, a fixed array with bounds contracts, or a task state machine.
This supports complex designs without hiding their implementation behind
runtime dispatch. The generated Lim source is available to inspect, search
and debug. The [generator tutorial](tutorial.md#generators-tutorial) starts
with a small example; the [reference](language.md#user-defined-generators)
describes the restricted generator language and its contracts.

## Follow a name to its definition {#following-declarations}

A direct file reference names both a source file and a declaration. An explicit
alias gives that exact declaration a shorter file-local spelling:

```lisp syntax
// Two ways to name the same function in math.lim:
#alias add = ./math.lim::add
#fn answer {
  #params = {};
  #returns = #u64;
  #body:
    #let first #u64 (./math.lim::add { left = 20; right = 22; });
    #return add { left = first; right = 0; };
}
```

The declaration's identity is its **canonical file plus declaration name**.
Aliases change the spelling you use, not the identity, signature or ownership
rules. This gives text search and editor go-to-definition a direct route to the
source. There is no nested namespace lookup, chain of implicit imports or
receiver-based method dispatch to unravel. A family spelling such as
`VecU64::sort` is a single declaration name; `::` within that name does not
introduce a namespace. See [direct references and aliases](language.md#direct-file-references-and-aliases)
for path resolution and visibility rules.

## Why a new language? {#why-a-new-language}

Lim is an intermediate representation you can read and audit. A generator or
language model can produce it, and you can open the result and follow what it
does: the types, named calls, ownership operations, and generated implementations
are available in source.

Generated programs still need human review. Following a call becomes harder
when its meaning depends on implicit conversions, receiver lookup, hidden
cleanup, or distant generic instantiations. Lim explores a deliberately smaller
design: make those decisions visible, give generators a simple tree to produce,
and check ownership and API requirements before emitting code.

Lim also avoids hidden call indirection. Function-pointer values, recursive
calls, and implicit or virtual dispatch are unavailable. Generators can produce
explicit branches, state machines and direct calls, and you can inspect that
emitted Lim source. The generated code still has to obey the same rules; code
generation does not permit recursion or indirect calls. References and raw
pointers exist: this restriction concerns how function call targets are chosen.

For example, distributed enums collect a closed set of contributed variants
at compile time. Fixed executors take an explicit list of tasks and emit direct
calls. These building blocks allow runtime selection through visible generated
branches with targets known for that build. See
[collections and cooperative tasks](collections-and-tasks.md) for their current
scope and examples.

The goal is to shorten the path from an idea to code you can understand and
run. The name evokes a limit as time approaches zero: less waiting to build,
less overhead to execute, less time reconstructing intent. These are engineering
targets. Lim is experimental and unreleased; syntax,
semantics, backend coverage, and tooling can still change.

## Keep testing and performance practical {#testing-and-performance}

Testability is part of the design. Explicit inputs, control flow and cleanup
make it easier to isolate a behavior, write a test for it, and understand a
failure. Contract audits can check whether a function's promises hold on the
paths your tests exercise. Generated implementations can be inspected and tested
as ordinary Lim code.

Very fast compilation is a first-class engineering goal, alongside excellent
execution performance. Lim aims to produce efficient, predictable native machine
code and minimize the work needed to build it. Cached generation, concrete
implementations, and the internal encoder and linker support that direction.
The [performance baseline and benchmark harness](performance-baseline.md)
record measured results so representative workloads can guide optimization.

## Why these design choices? {#design-reasoning}

| Choice | Reason and tradeoff |
| --- | --- |
| One canonical tree, a small surface notation | Generators work with whole structures; readers can use records, indentation and infix expressions. Sugar lowers to the same forms instead of defining a second execution model. |
| Explicit types and operations | Bindings and arithmetic expose their meaning locally. There is no general type inference; unsuffixed literals can use an explicitly declared contextual type. This costs some extra source text. |
| Free-standing functions and explicit names | `Work::poll` is a function name; `Choice.Ready` is an enum variant. There are no methods, traits, closures, function pointers or recursive calls to resolve. This restricts familiar abstractions. |
| Concrete generated definitions | Pure compile-time generators produce ordinary Lim types and functions instead of user-facing generic types. Cached output in `.lim` is inspectable source with invocation provenance; concrete code can increase output size. |
| Reserved `#` builtins | New language keywords use reserved spellings such as `#feature`, leaving ordinary names such as `feature` available for user declarations. |
| Native compilation | The dependency-free Rust compiler encodes and links x86-64 Linux ELF executables internally. AArch64 and browser WebAssembly backends currently support smaller subsets. |

## What the compiler checks {#safety}

**Rust-inspired whole-program borrow checking** follows moves, exclusive access,
returned references and retained loans across functions and library boundaries,
including generated implementations, without user-written lifetime annotations.
Linear values need explicit consumption; destruction is visible rather than
silently inserted. Raw pointers and unsafe operations have an explicit boundary
and still need an audit.

## State API conditions without multiplying types {#conditions-and-evidence}

Often an API needs an ordinary value under a particular condition. One function
might accept a `#u64` only when it is positive; another might need that same type
under a limit. Predicate contracts express those conditions without inventing
a separate type for each one.

`#requires` says which exact evidence a caller must have. A `#if-valid` branch
runs a predicate and supplies that fact in its successful branch. `#ensures`
states facts subsequent code may rely on after a call; `#preserves` keeps a
specified fact when the caller already had it, without requiring that fact to
be supplied. Mutations can invalidate evidence about changed storage, so an
earlier validation is not permission to use a later, altered value.

The checker tracks explicit predicate evidence across these boundaries; it does
not search for theorems. The truth of `#ensures` and `#preserves` remains a
programmer promise. `--check-contracts` audits those promises on exercised paths,
which helps test an API without turning tests into mathematical proofs.
`#assume` is a separate, explicit trust point: it accepts a claim without running
the predicate. See the [contract tutorial](tutorial.md#contracts-tutorial) and
[verification notes](program-verification.md).

## Read, try, build {#start}

- Start with the [tutorial](tutorial.md), then use the
  [language reference](language.md) for precise rules and builtin forms.
- Open the [browser playground](playground.html) to edit and compile toy
  examples locally. Only the playground loads JavaScript and the compiler;
  this handbook requires neither. Runnable browser programs currently use a
  scalar subset; [browser support and limits](webassembly.md#browser-support)
  describe the boundary.
- From a repository checkout, build and run the native example:

```sh
nix develop
cargo build --release
./target/release/lim docs/answer.lim -o answer
./answer
# Exit status: 42
```

The complete handbook is this page. Use **Ctrl+F / Cmd+F** for a keyword or error
code, or save the HTML file for offline reading. Nothing is hidden in collapsed
panels.
