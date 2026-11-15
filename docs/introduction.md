# Meet Lim {#introduction}

Lim is an experimental, statically typed, compiled Lisp for programs that people
and machines can both read. It aims to be a human-readable intermediate
representation for generated code: straightforward for a generator or language
model to produce, and explicit enough for a developer to inspect and change.
You can also write it by hand. This page introduces the design, teaches the
language, and keeps the full reference in one searchable document.

## Read what runs {#language}

Lim has explicit types, named call arguments, visible control flow, and explicit
returns. Arithmetic names its type and overflow behavior. Builtins begin with
`#`; your declarations use ordinary names. A small surface notation makes
handwritten code lighter while reducing to the same parenthesized trees that
code generators manipulate.

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

## Why a new language? {#why-a-new-language}

Generated programs still need human review. Following a call becomes harder
when its meaning depends on implicit conversions, receiver lookup, hidden
cleanup, or distant generic instantiations. Lim explores a deliberately smaller
design: make those decisions visible in source, give generators a simple tree
to produce, and check ownership and API requirements before emitting code.

The goal is to shorten the path from an idea to code you can understand and
run. The name evokes a limit as time approaches zero: less waiting to build,
less overhead to execute, less time reconstructing intent. These are engineering
targets, not benchmark results or a claim that Lim replaces established
languages for every project. Lim is experimental and unreleased; syntax,
semantics, backend coverage, and tooling can still change.

## Why these design choices? {#design-reasoning}

| Choice | Reason and tradeoff |
| --- | --- |
| One canonical tree, a small surface notation | Generators work with whole structures; readers can use records, indentation and infix expressions. Sugar lowers to the same forms instead of defining a second execution model. |
| Explicit types and operations | Bindings and arithmetic expose their meaning locally. There is no general type inference; unsuffixed literals can use an explicitly declared contextual type. This costs some extra source text. |
| Free-standing functions and explicit names | `Work::poll` is a function name; `Choice.Ready` is an enum variant. There are no methods, traits, closures, function pointers or recursive calls to resolve. This restricts familiar abstractions. |
| Concrete generated definitions | Pure compile-time generators produce ordinary Lim types and functions instead of user-facing generic types. Cached output in `.lim` is inspectable source with invocation provenance; concrete code can increase output size. |
| Reserved `#` builtins | Language additions such as `#feature` avoid taking the user name `feature`. The prefix protects names, not every possible syntax or semantic change. |
| Native compilation | The dependency-free Rust compiler encodes and links x86-64 Linux ELF executables internally. AArch64 and browser WebAssembly backends currently support smaller subsets. |

## What the compiler checks {#safety}

Ownership and borrowing checks track moves, exclusive access, returned references
and retained loans across functions, without user-written lifetime annotations.
Linear values need explicit consumption; destruction is visible rather than
silently inserted. Raw pointers and unsafe operations have an explicit boundary
and still need an audit. These checks target specific classes of mistakes;
they do not establish that every program is correct.

Predicate contracts let an API say what evidence a caller must supply. A
`#if-valid` branch runs a predicate and makes that exact fact available in its
true branch. `#requires`, `#ensures` and `#preserves` make function boundaries
explicit; mutations invalidate facts that depend on changed storage. There is
no automatic theorem search. Programmer-written promises in `#ensures` and
`#preserves`, and assertions through `#assume`, are trust boundaries. Optional
runtime contract audits check exercised paths; they are not mathematical proofs.
See the [contract tutorial](tutorial.md#contracts-tutorial) and
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
