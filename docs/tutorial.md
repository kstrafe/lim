# Tutorial {#tutorial}

Lim is a statically typed Lisp with explicit returns, ownership and arithmetic
behavior. Surface syntax sugar—named records, colon and indentation grouping,
and typed infix expressions—reduces nesting and visual noise while keeping those
semantics explicit. Builtins begin with `#`; your names do not.

Start here, then use the [complete language reference](#language-reference),
[alphabetical builtin table](#complete--builtin-reference-alphabetical), or
[contract reference](#predicate-contracts-and-constrained-types). The separate
[browser playground](playground.html) runs small examples with the real compiler.
The full native language is broader than its first WebAssembly backend.

## 1. Print Hello, world! {#first-program}

This program builds a string, prints it to standard output, releases it, and
explicitly returns unit:

```lisp run=0
#std

#fn main {
  #params = {};
  #returns = ();
  #effects = (
    (#effects-of String::from-chars)
    (#effects-of std-println)
    (#effects-of String::free)
  );
  #body:
    #let greeting (#array #char 13) "Hello, world!";
    #let message String:
      #match String::from-chars { text = (#borrow-slice greeting); }
        (#case (StringCreateResult.StringCreated owned) owned)
        (#case (StringCreateResult.StringCreateFailed error) (#panic))
    #assert [#i64; (#println (#borrow message)) == 0i64];
    String::free { string = message; };
    #return ();
}
```

`#std` opts into the bundled String and stdout modules. `String::from-chars`
returns a result, so the program handles both success and failure. `#println`
borrows the string, writes its UTF-8 text and a newline, and returns zero on
success; the assertion checks that status. The string remains owned until
`String::free` releases it.

`#effects` explicitly includes the allocation, printing, and cleanup APIs used
by `main`. These permissions are separate from predicate preconditions; omitting
them does not make an effectful function pure.

`#fn` declares a function. `#params` is a record of parameter names and types;
this function has none. `#returns` is always explicit, and `#body` contains the
function’s forms. A function with no value uses `#returns = ();` and
`#return ();`.

## 2. Return a value {#return-value-tutorial}

This program returns 42 as its exit status:

```lisp run=42
#fn main {
  #params = {};
  #returns = #u64;
  #body: #return 42;
}
```

`#u64` is an unsigned 64-bit integer. An unsuffixed literal gets its type from
this explicitly declared context; `42u64` spells it directly. The playground
displays the returned value. Native exit statuses are limited by the operating
system, so returning a number is different from printing text.

Run the printing example natively from a checkout:

```sh
nix develop
cargo build
./target/debug/lim examples/tutorial_hello.lim -o /tmp/tutorial-hello
/tmp/tutorial-hello
```

## 3. Read the tree beneath the sugar {#syntax-cheat-sheet}

Each surface form has a local, mechanical interpretation:

| Surface spelling | Tree or meaning |
| --- | --- |
| `{ left = x; right = y; }` | `((left x) (right y))` |
| `{ left; right; }` | `((left left) (right right))` |
| `(a : b c)` | `(a (b c))` |
| `(a : b : c)` | `(a (b (c)))` |
| `: a b` | `(a b)` |
| `(: a b)` | `((a b))` |
| `#return x; #return y;` inside a sequence | Two complete forms, each grouped by its semicolon |
| A colon at the end of a line | Group the following indented syntax; close on dedent |
| `[#u64 #wrap; x + y * z]` | `(#u64::add-wrap x (#u64::mul-wrap y z))` |
| `// comment` | A line comment |

Inline colons consume through a newline, semicolon, or enclosing closing
delimiter. Consecutive colons nest to the right. Semicolons inside explicit
parentheses or an indented group belong to that group. Use spaces for layout.

Curly braces contain named entries: `key = value;`, or `key;` when the variable
has the same name. Borrowing stays explicit. Use `key:` when the value is
colon-grouped. Parentheses delimit ordinary forms; square brackets
select infix parsing. Nested square brackets inherit their arithmetic header
only through direct bracket nesting. A function-call parenthesis ends that
inheritance, so brackets inside the call need their own header.

Canonical S-expressions describe the trees used by generators. This example
shows syntax data beneath the surface notation; source files use bare roots:

```lisp syntax
(#fn main () #u64
  (#return (#u64::add-wrap 40u64 2u64)))
```

## 4. Declare and call a function {#functions-tutorial}

Calls name their arguments. Their written order can differ from the declaration;
expressions are evaluated once in the order you write them. Names choose the
destination parameters; they do not rearrange effects. An earlier argument
finishes before a later one starts, and all arguments finish before callee entry.

```lisp run=42
#fn subtract {
  #params = { left = #u64; right = #u64; };
  #returns = #u64;
  #body: #return [#u64 #wrap; left - right];
}

#fn main {
  #params = {};
  #returns = #u64;
  #body: #return subtract { right = 2; left = 44; };
}
```

`#wrap` states overflow behavior. Integer arithmetic must choose the required
wrapping or saturation behavior explicitly; comparisons use a type header without
an arithmetic mode, such as `[#u64; value < 100]`.

`#call` remains a canonical form understood by the compiler and generators.
Handwritten code can call an ordinary function with its name and an argument
record. Functions are free-standing declarations; there is no method lookup.

## 5. Mutate a local and write a loop {#loops-tutorial}

`#let` binds an immutable value. `#let-mut` permits assignment with `#set`.
A range is half-open: `1` through `11` means the numbers 1 through 10.

```lisp run=55
#fn main {
  #params = {};
  #returns = #u64;
  #body:
    #let-mut total #u64 0;
    #for-range (number #u64) 1 11:
      #set total [#u64 #wrap; total + number];
    #return total;
}
```

The loop’s colon opens its body. Dedent closes it; the final return belongs to
the function. `#while`, `#for` and `#loop` cover other iteration shapes.
`#break` exits a loop; `#continue` starts its next iteration. In a `#for` loop,
continuing still executes the step. Names cannot shadow existing bindings.

For actual printed output, see the working
[1-through-10 native printing example](../examples/print_numbers.lim).
The browser’s initial scalar backend reports return values instead of host I/O.

## 6. Validate an API argument once {#contracts-tutorial}

A predicate is an ordinary pure Boolean function. A function that requires it
can be called only where the checker already has matching evidence.

```lisp run=42
#fn positive {
  #params = { value = #u64; };
  #returns = #bool;
  #body: #return [#u64; value > 0];
}

#fn accept {
  #params = { value = #u64; };
  #returns = #u64;
  #requires: positive { value = value; };
  #ensures: positive { value = (#result); };
  #body: #return value;
}

#fn main {
  #params = {};
  #returns = #u64;
  #body:
    #let input #u64 42;
    #return (#if-valid positive { value = input; }
      accept { value = input; }
      0u64);
}
```

`#if-valid` runs the predicate. Its successful branch carries the evidence into
the call. Ordinary `#if` does not grant this evidence. Removing the validation
branch makes the call fail to check, even though this particular literal is 42.
The checker follows explicit claims; it does not unfold predicates or solve
arithmetic implications.

| Mechanism | What it gives you |
| --- | --- |
| `#requires` | Evidence the caller must provide; available on function entry. Multiple clauses mean AND. |
| `#ensures` | A programmer promise available after normal return. Instrumented builds audit it. |
| `#preserves` | If the caller already had the property, it survives the call; it is not a prerequisite. |
| `#result` | The returned value, available in a postcondition. |
| `#old` | An entry observation for a postcondition; use scalar observations. |
| `#assume` | Explicitly trust a claim without evaluating its predicate or arguments. |
| `#where` | A fixed storage constraint with the base type’s representation. |

Use `--check-contracts` when testing native programs. It audits requirements,
postconditions and preservation, but does not prove a programmer’s promise for
all inputs. Production can omit these extra audits. The playground enables them.

## 7. Borrow storage explicitly {#borrowing-tutorial}

A mutable reference grants exclusive access. End it before using the owner again:

```lisp run=42
#fn main {
  #params = {};
  #returns = #u64;
  #body:
    #let-mut number #u64 40u64;
    #let view (#ref-mut #u64): #borrow-mut number;
    #deref-set view 42u64;
    #forget view;
    #return number;
}
```

`#forget` explicitly consumes this handle. Ownership and borrow checking remain
active inside `#unsafe`. Linear values must be consumed; Copy values may be
reused. Destruction is explicit. Returned references retain the source storage’s
lifetime obligations.

Evidence is tied to the storage read by a predicate. A relevant write can revoke
a temporary fact. Fixed constraints in stored types must instead be restored
before an exclusive borrow returns access to the owner. See
[constrained types](#predicate-contracts-and-constrained-types) for the detailed
restoration rules. A valid property of an unrelated field can remain available.

This example can use **Check only** in the browser; reference code generation
currently belongs to the native backend.

## 8. Prove an array index {#array-evidence-tutorial}

This checks the exact comparison needed by the access, then uses its evidence:

```lisp run=42
#fn main {
  #params = {};
  #returns = #u64;
  #body:
    #let items (#array #u64 2): #array-of (#array #u64 2) 20u64 42u64;
    #let view (#ref (#array #u64 2)): #borrow items;
    #let index #usize 1usize;
    #return: #if-valid [#usize; index < 2usize] (#index-proven view index) 0u64;
}
```

The index must be `#usize`, and the comparison must mention this index and this
array length. A fact about another index or bound does not match. A named
validator with the same implementation is still a distinct predicate.

To connect claims, call an ordinary helper with explicit `#requires` and
`#ensures`. The [generated fixed-array API](#fixed-array-apis) supplies such a
helper. The checker does not discover the conversion on its own. Proven access
omits the bounds check in production; instrumented compilation audits the access.
This example is available through **Check only** in the browser.

## 9. Generate a concrete type {#generators-tutorial}

Generators produce concrete declarations instead of hidden runtime dispatch:

```lisp run=42
#generate #optional { type = #u64; name = MaybeNumber; }

#fn main {
  #params = {};
  #returns = #u64;
  #body:
    #let value MaybeNumber: MaybeNumber::construct { value = 42u64; };
    #return: #match value (#case (MaybeNumber.Some number) number) (#case MaybeNumber.None 0u64);
}
```

Generated source is inspectable in `.lim/generated/`. Builtin and library
generators use reserved names such as `#optional`; user generators use ordinary
names. The pure generator language uses `#gn`, `#gn-fn` and the restricted
`#gn-*` operations. All emitted runtime code still passes ordinary validation.

Use the [generator reference](#user-defined-generators) for syntax bundles,
quoting, generated declarations, validation witnesses and file authority.
Generating a type does not make it an opaque mathematical proof.

## 10. Follow a diagnostic {#diagnostics-tutorial}

The compiler distinguishes parsing, generation, types, borrows, linearity,
unsafe use, contracts, code generation and linking. A failed check gives a
source location and, where available, related locations.

```lisp error=E4000
#fn main {
  #params = {};
  #returns = #u64;
  #body:
    #let answer #u64 false;
    #return answer;
}
```

Here the declared type is `#u64` and the value is `#bool`. Change `false` to 42.
For contract errors, first compare the required predicate and argument identities
with the available evidence. For borrow errors, inspect which owner or reference
still has access. For unsupported WebAssembly code generation, use **Check only**
or run the example natively.

## 11. Keep the compiler stages in view {#pipeline-tutorial}

<svg class="pipeline" xmlns="http://www.w3.org/2000/svg" viewBox="0 0 720 120" role="img" aria-labelledby="pipeline-title pipeline-desc">
<title id="pipeline-title">Lim compilation pipeline</title><desc id="pipeline-desc">Source is read into trees, expanded, checked, then emitted for native execution or the teaching WebAssembly backend.</desc>
<rect x="1" y="24" width="128" height="60" rx="7"/><rect x="165" y="24" width="128" height="60" rx="7"/><rect x="329" y="24" width="128" height="60" rx="7"/><rect x="493" y="24" width="226" height="60" rx="7"/>
<text x="65" y="59" text-anchor="middle">Read trees</text><text x="229" y="59" text-anchor="middle">Expand</text><text x="393" y="59" text-anchor="middle">Check</text><text x="606" y="51" text-anchor="middle">Emit native code</text><text x="606" y="69" text-anchor="middle">or teaching Wasm</text>
<path d="M130 54h30m-6-5 6 5-6 5M294 54h30m-6-5 6 5-6 5M458 54h30m-6-5 6 5-6 5"/>
</svg>

Surface syntax changes how a tree is written. Generators change which concrete
program is checked. Type, ownership, borrow and contract checking decide whether
that program is accepted. A backend then emits code for its supported operations.
An unsupported backend feature is an error, not permission to skip validation.

The rest of this page is the full language reference. Its examples are checked
against the native compiler. The [WebAssembly notes](webassembly.md) describe the
smaller runnable browser subset, build command and versioned compiler interface.
