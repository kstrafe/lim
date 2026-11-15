# Distributed dispatch

Declare an operation once and register direct handlers next to enum
contributions. After ordinary generator expansion and distributed enum
collection, the compiler emits one ordinary function containing an exhaustive
`#match` and direct handler calls. The emitted `.lim` file is the implementation
that is type checked and compiled, including on cache hits.

The runnable [example](../examples/distributed_dispatch.lim) returns 42:

```lisp run=42
#distributed-enum Message ()
#enum-contribute Message (Message.Number #u64)
#enum-contribute Message (Message.Empty)

#dispatch-fn evaluate {
  #params = { message = Message; offset = #u64; };
  #returns = #u64;
  #dispatch-on = message;
}
#dispatch-case evaluate Message.Number evaluate-number
#dispatch-case evaluate Message.Empty evaluate-empty

#fn evaluate-number {
  #params = { offset = #u64; message = #u64; };
  #returns = #u64;
  #body: #return (#u64::add-wrap message offset);
}
#fn evaluate-empty {
  #params = { offset = #u64; };
  #returns = #u64;
  #body: #return offset;
}
#fn main {
  #params = {};
  #returns = #u64;
  #body: #return (evaluate { message = (Message.Number 40u64); offset = 2u64; });
}
```

`#params`, `#returns` and `#dispatch-on` are required. The selector names exactly
one parameter. Other allowed sections are `#effects`, `#requires`, `#ensures`
and `#preserves`, with the same meanings as ordinary function sections.
A dispatcher has no authored `#body`. There are no implicit parameter values,
catch-all registrations, registration priorities or additional generator phases.
A concrete ordinary enum may also supply the selected type.

Each variant needs exactly one resolved handler. Repeating the same dispatcher,
variant and handler through aliases or files is permitted and retains every
registration origin. Different handlers for the same variant fail, as do unknown
dispatchers, handlers and variants. Registrations and contributions may occur
before their declarations; the compiler freezes collection before checking
coverage. Reordering or repeating identical registrations retains the same
implementation cache identity.

## Handler signatures and ownership

Handlers are ordinary safe functions. Their return type must equal the declared
dispatch return type after type-alias resolution. Every uncontrolled parameter
is passed unchanged by its declared name and type. The controlled parameter is
replaced by the single payload, using the same parameter name; a fieldless
variant omits it entirely. Parameter declaration order may differ. Use a named
struct payload for multiple fields. Unsafe and external functions cannot be
registered directly; write an ordinary safe adapter with the necessary unsafe
block and explicit effect interface. Compiler-only native/async signatures also
need an ordinary `#fn` adapter as the registered target.

For an enum `Message` with payload `Payload`, the selected type determines
projection:

| Dispatcher parameter type | Generated arm | Handler controlled parameter type |
| --- | --- | --- |
| `Message` | `#case` | `Payload` |
| `(#ref Message)` | `#case-ref` | `(#ref Payload)` |
| `(#ref-mut Message)` | `#case-ref-mut` | `(#ref-mut Payload)` |
| `(#pin-ref Message)` | `#case-pin` | `(#pin-ref Payload)` |
| `(#pin-ref-mut Message)` | `#case-pin-mut` | `(#pin-ref-mut Payload)` |

Raw pointers are not dispatch inputs. Normal borrow, pin, linear consumption,
return-reference dependencies and direct-call recursion rules apply to the
emitted function. Registration neither moves a value nor creates a loan.

## Effects, contracts and visibility

Effects remain explicit. Omitting `#effects` permits no IO or global effects.
For an output handler, an operation can author `#effects = (#io-output);` or
include its declared interface with `#effects = ((#effects-of write-handler));`.
Input-only permission rejects an output handler. Registering a handler never
widens the dispatcher interface. Normal handler-call prerequisite checks also
apply inside each arm; contract facts must follow from the authored dispatcher
contract or ordinary local evidence. Actual handler writes still invalidate
dependency facts through the normal read/write summaries.

A handler must be visible from both its registration and dispatcher contexts.
A private implementation needs an exported ordinary adapter when the dispatcher
is outside its library. Registration confers no private representation access,
effect authority, unsafe permission or borrow exemption. Generated sources keep
the dispatcher's original module authority, including on cached runs.

## Inspection and navigation

`#dispatch-fn` and `#dispatch-case` support the same generated-file lookup as
`#generate`. In the LSP, go-to-definition on either keyword opens the inspected
implementation; runtime calls target the generated function. Variant and handler
operands navigate to their exact declarations through file paths and aliases.
The generated function name returns to the authored declaration, and a generated
case keyword links to its registrations and handler. Errors in emitted cases
include registration and handler locations.

Tooling can call `lim::with_dispatch_manifest` around a compilation to receive
`DispatchManifest` values. Each includes the canonical name, authored declaration,
compiled source ID, artifact path and `DispatchRegistration` entries. Each
registration retains its original source tree and exact generated case,
case-keyword, variant and direct-call handler spans. For parse-only/editor
expansion the artifact path can be virtual; LSP publication uses the existing
checked snapshot path. Persisted cache comments are not authority or trusted
source maps.
