# Explicit Result propagation

When the failure payload is not needed, name only the success variant:

```lim
(#let-else (Input.Ok number) value
  (#else
    (#return (#call Output::err (: error 1u32)))))
```

The variant declares the expected enum type. The initializer is one expression
(possibly a `#block`); `#else` contains one or more statements. On failure all
paths must return, break/continue an enclosing loop, or otherwise diverge;
neither the following code nor the success binding can be reached. Merely
breaking a loop introduced inside the failure branch does not satisfy this.

`#let-else` can bind the failure payload of its original value:

```lim
(#generate #result (: ok #u64 : error #u32 : name Input))
(#generate #result (: ok #bool : error #u32 : name Output))

(#fn convert (: value Input) Output
  (#let-else (Input.Ok number) Input value
    (#else (Input.Err error)
      (#return (#call Output::err (: error error)))))
  (#return (#call Output::ok (: value (#u64::eq number 42u64)))))
```

The general syntax is
`(#let-else success-pattern ExplicitType value (#else failure-pattern statements...))`.
The compiler checks `value` against the explicit type and evaluates it once.
On success, success bindings are available in subsequent statements. On failure,
the failure pattern destructures the same value; its bindings are available only
inside `#else`. The failure statements must diverge, just like a plain let-else
fallback. Existing divergent fallbacks without `#else` remain accepted.

Both patterns are checked against the explicit type. Together they must cover
every possibility: the failure pattern must cover all success mismatches,
including mismatched payload literals within a success variant. Overlap is
permitted because the success pattern is tried first. Enum constructors,
aggregate fields, boolean alternatives, and wildcard patterns participate in
coverage checking. Integer and character patterns require a wildcard or binding
to establish complete coverage; numeric ranges alone do not establish coverage.
Existing restrictions on or-pattern bindings still apply.

Binding names cannot shadow an existing local. A failure binding cannot be used
after the let-else, and a success binding cannot be used inside its failure body.
Linear payloads must be consumed exactly once on their path. References retain
their borrowing provenance through destructuring and rewrapping. There is no
inferred propagation, conversion, or implicit destruction: explicitly construct
the destination Result's error variant with a payload of the same error type.

Built-in `#generate #result` and `#generate #optional` always generate their enum and constructors,
including for linear payloads. Their by-value predicates (`is-ok`, `is-some`)
and fallback unwrap helpers are generated only when the enum and all payloads
are Copy. These helpers discard payloads or fallbacks on some paths, so they
are omitted for linear values and exclusive references. Use explicit matching
or `#let-else` instead; no implicit `#forget` is generated. Copy payloads keep
the existing helper API. Inspectable generated source uses the same policy,
and its cache identity includes the declaration-dependent Copy context.
