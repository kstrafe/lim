# Explicit Result propagation

`#let-else` can bind the failure payload of its original value:

```lim
(@result (: ok #u64 : error #u32 : name Input))
(@result (: ok #bool : error #u32 : name Output))

(#fn convert (: value Input) Output
  (#let-else (Input-ok-value number) Input value
    (#else (Input-err-value error)
      (#return (#call Output-err (: error error)))))
  (#return (#call Output-ok (: value (#u64.== number 42u64)))))
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

The current built-in `@result` fallback unwrap helpers are unsuitable for linear
payloads because those helpers discard payloads or fallbacks on some paths.
Equivalent explicitly declared enums support linear propagation with this syntax.
