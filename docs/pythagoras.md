# Pythagoras in Lim

[pythagoras.lim](../theorems/pythagoras.lim) contains a directly written proof
of the orthogonal-vector identity

\[
  Q(u+v) = Q(u) + Q(v),\qquad
  Q(x)=\langle x,x\rangle,\qquad \langle u,v\rangle=0.
\]

The theorem is universally quantified over the scalar and vector types,
their addition operations, a scalar zero, and a pairing. Its explicit proof
parameters supply exactly these laws:

- Scalar addition has a left and a right zero identity.
- The pairing is symmetric.
- The pairing distributes over vector addition in each argument.
- The two given vectors are orthogonal: their pairing is zero.

These are assumptions of the theorem, represented by bound proof parameters.
No global axiom, classical foundation constant, external certificate, bounded
numeric search or unproved theorem supplies evidence.

The proof expands both arguments of the pairing. Symmetry makes the reversed
cross term zero. Equality congruence and the scalar zero identities cancel
both cross terms, leaving the sum of the two squared lengths. The equality
helpers are themselves proved with the kernel's equality eliminator.

This algebraic formulation applies to every real inner product space when
its operations and law proofs are supplied. This file does not construct
the real numbers, a metric, square roots or an angle function, and does not
import Mathlib's distance-and-angle theorem. In particular, the empty global
foundation inventory does not remove the explicit hypotheses above.

Check the proof through the usual theorem interface:

```sh
target/debug/lim --check-theorem theorems/pythagoras.lim pythagoras-orthogonal
```

Recheck the closed source using the independent artifact interface:

```sh
target/debug/lim --check-proof-artifact theorems/pythagoras.lim pythagoras-orthogonal
```

Both commands check every declaration, including the equality helpers. No
Lean export is needed. Development checks should retain the resource guard:

```sh
bash scripts/limited-run.sh target/debug/lim \
  --check-theorem theorems/pythagoras.lim pythagoras-orthogonal
```
