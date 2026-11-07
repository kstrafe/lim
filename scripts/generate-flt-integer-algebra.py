#!/usr/bin/env python3
"""Author ordinary checked Nat identities for the formal-difference integers.

This source-writing tool supplies no proof authority. Its outputs use only
explicit equality proofs from previously checked Nat semiring lemmas.
"""

import argparse
import importlib.util
import re
import sys
from dataclasses import dataclass
from pathlib import Path

_spec = importlib.util.spec_from_file_location("flt_cube_authoring", Path(__file__).with_name("generate-flt-cubes.py"))
_cubes = importlib.util.module_from_spec(_spec)
sys.modules[_spec.name] = _cubes
_spec.loader.exec_module(_cubes)
add, mul = _cubes.add, _cubes.mul


class IntegerBuilder(_cubes.CoefficientBuilder):
    def theorem(self, name, variables, left, right):
        origin = f"scripts/generate-flt-integer-algebra.py:{sys._getframe(1).f_lineno}"
        super().theorem(name, variables, left, right)
        self.origins[-1] = origin

    def source(self):
        return super().source().replace("scripts/generate-flt-cubes.py", "scripts/generate-flt-integer-algebra.py")


@dataclass(frozen=True)
class Difference:
    positive: object
    negative: object

    def __add__(self, other):
        return Difference(add(self.positive, other.positive), add(self.negative, other.negative))

    def __neg__(self):
        return Difference(self.negative, self.positive)

    def __mul__(self, other):
        return Difference(add(mul(self.positive, other.positive), mul(self.negative, other.negative)),
                          add(mul(self.positive, other.negative), mul(self.negative, other.positive)))

    def cube(self):
        return self * (self * self)


def ring_laws():
    a = Difference("first-positive", "first-negative")
    b = Difference("second-positive", "second-negative")
    c = Difference("third-positive", "third-negative")
    zero, one = Difference(0, 0), Difference(1, 0)
    return [
        ("commutative", (a, b), a * b, b * a),
        ("associative", (a, b, c), (a * b) * c, a * (b * c)),
        ("distributive", (a, b, c), (a + b) * c, a * c + b * c),
        ("one", (a,), a * one, a),
        ("zero", (a,), a * zero, zero),
        ("negative", (a, b), (-a) * b, -(a * b)),
    ]


def generate_sources():
    result = {}
    builder = IntegerBuilder()
    a, b, c, d = "first", "second", "third", "fourth"
    builder.theorem("sum-four-interchange", (a, b, c, d), add(add(a, b), add(c, d)), add(add(a, c), add(b, d)))
    builder.theorem("sum-three-permutation", (a, b, c), add(add(a, b), c), add(add(a, c), b))
    ap, an, bp, bn, cp, cn = "first-positive", "first-negative", "second-positive", "second-negative", "factor-positive", "factor-negative"
    variables = (ap, an, bp, bn, cp, cn)
    builder.theorem("product-cross-group", variables,
                    add(add(mul(ap, cp), mul(an, cn)), add(mul(bp, cn), mul(bn, cp))),
                    add(mul(cp, add(ap, bn)), mul(cn, add(an, bp))))
    result["integer-cross-identities.lim"] = builder.source()
    # Independent small files keep each authoring DAG and each source form bounded.
    # The existing kernel budgets and the inherited authoring limits are unchanged.
    for name, operands, left, right in ring_laws():
        builder = IntegerBuilder()
        variables = tuple(part for operand in operands for part in (operand.positive, operand.negative))
        builder.theorem(f"product-{name}-positive", variables, left.positive, right.positive)
        builder.theorem(f"product-{name}-negative", variables, left.negative, right.negative)
        result[f"integer-product-{name}-identities.lim"] = builder.source()
    builder = IntegerBuilder()
    n = "number"
    natural_cube = mul(n, mul(n, n))
    for label, value, expected in [("positive", Difference(n, 0), Difference(natural_cube, 0)),
                                   ("negative", Difference(0, n), Difference(0, natural_cube))]:
        actual = value.cube()
        builder.theorem(f"cube-{label}-positive-component", (n,), actual.positive, expected.positive)
        builder.theorem(f"cube-{label}-negative-component", (n,), actual.negative, expected.negative)
    result["integer-cube-identities.lim"] = builder.source()
    builder = IntegerBuilder()
    a, b = "first", "second"
    actual = Difference(a, 0) * Difference(b, 0)
    builder.theorem("natural-product-positive-component", (a, b), actual.positive, mul(a, b))
    builder.theorem("natural-product-negative-component", (a, b), actual.negative, 0)
    result["integer-embedding-identities.lim"] = builder.source()
    builder = IntegerBuilder()
    from itertools import product
    a, b, c = "first", "second", "third"
    for signs in product((False, True), repeat=3):
        values = [Difference(0, value) if negative else Difference(value, 0)
                  for negative, value in zip(signs, (a, b, c))]
        first_two = values[0] + values[1]
        left = add(first_two.positive, values[2].negative)
        right = add(values[2].positive, first_two.negative)
        labels = "".join("n" if sign else "p" for sign in signs)
        expected = {
            "ppp": (add(a, b), c), "ppn": (add(add(a, b), c), 0),
            "pnp": (a, add(c, b)), "pnn": (add(a, c), b),
            "npp": (b, add(c, a)), "npn": (add(b, c), a),
            "nnp": (0, add(c, add(a, b))), "nnn": (c, add(a, b)),
        }[labels]
        builder.theorem(f"signed-sum-{labels}-left", (a, b, c), left, expected[0])
        builder.theorem(f"signed-sum-{labels}-right", (a, b, c), right, expected[1])
    result["integer-signed-sum-identities.lim"] = builder.source()
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent / "theorems/flt"
    def tokens(text):
        return re.findall(r"[()]|[^()\s]+", re.sub(r";[^\n]*", "", text))
    def origins(text):
        return [line.strip() for line in text.splitlines()
                if line.strip().startswith("; scripts/generate-flt-integer-algebra.py:")]
    generated = generate_sources()
    for name, source in generated.items():
        path = root / name
        current = path.read_text() if path.is_file() else None
        matches = current is not None and tokens(current) == tokens(source) and origins(current) == origins(source)
        if args.check:
            if not matches:
                raise SystemExit(f"{name}: source differs; regenerate with this script")
        elif not matches:
            path.write_text(source)


if __name__ == "__main__":
    main()
