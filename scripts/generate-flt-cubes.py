#!/usr/bin/env python3
"""Author checked Lim cube identities with compact, explicit coefficients.

The script emits equality proofs from the existing semiring lemmas. It is
not used by the compiler and grants no proof authority. Coefficients stay
numerals instead of expanding into a deep sum of repeated monomials.
"""

import argparse
import importlib.util
import re
import sys
from pathlib import Path

_spec = importlib.util.spec_from_file_location("flt_semiring_authoring", Path(__file__).with_name("generate-flt-semiring.py"))
_semiring = importlib.util.module_from_spec(_spec)
sys.modules[_spec.name] = _semiring
_spec.loader.exec_module(_semiring)
Builder = _semiring.Builder
add, mul = _semiring.add, _semiring.mul
monomial = _semiring.monomial


def term(item):
    variables, coefficient = item
    return mul(coefficient, monomial(variables))


def polynomial(items):
    if not items:
        return 0
    return term(items[0]) if len(items) == 1 else add(term(items[0]), polynomial(items[1:]))


class CoefficientBuilder(Builder):
    def append_sum(self, first, second):
        left = add(polynomial(first), polynomial(second))
        right = polynomial(first + second)
        if not first:
            return self.reflexivity(left, right)
        if not second:
            return self.lemma("add-zero-right", [polynomial(first)], left, right)
        if len(first) == 1:
            return self.reflexivity(left, right)
        a, b, c = term(first[0]), polynomial(first[1:]), polynomial(second)
        associate = self.lemma("add-associative", [a, b, c], left, add(a, add(b, c)))
        return self.transitive(associate, self.congruent(lambda x: add(a, x), self.append_sum(first[1:], second)))

    def combine_equal(self, first, second):
        variables, a = first
        other, b = second
        assert variables == other and 0 < a + b <= 128
        value = monomial(variables)
        split = self.lemma("multiply-add-left", [a, b, value], mul(add(a, b), value), add(term(first), term(second)))
        evaluated = self.congruent(lambda x: mul(x, value), self.reflexivity(add(a, b), a + b))
        return (variables, a + b), self.transitive(self.symmetric(split), evaluated)

    def insert_term(self, first, ordered):
        source = (first,) + ordered
        if not ordered or first[0] < ordered[0][0]:
            return source, self.reflexivity(polynomial(source))
        a, b = term(first), term(ordered[0])
        if first[0] == ordered[0][0]:
            combined, evidence = self.combine_equal(first, ordered[0])
            if len(ordered) == 1:
                return (combined,), evidence
            tail = polynomial(ordered[1:])
            reassociate = self.symmetric(self.lemma("add-associative", [a, b, tail], add(add(a, b), tail), polynomial(source)))
            lifted = self.congruent(lambda x: add(x, tail), evidence)
            return (combined,) + ordered[1:], self.transitive(reassociate, lifted)
        if len(ordered) == 1:
            return (ordered[0], first), self.lemma("add-commutative", [a, b], add(a, b), add(b, a))
        rest = polynomial(ordered[1:])
        swapped = self.lemma("add-left-commutative", [a, b, rest], polynomial(source), add(b, add(a, rest)))
        tail, evidence = self.insert_term(first, ordered[1:])
        return (ordered[0],) + tail, self.transitive(swapped, self.congruent(lambda x: add(b, x), evidence))

    def order_terms(self, items):
        if len(items) <= 1:
            return items, self.reflexivity(polynomial(items))
        tail, evidence = self.order_terms(items[1:])
        lifted = self.congruent(lambda x: add(term(items[0]), x), evidence)
        result, inserted = self.insert_term(items[0], tail)
        return result, self.transitive(lifted, inserted)

    def sum(self, first, second):
        appended = self.append_sum(first, second)
        result, collected = self.order_terms(first + second)
        return result, self.transitive(appended, collected)

    def multiply_terms(self, first, second):
        m, a = first
        n, b = second
        assert 0 < a * b <= 128
        x, y = monomial(m), monomial(n)
        left = mul(term(first), term(second))
        step1 = self.lemma("multiply-associative", [a, x, mul(b, y)], left, mul(a, mul(x, mul(b, y))))
        commute = self.lemma("multiply-left-commutative", [x, b, y], mul(x, mul(b, y)), mul(b, mul(x, y)))
        step2 = self.congruent(lambda z: mul(a, z), commute)
        step3 = self.symmetric(self.lemma("multiply-associative", [a, b, mul(x, y)], mul(mul(a, b), mul(x, y)), mul(a, mul(b, mul(x, y)))))
        step4 = self.congruent(lambda z: mul(z, mul(x, y)), self.reflexivity(mul(a, b), a * b))
        flattened = self.append(m, n, True)
        variables, ordered = self.ordered(m + n, True)
        monomial_proof = self.transitive(flattened, ordered)
        step5 = self.congruent(lambda z: mul(a * b, z), monomial_proof)
        proof = step1
        for next_proof in (step2, step3, step4, step5):
            proof = self.transitive(proof, next_proof)
        return ((variables, a * b),), proof

    def product(self, first, second):
        left = mul(polynomial(first), polynomial(second))
        if not first:
            return (), self.reflexivity(left, 0)
        if not second:
            return (), self.lemma("multiply-zero-right", [polynomial(first)], left, 0)
        if len(first) == len(second) == 1:
            return self.multiply_terms(first[0], second[0])
        if len(first) > 1:
            a, b, c = term(first[0]), polynomial(first[1:]), polynomial(second)
            split = self.lemma("multiply-add-left", [a, b, c], left, add(mul(a, c), mul(b, c)))
            terms1, proof1 = self.product(first[:1], second)
            terms2, proof2 = self.product(first[1:], second)
        else:
            a, b, c = polynomial(first), term(second[0]), polynomial(second[1:])
            split = self.lemma("multiply-add-right", [a, b, c], left, add(mul(a, b), mul(a, c)))
            terms1, proof1 = self.product(first, second[:1])
            terms2, proof2 = self.product(first, second[1:])
        lifted = self.binary(add, proof1, proof2)
        result, collected = self.sum(terms1, terms2)
        return result, self.transitive(self.transitive(split, lifted), collected)

    def normalize(self, expression):
        if isinstance(expression, str):
            canonical = ((expression,), 1)
            evidence = self.lemma("multiply-one-left", [expression], term(canonical), expression)
            return (canonical,), self.symmetric(evidence)
        if isinstance(expression, int):
            if expression == 0:
                return (), self.reflexivity(0)
            canonical = ((), expression)
            evidence = self.lemma("multiply-one-right", [expression], term(canonical), expression)
            return (canonical,), self.symmetric(evidence)
        kind, *args = expression
        if kind == "successor":
            expanded = add(1, args[0])
            terms, evidence = self.normalize(expanded)
            return terms, self.transitive(self.reflexivity(expression, expanded), evidence)
        first, proof1 = self.normalize(args[0])
        second, proof2 = self.normalize(args[1])
        operation = add if kind == "add" else mul
        lifted = self.binary(operation, proof1, proof2)
        terms, evidence = self.sum(first, second) if kind == "add" else self.product(first, second)
        return terms, self.transitive(lifted, evidence)

    def theorem(self, name, variables, left, right):
        origin = f"scripts/generate-flt-cubes.py:{sys._getframe(1).f_lineno}"
        super().theorem(name, variables, left, right)
        self.origins[-1] = origin

    def source(self):
        return super().source().replace("scripts/generate-flt-semiring.py", "scripts/generate-flt-cubes.py")


def cube(x):
    return mul(x, mul(x, x))


def generated_source():
    builder = CoefficientBuilder()
    x, y = "first", "second"
    builder.theorem("cube-three-multiple", (x,), cube(mul(3, x)), mul(9, mul(3, cube(x))))
    builder.theorem("cube-three-plus-one", (x,), cube(add(mul(3, x), 1)), add(mul(9, add(add(mul(3, cube(x)), mul(3, mul(x, x))), x)), 1))
    builder.theorem("cube-three-plus-two", (x,), cube(add(mul(3, x), 2)), add(mul(9, add(add(mul(3, cube(x)), mul(6, mul(x, x))), mul(4, x))), 8))
    builder.theorem("ninth-residues-one-one", (x, y), add(add(mul(9, x), 1), add(mul(9, y), 1)), add(mul(9, add(x, y)), 2))
    builder.theorem("ninth-residues-one-eight", (x, y), add(add(mul(9, x), 1), add(mul(9, y), 8)), mul(9, add(add(x, y), 1)))
    builder.theorem("ninth-residues-eight-eight", (x, y), add(add(mul(9, x), 8), add(mul(9, y), 8)), add(mul(9, add(add(x, y), 1)), 7))
    return builder.source()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    output = Path(__file__).resolve().parent.parent / "theorems/flt/natural-cube-identities.lim"
    generated = generated_source()
    def tokens(text):
        return re.findall(r"[()]|[^()\s]+", re.sub(r";[^\n]*", "", text))
    def origins(text):
        return [line.strip() for line in text.splitlines() if line.strip().startswith("; scripts/generate-flt-cubes.py:")]
    current = output.read_text() if output.is_file() else None
    matches = current is not None and tokens(current) == tokens(generated) and origins(current) == origins(generated)
    if args.check:
        if not matches:
            raise SystemExit("cube proof source differs; regenerate with this script")
    elif not matches:
        output.write_text(generated)


if __name__ == "__main__":
    main()
