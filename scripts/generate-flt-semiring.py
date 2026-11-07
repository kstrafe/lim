#!/usr/bin/env python3
"""Write explicit Lim equality proofs for the small FLT semiring identities.

This is an authoring tool, not a compiler dependency or a proof oracle.
Every emitted definition is checked by Lim's existing kernel. No Lean export,
external algebra package, new kernel rule or unchecked arithmetic claim is used.
"""

import argparse
import re
import sys
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path


def add(a, b):
    return ("add", a, b)


def mul(a, b):
    return ("multiply", a, b)


def successor(a):
    return ("successor", a)


def square(a):
    return mul(a, a)


@lru_cache(None)
def render(expression):
    if isinstance(expression, str):
        return expression
    if isinstance(expression, int):
        assert 0 <= expression <= 128
        return f"(#pt-numeral {expression})"
    kind, *arguments = expression
    if kind == "successor":
        return f"(#pt-succ {render(arguments[0])})"
    return f"(#pt-app (#pt-use {kind} ()) {' '.join(map(render, arguments))})"


@lru_cache(None)
def expression_depth(expression):
    if not isinstance(expression, tuple):
        return 2
    return 1 + max(map(expression_depth, expression[1:]))


def application(name, arguments, universes="()"):
    head = f"(#pt-use {name} {universes})"
    return f"(#pt-app {head} {' '.join(arguments)})" if arguments else head


def equality(left, right):
    return f"(#pt-eq #pt-nat {render(left)} {render(right)})"


@lru_cache(None)
def monomial(variables):
    if not variables:
        return 1
    return variables[0] if len(variables) == 1 else mul(variables[0], monomial(variables[1:]))


@lru_cache(None)
def polynomial(terms):
    if not terms:
        return 0
    return monomial(terms[0]) if len(terms) == 1 else add(monomial(terms[0]), polynomial(terms[1:]))


@dataclass(frozen=True)
class Evidence:
    left: object
    right: object
    term: str
    depth: int


class Builder:
    def __init__(self):
        self.variables = ()
        self.helpers = []
        self.theorems = []
        self.cache = {}
        self.origins = []

    def emit(self, left, right, term, depth):
        key = (left, right)
        if key in self.cache:
            return self.cache[key]
        if len(term) > 4096 or depth > 26:
            if len(self.helpers) >= 384:
                raise ValueError("authoring helper bound exceeded")
            name = f"normalization-step-{len(self.helpers):03}"
            binders = " ".join(f"({name} #pt-nat)" for name in self.variables)
            ty = equality(left, right)
            if binders:
                ty = f"(#pt-pi ({binders}) {ty})"
                term = f"(#pt-lambda ({binders}) {term})"
            self.helpers.append(f"(#math-definition {name} () {ty} {term})")
            term = application(name, list(self.variables))
            depth = 3
        proof = Evidence(left, right, term, depth)
        self.cache[key] = proof
        return proof

    def reflexivity(self, expression, right=None):
        # A differing endpoint is used only for definitional arithmetic or
        # the first-operand definitions of add/multiply. Lim verifies it.
        if right is None:
            right = expression
        return self.emit(expression, right, f"(#pt-refl #pt-nat {render(expression)})", 1 + expression_depth(expression))

    def lemma(self, name, arguments, left, right):
        return self.emit(left, right, application(name, list(map(render, arguments))), 2 + max(map(expression_depth, arguments), default=0))

    def transitive(self, first, second):
        if first.right != second.left:
            raise ValueError("authoring equality endpoints do not match")
        if first.left == first.right:
            return second
        if second.left == second.right:
            return first
        args = ["#pt-nat", render(first.left), render(first.right), render(second.right), first.term, second.term]
        return self.emit(first.left, second.right, application("transitivity", args, "(0)"), 1 + max(first.depth, second.depth, expression_depth(first.left), expression_depth(first.right), expression_depth(second.right)))

    def symmetric(self, proof):
        args = ["#pt-nat", render(proof.left), render(proof.right), proof.term]
        return self.emit(proof.right, proof.left, application("symmetry", args, "(0)"), 1 + max(proof.depth, expression_depth(proof.left), expression_depth(proof.right)))

    def congruent(self, context, proof):
        parameter = "normalization-input"
        left, right = context(proof.left), context(proof.right)
        function = f"(#pt-lambda (({parameter} #pt-nat)) {render(context(parameter))})"
        args = ["#pt-nat", "#pt-nat", function, render(proof.left), render(proof.right), proof.term]
        return self.emit(left, right, application("congruence", args, "(0 0)"), 2 + max(proof.depth, expression_depth(left), expression_depth(right)))

    def binary(self, operation, first, second):
        a = self.congruent(lambda x: operation(x, second.left), first)
        b = self.congruent(lambda x: operation(first.right, x), second)
        return self.transitive(a, b)

    def append(self, first, second, product=False):
        term = monomial if product else polynomial
        operation = mul if product else add
        left = operation(term(first), term(second))
        right = term(first + second)
        if not first:
            if product:
                return self.lemma("multiply-one-left", [term(second)], left, right)
            return self.reflexivity(left, right)
        if not second:
            name = "multiply-one-right" if product else "add-zero-right"
            return self.lemma(name, [term(first)], left, right)
        if len(first) == 1:
            return self.reflexivity(left, right)
        head = first[0] if product else monomial(first[0])
        rest = term(first[1:])
        middle = operation(head, operation(rest, term(second)))
        name = "multiply-associative" if product else "add-associative"
        a = self.lemma(name, [head, rest, term(second)], left, middle)
        b = self.congruent(lambda x: operation(head, x), self.append(first[1:], second, product))
        return self.transitive(a, b)

    def insert(self, first, ordered, product=False):
        term = monomial if product else polynomial
        operation = mul if product else add
        source = (first,) + ordered
        if not ordered or first <= ordered[0]:
            return source, self.reflexivity(term(source))
        a = first if product else monomial(first)
        b = ordered[0] if product else monomial(ordered[0])
        if len(ordered) == 1:
            target = (ordered[0], first)
            name = "multiply-commutative" if product else "add-commutative"
            return target, self.lemma(name, [a, b], term(source), term(target))
        rest = term(ordered[1:])
        middle = operation(b, operation(a, rest))
        name = "multiply-left-commutative" if product else "add-left-commutative"
        swap = self.lemma(name, [a, b, rest], term(source), middle)
        tail, proof = self.insert(first, ordered[1:], product)
        lift = self.congruent(lambda x: operation(b, x), proof)
        return (ordered[0],) + tail, self.transitive(swap, lift)

    def ordered(self, items, product=False):
        term = monomial if product else polynomial
        operation = mul if product else add
        if len(items) <= 1:
            return items, self.reflexivity(term(items))
        tail, proof = self.ordered(items[1:], product)
        head = items[0] if product else monomial(items[0])
        lift = self.congruent(lambda x: operation(head, x), proof)
        result, inserted = self.insert(items[0], tail, product)
        return result, self.transitive(lift, inserted)

    def sum(self, first, second):
        appended = self.append(first, second)
        result, sorted_proof = self.ordered(first + second)
        return result, self.transitive(appended, sorted_proof)

    def product(self, first, second):
        left = mul(polynomial(first), polynomial(second))
        if not first:
            return (), self.reflexivity(left, 0)
        if not second:
            return (), self.lemma("multiply-zero-right", [polynomial(first)], left, 0)
        if len(first) == len(second) == 1:
            flattened = self.append(first[0], second[0], True)
            variables, sorted_proof = self.ordered(first[0] + second[0], True)
            return (variables,), self.transitive(flattened, sorted_proof)
        if len(first) > 1:
            a, b, c = monomial(first[0]), polynomial(first[1:]), polynomial(second)
            split = self.lemma("multiply-add-left", [a, b, c], left, add(mul(a, c), mul(b, c)))
            terms1, proof1 = self.product(first[:1], second)
            terms2, proof2 = self.product(first[1:], second)
        else:
            a, b, c = polynomial(first), monomial(second[0]), polynomial(second[1:])
            split = self.lemma("multiply-add-right", [a, b, c], left, add(mul(a, b), mul(a, c)))
            terms1, proof1 = self.product(first, second[:1])
            terms2, proof2 = self.product(first, second[1:])
        lift = self.binary(add, proof1, proof2)
        terms, collected = self.sum(terms1, terms2)
        return terms, self.transitive(self.transitive(split, lift), collected)

    def normalize(self, expression):
        if isinstance(expression, str):
            terms = ((expression,),)
            return terms, self.reflexivity(expression)
        if isinstance(expression, int):
            terms = ((),) * expression
            return terms, self.reflexivity(expression, polynomial(terms))
        kind, *args = expression
        if kind == "successor":
            expanded = add(1, args[0])
            terms, proof = self.normalize(expanded)
            return terms, self.transitive(self.reflexivity(expression, expanded), proof)
        first, proof1 = self.normalize(args[0])
        second, proof2 = self.normalize(args[1])
        operation = add if kind == "add" else mul
        lift = self.binary(operation, proof1, proof2)
        terms, proof = self.sum(first, second) if kind == "add" else self.product(first, second)
        return terms, self.transitive(lift, proof)

    def theorem(self, name, variables, left, right):
        self.origins.append(f"scripts/generate-flt-semiring.py:{sys._getframe(1).f_lineno}")
        self.variables = variables
        self.cache = {}
        left_terms, left_proof = self.normalize(left)
        right_terms, right_proof = self.normalize(right)
        if left_terms != right_terms:
            raise ValueError(f"{name}: candidate identity is false")
        proof = self.transitive(left_proof, self.symmetric(right_proof))
        parameters = " ".join(f"(#parameter {variable} #pt-nat)" for variable in variables)
        self.theorems.append(f"(#theorem {name} (#universes) (#parameters {parameters}) (#statement {equality(left, right)}) (#proof {proof.term}))")

    def source(self):
        aliases = {
            "add": "../fermat_statement.lim",
            "multiply": "../fermat_statement.lim",
            "symmetry": "./equality.lim",
            "transitivity": "./equality.lim",
            "congruence": "./equality.lim",
            "add-zero-right": "./natural-addition.lim",
            "add-commutative": "./natural-addition.lim",
            "add-associative": "./natural-addition.lim",
            "add-left-commutative": "./natural-multiplication-commutative.lim",
            "multiply-zero-right": "./natural-multiplication-right.lim",
            "multiply-one-right": "./natural-multiplication-right.lim",
            "multiply-one-left": "./natural-multiplication.lim",
            "multiply-associative": "./natural-multiplication.lim",
            "multiply-add-left": "./natural-multiplication.lim",
            "multiply-add-right": "./natural-multiplication-order.lim",
            "multiply-commutative": "./natural-multiplication-commutative.lim",
            "multiply-left-commutative": "./natural-square-arithmetic.lim",
        }
        header = "; Generated by scripts/generate-flt-semiring.py; native proof terms, not trusted results.\n"
        header += "; Lim checks every auxiliary definition and theorem against the existing semiring lemmas.\n"
        header += "; Generated from:\n" + "".join(f"; {origin}\n" for origin in self.origins)
        header += "\n".join(f"(#alias {name} = {path}::{name})" for name, path in aliases.items())
        result = header + "\n\n" + "\n\n".join(self.helpers + self.theorems) + "\n"
        if len(result.encode()) > 8 * 1024 * 1024:
            raise ValueError("authoring source bound exceeded")
        return result


def generated_source():
    builder = Builder()
    a, b = "first", "second"
    builder.theorem("double-as-sum", (a,), mul(2, a), add(a, a))
    builder.theorem("double-square", (a,), square(mul(2, a)), mul(4, square(a)))
    builder.theorem("odd-square", (a,), square(successor(mul(2, a))), successor(mul(4, add(square(a), a))))
    builder.theorem("two-odd-residues-add", (a, b), add(successor(mul(4, a)), successor(mul(4, b))), add(mul(4, add(a, b)), 2))
    builder.theorem("two-odd-values-add", (a, b), add(successor(mul(2, a)), successor(mul(2, b))), mul(2, successor(add(a, b))))
    builder.theorem("double-product", (a, b), mul(mul(2, a), mul(2, b)), mul(4, mul(a, b)))
    builder.theorem("square-add", (a, b), square(add(a, b)), add(add(square(a), mul(2, mul(a, b))), square(b)))
    builder.theorem("square-gap-product", (a, b), square(add(a, b)), add(square(a), mul(add(add(a, b), a), b)))
    builder.theorem("square-double-gap", (a, b), square(add(a, mul(2, b))), add(square(a), mul(4, mul(b, add(a, b)))))
    builder.theorem("add-one-is-successor", (a,), add(a, 1), successor(a))
    return builder.source()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="verify generated tokens, allowing Lim formatting")
    args = parser.parse_args()
    output = Path(__file__).resolve().parent.parent / "theorems/flt/natural-semiring-identities.lim"
    source = generated_source()
    # These generated terms contain no string literals. Comments and
    # whitespace therefore separate tokens without affecting their values.
    def tokens(text):
        return re.findall(r"[()]|[^()\s]+", re.sub(r";[^\n]*", "", text))

    def origins(text):
        return [line.strip() for line in text.splitlines()
                if line.strip().startswith("; scripts/generate-flt-semiring.py:")]

    current = output.read_text() if output.is_file() else None
    matches = current is not None and tokens(current) == tokens(source) and origins(current) == origins(source)
    if args.check:
        if not matches:
            raise SystemExit("semiring proof source differs; regenerate with this script")
    elif not matches:
        output.write_text(source)


if __name__ == "__main__":
    main()
