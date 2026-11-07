#!/usr/bin/env python3
"""Author bounded native Lim proofs of the cubic descent ring expansion.

The optional tool composes the existing Eisenstein ring theorems. It grants
no authority: Lim checks every emitted helper and theorem. No compiler or
kernel modification, external algebra package or Lean export is required.
"""
import argparse
import importlib.util
import re
import sys
from pathlib import Path

_spec = importlib.util.spec_from_file_location(
    'flt_cubic_semiring', Path(__file__).with_name('generate-flt-semiring.py'))
_semiring = importlib.util.module_from_spec(_spec)
sys.modules[_spec.name] = _semiring
_spec.loader.exec_module(_semiring)
add, mul = _semiring.add, _semiring.mul


def call(name, *arguments):
    head = f'(#pt-use {name} ())'
    return f'(#pt-app {head} {" ".join(arguments)})' if arguments else head


def render(expression):
    if isinstance(expression, str):
        return expression
    if isinstance(expression, int):
        if expression not in (0, 1):
            raise ValueError('only zero and one occur in this ring expansion')
        return call('eisenstein-one' if expression else 'eisenstein-zero')
    if expression[0] not in ('add', 'multiply'):
        raise ValueError('unsupported authoring operation')
    return call('eisenstein-' + expression[0], *(render(x) for x in expression[1:]))


def equality(left, right):
    return call('eisenstein-equal', render(left), render(right))


class RingBuilder(_semiring.Builder):
    def emit(self, left, right, proof, depth):
        key = (left, right)
        if key in self.cache:
            return self.cache[key]
        if len(proof) > 4096 or depth > 26:
            if len(self.helpers) >= 384:
                raise ValueError('authoring helper bound exceeded')
            name = f'cubic-ring-step-{len(self.helpers):03}'
            binders = ' '.join(f'({v} (#pt-use eisenstein ()))' for v in self.variables)
            self.helpers.append(
                f'(#math-definition {name} () (#pt-pi ({binders}) {equality(left, right)}) '
                f'(#pt-lambda ({binders}) {proof}))')
            proof = call(name, *self.variables)
            depth = 3
        result = _semiring.Evidence(left, right, proof, depth)
        self.cache[key] = result
        return result

    def reflexivity(self, expression, right=None):
        right = expression if right is None else right
        # Different endpoints arise only from first-operand zero reduction.
        # Their definitional conversion is checked independently by Lim.
        return self.emit(expression, right, call('eisenstein-reflexive', render(expression)), 2)

    def transitive(self, first, second):
        if first.right != second.left:
            raise ValueError('authoring equality endpoints do not match')
        if first.left == first.right:
            return second
        if second.left == second.right:
            return first
        return self.emit(first.left, second.right, call(
            'eisenstein-transitive', render(first.left), render(first.right),
            render(second.right), first.term, second.term), 1 + max(first.depth, second.depth))

    def symmetric(self, proof):
        return self.emit(proof.right, proof.left, call(
            'eisenstein-symmetric', render(proof.left), render(proof.right), proof.term), 1 + proof.depth)

    def binary(self, operation, first, second):
        name = 'eisenstein-add-congruent' if operation is add else 'eisenstein-multiply-congruent'
        return self.emit(operation(first.left, second.left), operation(first.right, second.right),
                         call(name, render(first.left), render(second.left), render(first.right),
                              render(second.right), first.term, second.term),
                         1 + max(first.depth, second.depth))

    def congruent(self, context, proof):
        marker = 'cubic-authoring-input'
        def contains(x):
            return x == marker or (isinstance(x, tuple) and any(contains(y) for y in x[1:]))
        def walk(x):
            if x == marker:
                return proof
            if not contains(x):
                return self.reflexivity(x)
            return self.binary(add if x[0] == 'add' else mul, walk(x[1]), walk(x[2]))
        return walk(context(marker))

    def lemma(self, name, arguments, left, right):
        names = {
            'add-zero-right': 'eisenstein-add-zero',
            'add-commutative': 'eisenstein-add-commutative',
            'add-associative': 'eisenstein-add-associative',
            'multiply-zero-right': 'eisenstein-multiply-zero',
            'multiply-one-right': 'eisenstein-multiply-one',
            'multiply-one-left': 'eisenstein-one-multiply',
            'multiply-associative': 'eisenstein-multiply-associative',
            'multiply-add-left': 'eisenstein-multiply-distributive',
            'multiply-add-right': 'eisenstein-multiply-distribute-second',
            'multiply-commutative': 'eisenstein-multiply-commutative',
        }
        if name in ('add-left-commutative', 'multiply-left-commutative'):
            a, b, c = arguments
            operation, prefix = (add, 'add') if name.startswith('add') else (mul, 'multiply')
            first = self.symmetric(self.lemma(prefix + '-associative', [a, b, c],
                operation(operation(a, b), c), operation(a, operation(b, c))))
            second = self.congruent(lambda x: operation(x, c), self.lemma(prefix + '-commutative',
                [a, b], operation(a, b), operation(b, a)))
            third = self.lemma(prefix + '-associative', [b, a, c],
                operation(operation(b, a), c), operation(b, operation(a, c)))
            return self.transitive(self.transitive(first, second), third)
        return self.emit(left, right, call(names[name], *(render(x) for x in arguments)), 3)

    def theorem(self, name, variables, left, right):
        self.variables = variables
        self.cache = {}
        self.origins.append(f'scripts/generate-flt-cubic-factorization.py:{sys._getframe(1).f_lineno}')
        first, first_proof = self.normalize(left)
        second, second_proof = self.normalize(right)
        if first != second:
            raise ValueError(f'{name}: false candidate ring identity')
        proof = self.transitive(first_proof, self.symmetric(second_proof))
        parameters = ' '.join(f'(#parameter {v} (#pt-use eisenstein ()))' for v in variables)
        self.theorems.append(f'(#theorem {name} (#universes) (#parameters {parameters}) '
                             f'(#statement {equality(left, right)}) (#proof {proof.term}))')

    def source(self):
        aliases = {n: 'eisenstein-defs' for n in (
            'eisenstein', 'eisenstein-zero', 'eisenstein-one', 'eisenstein-add',
            'eisenstein-multiply', 'eisenstein-equal')}
        aliases.update({n: 'eisenstein-equality' for n in (
            'eisenstein-reflexive', 'eisenstein-symmetric', 'eisenstein-transitive',
            'eisenstein-add-congruent', 'eisenstein-multiply-congruent')})
        aliases.update({n: 'eisenstein-ring' for n in (
            'eisenstein-add-zero', 'eisenstein-add-commutative', 'eisenstein-add-associative',
            'eisenstein-multiply-zero', 'eisenstein-multiply-one', 'eisenstein-multiply-associative',
            'eisenstein-multiply-distributive', 'eisenstein-multiply-distribute-second',
            'eisenstein-multiply-commutative')})
        aliases['eisenstein-one-multiply'] = 'eisenstein-cubic-bridge'
        source = '; Generated by scripts/generate-flt-cubic-factorization.py; native checked proofs.\n; Generated from:\n'
        source += ''.join(f'; {origin}\n' for origin in self.origins)
        source += ''.join(f'(#alias {n} = ./{m}.lim::{n})\n' for n, m in aliases.items())
        source += '\n' + '\n\n'.join(self.helpers + self.theorems) + '\n'
        if len(source.encode()) > 8 * 1024 * 1024:
            raise ValueError('authoring source-size bound exceeded')
        return source


def cube(x):
    return mul(x, mul(x, x))


def generated_source():
    a, b, w, v = 'first', 'second', 'root', 'root-square'
    product = mul(mul(add(a, b), add(a, mul(w, b))), add(a, mul(v, b)))
    expansion = add(cube(a), add(mul(mul(mul(a, a), b), add(add(v, w), 1)),
        add(mul(mul(a, mul(b, b)), add(add(v, w), mul(w, v))), mul(mul(w, v), cube(b)))))
    builder = RingBuilder()
    builder.theorem('eisenstein-cubic-factor-expansion', (a, b, w, v), product, expansion)
    builder.theorem('eisenstein-cubic-product-expansion', (a, b),
                    cube(mul(a, b)), mul(cube(a), cube(b)))
    return builder.source()


def tokens(text):
    return re.findall(r'[()]|[^()\s]+', re.sub(r';[^\n]*', '', text))


def origins(text):
    return [line.strip() for line in text.splitlines()
            if line.strip().startswith('; scripts/generate-flt-cubic-factorization.py:')]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    path = Path(__file__).resolve().parent.parent / 'theorems/flt/eisenstein-cubic-factor-expansion.lim'
    source = generated_source()
    unchanged = path.exists() and tokens(path.read_text()) == tokens(source) and origins(path.read_text()) == origins(source)
    if args.check:
        if not unchanged:
            raise SystemExit(f'{path}: generated proof differs')
        print('Cubic ring expansion matches the checked source')
    elif not unchanged:
        path.write_text(source)
        print(f'Wrote {path.name}')
    else:
        print('Cubic ring expansion unchanged; bytes and mtime preserved')


if __name__ == '__main__':
    main()
