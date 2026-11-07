#!/usr/bin/env python3
"""Author bounded native scalar proofs for the third-cyclotomic cube argument.

This tool composes proved integer ring laws. It grants no mathematical
assumption: every generated helper and theorem is checked by Lim.
"""
import argparse
import importlib.util
import re
import sys
from pathlib import Path

_spec = importlib.util.spec_from_file_location(
    'flt_cube_congruence_ring', Path(__file__).with_name('generate-flt-eisenstein-algebra.py'))
_ring = importlib.util.module_from_spec(_spec)
sys.modules[_spec.name] = _ring
_spec.loader.exec_module(_ring)
add, mul, negative, Eisenstein = _ring.add, _ring.mul, _ring.negative, _ring.Eisenstein

class CongruenceBuilder(_ring.IntegerPolynomialBuilder):
    def theorem(self, name, variables, left, right):
        super().theorem(name, variables, left, right)
        self.origins = [f'scripts/generate-flt-cube-congruences.py:{sys._getframe(1).f_lineno}']

    def source(self):
        return super().source().replace(
            'scripts/generate-flt-eisenstein-algebra.py',
            'scripts/generate-flt-cube-congruences.py')

def power(value, exponent):
    result = Eisenstein(1, 0)
    for _ in range(exponent):
        result = value * result
    return result

def identities():
    a, b = 'real-coordinate', 'omega-coordinate'
    y, one, omega = Eisenstein(a, b), Eisenstein(1, 0), Eisenstein(0, 1)
    omega_square, lam = Eisenstein(-1, -1), Eisenstein(-1, 1)
    x = one + lam * y
    result = []
    for label, left, right in [
        ('factor', (y * (y * y)) + (-one), ((y + (-one)) * (y + (-omega))) * (y + (-omega_square))),
        ('shift-omega', x + (-omega), lam * (y + (-one))),
        ('shift-square', x + (-omega_square), lam * (y + (-(omega + one)))),
        ('third-residue-shift', y + (-(omega + one)), (y + one) + (-(lam + Eisenstein(3, 0)))),
    ]:
        for coordinate in ['real', 'omega']:
            result.append((label + '-' + coordinate, (a, b), getattr(left, coordinate), getattr(right, coordinate)))
    for label, value, right in [
        ('coordinate-plus-one', y + one, add(add(a, b), 1)),
        ('coordinate-minus-one', y + (-one), add(add(a, b), negative(1))),
    ]:
        result.append((label, (a, b), add(value.real, value.omega), right))
    result.append(('integer-shift-cycle', ('number',), add(add('number', 1), 1), add(add('number', negative(1)), 3)))
    return result

def generate_sources():
    sources = {}
    for label, variables, left, right in identities():
        name = 'eisenstein-cube-scalar-' + label
        builder = CongruenceBuilder(name)
        builder.theorem(name, variables, left, right)
        sources[name + '.lim'] = builder.source()
    return sources

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent / 'theorems/flt'
    def tokens(source):
        return re.findall(r'[()]|[^()\s]+', re.sub(r';[^\n]*', '', source))
    def origins(source):
        return [line.strip() for line in source.splitlines()
                if line.strip().startswith('; scripts/generate-flt-cube-congruences.py:')]
    generated = generate_sources()
    for path in root.glob('eisenstein-cube-scalar-*.lim'):
        if path.name not in generated:
            raise SystemExit(f'{path.name}: unexpected scalar proof source')
    for name, source in generated.items():
        path = root / name
        current = path.read_text() if path.exists() else None
        matches = current is not None and tokens(current) == tokens(source) and origins(current) == origins(source)
        if args.check:
            if not matches:
                raise SystemExit(f'{name}: source differs; regenerate with this script')
        elif not matches:
            path.write_text(source)

if __name__ == '__main__':
    main()
