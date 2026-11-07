#!/usr/bin/env python3
"""Author a bounded native ring expansion for cubic Bezout transport.

Lim checks every emitted helper and theorem. This optional authoring tool
adds no compiler dependency or logical authority.
"""
import argparse
import importlib.util
import sys
from pathlib import Path

_spec = importlib.util.spec_from_file_location(
    'flt_bezout_ring', Path(__file__).with_name('generate-flt-cubic-factorization.py'))
_ring = importlib.util.module_from_spec(_spec)
sys.modules[_spec.name] = _ring
_spec.loader.exec_module(_ring)
add, mul = _ring.add, _ring.mul

class BezoutBuilder(_ring.RingBuilder):
    def theorem(self, name, variables, left, right):
        super().theorem(name, variables, left, right)
        self.origins[-1] = f'scripts/generate-flt-cubic-bezout.py:{sys._getframe(1).f_lineno}'

    def source(self):
        return super().source().replace('scripts/generate-flt-cubic-factorization.py',
                                        'scripts/generate-flt-cubic-bezout.py')

def generated_source():
    s,t,c,d,e,f,x,y = 'left','right','first-x','first-y','second-x','second-y','x','y'
    left = add(mul(s,add(mul(c,x),mul(d,y))),mul(t,add(mul(e,x),mul(f,y))))
    right = add(mul(add(mul(s,c),mul(t,e)),x),mul(add(mul(s,d),mul(t,f)),y))
    builder = BezoutBuilder()
    builder.theorem('eisenstein-bezout-linear-expansion',(s,t,c,d,e,f,x,y),left,right)
    return builder.source()

def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--check',action='store_true');args=parser.parse_args()
    path=Path(__file__).resolve().parent.parent/'theorems/flt/eisenstein-bezout-linear-expansion.lim'
    source=generated_source()
    def origins(text):return [line for line in text.splitlines() if line.startswith('; scripts/generate-flt-cubic-bezout.py:')]
    unchanged=path.exists() and _ring.tokens(path.read_text())==_ring.tokens(source) and origins(path.read_text())==origins(source)
    if args.check:
        if not unchanged:raise SystemExit(f'{path}: generated proof differs')
        print('Bezout ring expansion matches the checked source')
    elif unchanged:print('Bezout ring expansion unchanged; bytes and mtime preserved')
    else:path.write_text(source);print(f'Wrote {path.name}')

if __name__=='__main__':main()
