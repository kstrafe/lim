#!/usr/bin/env python3
"""Author the bounded native polynomial certificate for unit coordinates.

Every emitted helper and theorem is independently checked by Lim. This
optional source authoring tool supplies no compiler or proof authority.
"""
import argparse
import importlib.util
import re
import sys
from pathlib import Path

_spec=importlib.util.spec_from_file_location('flt_unit_coefficients',Path(__file__).with_name('generate-flt-cubes.py'))
_cubes=importlib.util.module_from_spec(_spec);sys.modules[_spec.name]=_cubes;_spec.loader.exec_module(_cubes)
add,mul=_cubes.add,_cubes.mul

class UnitBuilder(_cubes.CoefficientBuilder):
    def theorem(self,name,variables,left,right):
        super().theorem(name,variables,left,right)
        self.origins[-1]=f'scripts/generate-flt-unit-bounds.py:{sys._getframe(1).f_lineno}'
    def source(self):
        text=super().source().replace('scripts/generate-flt-cubes.py','scripts/generate-flt-unit-bounds.py')
        if len(text.encode())>8*1024*1024:raise ValueError('authoring source-size bound exceeded')
        return text

def generated_source():
    g='offset';large=add(2,g)
    builder=UnitBuilder()
    builder.theorem('natural-large-square-triple',(g,),mul(3,mul(large,large)),
        add(12,add(mul(12,g),mul(3,mul(g,g)))))
    return builder.source()

def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--check',action='store_true');args=parser.parse_args()
    path=Path(__file__).resolve().parent.parent/'theorems/flt/natural-unit-bound-polynomial.lim'
    source=generated_source()
    def tokens(text):return re.findall(r'[()]|[^()\s]+',re.sub(r';[^\n]*','',text))
    def origins(text):return [line for line in text.splitlines() if line.startswith('; scripts/generate-flt-unit-bounds.py:')]
    unchanged=path.exists() and tokens(path.read_text())==tokens(source) and origins(path.read_text())==origins(source)
    if args.check:
        if not unchanged:raise SystemExit(f'{path}: generated proof differs')
        print('Unit bound polynomial matches the checked source')
    elif unchanged:print('Unit bound polynomial unchanged; bytes and mtime preserved')
    else:path.write_text(source);print(f'Wrote {path.name}')

if __name__=='__main__':main()
