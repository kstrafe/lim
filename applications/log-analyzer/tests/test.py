#!/usr/bin/env python3
"""Black-box native executable tests; run from the repository root."""
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]

def summary(total=0, info=0, warn=0, error=0, other=0):
    return f'TOTAL {total}\nINFO {info}\nWARN {warn}\nERROR {error}\nOTHER {other}\n'.encode()

def check(name, data, expected):
    result = subprocess.run([str(ROOT / 'log-analyzer')], input=data, capture_output=True, check=False)
    assert (result.returncode, result.stdout, result.stderr) == (0, expected, b''), (name, result)
    print(f'PASS {name}')

check('empty', b'', summary())
check('mixed fixture', (ROOT / 'tests/fixtures/mixed.log').read_bytes(), summary(7, 2, 1, 1, 3))
check('CRLF', b'INFO ready\r\nWARN\r\nERROR failed\r\n\r\n', summary(4, 1, 1, 1, 1))
check('long lines', b'INFO ' + b'x' * 131072 + b'\n' + b'x' * 65536 + b'\n', summary(2, 1, 0, 0, 1))
check('final line without newline', b'WARN ready\nERROR', summary(2, 0, 1, 1))
check('token boundaries', b'INFORMATION\nWARNING\nERRORS\n info\nINFO\tready\nWARN\nERROR\n', summary(7, 1, 1, 1, 4))
check('decimal counts', b'INFO\n' * 123, summary(123, 123))
check('blank and final CR', b'\n\nINFO\r', summary(3, 1, 0, 0, 2))
result = subprocess.run([str(ROOT / 'log-analyzer')], input=b'INFO ok\n\xff', capture_output=True)
assert result.returncode == 1 and result.stdout == b'', result
print('PASS invalid UTF-8')
with open(os.devnull, 'wb') as closed_input:
    result = subprocess.run([str(ROOT / 'log-analyzer')], stdin=closed_input, capture_output=True)
assert result.returncode == 1 and result.stdout == b'', result
print('PASS stdin read error')
with open('/dev/full', 'wb') as full:
    result = subprocess.run([str(ROOT / 'log-analyzer')], input=b'INFO\n', stdout=full, stderr=subprocess.PIPE)
assert result.returncode == 2, result
print('PASS stdout write error')
