#!/usr/bin/env python3
"""Negative control: corrupt only the native closed-residue oracle.

The logical definitions remain intact. A false proposal must fail kernel
checking, restore state, and fall back; a later true proof must still pass.
Run from the repository root with the pinned Lean prefix as the first argument.
"""
import os
from pathlib import Path
import subprocess
import sys

prefix = Path(sys.argv[1]).resolve()
output = Path('.lake/spec-proposal-negative').resolve()
output.mkdir(parents=True, exist_ok=True)
# Reuse existing optional diagnostic objects without modifying their library.
for obj in Path('.lake/frontend-native').glob('*.o'):
    target = output / obj.name
    if not target.exists():
        target.symlink_to(obj.resolve())
builder = Path('scripts/build-frontend-plugin.py').read_text()
needle = '    digest = hashlib.sha256(raw).hexdigest()'
assert builder.count(needle) == 1
injection = '''    if module == 'Solidity.Calculus.ProvesDerive':
        body = raw.decode()
        pattern = r'LEAN_EXPORT lean_object\\* l_Solidity_Seq_residueQuoteWithin___redArg\\([^;\\n]*\\) \\{'
        match = re.search(pattern, body)
        if not match: raise RuntimeError('closed oracle C symbol missing')
        start = match.end() - 1
        end = start + 1
        depth = 1
        while depth:
            if body[end] == '{': depth += 1
            elif body[end] == '}': depth -= 1
            end += 1
        replacement = '{ puts("SPEC_PROPOSAL_ORACLE_CORRUPTED"); lean_dec(x_1); lean_dec(x_2); lean_dec(x_4); lean_dec(x_5); lean_dec(x_6); lean_dec(x_7); lean_object* result=lean_alloc_ctor(1,1,0); lean_ctor_set(result,0,lean_box(0)); return result; }'
        raw = ('extern int puts(const char*);\\n' + body[:start] + replacement + body[end:]).encode()
        source = output / 'CorruptedOracle.c'
        source.write_bytes(raw)
'''
builder = builder.replace(needle, injection + needle)
original_args = sys.argv
try:
    sys.argv = ['build-frontend-plugin.py', str(prefix), str(output)]
    exec(compile(builder, 'negative-control-builder', 'exec'), {'__name__': '__main__'})
finally:
    sys.argv = original_args
run = subprocess.run([str(prefix / 'bin/lean'), 'tests/automation/ClosedSpecRejected.lean',
    '-j1', '--tstack=131072', '-DElab.async=false',
    '--plugin=' + str(output / 'libSolidity_Frontend_Testing.so')],
    text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=False)
(output / 'result.log').write_text(run.stdout)
print(run.stdout)
if run.returncode != 0 or run.stdout.count('SPEC_PROPOSAL_ORACLE_CORRUPTED') < 2:
    raise SystemExit('negative control failed or corrupted oracle was not exercised')
if 'closed128: falseStore' not in run.stdout or 'semantic: falseStore' not in run.stdout:
    raise SystemExit('kernel rejection did not retry the semantic path')
print('PASS: corrupted native proposal rejected; fallback and later proof succeeded.')
