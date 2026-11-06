#!/usr/bin/env python3
"""Acceptance for census boundaries and refusal behavior; not semantic proof."""
import json
from pathlib import Path
import subprocess
import sys
from census import ROOT, collect, masked, signature_end


def require(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    fixture = Path(sys.argv[1])
    data = collect(ROOT)
    require(data['summary']['files'] == 82, 'lost source file')
    require(data['summary']['control_files'] == 18, 'lost control file')
    require(data['summary']['declarations'] == 826, 'lost declaration')
    require(data['summary']['control_kinds'] == dict(abbrev=53, **{'def':204},example=3,theorem=216), 'lost control or anonymous case')
    keys = [(d['path'], d['name']) for d in data['declarations']]
    require(len(set(keys)) == len(keys), 'duplicate declaration identity')
    repaired = {
        'Bitwise.Selected.evalE_selected', 'Bitwise.Source.evalE_operand',
        'UnsignedCast.Compiler.machine_run', 'UnsignedCast.Controls.executions',
        'UnsignedCast.Transport.transport', 'UnsignedMul.Execution.execution'}
    for short in repaired:
        family, file, declaration = short.split('.')
        row = next(d for d in data['declarations'] if d['path'].endswith(f'/{family}/{file}.lean') and d['name'].split('.')[-1] == declaration)
        require('let ' in row['signature'] and (' = ' in row['signature'] or ' =\n' in row['signature']), f'incomplete let signature: {short}')
    synthetic = 'theorem t : let x := (let y := 1; y); let z := 2; x + z = 3 := by rfl'
    end = signature_end(masked(synthetic),0,len(synthetic))
    require(synthetic[end:] == ':= by rfl', 'nested let boundary')
    source = '-- theorem fake : False := by\n/- nested /- theorem fake2 -/ -/\ntheorem real : True := by trivial'
    require(masked(source).count('theorem') == 1, 'comment scanner')
    script = ROOT/'scripts/h62/item4/generic-primitive-packets/census.py'
    for flags in ([], ['-O']):
        command = [sys.executable,*flags,str(script),'--check',str(fixture)]
        passed = subprocess.run(command,capture_output=True,text=True)
        require(passed.returncode == 0, passed.stderr)
        bad = subprocess.run([sys.executable,*flags,str(script),'--check',str(fixture)+'.missing'],capture_output=True,text=True)
        require(bad.returncode != 0 and 'FROZEN_SOURCE_INVENTORY_PASS' not in bad.stdout, 'missing fixture accepted')
    require(json.loads(fixture.read_text()) == data, 'fixture mismatch')
    print('CENSUS_ACCEPTANCE_PASS: complete inventory, six let signatures, nested lets, comments, ordinary/optimized refusal')


if __name__ == '__main__':
    main()
