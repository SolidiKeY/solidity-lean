#!/usr/bin/env python3
"""Acceptance for census boundaries and refusal behavior; not semantic proof."""
import json
from pathlib import Path
import subprocess
import sys
from census import ROOT, collect, masked, signature_end
import re


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
    table = (ROOT/'tests/h62/item4/generic-primitive-packets/SubFixtures.lean').read_text()
    expected_names = {'minimum','maximum','equal','regular','underflow','far_underflow','wrong_order_refused'}
    rows = re.findall(r'^  \| \.(\w+) => ⟨⟨([^,]+), by decide⟩, ⟨([^,]+), by decide⟩⟩$', table, re.M)
    require({n for n,_,_ in rows} == expected_names and len(rows) == 7, 'lost or added concrete target table case')
    for name, left, right in rows:
        original = next(d for d in data['declarations'] if d['path'].endswith('/CheckedSub/Controls.lean') and d['name'].split('.')[-1] == name)
        run = re.search(r'run differenceCode \{machine (\(W-1\)|\d+) (\(W-1\)|\d+)', original['signature'])
        require(run is not None, f'missing original run observation: {name}')
        normalize = lambda t: t.replace('wordBound','W').strip('()')
        require(tuple(map(normalize,(left,right))) == tuple(map(normalize,run.groups())), f'changed operand table row: {name}')
    script = ROOT/'scripts/h62/item4/generic-primitive-packets/census.py'
    for flags in ([], ['-O']):
        command = [sys.executable,*flags,str(script),'--check',str(fixture)]
        passed = subprocess.run(command,capture_output=True,text=True)
        require(passed.returncode == 0, passed.stderr)
        bad = subprocess.run([sys.executable,*flags,str(script),'--check',str(fixture)+'.missing'],capture_output=True,text=True)
        require(bad.returncode != 0 and 'FROZEN_SOURCE_INVENTORY_PASS' not in bad.stdout, 'missing fixture accepted')
    require(json.loads(fixture.read_text()) == data, 'fixture mismatch')
    print('CENSUS_ACCEPTANCE_PASS: complete inventory, six let signatures, nested lets, comments, ordinary/optimized refusal, seven original operand bindings')


if __name__ == '__main__':
    main()
