#!/usr/bin/env python3
"""Reproduce the unblocked validation packet; required full gates stay pending."""
import json
import os
from pathlib import Path
import subprocess
import sys
from generate import REPO
from build_closure import RUNTIME, LEAN


def main():
    evidence = RUNTIME/'evidence'
    script = Path(__file__).parent.resolve()
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
    commands = [
        ('census-tests', [sys.executable, str(script/'test_census.py')]),
        ('bounds-tests', [sys.executable, str(script/'test_bounds.py')]),
        ('generator-tests', [sys.executable, str(script/'test_generate.py')]),
        ('census-check', [sys.executable, str(script/'census.py'), '--output', str(evidence/'frontend-inventory.json'), '--check']),
        ('generation-check', [sys.executable, str(script/'generate.py'), '--check']),
        ('static-acceptance', [sys.executable, str(script/'acceptance.py'), '--inventory', str(evidence/'frontend-inventory.json'), '--output', str(evidence/'static-acceptance.json')]),
        ('keysort', [sys.executable, str(script/'bounded.py'), '--log', str(evidence/'keysort-final.log'), '--', str(LEAN), '-j1', '--tstack=131072', 'Solidity/KeySort.lean']),
        ('core-controls', [sys.executable, str(script/'build_closure.py'), 'tests.h62.item4.generic-source-frontend.CoreControls']),
        ('layers', ['node', 'scripts/check-layers.mjs']),
        ('roots', ['bash', 'scripts/coord-tools/register.sh', '--check']),
        ('fragments', ['bash', 'scripts/coord-tools/fragments.sh', '--check'])]
    results = []
    for label, command in commands:
        log = evidence/(label+'-gate.log')
        with log.open('w') as out:
            completed = subprocess.run(command, cwd=REPO, env=env, stdout=out, stderr=subprocess.STDOUT)
        result = dict(name=label, command=command, exit=completed.returncode,
                      status='pass' if completed.returncode == 0 else 'fail', log=str(log))
        results.append(result)
        print(json.dumps(result), flush=True)
        (evidence/'gate-results.json').write_text(json.dumps(results, indent=2)+'\n')
        if completed.returncode:
            raise SystemExit(completed.returncode)
    print('UNBLOCKED_PACKET_PASS; assignment, real parser/table, owner and full timing gates remain blocked')

if __name__ == '__main__':
    main()
