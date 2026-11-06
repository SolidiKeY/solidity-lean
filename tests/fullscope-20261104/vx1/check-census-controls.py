#!/usr/bin/env python3
"""Execute the census checker on valid input and corrupt identity/fork inputs."""
import argparse, copy, json, subprocess, sys, tempfile
from pathlib import Path
HERE = Path(__file__).resolve().parent
parser = argparse.ArgumentParser()
parser.add_argument('--upstream', type=Path, required=True)
args = parser.parse_args()
original = json.loads((HERE / 'environment-census.json').read_text())
command = [sys.executable, str(HERE / 'check-census.py'), '--upstream', str(args.upstream)]
valid = subprocess.run(command, text=True, capture_output=True)
assert valid.returncode == 0, valid.stdout + valid.stderr
print(valid.stdout, end='')
cases = []
def mutated(name, change):
    data = copy.deepcopy(original)
    change(data)
    cases.append((name, data))
mutated('missing-source', lambda d: d['upstream']['sources'].pop())
mutated('duplicate-source', lambda d: d['upstream']['sources'].__setitem__(6, copy.deepcopy(d['upstream']['sources'][0])))
mutated('extra-source', lambda d: d['upstream']['sources'].append(copy.deepcopy(d['upstream']['sources'][0])))
mutated('unexpected-source', lambda d: d['upstream']['sources'][0].__setitem__('path', 'unexpected.cpp'))
mutated('wrong-source-hash', lambda d: d['upstream']['sources'][0].__setitem__('sha256', '0'*64))
mutated('missing-fork', lambda d: d['forkBoundaries'].pop('hasPrevRandao'))
mutated('extra-fork', lambda d: d['forkBoundaries'].__setitem__('hasUnexpected', 'osaka'))
mutated('wrong-fork', lambda d: d['forkBoundaries'].__setitem__('hasPrevRandao', 'london'))
with tempfile.TemporaryDirectory(prefix='.census-controls-', dir=HERE) as directory:
    for name, data in cases:
        path = Path(directory) / (name + '.json')
        path.write_text(json.dumps(data))
        result = subprocess.run(command + ['--census', str(path)], text=True, capture_output=True)
        assert result.returncode != 0, name + ': corrupted census accepted'
        print('NEGATIVE_PASS:', name)
print('CENSUS_CONTROLS_PASS:', len(cases), 'corruptions rejected')
