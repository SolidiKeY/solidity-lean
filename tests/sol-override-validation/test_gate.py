"""Adversarial regression controls for the external evidence gate."""
from copy import deepcopy
import importlib.util
import json
import sys
sys.dont_write_bytecode = True
from pathlib import Path

root = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('gate', root / 'scripts/check-sol-override-validation.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)
rows = json.loads((gate.TESTS / 'matrix.json').read_text())
evidence = json.loads((gate.TESTS / 'evidence/compiler-matrix.json').read_text())
if gate.validate(rows, evidence) != len(rows):
    raise RuntimeError('baseline row count mismatch')

def reject(name, change):
    value = deepcopy(evidence)
    change(value)
    try:
        gate.validate(rows, value)
    except ValueError:
        print('PASS rejects ' + name)
    else:
        raise RuntimeError('gate accepted ' + name)

reject('missing row', lambda x: x['rows'].pop())
reject('extra row', lambda x: x['rows'].append(deepcopy(x['rows'][0])))
reject('reordered IDs', lambda x: x['rows'].reverse())
reject('changed source bytes', lambda x: x['rows'][0].update(sourceSha256='0'*64))
reject('changed compiler pin', lambda x: x.update(compilerSha256='0'*64))
reject('changed compiler version', lambda x: x.update(version='0.8.34'))
reject('changed verdict', lambda x: x['rows'][0].update(accepted=not x['rows'][0]['accepted']))
negative = next(i for i, r in enumerate(rows) if not r['expected'])
reject('missing diagnostic list', lambda x: x['rows'][negative].pop('errors'))
reject('object diagnostic list', lambda x: x['rows'][negative].update(errors={}))
reject('malformed diagnostic', lambda x: x['rows'][negative].update(errors=[{}]))
print('PASS 10 adversarial evidence controls')

# Replay controls deliberately rehash mutated output: they test semantic checks,
# rather than relying only on the outer integrity hash to reject corruption.
from unittest.mock import patch
import hashlib
manifest = json.loads((gate.TESTS / 'evidence/replay-manifest.json').read_text())
try:
    gate.validate_replays(rows, manifest)
except ValueError as error:
    if 'inputs changed' not in str(error):
        raise
    print('PASS rejects stale replay fingerprints after reviewed gate change')
# Isolate the semantic mutations below from the intentionally stale historical
# input fingerprint. This mock exists only in this regression process; neither
# recorded evidence nor production validation is rewritten.
gate.replay_inputs = lambda: manifest['inputs']
gate.validate_replays(rows, manifest)

def reject_manifest(name, change):
    value = deepcopy(manifest)
    change(value)
    try:
        gate.validate_replays(rows, value)
    except ValueError:
        print('PASS rejects ' + name)
    else:
        raise RuntimeError('gate accepted ' + name)

reject_manifest('unbound transitive input', lambda x: x['inputs'].pop('Solidity/Keccak.lean'))
reject_manifest('wrong Lean pin', lambda x: x.update(leanVersion='Lean 4.24.1'))
reject_manifest('wrong memory bound', lambda x: x.update(memoryBytes=20*1024**3))
reject_manifest('swap enabled', lambda x: x.update(swapBytes=1))
reject_manifest('failed build', lambda x: x['build'].update(exitCode=1))
reject_manifest('changed build log', lambda x: x['build'].update(sha256='0'*64))
reject_manifest('failed candidate', lambda x: x['candidate'].update(exitCode=1))
reject_manifest('changed candidate log', lambda x: x['candidate'].update(sha256='0'*64))

original_read_text = Path.read_text
original_read_bytes = Path.read_bytes

def reject_output(name, kind, change):
    filename = 'candidate-matrix.tsv' if kind == 'candidate' else 'current-checker.tsv'
    target = gate.TESTS / 'evidence' / filename
    lines = target.read_text().splitlines()
    change(lines)
    content = '\n'.join(lines) + '\n'
    value = deepcopy(manifest)
    value[kind]['sha256'] = hashlib.sha256(content.encode()).hexdigest()
    def read_text(path, *args, **kwargs):
        return content if path == target else original_read_text(path, *args, **kwargs)
    def read_bytes(path, *args, **kwargs):
        return content.encode() if path == target else original_read_bytes(path, *args, **kwargs)
    with patch.object(Path, 'read_text', read_text), patch.object(Path, 'read_bytes', read_bytes):
        try:
            gate.validate_replays(rows, value)
        except ValueError:
            print('PASS rejects ' + name)
        else:
            raise RuntimeError('gate accepted ' + name)

semantic_negative = next(i for i,r in enumerate(rows) if r['phase']=='override-control' and not r['expected'])
for kind in ['candidate', 'current']:
    def parse_refusal(lines):
        path = lines[semantic_negative].split('\t')[0]
        lines[semantic_negative] = path + '\tparse-error\t-\t' + ('0' if kind=='candidate' else '-')
    reject_output(kind + ' parser bypass of graph refusal', kind, parse_refusal)
reject_output('missing candidate row', 'candidate', lambda x: x.pop())
reject_output('reordered candidate rows', 'candidate', lambda x: x.reverse())
def flip(lines):
    fields=lines[semantic_negative].split('\t');fields[2]='true';lines[semantic_negative]='\t'.join(fields)
reject_output('candidate false pass', 'candidate', flip)
for name, data in [('package serial flag', b'name="test"\n[[lean_lib]]\nname="Test"\nweakLeanArgs=["-j1"]\n'),
                   ('library serial flag', b'name="test"\nweakLeanArgs=["-j1"]\n[[lean_lib]]\nname="Test"\n')]:
    try:
        gate.validate_serial_config(data)
    except ValueError:
        print('PASS rejects missing ' + name)
    else:
        raise RuntimeError('gate accepted missing ' + name)
print('PASS 25 adversarial compiler/replay evidence controls')
