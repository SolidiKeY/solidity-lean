"""Run both checked-Source replays in the existing bounded serial container.

This records executions, not a compiler-equivalence theorem. Invoke from root.
"""
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('gate', ROOT / 'scripts/check-sol-override-validation.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)
rows = json.loads((gate.TESTS / 'matrix.json').read_text())
gate.validate(rows, json.loads((gate.TESTS / 'evidence/compiler-matrix.json').read_text()))
evidence = gate.TESTS / 'evidence'
prefix = ['docker', 'exec', '-e', 'LEAN_NUM_THREADS=1', 'sol-ov-session']
version = subprocess.check_output(prefix + ['lean', '--version'], text=True).strip()
limits = subprocess.check_output(prefix + ['sh', '-c', 'cat /sys/fs/cgroup/memory.max /sys/fs/cgroup/memory.swap.max'], text=True).splitlines()
effective = subprocess.check_output(prefix + ['cat', '/workspace/solidity-lean/lakefile.toml'])
gate.validate_serial_config(effective)
(evidence / 'serial-lakefile.toml').write_bytes(effective)
manifest = dict(inputs=gate.replay_inputs(), leanVersion=version, threads=1,
                memoryBytes=int(limits[0]), swapBytes=int(limits[1]),
                head=subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip())
build_args = prefix + ['lake', 'build', 'Solidity.Frontend.OverrideValidation.Memoized',
                       'Solidity.Frontend.Static.Inheritance', 'Solidity.Frontend.Checked.Check']
with (evidence / 'replay-build.log').open('w') as output:
    build = subprocess.run(build_args, stdout=output, stderr=subprocess.STDOUT, timeout=180)
if build.returncode:
    raise SystemExit(f'replay dependency build failed: exit {build.returncode}')
manifest['build'] = dict(command=build_args, exitCode=build.returncode,
    sha256=hashlib.sha256((evidence / 'replay-build.log').read_bytes()).hexdigest())
print('serial dependency build: execution exit 0', flush=True)
for kind, runner, output in [('candidate', 'CandidateReplay.lean', 'candidate-matrix.tsv'),
                             ('current', 'CurrentChecker.lean', 'current-checker.tsv')]:
    args = prefix + ['lake', 'env', 'lean', '-j1', '--tstack=131072', '--run',
                    'tests/sol-override-validation/' + runner]
    args += ['tests/sol-override-validation/' + row['file'] for row in rows]
    path = evidence / output
    with path.open('w') as out, (evidence / (kind + '-run.log')).open('w') as err:
        result = subprocess.run(args, stdout=out, stderr=err, timeout=180)
    if result.returncode:
        raise SystemExit(f'{kind} replay failed: exit {result.returncode}; see {kind}-run.log')
    manifest[kind] = dict(exitCode=result.returncode, command=args,
                         sha256=hashlib.sha256(path.read_bytes()).hexdigest())
    print(kind + ': execution exit 0', flush=True)
if gate.replay_inputs() != manifest['inputs']:
    raise SystemExit('replay input changed during execution')
summary = gate.validate_replays(rows, manifest)
(evidence / 'replay-manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
(evidence / 'replay-summary.json').write_text(json.dumps(summary, indent=2) + '\n')
print('PASS both complete replays and every documented original false-pass family', flush=True)
