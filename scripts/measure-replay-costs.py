#!/usr/bin/env python3
"""Measure uncached kernel certificates on prepared simple-program fixtures.

Run scripts/measure-simple.mjs first. An optional --plugin enables native
project code; these timings measure kernel phases, not whole IDE latency.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('lean_prefix', type=Path)
parser.add_argument('--inputs', type=Path, default=Path('.lake/simple-measurement'))
parser.add_argument('--output', type=Path, default=Path('.lake/replay-costs'))
parser.add_argument('--plugin', type=Path)
args = parser.parse_args()
root = Path(__file__).resolve().parent.parent
os.chdir(root)
prefix, output = args.lean_prefix.resolve(), args.output.resolve()
output.mkdir(parents=True, exist_ok=True)
inputs = json.loads((args.inputs / 'inputs.json').read_text())
native = (args.inputs / 'Native.lean').read_text()
hashes = {json.loads(m[1]): m[2] for m in re.finditer(
    r'solc_import ("[^"\n]+") hash (0x[0-9a-f]+) as', native)}
helper = root / 'tests/automation/ReplayCosts.lean'
source = helper.read_text() + '\n'
for i, trial in enumerate(inputs['trials']):
    fixture = str(Path(trial['fixture']).resolve())
    source_hash = hashlib.sha256(Path(trial['source']).read_bytes()).hexdigest()
    assert source_hash == trial['sourceHash'], 'stale source hash'
    assert json.loads(Path(fixture).read_text())['header']['sourceSha256'] == source_hash, 'stale fixture source'
    namespace = f'ReplayCost.C{i}.Simple'
    target = output / f'{trial["name"]}-{trial["repeat"]}.json'
    source += f'solc_import {json.dumps(fixture)} hash {hashes[fixture]} as {namespace} testing\n'
    source += f'#split_replay {namespace} to {json.dumps(str(target))}\n'
runner = output / 'Cases.lean'
runner.write_text(source)
env = dict(os.environ, LEAN_NUM_THREADS='1')
env['LEAN_PATH'] = os.pathsep.join(filter(None, [str(root / '.lake/build/lib/lean'), env.get('LEAN_PATH')]))
command = [str(prefix / 'bin/lean'), '-j1', '--tstack=131072']
if args.plugin:
    command += ['--plugin=' + str(args.plugin.resolve())]
command.append(str(runner))
with (output / 'result.log').open('w') as log:
    subprocess.run(command, env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
rows = []
for trial in inputs['trials']:
    result = json.loads((output / f'{trial["name"]}-{trial["repeat"]}.json').read_text())
    assert result and all(r['status'] == 'checked-diagnostic-components' for r in result)
    rows.append({'name': trial['name'], 'repeat': trial['repeat'], 'sourceHash': trial['sourceHash'], 'results': result})
report = {'scope': 'uncached kernel phase certificates; not complete program proofs',
    'helperSha256': hashlib.sha256(helper.read_bytes()).hexdigest(),
    'leanCommit': subprocess.check_output([str(prefix / 'bin/lean'), '--githash'], text=True).strip(),
    'pluginSha256': hashlib.sha256(args.plugin.read_bytes()).hexdigest() if args.plugin else None,
    'command': command, 'trials': rows}
(output / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
print(f'Checked {len(rows)} diagnostic cases: {output / "report.json"}')
