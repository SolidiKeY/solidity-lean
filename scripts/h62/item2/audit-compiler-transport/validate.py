#!/usr/bin/env python3
"""Run after the fresh closure build, under the writer lock. All Lean is serial.
This gate does not substitute for run-lean.sh and never emits RUNTIME_GATE_PASS.
"""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
from bounded import run

ROOT = Path.cwd()
E = Path('/workspace/h62-audit-compiler-transport/evidence')
LEAN = Path('/workspace/.setup/tools/lean-4.24.0-linux/bin/lean')
TESTS = Path('tests/h62/item2/audit-compiler-transport')
SCRIPTS = Path('scripts/h62/item2/audit-compiler-transport')
O = E/'olean'
os.environ['LEAN_PATH'] = str(O)
os.environ['LEAN_NUM_THREADS'] = '1'

def checked(command, name):
    result = run(command, E/(name+'.log'))
    (E/(name+'.json')).write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result), flush=True)
    if result['exit'] or result['stop_reason']:
        raise SystemExit(result['exit'] or 1)
    return result

build = [json.loads(l) for l in (E/'build-metrics.jsonl').read_text().splitlines()]
if not build or build[-1]['index'] != build[-1]['total'] or any(r['exit'] or r['stop_reason'] for r in build):
    print('BLOCKED: dependency closure did not pass; additive proofs remain unchecked', flush=True)
    raise SystemExit(2)

# All original imported artifacts and sources are fixed across the comparison.
cache_hash = hashlib.sha256()
for row in build:
    path = O/(row['module'].replace('.', '/')+'.olean')
    cache_hash.update(str(path.relative_to(O)).encode())
    cache_hash.update(hashlib.sha256(path.read_bytes()).digest())
context = {'base':'c6f550e281a7e5affa9a99bc2cdaed556dec00e4',
           'original_import_cache_sha256':cache_hash.hexdigest(),
           'lean_version':subprocess.check_output([str(LEAN),'--version'],text=True).strip(),
           'threads':1, 'Elab.async':False, 'address_space_limit_gib':12, 'reserve_gib':4,
           'vm_memory_max':Path('/sys/fs/cgroup/memory.max').read_text().strip(),
           'swap_total':next(l for l in Path('/proc/meminfo').read_text().splitlines() if l.startswith('SwapTotal:')),
           'original_file_sha256':hashlib.sha256((ROOT/'Solidity/Backend/Passes/CompilerWholeScope.lean').read_bytes()).hexdigest()}
# Bind samples to one permitted CPU, avoiding scheduler placement differences.
cpu = min(os.sched_getaffinity(0))
os.sched_setaffinity(0, {cpu})
context['cpu_affinity'] = [cpu]
timing_command = [str(LEAN),'-j1','-DElab.async=false','--tstack=131072','Solidity/Backend/Passes/CompilerWholeScope.lean']
# Warm the common imports before collecting either side.
if '--resume-before' in sys.argv:
    for i in range(3):
        previous = json.loads((E/f'before-{i}.json').read_text())
        assert previous['exit'] == 0 and not previous['stop_reason'] and previous['context'] == context
    print('Reusing verified unchanged-target before samples after additive syntax fix',flush=True)
else:
    checked(timing_command, 'timing-warmup')
    for i in range(3):
        result = checked(timing_command, f'before-{i}')
        result['context'] = context
        (E/f'before-{i}.json').write_text(json.dumps(result, indent=2)+'\n')
for name in ['JointHypotheses','Reflect','Audit','Witnesses']:
    source = TESTS/(name+'.lean')
    target = O/TESTS/(name+'.olean')
    target.parent.mkdir(parents=True, exist_ok=True)
    checked([str(LEAN),'-j1','-DElab.async=false','--tstack=131072','-o',str(target),str(source)], 'check-'+name)
checked([str(LEAN),'-j1','-DElab.async=false','--tstack=131072','--root='+str(E),str(E/'ReflectionDriver.lean')], 'reflection')
# Expanded reconciliation and H69 cases are checked by h69_validate.py.
cache_after = hashlib.sha256()
for row in build:
    path = O/(row['module'].replace('.', '/')+'.olean')
    cache_after.update(str(path.relative_to(O)).encode())
    cache_after.update(hashlib.sha256(path.read_bytes()).digest())
assert cache_after.hexdigest() == context['original_import_cache_sha256'], 'original imports changed during validation'
assert hashlib.sha256((ROOT/'Solidity/Backend/Passes/CompilerWholeScope.lean').read_bytes()).hexdigest() == context['original_file_sha256']
checked(timing_command, 'timing-after-warmup')
for i in range(3):
    result = checked(timing_command, f'after-{i}')
    result['context'] = context
    (E/f'after-{i}.json').write_text(json.dumps(result, indent=2)+'\n')
command = [sys.executable,str(SCRIPTS/'compare_timings.py'),'--before']
command += [str(E/f'before-{i}.json') for i in range(3)]
command += ['--after']+[str(E/f'after-{i}.json') for i in range(3)]
command += ['--output',str(E/'timing-comparison.json')]
subprocess.run(command,check=True)
print('PASS: additive diagnostics, statement fidelity and matched original-file timing; full run-lean.sh remains a separate gate',flush=True)
