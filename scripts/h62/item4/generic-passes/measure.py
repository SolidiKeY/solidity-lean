#!/usr/bin/env python3
"""Paired same-source-condition measurement, after complete v4.35 acceptance.
Generates bulk variants outside git. Both variants import the same generic
module and keep every original signature, declaration and owner producer.
Only execution's physical proof suffix differs. Alternates order over 5 rounds,
includes first checks as warmups, stops if the median pair slowdown exceeds 10%.
This measures the isolated three pass modules, not repository full-build time.
"""
import argparse, hashlib, json, statistics, subprocess, sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]; HERE=Path(__file__).parent
from runtime_paths import EVIDENCE as E, load_pin
p=argparse.ArgumentParser(); p.add_argument('--run-id',required=True); p.add_argument('--acceptance',type=Path,required=True); a=p.parse_args()
if not __import__('re').fullmatch('[a-zA-Z0-9-]+',a.run_id): raise SystemExit('simple unique run ID required')
# Fail closed: a failed prerequisite cannot be converted into a timing result.
if not a.acceptance.is_file(): raise SystemExit('PENDING: successful acceptance manifest required')
manifest=json.loads(a.acceptance.read_text())
pin=load_pin()
if manifest.get('status')!='pass' or manifest.get('toolchain')!=pin:
    raise SystemExit('PENDING: full additive acceptance on exact pin required')
for name,want in manifest['source_sha256'].items():
    if hashlib.sha256((ROOT/name).read_bytes()).hexdigest()!=want:
        raise SystemExit('PENDING: source changed since acceptance: '+name)
for name,want in manifest['artifact_sha256'].items():
    if not Path(name).is_file() or hashlib.sha256(Path(name).read_bytes()).hexdigest()!=want:
        raise SystemExit('PENDING: artifact changed since acceptance: '+name)
required=['Generic','Instances','Fixtures','Correspondence']
for name in required:
    path=E/'build-v4.35.0/tests/h62/item4/generic-passes'/(name+'.olean')
    if not path.exists(): raise SystemExit('PENDING: validated additive prerequisite missing: '+str(path))
work=E/('measure-'+a.run_id)
if work.exists(): raise SystemExit('preserve previous evidence; choose fresh ID')
work.mkdir()
instances=(ROOT/'tests/h62/item4/generic-passes/Instances.lean').read_text()
records=[]
for name in ['Addition','Subtraction','Multiplication']:
    original=(ROOT/('Solidity/Backend/Passes/Assignment'+name+'Pass.lean')).read_text()
    begin=original.index('theorem execution'); split=original.index(' := by',begin)+len(' := by')
    end=original.index('\nend ',split)
    instance_start=instances.index('theorem execution_'+name.lower())
    body_start=instances.index(' := by',instance_start)+len(' := by')
    body_end=instances.index('\ntheorem exact_',body_start)
    body=instances[body_start:body_end].rstrip()+'\n'
    prefix='import tests.h62.item4.«generic-passes».Generic\n'
    variants=dict(before=prefix+original,after=prefix+original[:split]+body+original[end:])
    for mode,source in variants.items():
        (work/(name+mode+'.lean')).write_text(source)
    timing=dict(before=[],after=[])
    for round in range(6):
        order=['before','after'] if round%2==0 else ['after','before']
        for mode in order:
            label=a.run_id+'-'+name+'-'+mode+'-'+str(round)
            cmd=[sys.executable,str(HERE/'bounded.py'),label,'--','-j1','--tstack=131072',
                '--root='+str(work),str(work/(name+mode+'.lean'))]
            subprocess.run(cmd,cwd=ROOT,check=True)
            result=json.loads((E/(label+'.json')).read_text())
            if round: timing[mode].append(result['elapsed_seconds'])
    before=statistics.median(timing['before']); after=statistics.median(timing['after'])
    delta=100*(after/before-1)
    records.append(dict(module=name,samples=timing,before_median=before,after_median=after,delta_percent=delta,
        source_sha256={mode:hashlib.sha256(source.encode()).hexdigest() for mode,source in variants.items()}))
    (work/'results.json').write_text(json.dumps(records,indent=2)+'\n')
    if delta>10: raise SystemExit('STOP: slowdown exceeds 10%: '+name+' '+str(delta))
print('PASS bounded paired module timing; see '+str(work/'results.json'))
