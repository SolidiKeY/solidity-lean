#!/usr/bin/env python3
"""Reproduce this partial H69 audit after build_serial.py; hold the writer lock.

Generates all bulk outputs outside Git and preserves default proof budgets.
Does not replace run-lean.sh, classify every semantic domain, or claim totality.
"""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
from bounded import run
from census import generate, declarations

ap=argparse.ArgumentParser()
ap.add_argument('--evidence',type=Path,default=Path('/workspace/h62-audit-compiler-transport/evidence'))
ap.add_argument('--lean',type=Path,default=Path('/workspace/.setup/tools/lean-4.24.0-linux/bin/lean'))
a=ap.parse_args();e=a.evidence.resolve();h=e/'h69';h.mkdir(exist_ok=True)
cache=e/'olean';tests=Path('tests/h62/item2/audit-compiler-transport')
scripts=Path(__file__).resolve().parent
os.environ['LEAN_NUM_THREADS']='1';os.environ['LEAN_PATH']=str(cache)
flags=[str(a.lean),'-j1','-DElab.async=false','--tstack=131072']
def check(command,label):
    r=run(command,h/(label+'.log'))
    (h/(label+'.json')).write_text(json.dumps(r,indent=2)+'\n')
    assert r['exit']==0 and not r['stop_reason'],r
    assert not any(t in Path(r['log']).read_text() for t in ['error:', 'PANIC', 'sorryAx'])
    print(label,'PASS',round(r['wall_seconds'],3),flush=True)
def python(script,*args):
    subprocess.run([sys.executable,str(scripts/script),*map(str,args)],check=True)
# Original sources are checked against BASE before using the task-owned cache.
census=generate(Path.cwd());(e/'census.json').write_text(json.dumps(census,indent=2)+'\n')
check(flags+['Solidity/KeySort.lean'],'keysort')
for name in ['JointHypotheses','Reflect','Audit','Witnesses','H69','NilFixture','OptimizerFixture','ExplicitCases','AutoWitness','CarrierInventory']:
    target=cache/tests/(name+'.olean');target.parent.mkdir(parents=True,exist_ok=True)
    check(flags+['-o',str(target),str(tests/(name+'.lean'))],'check-'+name)
proof_names = [r['source_name'] for p in sorted(tests.glob('*.lean')) for r in declarations(p.read_text(),str(p))]
proof_driver = h/'ProofAuditDriver.lean'
proof_driver.write_text('\n'.join('import tests.h62.item2.«audit-compiler-transport».'+p.stem for p in sorted(tests.glob('*.lean')))+'\n'+'\n'.join('#print axioms '+n for n in proof_names)+'\n')
check(flags+['--root='+str(h),str(proof_driver)],'proof-audit')
(h/'own-theorems.json').write_text(json.dumps(proof_names,indent=2)+'\n')
python('generate_reflection.py','--driver',h/'ReflectionDriver.lean','--output',h/'elaborated')
check(flags+['--root='+str(h),str(h/'ReflectionDriver.lean')],'reflection')
modules=[r['module'][:-5].replace('/','.') for r in census['modules']]
carriers=h/'carriers';carriers.mkdir(exist_ok=True)
imports='\n'.join('import '+m for m in modules)
commands=['set_option pp.all true in\n#audit_carriers '+json.dumps(str(carriers/(m+'.json')))+' module '+json.dumps(m) for m in modules]
driver=h/'CarrierDriver.lean'
driver.write_text(imports+'\nimport tests.h62.item2.«audit-compiler-transport».CarrierInventory\n'+'\n'.join(commands)+'\n')
check(flags+['--root='+str(h),str(driver)],'carriers')
python('generate_witnesses.py','--reflected',h/'elaborated','--output',h/'generated')
python('run_witness_batches.py','--lean',a.lean,'--generated',h/'generated')
python('reconcile.py','--census',e/'census.json','--reflected',h/'elaborated','--output',h/'coverage.json','--witness-metrics',h/'check-Witnesses.json','--h69',h)
print('PASS partial H69 reproduction; full semantic coverage and final gates remain pending')
