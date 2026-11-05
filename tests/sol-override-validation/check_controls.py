"""Serial per-file diagnostics, real axiom collection, guarded pins and checks.
Run only under the writer lock after the existing Docker build has finished.
"""
import json
from pathlib import Path
import re
import subprocess
import time
ROOT=Path(__file__).resolve().parents[2]
TESTS=ROOT/'tests/sol-override-validation'
E=TESTS/'evidence'
prefix=['docker','exec','-e','LEAN_NUM_THREADS=1','sol-ov-session']
for attempt in range(50):
    processes=subprocess.check_output(prefix+['ps','-eo','stat=,comm='],text=True).splitlines()
    if not any(row.split()[-1] in ['lake','lean'] and not row.split()[0].startswith('Z') for row in processes):
        break
    time.sleep(0.2)
else:
    raise SystemExit('live Lean/Lake process exists; no concurrent Lean check started')
results=[]
def run(name,args):
    with (E/(name+'.log')).open('w') as out:
        result=subprocess.run(prefix+['timeout','--kill-after=10','180']+args,stdout=out,stderr=subprocess.STDOUT)
    results.append(dict(name=name,command=prefix+['timeout','--kill-after=10','180']+args,exitCode=result.returncode,status='pass' if result.returncode==0 else 'fail',evidence=str(E/(name+'.log'))))
    (E/'control-gates.json').write_text(json.dumps(results,indent=2)+'\n')
    print(name+': exit '+str(result.returncode),flush=True)
    if result.returncode: raise SystemExit(result.returncode)

for file,ns in [('DefensiveControls','DefensiveControls'),('GraphControls','Controls')]:
    p=TESTS/(file+'.lean');s=p.read_text()
    names=re.findall(r'^theorem (\S+)',s,re.M)
    targets=re.findall(r'^#print axioms (\S+)',s,re.M)
    for name in names:
        if not any(t==name or t.endswith('.'+name) for t in targets):
            s+='\n#print axioms Solidity.Frontend.OverrideValidation.'+ns+'.'+name+'\n'
    p.write_text(s)
    run('m4-diag-raw-'+file,['scripts/coord-tools/lean-mcp','diag','tests/sol-override-validation/'+file+'.lean'])
run('m4-stop-raw',['scripts/coord-tools/lean-mcp','stop'])
for file in ['DefensiveControls','GraphControls']:
    run('m4-axioms-'+file,['lake','env','lean','-j1','--tstack=131072','tests/sol-override-validation/'+file+'.lean'])
    p=TESTS/(file+'.lean');s=p.read_text();log=(E/('m4-axioms-'+file+'.log')).read_text()
    for message,name,axioms in re.findall(r"('([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms))",log):
        bad=set(re.split(r',\s*',axioms))-{'','propext','Classical.choice','Quot.sound'}
        if bad: raise SystemExit('nonstandard axiom: '+str((name,bad)))
        pattern=r'^#print axioms '+re.escape(name)+r'$'
        s,count=re.subn(pattern,lambda m:'/-- info: '+message+' -/\n#guard_msgs in\n'+m.group(),s,flags=re.M)
        if count!=1:raise SystemExit('axiom pin target count '+str((name,count)))
    p.write_text(s)
    run('m4-diag-'+file,['scripts/coord-tools/lean-mcp','diag','tests/sol-override-validation/'+file+'.lean'])
run('m4-stop-final',['scripts/coord-tools/lean-mcp','stop'])
for file in ['Trust','AdvancedControls','GraphControls','DefensiveControls']:
    run('m4-proof-'+file,['lake','env','lean','-j1','--tstack=131072','tests/sol-override-validation/'+file+'.lean'])
print('PASS all guarded library and control proofs; no nonstandard axiom',flush=True)
