#!/usr/bin/env python3
"""Check only isolated API cases with private standard implementation visibility.

The experimental.module option is enabled equally for both releases, solely
for this fixture's import-all. It does not change the assigned-build benchmark.
"""
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import resource
import re
import signal
import subprocess
import time

p=argparse.ArgumentParser()
p.add_argument('--toolchain',type=Path,required=True)
p.add_argument('--imports',type=Path,required=True)
p.add_argument('--out',type=Path,required=True)
a=p.parse_args()
root=Path(__file__).resolve().parents[4]
source=root/'tests/h62/item6/migrate-solkey/StringApiControls.lean'
if a.out.exists(): raise SystemExit('Refusing reused diagnostic output')
a.out.mkdir(parents=True)
lock=open('/tmp/solidity-lean-feature-groups-20261025/writer.lock','a')
fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
if len(Path('/proc/swaps').read_text().splitlines()) != 1: raise SystemExit('Swap configured')
def enough():
    current=int(Path('/sys/fs/cgroup/memory.current').read_text())
    maximum=int(Path('/sys/fs/cgroup/memory.max').read_text())
    available=int(next(s.split()[1] for s in Path('/proc/meminfo').read_text().splitlines() if s.startswith('MemAvailable:')))*1024
    return min(maximum-current,available) >= 4*1024**3
if not enough(): raise SystemExit('RESOURCE_RESERVE_STOP')
dest=a.out.resolve()/'lib/tests/h62/item6/migrate-solkey/StringApiControls.olean'
dest.parent.mkdir(parents=True)
cmd=[str(a.toolchain.resolve()/'bin/lean'),'-j1','--tstack=131072','-Dexperimental.module=true','--root='+str(root),'-o',str(dest),str(source)]
env=dict(os.environ,LEAN_NUM_THREADS='1',LEAN_PATH=str(a.out.resolve()/'lib')+os.pathsep+str(a.imports.resolve()))
def run(command,logname):
    if not enough(): return 1,'RESOURCE_RESERVE_STOP',0
    start=time.monotonic(); stop=None
    with (a.out/logname).open('w') as log:
        child=subprocess.Popen(command,cwd=root,env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
        while child.poll() is None:
            if not enough(): stop='RESOURCE_RESERVE_STOP'
            if time.monotonic()-start > 1800: stop='TIMEOUT_STOP'
            if stop:
                os.killpg(child.pid,signal.SIGTERM)
                try:child.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    os.killpg(child.pid,signal.SIGKILL);child.wait(timeout=5)
                break
            time.sleep(.25)
    return child.returncode,stop,time.monotonic()-start

start=time.monotonic()
code,stop,_=run(cmd,'output.log')
audit_cmd=[*cmd[:5],str(root/'tests/h62/item6/migrate-solkey/StringApiAxioms.lean')]
audit_code=None
if code == 0 and not stop:
    audit_code,stop,_=run(audit_cmd,'axioms.log')
axioms={}
if audit_code == 0 and not stop:
    text=(a.out/'axioms.log').read_text()
    for name in ['hashKeccakDrop','hashShaDrop','unicodeDrop','functionPrefixDrop','returnsPrefixAndSuffix','locationSuffixEta','absentLocationSuffix','locationSuffixCharacterBoundary']:
        full='H62.MigrateSolkey.StringApiControls.'+name
        if "'"+full+"' does not depend on any axioms" in text: axioms[name]=[]
        else:
            match=re.search(re.escape("'"+full+"' depends on axioms:")+r'\s*\[([^]]*)\]',text)
            if not match: raise SystemExit('Missing axiom audit: '+name)
            axioms[name]=sorted(s.strip() for s in match[1].split(',') if s.strip())
        if not set(axioms[name]) <= {'propext','Classical.choice','Quot.sound'}:
            raise SystemExit('Forbidden case axiom: '+name)
report={'mode':'isolated-api-cases','command':cmd,'versions':{exe:subprocess.check_output([str(a.toolchain.resolve()/'bin'/exe),'--version'],text=True).strip() for exe in ['lean','lake']},'exit':code,'axiom_command':audit_cmd,'axiom_exit':audit_code,'axioms':axioms,'stop':stop,'wall_seconds':time.monotonic()-start,'max_child_rss_kib':resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'proof_budget':'default maxHeartbeats=200000 unchanged; module visibility enabled only for fixture'}
(a.out/'gate.json').write_text(json.dumps(report,indent=2)+'\n')
print('API_CASES_PASS' if code == 0 and audit_code == 0 and not stop else 'API_CASES_FAIL')
raise SystemExit(0 if code == 0 and audit_code == 0 and not stop else 1)
