#!/usr/bin/env python3
"""Serial, bounded checks inside the verified Docker cgroup; sample aggregate RSS."""
import json, os, pathlib, signal, subprocess, time, sys, re
root=pathlib.Path.cwd(); kind=sys.argv[1] if len(sys.argv)>1 else 'import'; assert kind in ('import','data','resolution'); stamp=os.environ.get('VT1_EVIDENCE_STAMP',''); assert re.fullmatch('[A-Za-z0-9_-]*',stamp); evidence=root/'tests/fullscope-20261104/vt1/evidence'/(kind+('-'+stamp if stamp else '')); evidence.mkdir(parents=True,exist_ok=True)
assert pathlib.Path('/sys/fs/cgroup/memory.max').read_text().strip()=='12884901888'
assert pathlib.Path('/sys/fs/cgroup/memory.swap.max').read_text().strip()=='0'
def available():
    return next(int(line.split()[1])*1024 for line in pathlib.Path('/proc/meminfo').read_text().splitlines() if line.startswith('MemAvailable:'))
def rss():
    total=0
    for path in pathlib.Path('/proc').glob('[0-9]*/status'):
        try:
            total+=next((int(line.split()[1])*1024 for line in path.read_text().splitlines() if line.startswith('VmRSS:')),0)
        except (FileNotFoundError,ProcessLookupError,PermissionError): pass
    return total
assert available()>=4*1024**3
out=root/'.lake/build/lib/lean/Solidity/Frontend/SolcJson'; out.mkdir(parents=True,exist_ok=True)
node='/opt/codex/runtimes/codex-primary-runtime/dependencies/node/bin/node'
base=['lake','env','lean','-j1','--tstack=131072']
plan=[['lean','--version'],['lake','--version'],
 base+['-o',str(out/'IrImport.olean'),'Solidity/Frontend/SolcJson/IrImport.lean'],
 base+['tests/fullscope-20261104/vt1/IrImportChecks.lean'],
 [node,'tests/fullscope-20261104/vt1/generate-fixtures.mjs'],
 [node,'tests/fullscope-20261104/vt1/verify-fixtures.mjs'],
 [node,'tests/fullscope-20261104/vt1/verify-fixtures.test.mjs']]
if kind in ('data','resolution'):
    dataOut=root/'.lake/build/lib/lean/Solidity/SolcValidation'; dataOut.mkdir(parents=True,exist_ok=True)
    plan=[['lean','--version'],['lake','--version'],
      [node,'tests/fullscope-20261104/vt1/generate-object-data.mjs','--check'],
      base+['-o',str(dataOut/'DataLayout.olean'),'Solidity/SolcValidation/DataLayout.lean'],
      base+['-o',str(dataOut/'DataResolution.olean'),'Solidity/SolcValidation/DataResolution.lean'],
      base+['tests/fullscope-20261104/vt1/ObjectDataChecks.lean'],
      [node,'tests/fullscope-20261104/vt1/object-data.test.mjs']]
results=[]
for i,cmd in enumerate(plan):
    assert available()>=4*1024**3
    start=time.monotonic(); peak=rss(); reason=None
    log=evidence/f'measured-{i}.log'
    with log.open('w') as stream:
        proc=subprocess.Popen(cmd,stdout=stream,stderr=subprocess.STDOUT,start_new_session=True)
        while proc.poll() is None:
            peak=max(peak,rss())
            if time.monotonic()-start>180 or available()<4*1024**3:
                reason='180s timeout or 4GiB reserve stop'; os.killpg(proc.pid,signal.SIGTERM); proc.wait(); break
            time.sleep(.02)
    result=dict(command=cmd,exit=proc.returncode,wall_seconds=time.monotonic()-start,aggregate_peak_rss_bytes=peak,stop_reason=reason,log=str(log))
    results.append(result); print(json.dumps(result),flush=True)
    (evidence/'measured.json').write_text(json.dumps(results,indent=2)+'\n')
    if proc.returncode!=0: raise SystemExit(proc.returncode)
print('CGROUP_PEAK_BYTES',pathlib.Path('/sys/fs/cgroup/memory.peak').read_text().strip())
