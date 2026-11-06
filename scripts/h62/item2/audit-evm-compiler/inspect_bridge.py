#!/usr/bin/env python3
"""Capture optional mapped Bridge types serially and join unchanged core rows.
Caller holds the writer lock. Artifact existence only schedules inspection;
it is not reported as a source-freshness/build gate. Failed captures add no rows.
"""
import argparse, json, pathlib, subprocess, sys
p=argparse.ArgumentParser()
for key in ['source','config','packages','evidence','library','core-kernel','core-modules']:p.add_argument('--'+key,required=True)
a=p.parse_args();root=pathlib.Path(__file__).resolve().parents[4];e=pathlib.Path(a.evidence);e.mkdir(parents=True,exist_ok=True)
s=json.loads(pathlib.Path(a.source).read_text());rows=[json.loads(l) for l in pathlib.Path(a.core_kernel).read_text().splitlines() if l.startswith('{')]
assert not any(r['module'].startswith('SolidityBridge.') for r in rows), 'expected core-only seed'
summary=[r for r in json.loads(pathlib.Path(a.core_modules).read_text()) if not r['module'].startswith('SolidityBridge.')]
names=e/'bridge-source-names.txt';names.write_text('\n'.join(sorted({r['candidate_name'].replace('«','').replace('»','') for r in s['statements']}))+'\n')
for relative in s['modules']:
 if not relative.startswith('Bridge/'):continue
 module=relative.removeprefix('Bridge/').removesuffix('.lean').replace('/','.')
 if not (pathlib.Path(a.library)/(module.replace('.','/')+'.olean')).exists():
  summary.append(dict(module=module,status='pending-build'));print(module,'pending-build',flush=True);continue
 output=e/('kernel-'+module)
 command=[sys.executable,str(root/'scripts/h62/item2/audit-evm-compiler/bounded.py'),'--seconds','300','--output',str(output),'--','lake','-d','Bridge','-f',a.config,'--packages='+a.packages,'--keep-toolchain','env','lean','-j1','--tstack=131072','--run',str(root/'scripts/h62/item2/audit-evm-compiler/Inspect.lean'),str(names),module]
 result=subprocess.run(command,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 if result.returncode:
  summary.append(dict(module=module,status='failed',exit=result.returncode,evidence=str(output)));print(module,'FAILED',result.returncode,flush=True);continue
 captured=[json.loads(l) for l in pathlib.Path(str(output)+'.log').read_text().splitlines() if l.startswith('{')]
 expected=sum(r['file']==relative for r in s['statements'])
 if len(captured)!=expected:raise ValueError('Bridge source/kernel count mismatch: '+module)
 rows.extend(captured);summary.append(dict(module=module,status='types-extracted',count=len(captured),evidence=str(output)));print(module,len(captured),flush=True)
keys=[(r['module'],r['name']) for r in rows]
if len(set(keys))!=len(keys):raise ValueError('duplicate kernel declaration')
(e/'kernel.jsonl').write_text(''.join(json.dumps(r,ensure_ascii=False,sort_keys=True)+'\n' for r in sorted(rows,key=lambda r:(r['module'],r['name']))))
(e/'kernel-modules.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(dict(modules_inspected=sum(r['status']=='types-extracted' for r in summary),pending=sum(r['status']=='pending-build' for r in summary),failed=sum(r['status']=='failed' for r in summary),types=len(rows))))
raise SystemExit(int(any(r['status']=='failed' for r in summary)))
