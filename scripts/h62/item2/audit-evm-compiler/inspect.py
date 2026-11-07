#!/usr/bin/env python3
"""Inspect each already-built mapped module in a fresh bounded Lean process.
Caller holds the repository writer lock. Missing builds remain pending.
"""
import argparse,json,pathlib,subprocess,sys
p=argparse.ArgumentParser();p.add_argument('--source',required=True);p.add_argument('--config',required=True);p.add_argument('--evidence',required=True);p.add_argument('--library',required=True);a=p.parse_args()
root=pathlib.Path(__file__).resolve().parents[4]; evidence=pathlib.Path(a.evidence); source=json.loads(pathlib.Path(a.source).read_text())
names=evidence/'source-names.txt';names.write_text('\n'.join(sorted({r['candidate_name'].replace('«','').replace('»','') for r in source['statements']}))+'\n')
rows=[];summary=[]
for relative in source['modules']:
    file=relative if relative.startswith('Bridge/') else 'Solidity/'+relative
    module=file.removeprefix('Bridge/').removesuffix('.lean').replace('/','.')
    if not (pathlib.Path(a.library)/(module.replace('.','/')+'.olean')).exists():
        summary.append(dict(module=module,status='pending-build'));continue
    output=evidence/('kernel-'+module)
    command=[sys.executable,str(root/'scripts/h62/item2/audit-evm-compiler/bounded.py'),'--output',str(output),'--','lake','-f',a.config,'env','lean','-j1','--tstack=131072','--run',str(root/'scripts/h62/item2/audit-evm-compiler/Inspect.lean'),str(names),module]
    result=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    if result.returncode:
        summary.append(dict(module=module,status='failed',exit=result.returncode,evidence=str(output)));print(module,'FAILED',flush=True);continue
    module_rows=[json.loads(line) for line in pathlib.Path(str(output)+'.log').read_text().splitlines()]
    rows.extend(module_rows);summary.append(dict(module=module,status='types-extracted',count=len(module_rows),evidence=str(output)));print(module,len(module_rows),flush=True)
keys=[(r['module'],r['name']) for r in rows]
if len(set(keys))!=len(keys):raise ValueError('duplicate kernel declaration')
(evidence/'kernel.jsonl').write_text(''.join(json.dumps(r,ensure_ascii=False,sort_keys=True)+'\n' for r in sorted(rows,key=lambda r:(r['module'],r['name']))))
(evidence/'kernel-modules.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(dict(modules_inspected=sum(s['status']=='types-extracted' for s in summary),pending=sum(s['status']=='pending-build' for s in summary),failed=sum(s['status']=='failed' for s in summary),types=len(rows))))
raise SystemExit(int(any(s['status']=='failed' for s in summary)))
