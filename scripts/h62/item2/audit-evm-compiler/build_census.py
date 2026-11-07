#!/usr/bin/env python3
"""Build frozen mapped core imports serially; retain failures and blocked dependents.
Caller holds the writer lock. Source edits and external dependency installs are excluded.
Each build invocation retains the 300-second audit bound and explicit Lean -j1.
"""
import argparse, importlib.util, json, pathlib, re, subprocess, sys
p=argparse.ArgumentParser();p.add_argument('--source',required=True);p.add_argument('--config',required=True);p.add_argument('--evidence',required=True);p.add_argument('--library',required=True);a=p.parse_args()
root=pathlib.Path(__file__).resolve().parents[4];e=pathlib.Path(a.evidence);e.mkdir(parents=True,exist_ok=True);library=pathlib.Path(a.library)
spec=importlib.util.spec_from_file_location('census',root/'scripts/h62/item2/audit-evm-compiler/census.py');c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
source=json.loads(pathlib.Path(a.source).read_text());base=source['base']
subprocess.run(['git','merge-base','--is-ancestor',base,'HEAD'],check=True)
subprocess.run(['git','diff','--quiet',base,'--','Solidity','Bridge','docs/module-map'],check=True)
deps={};paths={};order=[];visiting=set()
def visit(module):
 if module in deps:return
 if module in visiting:raise ValueError('import cycle: '+module)
 relative=pathlib.Path(module.replace('.','/')+'.lean');path=root/relative
 if not path.exists():return
 visiting.add(module);paths[module]=str(relative);dependencies=[]
 for line in c.mask(path.read_text()).splitlines():
  m=re.match(r'^\s*(?:(?:public|meta)\s+)*import\s+(.+)$',line)
  if m:
   for name in m.group(1).split():
    if (root/(name.replace('.','/')+'.lean')).exists():dependencies.append(name);visit(name)
 visiting.remove(module);deps[module]=dependencies;order.append(module)
mapped=[];external=[]
for path in source['modules']:
 if path.startswith('Bridge/'):external.append(path);continue
 module=('Solidity/'+path).removesuffix('.lean').replace('/','.');mapped.append(module);visit(module)
(e/'build-plan.json').write_text(json.dumps(dict(base=base,mapped=mapped,external_pending=external,order=order,dependencies=deps),indent=2)+'\n')
statuses={};rows=[]
for module in order:
 blocked=[d for d in deps[module] if statuses.get(d) in ['failed','dependency-blocked']]
 if blocked:row=dict(module=module,status='dependency-blocked',dependencies=blocked)
 elif (library/(module.replace('.','/')+'.olean')).exists():row=dict(module=module,status='existing-artifact',source=paths[module])
 else:
  output=e/('build-'+module);command=[sys.executable,str(root/'scripts/h62/item2/audit-evm-compiler/bounded.py'),'--seconds','300','--output',str(output),'--','lake','-f',a.config,'--no-cache','build','+'+module+':olean']
  run=subprocess.run(command,capture_output=True,text=True);row=dict(module=module,status='built' if run.returncode==0 else 'failed',exit=run.returncode,evidence=str(output),source=paths[module]);print(module,row['status'],flush=True)
 statuses[module]=row['status'];rows.append(row)
 (e/'build-status.json').write_text(json.dumps(dict(rows=rows,mapped={m:statuses.get(m,'pending') for m in mapped},external_pending=external),indent=2)+'\n')
print(json.dumps(dict(planned=len(order),mapped=len(mapped),built=sum(r['status']=='built' for r in rows),failed=sum(r['status']=='failed' for r in rows),blocked=sum(r['status']=='dependency-blocked' for r in rows),existing=sum(r['status']=='existing-artifact' for r in rows))),flush=True)
raise SystemExit(int(any(r['status']=='failed' for r in rows)))
