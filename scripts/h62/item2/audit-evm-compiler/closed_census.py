#!/usr/bin/env python3
"""Audit pending zero-explicit-binder records, serially, against actual Lean types.
Caller holds writer lock. Bulk output is external. Direct closed equalities use
original checked proofs; no generated True lemmas or semantic success claims.
"""
import argparse,collections,hashlib,json,pathlib,re,subprocess,sys
p=argparse.ArgumentParser()
for k in ['census','config','bridge-config','bridge-packages','evidence']:p.add_argument('--'+k,required=True)
a=p.parse_args();root=pathlib.Path(__file__).resolve().parents[4];e=pathlib.Path(a.evidence).resolve();e.mkdir(parents=True,exist_ok=True)
x=json.loads(pathlib.Path(a.census).read_text());base=x['base'];subprocess.run(['git','merge-base','--is-ancestor',base,'HEAD'],cwd=root,check=True)
map_path='docs/module-map/evm-compiler.md'
frozen_map=subprocess.check_output(['git','show',base+':'+map_path],cwd=root)
if frozen_map!=(root/map_path).read_bytes():raise ValueError('frozen module map mismatch')
if x['modules']!=re.findall(r'^\| `([^`]+\.lean)`',frozen_map.decode(),re.M):raise ValueError('census mapped module list mismatch')
for m in x['modules']:
 f=m if m.startswith('Bridge/') else 'Solidity/'+m
 if subprocess.check_output(['git','show',base+':'+f],cwd=root)!=(root/f).read_bytes():raise ValueError('frozen source mismatch: '+f)
groups=collections.defaultdict(list)
for r in x['statements']:
 if r['simultaneous_witness']=='pending' and not r['kernel']['binders']:groups[r['kernel']['module']].append(r)
rows=[];links=[];summary=[]
for module,items in sorted(groups.items()):
 names=e/('names-'+module+'.txt');names.write_text('\n'.join(sorted(r['kernel']['name'] for r in items))+'\n')
 if module.startswith('SolidityBridge.'):
  lake=['lake','-d','Bridge','-f',a.bridge_config,'--packages='+a.bridge_packages,'--keep-toolchain']
 else:lake=['lake','-f',a.config]
 out=e/('closed-'+module)
 cmd=[sys.executable,str(root/'scripts/h62/item2/audit-evm-compiler/bounded.py'),'--seconds','300','--output',str(out),'--']+lake+['env','lean','-j1','--tstack=131072','--run',str(root/'scripts/h62/item2/audit-evm-compiler/Closed.lean'),str(names),module]
 result=subprocess.run(cmd,cwd=root,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 if result.returncode:
  summary.append(dict(module=module,status='failed',exit=result.returncode));print(module,'FAILED',result.returncode,flush=True);continue
 records=[json.loads(l) for l in pathlib.Path(str(out)+'.log').read_text().splitlines() if l.startswith('{')]
 by_name={r['kernel']['name']:r for r in items}
 if len(records)!=len(items) or len({r['name'] for r in records})!=len(items):raise ValueError('closed record count mismatch')
 accepted=0
 for record in records:
  original=by_name[record['name']]
  if record['module']!=module or record['type_expr']!=original['kernel']['type_expr'] or record['source_user_name']!=original['kernel']['source_user_name']:raise ValueError('actual kernel statement mismatch')
  if record['source_user_name'].replace('«','').replace('»','')!=original['candidate_name'].replace('«','').replace('»',''):raise ValueError('source/kernel original identity mismatch')
  record['statement_id']=original['statement_id'];rows.append(record)
  if record['status']!='closed-equality-checked':continue
  accepted+=1
  links.append(dict(original=original['candidate_name'],statement_id=original['statement_id'],source_signature_sha256=original['source_signature_sha256'],status='closed-no-input-binders',proof=record['name'],module=original['file'],classification='Direct equality, no leading inputs after definition-aware telescope expansion. Original compiled proof retained. Semantic success/refinement obligations are separate.'))
 summary.append(dict(module=module,status='checked',requested=len(items),accepted=accepted));print(module,accepted,'/',len(items),flush=True)
keys=[r['statement_id'] for r in rows]
if len(set(keys))!=len(keys):raise ValueError('duplicate closed statement')
(e/'closed-checks.jsonl').write_text(''.join(json.dumps(r,ensure_ascii=False,sort_keys=True)+'\n' for r in sorted(rows,key=lambda r:r['statement_id'])))
(e/'closed-coverage.json').write_text(json.dumps(dict(base=base,links=sorted(links,key=lambda r:r['statement_id'])),ensure_ascii=False,indent=2)+'\n')
failed=sum(r['status']=='failed' for r in summary)
report=dict(candidate_count=sum(len(v) for v in groups.values()),checked_count=len(rows),closed_equalities=len(links),remaining_non_equalities=len(rows)-len(links),failed_modules=failed,modules=summary,new_proof_declarations=0)
(e/'closed-summary.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k!='modules'}));raise SystemExit(int(failed!=0))
