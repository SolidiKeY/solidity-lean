#!/usr/bin/env python3
"""Pinned CI command and structured plan-citation inventory (not use edges).
Workflow shell blocks are retained verbatim; no shell execution or dependency
inference occurs. Plan rows match explicit ledger file/declaration identifiers.
"""
import argparse,hashlib,json,pathlib,re,runpy,subprocess,tomllib
HERE=pathlib.Path(__file__).resolve().parent
API=runpy.run_path(str(HERE/'audit.py'));BASE=API['BASE'];ROOT=API['ROOT']

def text(path):return subprocess.check_output(['git','show',BASE+':'+path],cwd=ROOT,text=True)

def action_step_indent(lines,index):
 """Find the containing step for both `- uses:` and named-step forms."""
 indent=len(lines[index])-len(lines[index].lstrip())
 for row in reversed(lines[:index+1]):
  width=len(row)-len(row.lstrip())
  if re.match(r'^\s*- ',row) and width<=indent:return width
  if row.strip() and width<indent:break
 raise AssertionError('Action has no containing step')

def action_settings(block):
 """Read only literal with-mapping children, excluding peer step metadata."""
 result={};within=None
 for row in block:
  if not row.strip():continue
  width=len(row)-len(row.lstrip())
  if within is not None and width<=within:within=None
  if re.match(r'^\s*with:\s*$',row):within=width;continue
  if within is not None and (m:=re.match(r'\s+([a-z-]+):\s*(.*)',row)):
   result[m.group(1)]=m.group(2).strip(' "' + chr(39))
 return result

def build():
 workflows=sorted(p for p in API['git']('ls-tree','-r','--name-only',BASE,'.github/workflows').splitlines() if p.endswith(('.yml','.yaml')))
 commands=[];actions=[]
 for path in workflows:
  lines=text(path).splitlines();job=None
  for i,line in enumerate(lines):
   m=re.match(r'^  ([A-Za-z_][A-Za-z_0-9-]*):\s*$',line)
   if m:job=m.group(1)
   m=re.match(r'^(\s*)(?:- )?run:\s*(.*)$',line)
   if m:
    value=m.group(2);indent=len(m.group(1))
    if value in ('|','|-','>','>-'):
     block=[]
     for row in lines[i+1:]:
      if row.strip() and len(row)-len(row.lstrip())<=indent:break
      block.append(row)
     nonempty=[len(x)-len(x.lstrip()) for x in block if x.strip()];cut=min(nonempty) if nonempty else 0
     value='\n'.join(x[cut:] for x in block)
    commands.append(dict(workflow=path,job=job,line=i+1,command=value))
   if re.search(r'uses:\s*leanprover/lean-action@',line):
    block=[];indent=action_step_indent(lines,i)
    for row in lines[i+1:]:
     if row.strip() and len(row)-len(row.lstrip())<=indent:break
     block.append(row)
    settings=action_settings(block)
    actions.append(dict(workflow=path,job=job,line=i+1,action=line.split('uses:',1)[1].strip(),settings=settings))
 config=tomllib.loads(text('lakefile.toml'));aliases={v['name']:v.get('root',v['name']) for kind in ('lean_lib','lean_exe') for v in config.get(kind,[])}
 literal=[]
 for row in commands:
  for offset,line in enumerate(row['command'].splitlines()):
   m=re.search(r'\blake build ([A-Za-z0-9_. -]+)',line)
   if not m:continue
   for target in m.group(1).split():
    if target in aliases:literal.append(dict(workflow=row['workflow'],command_line=row['line'],target=target,module=aliases[target]))
 ledger_path='docs/feature-work/roadmap-g03-ledger.json';ledger=json.loads(text(ledger_path));claims=[]
 candidates=[]
 for family in API['FAMILIES']:candidates.extend(json.loads((HERE/(family.strip('/').replace('/','_')+'-candidates.json')).read_text()))
 bysymbol={(r['path'],name):r for r in candidates for name in r['native_symbols']}
 for section in ('features','combinations','decisions'):
  for index,entry in enumerate(ledger.get(section,[])):
   for ci,cover in enumerate(entry.get('cover',[])):
    key=(cover.get('file'),cover.get('decl'))
    if key not in bysymbol:continue
    c=bysymbol[key]
    claims.append(dict(path=key[0],declaration=key[1],candidate_start_char=c['source_start_char'],candidate_status=c['status'],ledger=ledger_path,pointer=f'/{section}/{index}/cover/{ci}',item_id=entry.get('id',entry.get('key')),stage=cover.get('stage'),owners=entry.get('owners',{}),note=cover.get('note')))
 return dict(base=BASE,workflow_count=len(workflows),shell_command_blocks=commands,lean_actions=actions,literal_lake_targets=literal,structured_plan_candidate_claims=claims,
  boundaries=['Command blocks are syntax inventory, not an exact executed CI root set; delegated scripts, generated inputs and action defaults still require resolution.',
   'Plan citations are explicit ledger claims for candidate symbols, not proof of future work, actual use, or unused-but-planned classification.',
   'No lexical token match supplies a declaration dependency edge.'],unused_but_planned_verified_lines=0)

def main():
 p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args();data=build();body=json.dumps(data,indent=2,sort_keys=True)+'\n';assert len(body.encode())<1000000;path=HERE/'root-plan-catalog.json'
 if a.check:assert path.read_text()==body,'STALE catalog'
 else:path.write_text(body)
 print('ROOT_PLAN_CATALOG_PASS',data['workflow_count'],len(data['shell_command_blocks']),len(data['structured_plan_candidate_claims']))
if __name__=='__main__':main()
