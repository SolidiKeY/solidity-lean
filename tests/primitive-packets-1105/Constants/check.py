#!/usr/bin/env python3
"""Exact Constants scope, source, diagnostics, kernel and control acceptance."""
import copy,hashlib,json,pathlib,re,subprocess
ROOT=pathlib.Path(__file__).resolve().parents[3]
F=pathlib.Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
M=json.loads((F/'manifest.json').read_text())
def validate_inventory(rows):
 assert len(rows)==46 and len({r['name'] for r in rows})==46,'kernel cardinality'
 names={r['name']:r for r in rows}
 for d in M['declarations']: assert d['name'] in names and names[d['name']]['module']==d['module'],'authored declaration absent'
 for family in M['coverage'].values():
  if isinstance(family,list):
   for name in family: assert 'Solidity.Backend.PrimitivePackets.Constants.'+name in names,'control absent'
 for r in rows:
  assert r['signature'] and r['kind'] not in ('axiom','opaque'),'invalid kernel declaration'
  assert not r['isUnsafe'] and not r['isPartial'],'unsafe or partial'
  assert set(r['axioms']) <= {'propext','Classical.choice','Quot.sound'},'unapproved axiom'
def scope_candidates(diff,untracked): return set(diff)|set(untracked)
def validate_scope(paths):
 for p in paths:
  owned=p.startswith(('Solidity/Backend/PrimitivePackets/Constants/','tests/primitive-packets-1105/Constants/')) or p=='docs/feature-work/primitive-packets-1105-Constants.md'
  if not owned:
   assert p in M['preserved_untracked'] and sha(ROOT/p)==M['preserved_untracked'][p],'foreign write '+p
def validate_modules(paths):
 assert set(paths)==set(M['modules']),'unlisted/missing module'
def validate_authored():
 rows=[]
 for p in sorted(M['modules']):
  prefix='Solidity.Backend.PrimitivePackets.Constants.'+('Controls.' if p.endswith('/Controls.lean') else '')
  rows += [dict(name=prefix+n,kind=k,module=p[:-5].replace('/','.')) for k,n in re.findall(r'^(theorem|def|abbrev) (\w+)',(ROOT/p).read_text(),re.M)]
 assert rows==M['declarations'],'authored declaration enumeration drift'
def validate_published_modules(actual,integrated):
 assert set(actual)==set(integrated),'published module inventory differs'
def checkpoint_patch_id(commit):
 diff=subprocess.check_output(['git','show','--pretty=format:','--binary',commit],cwd=ROOT)
 words=subprocess.check_output(['git','patch-id','--stable'],input=diff,cwd=ROOT).decode().split()
 assert words,'empty checkpoint patch'
 return words[0]
def validate_checkpoint_equivalence(before,published,expected):
 assert checkpoint_patch_id(before)==expected==checkpoint_patch_id(published),'checkpoint patch differs'
def main():
 rebase=M['rebase']
 assert M['owned_start']==rebase['rebased_owned_start'] and M['published_delivery']['master']==rebase['target'],'rebase identity drift'
 for before,after in [(rebase['target'],M['owned_start']),(M['owned_start'],'HEAD'),(rebase['post_rebase_head'],'HEAD')]:
  subprocess.run(['git','merge-base','--is-ancestor',before,after],cwd=ROOT,check=True)
 if rebase.get('mode')=='integrated_checkpoint':
  assert M['owned_start']==rebase['target'] and not M['published_delivery']['remaining'],'invalid integrated baseline'
  assert set(M['published_delivery']['integrated'])==set(M['modules']),'integrated baseline omits modules'
  if 'published_equivalent_commit' in rebase:
   subprocess.run(['git','merge-base','--is-ancestor',rebase['published_equivalent_commit'],rebase['target']],cwd=ROOT,check=True)
   validate_checkpoint_equivalence(rebase['pre_rebase_head'],rebase['published_equivalent_commit'],rebase['patch_id'])
   try:validate_checkpoint_equivalence(rebase['pre_rebase_head'],rebase['target'],rebase['patch_id'])
   except AssertionError:pass
   else:raise AssertionError('different published commit accepted')
  else:subprocess.run(['git','merge-base','--is-ancestor',rebase['pre_rebase_head'],rebase['target']],cwd=ROOT,check=True)
  for p,h in M['modules'].items():assert hashlib.sha256(subprocess.check_output(['git','show',rebase['target']+':'+p],cwd=ROOT)).hexdigest()==h,'integrated baseline source drift'
 else:
  subprocess.run(['git','diff','--quiet',rebase['target'],M['owned_start'],'--','Solidity/Backend/PrimitivePackets/Constants'],cwd=ROOT,check=True)
  assert subprocess.check_output(['git','log','-1','--format=%s',M['owned_start']],cwd=ROOT,text=True).strip()=='Validate b86ae456 integration adoption','wrong protected baseline'
 subprocess.run(['git','merge-base','--is-ancestor',M['published_base'],'HEAD'],cwd=ROOT,check=True)
 validate_modules(str(p.relative_to(ROOT)) for p in (ROOT/'Solidity/Backend/PrimitivePackets/Constants').rglob('*.lean'))
 validate_authored()
 delivery=M['published_delivery']
 published_files=subprocess.check_output(['git','ls-tree','-r','--name-only',delivery['master'],'--','Solidity/Backend/PrimitivePackets/Constants/'],cwd=ROOT,text=True).splitlines()
 published_modules=[p for p in published_files if p.endswith('.lean')]
 validate_published_modules(published_modules,delivery['integrated'])
 try:validate_published_modules(published_modules,set(delivery['integrated'])|{'Solidity/Backend/PrimitivePackets/Constants/Unpublished.lean'})
 except AssertionError:pass
 else:raise AssertionError('forged published module accepted')
 subprocess.run(['git','merge-base','--is-ancestor',M['published_base'],delivery['master']],cwd=ROOT,check=True)
 subprocess.run(['git','merge-base','--is-ancestor',delivery['master'],'origin/master'],cwd=ROOT,check=True)
 assert set(delivery['integrated'])|set(delivery['remaining'])==set(M['modules']) and not set(delivery['integrated'])&set(delivery['remaining'])
 published_root=subprocess.check_output(['git','show',delivery['master']+':Solidity.lean'],cwd=ROOT,text=True)
 for p,h in delivery['integrated'].items():
  assert h==M['modules'][p] and hashlib.sha256(subprocess.check_output(['git','show',delivery['master']+':'+p],cwd=ROOT)).hexdigest()==h,'integrated source differs'
  assert 'import '+p[:-5].replace('/','.')+'\n' in published_root,'published registration absent'
 for p,h in M['inputs'].items():assert hashlib.sha256(subprocess.check_output(['git','show',delivery['master']+':'+p],cwd=ROOT)).hexdigest()==h,'published read-only API drift'
 for group in ('modules','inputs'):
  for p,h in M[group].items():assert sha(ROOT/p)==h,'source pin '+p
 assert sha(F/'kernel-inventory.json')==M['kernel_inventory_sha256']
 expected=json.loads((F/'kernel-inventory.json').read_text());actual=json.loads((F/'evidence/kernel-inventory.actual.json').read_text())
 assert sorted(actual,key=lambda x:x['name'])==expected,'fresh kernel inventory drift'
 validate_inventory(actual)
 # Both the frozen signatures and the generated namespace-outside sword.eq_1
 # belong to their actual defining modules, rather than a name-prefix filter.
 for label in ['source-diagnostics','selected-diagnostics','target-diagnostics','agreement-diagnostics','controls-final-diagnostics','axioms-diagnostics','rebase-axioms','integrated-axioms','latest-integration-axioms']:
  printed={}
  row=json.loads((F/'evidence'/ (label+'.json')).read_text());diag=json.loads((F/'evidence'/ (label+'.log')).read_text())
  assert row['exit']==0 and not row['resource_stop']
  assert diag['success'] and not diag['partial'] and not diag['timed_out'] and not diag['failed_dependencies']
  assert not [x for x in diag['items'] if x['severity'] in ('error','warning')],label
  for item in diag['items']:
   match=re.fullmatch(r"'([^']+)' depends on axioms: \[(.*?)\]",item['message'],re.S)
   if match: printed[match[1]]=set(x.strip() for x in match[2].split(',') if x.strip())
   match=re.fullmatch(r"'([^']+)' does not depend on any axioms",item['message'])
   if match: printed[match[1]]=set()
  if label in ('axioms-diagnostics','rebase-axioms','integrated-axioms','latest-integration-axioms'):assert printed=={r['name']:set(r['axioms']) for r in actual},'actual axiom prints differ'
 for label,module in [('source-build-corrected','Source'),('selected-build','Selected'),('target-build','Target'),('agreement-build','Agreement'),('controls-build','Controls')]:
  row=json.loads((F/'evidence'/ (label+'.json')).read_text());p='Solidity/Backend/PrimitivePackets/Constants/'+module+'.lean'
  assert row['exit']==0 and not row['resource_stop'] and row['proof_sources'][p]==M['modules'][p]
  assert row['limits']==dict(memory_max=12884901888,memory_swap_max=0,lean_num_threads=1)
  assert row['minimum_parent_headroom_bytes']>=4*1024**3
 final=json.loads((F/'evidence/controls-build.json').read_text());assert final['proof_sources']==M['modules']
 # Distinct mutation controls verify that inventory omissions and forged trust
 # are rejected. They do not replace the Lean refusal/control proofs.
 for kind in ['missing','axiom','unsafe']:
  bad=copy.deepcopy(actual)
  if kind=='missing':bad.pop()
  elif kind=='axiom':bad[0]['axioms'].append('sorryAx')
  else:bad[0]['isUnsafe']=True
  try:validate_inventory(bad)
  except AssertionError:pass
  else:raise AssertionError('mutation accepted '+kind)
 changed=subprocess.check_output(['git','diff','--name-only',M['owned_start'],'--'],cwd=ROOT,text=True).splitlines()
 untracked=subprocess.check_output(['git','ls-files','--others','--exclude-standard'],cwd=ROOT,text=True).splitlines()
 validate_scope(scope_candidates(changed,untracked))
 for candidate in [scope_candidates([],['Solidity/UntrackedForeign.lean']),scope_candidates(['Solidity/TrackedForeign.lean'],[])]:
  try:validate_scope(candidate)
  except AssertionError:pass
  else:raise AssertionError('foreign scope mutation accepted')
 try:validate_modules(set(M['modules'])|{'Solidity/Backend/PrimitivePackets/Constants/Unlisted.lean'})
 except AssertionError:pass
 else:raise AssertionError('unlisted module mutation accepted')
 for p in M['modules']:
  text=(ROOT/p).read_text();assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|maxHeartbeats)\b',text),'forbidden proof token'
 print('PASS: five modules, 34 authored and46 kernel declarations, all actual axiom prints/signatures, every positive/negative family, 13 pinned read-only inputs, resource bounds and eight mutation controls')
if __name__=='__main__':main()
