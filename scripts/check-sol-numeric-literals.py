#!/usr/bin/env python3
"""Scope-complete SOL-NL acceptance. Default mode also requires all final gates.
--implementation validates all scoped code/proofs/fixtures and reports remaining
integration gates without claiming assignment completion. Never updates a pin.
"""
import argparse,copy,importlib.util,json,os,pathlib,re,subprocess,sys,tempfile
ROOT=pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tests/sol-numeric-literals'))
from packetlib import BASE,ADOPTED_MASTER,FOLDER,PREFIX,CONSTRUCTOR_CONTROLS,REQUIRED_THEOREMS,blank_lean,case_families,controls,git,normalized_inventory,permitted,sha,source_snapshot

def require(condition,message):
 if not condition:raise ValueError(message)

def validate_inventory(actual,pinned,modules):
 names=[r['name'] for r in actual];require(len(names)==len(set(names)),'duplicate kernel declaration')
 require(normalized_inventory(actual)==pinned,'actual declarations/signatures/axiom sets differ from pin')
 byname={r['name']:r for r in actual};modnames={m['name'] for m in modules}
 for r in actual:
  require(r['module'] in modnames,'unregistered declaration owner '+r['name'])
  require(r['kind']!='axiom','new axiom '+r['name'])
  require(not r['isUnsafe'],'new unsafe declaration '+r['name'])
  require(set(r['axioms'])<= {'propext','Quot.sound','Classical.choice'},'nonstandard axiom '+r['name'])
  require('⋯' not in r['signature'],'incomplete signature '+r['name'])
 require({r['name'] for r in actual if r['isPartial']}=={PREFIX+'underscoreOk._unsafe_rec'},'generated partial helper inventory drift')
 require({r['name'] for r in actual if r['kind']=='constructor'}=={PREFIX+n for n in CONSTRUCTOR_CONTROLS},'constructor inventory incomplete')
 for ctor,witness in CONSTRUCTOR_CONTROLS.items():
  require(PREFIX+witness in byname,'missing inhabited constructor witness '+ctor)
  row=byname[PREFIX+witness]
  require(not row['signature'].lstrip().startswith('∀'),'constructor witness has a premise '+ctor)
 for name in REQUIRED_THEOREMS:
  require(PREFIX+name in byname and byname[PREFIX+name]['kind']=='theorem','missing required theorem '+name)
 for m in modules:
  for d in m['authored']:require(d['name'] in byname,'authored declaration absent from kernel inventory '+d['name'])
 return byname

def run(command):subprocess.run(command,cwd=ROOT,check=True)

def changed_paths(tree=None):
 target=[tree] if tree else []
 return set(git('diff','--name-only',BASE,*target,'--').splitlines()) | set(git('diff','--name-only',ADOPTED_MASTER,*target,'--').splitlines()) | set(git('ls-files','--others','--exclude-standard').splitlines())

def validate_foreign_paths(foreign,untracked,tree=None):
 require(not (set(foreign)&set(untracked)),'untracked foreign write')
 if foreign:
  command=['git','diff','--quiet',ADOPTED_MASTER]+([tree] if tree else [])+['--',*sorted(foreign)]
  result=subprocess.run(command,cwd=ROOT)
  require(result.returncode==0,'foreign work differs from adopted publication')

def validate_registration(registration):
 require(sha(ROOT/'Solidity.lean')==registration['desired_root_sha256'],'coordinator root registration is not present')
 require(sha(ROOT/registration['module_map_file'])==registration['desired_module_map_sha256'],'coordinator module-map registration is not present')
 run(['bash','scripts/coord-tools/register.sh','--check'])
 run([sys.executable,'scripts/coord-tools/module-map.py',BASE])

def validate_committed_inputs():
 # Every tracked and untracked input must match sealed HEAD, including evidence.
 changed=set(git('diff','HEAD','--name-only').splitlines())|set(git('ls-files','--others','--exclude-standard').splitlines())
 require(not changed,'checked inputs differ from sealed commit: '+str(sorted(changed)))

def validate_h35_completion():
 # H35 VM gates remain required; H41 replaces VM shipping with pack handoff.
 run([sys.executable,'tests/sol-numeric-literals/h35/validate-axioms.py'])
 expected={m['path']:m['sha256'] for m in source_snapshot()}
 for label in ('h35-owned-build','h35-print-axioms','h35-print-all-axioms','h35-controls'):
  gate=json.loads((FOLDER/'evidence'/(label+'.json')).read_text())
  require(gate['exit']==0 and not gate['resource_stop'],'H35 VM gate did not pass '+label)
  require(gate['proof_sources']==expected,'H35 source stamp differs '+label)
  require(gate['limits']==dict(memory_max=12884901888,memory_swap_max=0,lean_num_threads=1),'H35 resource envelope differs '+label)
  require(gate['minimum_parent_headroom_bytes']>=4*1024**3,'H35 reserve violated '+label)
 # H41 amends H35: preserve/verify the pack; the coordinator pulls it.
 # Coordinator-pending is the required VM handoff state, not a VM blocker.
 approved=json.loads((FOLDER/'h35/expected.json').read_text())
 path=FOLDER/'evidence/h41-cache-handoff.json'
 require(sha(path)==approved['h41_handoff_sha256'],'H41 handoff differs from committed approval')
 validate_h41_cache_record(json.loads(path.read_text()))

def validate_h41_cache_record(handoff):
 approved=json.loads((FOLDER/'h35/expected.json').read_text())
 require(handoff['archive_sha256']==approved['h41_archive_sha256'],'H41 approved archive digest differs')
 require(handoff['policy']=='H41 (H35 amended)' and handoff['status']=='coordinator-pending','H41 handoff policy/state differs')
 require(handoff['vm_shipping_forbidden'],'H41 forbids VM-side shipping')
 archive=pathlib.Path(handoff['archive'])
 require(sha(archive)==approved['h41_archive_sha256'],'H41 cache archive hash differs')
 prepared_path=ROOT/handoff['prepared_manifest']
 require(sha(prepared_path)==approved['h41_prepared_manifest_sha256'],'H41 prepared manifest differs from committed approval')
 prepared=json.loads(prepared_path.read_text())
 require(prepared['archive_sha256']==approved['h41_archive_sha256'],'H41 prepared manifest archive digest differs')
 expected={m['name']:m['sha256'] for m in source_snapshot()}
 require({m['module']:m['source_sha256'] for m in prepared['owned_modules']}==expected,'H41 cache sources differ')
 require(prepared['mapping_count']==len(expected),'H41 cache mapping coverage differs')

def validate_completion(registration,modules,manifest):
 # These are live checks, not conclusions inferred from ledger status strings.
 validate_committed_inputs()
 validate_registration(registration)
 require(pathlib.Path('/sys/fs/cgroup/memory.max').read_text().strip()=='12884901888','full gate requires approved 12 GiB envelope')
 require(pathlib.Path('/sys/fs/cgroup/memory.swap.max').read_text().strip()=='0','full gate requires no-swap envelope')
 require(os.environ.get('LEAN_NUM_THREADS')=='1','full gate requires LEAN_NUM_THREADS=1')
 reviews=json.loads((FOLDER/'evidence/final-reviews.json').read_text())
 expected={m['path']:m['sha256'] for m in modules}
 for role in ('finder','skeptic'):
  review=reviews[role]
  require(review['verdict']=='pass' and review['read_only'] and not review['lean_server_used'],'required review is not passing '+role)
  require(review['proof_sources']==expected,'review source stamp differs '+role)
  require(review['checker_sha256']==sha(ROOT/'scripts/check-sol-numeric-literals.py'),'review checker stamp differs '+role)
 handoff=json.loads((FOLDER/'evidence/handoff-seal.json').read_text());directory=pathlib.Path(handoff['directory'])
 require(json.loads((directory/'manifest.json').read_text())['head']==git('rev-parse','HEAD'),'sealed head differs from current head')
 run(['bash','scripts/coord-tools/seal.sh','--verify',str(directory)])
 logs=FOLDER/'evidence/complete-gates'
 env=dict(os.environ,GATE_BASE=BASE,GATE_LOGS=str(logs))
 subprocess.run(['bash','scripts/coord-tools/gate.sh','full'],cwd=ROOT,env=env,check=True)
 require((logs/'HEAD').read_text().strip()==git('rev-parse','HEAD'),'full-gate head differs')
 rows=[line.split('\t') for line in (logs/'gates.tsv').read_text().splitlines()]
 require(rows and all(r[0]=='PASS' for r in rows),'one or more live final gates failed')
 require({r[1] for r in rows}>={'build-touched','run-lean','trust','orphans','layers','roots','doc-paths','axiom-pins','testsuite','corpus','automatic-strict'},'final gate coverage incomplete')
 validate_h35_completion()

def check(implementation=False,self_test=False):
 manifest=json.loads((FOLDER/'acceptance.json').read_text());modules=source_snapshot()
 require(manifest['base']==BASE,'wrong base pin')
 require(git('branch','--show-current')=='codex/solidity-sol2-20261104/numeric-literals','wrong branch')
 run(['git','merge-base','--is-ancestor',BASE,'HEAD'])
 adoption=json.loads((FOLDER/'adoption.json').read_text())
 require(adoption['original_base']==BASE and adoption['adopted_master']==ADOPTED_MASTER,'adoption identity drift')
 require(manifest['adopted_master']==ADOPTED_MASTER,'acceptance adoption pin differs')
 run(['git','merge-base','--is-ancestor',BASE,ADOPTED_MASTER])
 run(['git','merge-base','--is-ancestor',ADOPTED_MASTER,'HEAD'])
 run(['git','merge-base','--is-ancestor',adoption['pre_adoption_head'],'HEAD'])
 changed=changed_paths()
 registration=json.loads((FOLDER/'registration.json').read_text())
 # The worker never writes these files. A coordinator may apply the exact
 # predeclared integration proposal; accepting it is observation, not authority.
 coordinator_files={'Solidity.lean':registration['desired_root_sha256'],registration['module_map_file']:registration['desired_module_map_sha256']}
 outside={p for p in changed if not permitted(p)}
 # Adopted upstream bytes are authorized inherited work, never a blanket
 # foreign-edit exemption. Every other foreign path must match that exact tree.
 untracked=set(git('ls-files','--others','--exclude-standard').splitlines())
 require(not (outside & untracked),'untracked foreign write: '+str(sorted(outside & untracked)))
 foreign=[p for p in outside if not (not implementation and p in coordinator_files and (ROOT/p).is_file() and sha(ROOT/p)==coordinator_files[p])]
 validate_foreign_paths(foreign,untracked)
 pins=json.loads((FOLDER/'source-pins.json').read_text())
 require(pins['base']==BASE,'wrong scanner base')
 for path,digest in pins['sha256'].items():
  require(sha(ROOT/path)==digest,'read-only source drift '+path)
  original=subprocess.check_output(['git','show',BASE+':'+path],cwd=ROOT)
  import hashlib
  require(hashlib.sha256(original).hexdigest()==digest,'source pin differs from published base '+path)
 require(modules==manifest['modules'],'module/declaration/import/source inventory drift')
 require(controls()==manifest['scanner_controls'],'scanner control coverage drift')
 require(len(controls())==len(set(controls())),'duplicate scanner control ID')
 require(case_families()==manifest['case_families'],'case family coverage drift')
 for path,digest in manifest['gate_scripts'].items():require(sha(ROOT/path)==digest,'gate script drift '+path)
 modmap={m['name']:m for m in modules};seen=set();active=set()
 def visit(name):
  if name in seen:return
  require(name not in active,'owned import cycle '+name);active.add(name)
  for dep in modmap[name]['imports']:
   if dep in modmap:visit(dep)
   else:require(dep in ('Lean',) or (ROOT/(dep.replace('.','/')+'.lean')).is_file(),'missing import '+dep)
  active.remove(name);seen.add(name)
 for name in modmap:visit(name)
 closure=set();stack=['Solidity.Frontend.NumericLiteralProofs.Audit']
 while stack:
  name=stack.pop()
  if name in closure:continue
  closure.add(name);stack.extend(d for d in modmap[name]['imports'] if d in modmap)
 require(closure==set(modmap),'audit import closure omits a new module')
 for m in modules:
  clean=blank_lean((ROOT/m['path']).read_text())
  require(not re.search(r'\b(?:sorry|sorryAx|admit|axiom|unsafe|native_decide|maxHeartbeats)\b',clean),'forbidden proof escape or budget override '+m['path'])
  for d in m['authored']:
   if d['kind']=='inductive':require(not re.search(r'\b(?:decNumber|hexNumber)\b',blank_lean(d['signature_source'])),'grammar invokes numeric decoder '+d['name'])
 audit=json.loads((FOLDER/'evidence/audit-validation.json').read_text())
 require(audit['exit']==0 and not audit['resource_stop'],'kernel audit did not pass')
 require(audit['proof_sources']=={m['path']:m['sha256'] for m in modules},'audit source stamp differs from current modules')
 require(audit['limits']==dict(memory_max=12884901888,memory_swap_max=0,lean_num_threads=1),'audit resource envelope drift')
 require(audit['minimum_parent_headroom_bytes']>=4*1024**3,'H1 reserve violated')
 actual=json.loads((FOLDER/'evidence/kernel-inventory.actual.json').read_text())
 pinned=json.loads((FOLDER/'kernel-inventory.json').read_text())
 validate_inventory(actual,pinned,modules)
 require(manifest['kernel_inventory_sha256']==sha(FOLDER/'kernel-inventory.json'),'kernel inventory file drift')
 registration=json.loads((FOLDER/'registration.json').read_text())
 require(registration['base']==BASE and registration['modules']==[m['name'] for m in modules],'coordinator registration manifest incomplete')
 require(len(registration['module_map_rows'])==len(modules),'module-map row inventory incomplete')
 require(sha(FOLDER/'registration.patch')==registration['root_patch_sha256'],'registration patch drift')
 require(sha(FOLDER/'registration.module-map.patch')==registration['module_map_patch_sha256'],'module-map patch drift')
 run([sys.executable,'tests/sol-numeric-literals/generate-wordtable.py','--check'])
 run([sys.executable,'tests/sol-numeric-literals/generate-fixtures.py','--check'])
 run(['node','tests/sol-numeric-literals/run-fixtures.mjs'])
 run([sys.executable,'tests/sol-numeric-literals/differential.py'])
 if self_test:
  # These mutations model concrete failures the scope gate must reject.
  for label,mutation in [
   ('missing declaration',lambda a:a.pop()),
   ('axiom growth',lambda a:a[0]['axioms'].append('sorryAx')),
   ('unsafe declaration',lambda a:a[0].update(isUnsafe=True)),
   ('changed signature',lambda a:a[0].update(signature='False')),
   ('duplicate declaration',lambda a:a.append(copy.deepcopy(a[0])))]:
   bad=copy.deepcopy(actual);mutation(bad)
   try:validate_inventory(bad,pinned,modules)
   except ValueError:pass
   else:raise ValueError('negative acceptance control passed: '+label)
  forged=copy.deepcopy(registration);forged['desired_root_sha256']='0'*64
  try:validate_registration(forged)
  except ValueError:pass
  else:raise ValueError('forged completion ledger bypassed actual registration')
  fd,temporary=tempfile.mkstemp(prefix='uncommitted-input-',suffix='.json',dir=FOLDER)
  os.close(fd);relative=pathlib.Path(temporary).relative_to(ROOT).as_posix()
  try:
   try:validate_committed_inputs()
   except ValueError as e:require(relative in str(e),'uncommitted input was not detected')
   else:raise ValueError('uncommitted checked input bypassed the seal binding')
  finally:pathlib.Path(temporary).unlink()
  run([sys.executable,'tests/sol-numeric-literals/runtime/test-check.py'])
  run([sys.executable,'tests/sol-numeric-literals/h35/test-h41.py'])
  run([sys.executable,'tests/sol-numeric-literals/test-adoption.py'])
  print('acceptance negative controls: 5 inventory mutations, forged completion, uncommitted input and MOCK resource-stop reporting passed')
 authored=sum(len(m['authored']) for m in modules)
 print(f'implementation acceptance: {len(modules)} modules, {authored} authored declarations, {len(actual)} kernel declarations, {len(CONSTRUCTOR_CONTROLS)} inhabited constructors, {len(controls())} scanner controls, 42 paired fixtures')
 obligations=json.loads((FOLDER/'obligations.json').read_text())
 required={'inventory','scanner-correspondence','erasure-and-values','token-classification','refusal-families','backfill','constructor-controls','compiler-fixtures','trust-inventory','independent-reviews','target-import-closure','static-gates','coordinator-registration','full-runtime-gate','immutable-handoff'}
 require({o['id'] for o in obligations}==required,'obligation ledger incomplete')
 open_items=[o['id'] for o in obligations if o['status']!='done']
 if open_items:
  print('open assignment obligations: '+', '.join(open_items))
  require(implementation,'assignment acceptance blocked by open obligations')
 if not implementation:validate_completion(registration,modules,manifest)
 return 0

if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--implementation',action='store_true');p.add_argument('--self-test',action='store_true');a=p.parse_args()
 try:sys.exit(check(a.implementation,a.self_test))
 except (ValueError,AssertionError,KeyError,FileNotFoundError,subprocess.CalledProcessError) as e:
  print('numeric-literals: FAIL: '+str(e),file=sys.stderr);sys.exit(1)
