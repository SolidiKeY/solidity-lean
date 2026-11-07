#!/usr/bin/env python3
"""Coordinator-only map proposal; default checks pins and never edits a registry."""
import copy,difflib,hashlib,json,pathlib,re,runpy,subprocess,sys,tempfile,os
ROOT=pathlib.Path(__file__).resolve().parents[3]
F=pathlib.Path(__file__).resolve().parent
BASE='3883c64ef750dd49acdb7d83adcdf0f101d42c6c'
DEST='docs/module-map/frontend.md'
INPUT_ROOT=pathlib.Path(os.environ.get('SOL_NL_VALIDATION_INPUTS',str(ROOT)))
INPUT_FOLDER=INPUT_ROOT/'tests/primitive-packets-1105/Constants'
sha=lambda data:hashlib.sha256(data).hexdigest()
def read_json(path):return json.loads((ROOT/path).read_text())
def encoded(obj):return (json.dumps(obj,sort_keys=True,indent=2)+'\n').encode()
def collect():
 subprocess.run(['git','merge-base','--is-ancestor',BASE,'HEAD'],cwd=ROOT,check=True)
 changed=set(subprocess.check_output(['git','diff','--name-only',BASE,'--'],cwd=ROOT,text=True).splitlines())|set(subprocess.check_output(['git','ls-files','--others','--exclude-standard'],cwd=ROOT,text=True).splitlines())
 prefixes=('Solidity/Frontend/NumericLiteralProofs/','tests/sol-numeric-literals/','Solidity/Backend/PrimitivePackets/Constants/','tests/primitive-packets-1105/Constants/')
 exact={'scripts/check-sol-numeric-literals.py','docs/feature-work/numeric-literal-proofs.md','docs/feature-work/primitive-packets-1105-Constants.md'}
 assert all(p.startswith(prefixes) or p in exact for p in changed),'write outside explicitly assigned lanes'
 nl=runpy.run_path(str(ROOT/'scripts/check-sol-numeric-literals.py'))
 cm=runpy.run_path(str(F/'check.py'))
 nm=read_json('tests/sol-numeric-literals/acceptance.json');constants=cm['M']
 numeric=nl['source_snapshot']();assert numeric==nm['modules'],'numeric source/declaration drift'
 nk=read_json('tests/sol-numeric-literals/kernel-inventory.json')
 ck=read_json('tests/primitive-packets-1105/Constants/kernel-inventory.json')
 assert sha((ROOT/'tests/sol-numeric-literals/kernel-inventory.json').read_bytes())==nm['kernel_inventory_sha256']
 assert sha((F/'kernel-inventory.json').read_bytes())==constants['kernel_inventory_sha256']
 nl['validate_inventory'](nk,nk,numeric);cm['validate_inventory'](ck)
 proofs={m['path']:m['sha256'] for m in numeric}|constants['modules']
 actual={str(p.relative_to(ROOT)) for folder in ['Solidity/Frontend/NumericLiteralProofs','Solidity/Backend/PrimitivePackets/Constants'] for p in (ROOT/folder).rglob('*.lean')}
 assert actual==set(proofs) and len(proofs)==47,'owned module coverage'
 for path,digest in proofs.items():assert sha((ROOT/path).read_bytes())==digest,'proof source pin '+path
 for pins in [read_json('tests/sol-numeric-literals/source-pins.json')['sha256'],constants['inputs']]:
  for path,digest in pins.items():assert sha((ROOT/path).read_bytes())==digest,'read-only API pin '+path
 rows=nk+ck;assert len(rows)==1037 and len({r['name'] for r in rows})==1037
 helpers=runpy.run_path(str(ROOT/'scripts/coord-tools/module-map.py'))
 maps={str(p.relative_to(ROOT)):p.read_bytes().decode() for p in sorted((ROOT/'docs/module-map').glob('*.md'))}
 names=set().union(*(helpers['named'](text) for text in maps.values()))
 root=(ROOT/'Solidity.lean').read_bytes().decode();imports=re.findall(r'^import (\S+)$',root,re.M)
 modules=[];missing=[]
 summaries={
 'Audit':'Full owned kernel declaration, signature and transitive axiom inventory.',
 'Backfill':'Exact numeric consumed-prefix, source-range and denomination-separation theorems.',
 'Classification':'Accepted numeric token classification and nonnumeric word separation.',
 'Controls':'Inhabited grammar constructors and scanner-arm positive and refusal controls.',
 'Digits':'Independent decimal digit spelling and universal scanner correspondence with suffix preservation.',
 'Fixtures':'Typed fixed solc-0.8.38 differential spelling fixtures.',
 'Refusals':'Arbitrary-length numeric refusal families and malformed spelling boundaries.',
 'Span':'Numeric source-range and suffix-consumption correspondence.',
 'Spellings':'Independent decimal and hexadecimal spelling relations and exact decoder correspondence.',
 'Underscores':'Grammar-admitted underscore erasure preserves digit sequences and values.',
 'Values':'Exact decimal scale/exponent and hexadecimal numeric interpretation.',
 'WordTable':'All fixed words are disjoint from numeric token results.'}
 for path,digest in sorted(proofs.items()):
  name=path[:-5].replace('/','.');assert imports.count(name)==1,'root import missing/duplicate '+name
  owned=[r for r in rows if r['module']==name]
  modules.append(dict(path=path,sha256=digest,declarations=[r['name'] for r in sorted(owned,key=lambda x:x['name'])],kernel_signature_digest=sha(encoded(sorted(owned,key=lambda x:x['name'])))))
  if helpers['covered'](helpers['stem'](path),names):continue
  stem=path.removeprefix('Solidity/');leaf=pathlib.Path(path).stem
  if '/WordTable/Part' in path:summary='Structural fixed-word prefix decision proofs; numeric tokens are refused for this table segment.'
  elif path.startswith('Solidity/Backend/'):summary='Kernel integer-constant controls for every legal width/sign, endpoints, saved stack and invalid values.'
  else:summary=summaries[leaf]
  missing.append(dict(path=path,module=name,destination=DEST,row='| `'+stem+'` | '+summary+' |'))
 before=maps[DEST];after=before.rstrip()+'\n'+''.join(r['row']+'\n' for r in missing)
 if not missing:after=before
 patch=''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='a/'+DEST,tofile='b/'+DEST))
 # A proposal adds only exact literal rows; no directory/glob can hide a module.
 after_names=helpers['named'](after)|set().union(*(helpers['named'](t) for p,t in maps.items() if p!=DEST))
 assert all(helpers['covered'](helpers['stem'](p),after_names) for p in proofs)
 for row in missing:assert re.fullmatch(r'\| `'+re.escape(row['path'].removeprefix('Solidity/'))+r'` \| [^|]+ \|',row['row'])
 inputs=['scripts/coord-tools/module-map.py','tests/sol-numeric-literals/acceptance.json','tests/sol-numeric-literals/kernel-inventory.json','tests/sol-numeric-literals/source-pins.json','tests/primitive-packets-1105/Constants/manifest.json','tests/primitive-packets-1105/Constants/kernel-inventory.json']
 plan=dict(base=BASE,generator_sha256=sha(pathlib.Path(__file__).read_bytes()),status='proposal-pending-coordinator' if missing else 'registration-observed',owner='coordinator; shared roots/maps remain untouched',root_sha256=sha(root.encode()),map_sha256={p:sha(t.encode()) for p,t in maps.items()},input_sha256={p:sha((ROOT/p).read_bytes()) for p in inputs},owned_modules=modules,kernel_declarations=1037,numeric_authored=sum(len(m['authored']) for m in numeric),constant_authored=len(constants['declarations']),missing_rows=missing,desired_map_sha256=sha(after.encode()),patch_sha256=sha(patch.encode()),boundary='Registration and pinned inventory validation only; does not replace live Lean proofs, solc fixtures, full scoped acceptance or final runtime gates.')
 plan['imported_continuity']=[row for row in ck if not row['module'].startswith('Solidity.Backend.PrimitivePackets.Constants.')]
 plan['owned_kernel_declarations']=len(rows)-len(plan['imported_continuity'])
 return plan,patch

def compare(plan,patch,expected,expected_patch):
 assert plan==expected,'proposal inventory/context mismatch'
 assert patch==expected_patch,'proposal changes more than required exact rows'
 assert sha(patch.encode())==plan['patch_sha256']

def validate(plan,patch):compare(plan,patch,*collect())

def mutation_controls(plan,patch):
 # Freeze an already validated context. The synthetic empty state below tests
 # mutation generation only; it never becomes a claim about the shared map.
 dummy=dict(path='Solidity/Unpublished.lean',module='Solidity.Unpublished',destination=DEST,row='invalid')
 cases=['omitted-row' if plan['missing_rows'] else 'spurious-row','extra-row','source-pin','declaration','false-status','wrong-area']
 for kind in cases:
  bad=copy.deepcopy(plan)
  if kind=='omitted-row':bad['missing_rows'].pop()
  elif kind in ('spurious-row','extra-row'):bad['missing_rows'].append(dict(bad['missing_rows'][0]) if bad['missing_rows'] else dict(dummy))
  elif kind=='source-pin':bad['owned_modules'][0]['sha256']='0'*64
  elif kind=='declaration':next(m for m in bad['owned_modules'] if m['declarations'])['declarations'].pop()
  elif kind=='false-status':bad['status']='registration-observed' if plan['missing_rows'] else 'proposal-pending-coordinator'
  else:
   if not bad['missing_rows']:bad['missing_rows'].append(dict(dummy))
   bad['missing_rows'][0]['destination']='docs/module-map/yul.md'
  try:compare(bad,patch,plan,patch)
  except AssertionError:pass
  else:raise AssertionError('mutation accepted '+kind)
 try:compare(plan,patch+'\n+| `Frontend/**` | invalid glob |\n',plan,patch)
 except AssertionError:pass
 else:raise AssertionError('overbroad patch accepted')
 return len(cases)+1

def index_check(patch):
 # Temporary index only: the shared registry working tree is never modified.
 with tempfile.TemporaryDirectory() as td:
  index=pathlib.Path(td)/'index';env=dict(os.environ,GIT_INDEX_FILE=str(index))
  subprocess.run(['git','read-tree','HEAD'],cwd=ROOT,env=env,check=True)
  if patch:
   subprocess.run(['git','apply','--cached','--check','-'],input=patch.encode(),cwd=ROOT,env=env,check=True)
   subprocess.run(['git','apply','--cached','-'],input=patch.encode(),cwd=ROOT,env=env,check=True)
  tree=subprocess.check_output(['git','write-tree'],cwd=ROOT,env=env,text=True).strip()
  changed=subprocess.check_output(['git','diff','--name-only','HEAD',tree],cwd=ROOT,text=True).splitlines()
  assert changed==([DEST] if patch else []),'unrelated temporary-index change'
  return tree

def required_inputs():return [INPUT_FOLDER/'registration-current.json',INPUT_FOLDER/'registration-current.patch']

def main():
 plan_path,patch_path=required_inputs()
 if sys.argv[1:]==['--write']:
  plan,patch=collect();plan_path.write_bytes(encoded(plan));patch_path.write_text(patch)
 else:
  assert not sys.argv[1:],'usage: registration-plan.py [--write]'
  missing=[str(p) for p in required_inputs() if not p.is_file()]
  if missing:
   raise SystemExit('FAIL: required registration inputs missing: '+', '.join(missing))
  plan=json.loads(plan_path.read_text());patch=patch_path.read_text();validate(plan,patch)
  mutation_controls(plan,patch)
  empty=copy.deepcopy(plan);empty.update(missing_rows=[],status='registration-observed',patch_sha256=sha(b''))
  mutation_controls(empty,'')
  tree=index_check(patch)
  print('PASS:47 source pins,1037 kernel declarations,'+str(len(plan['missing_rows']))+' exact proposed rows; comparator self-checks (not independent mutations); temporary tree '+tree)
if __name__=='__main__':main()
