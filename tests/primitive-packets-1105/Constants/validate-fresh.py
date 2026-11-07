#!/usr/bin/env python3
"""Fresh unaffected numeric proof evidence; never claims final runtime completion."""
import copy,json,pathlib,re,runpy,hashlib,subprocess,tempfile,os
ROOT=pathlib.Path(__file__).resolve().parents[3]
F=pathlib.Path(__file__).resolve().parent
N=ROOT/'tests/sol-numeric-literals'
INPUT_ROOT=pathlib.Path(os.environ.get('SOL_NL_VALIDATION_INPUTS',str(ROOT)))
def input_path(path):return INPUT_ROOT/path.relative_to(ROOT)
TARGETS={
 'h55-owned-audit':('Solidity/Frontend/NumericLiteralProofs/Audit.lean',180),
 'h55-all-axioms':('tests/sol-numeric-literals/h35/PrintAllAxioms.lean',180),
 'h55-keysort':('Solidity/KeySort.lean',120)}
def validate_gate(label,row,diag,expected):
 path,timeout=TARGETS[label]
 assert len(row['command'])==4 and row['command'][:3]==['scripts/coord-tools/lean-mcp','call','lean_diagnostic_messages'],'wrong diagnostic method'
 assert json.loads(row['command'][3])==dict(file_path=str(ROOT/path),interactive=False,timeout_s=timeout),'wrong diagnostic target/arguments'
 assert row['log']==str(N/'evidence'/(label+'.log')),'wrong diagnostic log binding'
 assert row['exit']==0 and not row['resource_stop'] and row['proof_sources']==expected
 assert row['limits']==dict(memory_max=12884901888,memory_swap_max=0,lean_num_threads=1)
 assert row['minimum_parent_headroom_bytes']>=4*1024**3
 assert diag['success'] and not diag['partial'] and not diag['timed_out'] and not diag['failed_dependencies']
 assert not [i for i in diag['items'] if i['severity'] in ('error','warning')]
def required_inputs():
 paths=[N/'evidence/kernel-inventory.actual.json',F/'registration-current.json',F/'registration-current.patch',F/'evidence/h55-toolchain.log']
 for folder,labels in [(N,list(TARGETS)+['h55-owned-build']),(F,['h55-constants-build'])]:
  paths.extend(folder/'evidence'/(label+suffix) for label in labels for suffix in ['.json','.log'])
 return [input_path(p) for p in paths]

def main():
 missing=[str(p) for p in required_inputs() if not p.is_file()]
 if missing:
  raise SystemExit('FAIL: required diagnostic/build evidence missing: '+', '.join(missing))
 nl=runpy.run_path(str(ROOT/'scripts/check-sol-numeric-literals.py'))
 modules=nl['source_snapshot']();pins=json.loads((N/'kernel-inventory.json').read_text())
 actual=json.loads(input_path(N/'evidence/kernel-inventory.actual.json').read_text())
 nl['validate_inventory'](actual,pins,modules)
 expected={m['path']:m['sha256'] for m in modules}
 evidence={}
 for label in ['h55-owned-audit','h55-all-axioms','h55-keysort']:
  row=json.loads(input_path(N/'evidence'/(label+'.json')).read_text());diag=json.loads(input_path(N/'evidence'/(label+'.log')).read_text())
  validate_gate(label,row,diag,expected)
  evidence[label]=dict(seconds=row['seconds'],errors=0,source_modules=len(expected))
 row=json.loads(input_path(N/'evidence/h55-keysort.json').read_text());diag=json.loads(input_path(N/'evidence/h55-keysort.log').read_text())
 for kind in ['wrong-file','wrong-method','wrong-log']:
  bad=copy.deepcopy(row)
  if kind=='wrong-file':
   args=json.loads(bad['command'][3]);args['file_path']=str(ROOT/'Solidity/AST.lean');bad['command'][3]=json.dumps(args)
  elif kind=='wrong-method':bad['command'][2]='lean_file_outline'
  else:bad['log']=str(N/'evidence/unrelated.log')
  try:validate_gate('h55-keysort',bad,diag,expected)
  except AssertionError:pass
  else:raise AssertionError('diagnostic binding mutation accepted '+kind)
 raw=json.loads(input_path(N/'evidence/h55-all-axioms.log').read_text());printed={}
 for item in raw['items']:
  assert item['severity']=='info'
  m=re.fullmatch(r"'(.+)' depends on axioms: \[(.*?)\]",item['message'],re.S)
  if m:name=m[1];axioms={a.strip() for a in m[2].split(',') if a.strip()}
  else:
   m=re.fullmatch(r"'(.+)' does not depend on any axioms",item['message'],re.S);assert m,item['message']
   name=m[1];axioms=set()
  assert name not in printed;printed[name]=axioms
 theorems={r['name']:set(r['axioms']) for r in pins if r['kind']=='theorem'}
 assert printed==theorems and len(printed)==808,'fresh theorem/axiom coverage drift'
 plan=runpy.run_path(str(F/'registration-plan.py'));expected_plan,patch=plan['collect']()
 plan['validate'](json.loads(input_path(F/'registration-current.json').read_text()),input_path(F/'registration-current.patch').read_text())
 source_modules={m['path']:m['sha256'] for m in expected_plan['owned_modules']}
 builds={}
 for label,folder,target,source_pins in [
  ('h55-owned-build',N,'Solidity.Frontend.NumericLiteralProofs.Audit',expected),
  ('h55-constants-build',F,'Solidity.Backend.PrimitivePackets.Constants.Controls',{p:h for p,h in source_modules.items() if p.startswith('Solidity/Backend/')})]:
  row=json.loads(input_path(folder/'evidence'/(label+'.json')).read_text())
  assert row['command']==['lake','build',target] and row['log']==str(folder/'evidence'/(label+'.log')),'wrong owned build binding'
  assert row['exit']==0 and not row['resource_stop'] and row['proof_sources']==source_pins
  assert row['limits']==dict(memory_max=12884901888,memory_swap_max=0,lean_num_threads=1)
  assert row['minimum_parent_headroom_bytes']>=4*1024**3
  assert 'Build completed successfully' in input_path(folder/'evidence'/(label+'.log')).read_text()
  builds[label]=dict(seconds=row['seconds'],modules=len(source_pins),boundary='matching-cache replay, not a clean compile')
 changed=subprocess.check_output(['git','diff','--name-only',plan['BASE'],'--'],cwd=ROOT,text=True).splitlines()
 assert not any(p.startswith('Solidity/Yul/') for p in changed),'reserved-area source changed'
 toolchain=input_path(F/'evidence/h55-toolchain.log').read_text()
 assert '12884901888\n0\n1\n' in toolchain
 assert 'Lake version 5.0.0-src+797c613' in toolchain and 'Lean (version 4.24.0' in toolchain
 result=dict(status='pass-scoped-validation',proof_sources=source_modules,numeric_kernel_declarations=len(pins),fresh_theorem_prints=len(printed),combined_pinned_kernel_declarations=expected_plan['kernel_declarations'],proposal_rows=len(expected_plan['missing_rows']),gates=evidence,owned_builds=builds,lean='4.24.0',lake='5.0.0-src+797c613',reserved_source_files_edited=[],diagnostic_binding_mutations=3,runtime_gate_pass=False,limits='12GiB aggregate/no swap/CPU1/Lean-j1/H1>=4GiB',boundary='Validation of archived VM numeric kernel/signature/axiom and KeySort checks plus pinned Constants inventory and coordinator-only registration proposal; prior full-runtime failures remain open.')
 with tempfile.NamedTemporaryFile(mode='w',prefix='sol-numeric-literals-validated-',suffix='.json',dir='/tmp',delete=False) as output:
  output.write(json.dumps(result,indent=2)+'\n')
 print('External validation result: '+output.name)
 print('PASS: archived VM evidence binds 991 numeric declarations, 808 exact theorem axiom sets, KeySort 0 errors; 47 source pins/1037 pinned declarations/'+str(result['proposal_rows'])+'proposalrows;3diagnostic-binding mutations; no RuntimeGatePass')
if __name__=='__main__':main()
