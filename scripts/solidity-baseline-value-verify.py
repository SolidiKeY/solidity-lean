#!/usr/bin/env python3
"""Independent exact expectations for the bounded value-entry diagnostics.
Static mutation controls test this verifier; they are not extra runtime results.
"""
import argparse,copy,hashlib,json,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
PIN='6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
def check_observations(x):
 expected=[('nonpayableEntry()',0,False,9,0,0,0),('nonpayableEntry()',1,True,9,0,0,0),('payableEntry()',5,False,11,5,5,7),('writeFail()',2,True,11,5,5,7),('internalCall()',3,False,13,8,3,7),('nonpayableEntry()',1,True,13,8,3,7),('ordinary()',1,True,13,8,3,7),('ordinary()',0,False,14,8,3,7)]
 def world(w,counter,balance,value,sender,timestamp):
  assert w['storage']==[f'counter = {counter}',f'seenValue = {value}',f'seenSender = {sender}',f'seenBalance = {balance}']
  assert w['balance']==str(balance) and w['ledger']==[{'address':'7','amount':str(balance)}]
  assert w['selfAddress']=='9' and w['timestamp']==str(timestamp)
 world(x['deployed'],3,0,0,0,0);assert len(x['observed'])==len(expected)
 prior=x['deployed']
 for i,(o,(signature,payment,failed,counter,balance,value,sender)) in enumerate(zip(x['observed'],expected)):
  assert o['before']==prior and o['signature']==signature
  assert o['tx']==dict(sender='7',value=str(payment),selfAddress='9',timestamp=str(i+1))
  assert o['acceptedPremises'] is True and o['failed']==failed and o['runReturnedWorld']==(not failed)
  assert o['fundingAssumptionRemaining']==str(100-balance)
  assert o['revertBytes']==([78,72,123,113]+[0]*31+[1] if signature=='writeFail()' else [])
  world(o['after'],counter,balance,value,sender,i+1)
  if failed:assert {k:v for k,v in o['before'].items() if k!='timestamp'}=={k:v for k,v in o['after'].items() if k!='timestamp'}
  prior=o['after']
 assert x['internalOnlyAbi']==dict(refused=True,reason='no imported ABI entry for helper()')
 return True

def verify(base):
 before=read(base/'before.json');assert len(before['snapshots'])==309
 assert all(sha(Path(p))==v for p,v in before['snapshots'].items())
 overlay=read(base/'overlay-imports.json');assert len(overlay)==77
 assert all(sha(base/p)==v['sha256'] and str((base/p).resolve())==v['resolved'] for p,v in overlay.items())
 assert sha(ROOT/'Solidity/Semantics/Lifetime.lean')==before['sourceSha256']
 assert sha(base/'overlay/Solidity/Semantics/Lifetime.olean')==read(base/'after.json')['privateRootArtifacts']['overlay/Solidity/Semantics/Lifetime.olean']['sha256']
 summary={};observed=[]
 for mode in ['legacy','viaIR']:
  job=base/'runtime-final'/mode;x=read(job/'observed.json');check_observations(x);observed.append(x)
  ast=read(job/'source.ast.json');h=ast['header'];assert h['compilerSha256']==PIN and h['sourceSha256']==sha(ROOT/'tests/upstream/baseline-20261028/value-runtime/inputs/ValueEntry.sol') and h['settings']['viaIR']==(mode=='viaIR')
  declarations={}
  def walk(v):
   if isinstance(v,dict):
    if v.get('nodeType')=='FunctionDefinition':declarations[v['id']]=v
    assert v.get('nodeType') not in ['ForStatement','WhileStatement','DoWhileStatement','InlineAssembly']
    for w in v.values():walk(w)
   elif isinstance(v,list):
    for w in v:walk(w)
  walk(ast['ast'])
  assert (job/'ValueRuntime.lean').read_text().startswith((ROOT/'tests/upstream/baseline-20261028/value-runtime/ValueAdapter.lean').read_text())
  rows=read(job/'typed-import.json');assert rows and all(r['status']=='elaborated' and r['admissionChecked'] for r in rows)
  for o in x['observed']:
   r=[r for r in rows if r['sourceId']==o['sourceId']];assert len(r)==1;r=r[0];d=declarations[o['sourceId']]
   assert r['name']==o['resolvedName'] and r['signature']==o['signature']==d['name']+'()'
   assert d['visibility'] in ['public','external'] and d['parameters']['parameters']==[]
   assert r['payable']==o['payableFromDeclarationAndRow']==(d['stateMutability']=='payable')
  # Deliberately unchanged original scalar false-output control, not a payment comparator.
  negative=read(job/'false-output.json');assert len(negative)==1;n=negative[0]
  assert n['pipeline']==mode and n['status']=='broken' and n['reason']=='runtime expectation mismatch: identifiers()'
  assert n['observed']==[dict(values=['7'],signature='identifiers()',revertBytes=[],returnBytes=[],failed=False)]
  assert n['expected']==dict(signature='identifiers()',revertBytes=[],failure=False,expected=['8'],args=[])
  original=ROOT/f'tests/upstream/baseline-20261028/native-cache/runs/NativePositive/{mode}/negative-jobs.json'
  ledger=read(ROOT/'tests/upstream/baseline-20261028/native-cache/archive.json')
  assert sha(original)==ledger['files'][f'runs/NativePositive/{mode}/negative-jobs.json']['sha256']
  assert sha(ROOT/'tests/upstream/baseline-20261028/native-cache/evidence.tar.gz')==ledger['sha256']
  summary[mode]=dict(typedImportRows=len(rows),matchingTransactions=8,helperAbiRefusals=1,unchangedScalarFalseOutputControls=1)
 assert observed[0]==observed[1]
 for record in read(base/'runtime-final-commands.json'):
  assert record['exitCode']==0 and sha(base/record['log'])==record['sha256']
 controls=[]
 mutations=[('leaked-body-effect',lambda x:x['observed'][5]['after']['storage'].__setitem__(0,'counter = 9')),
 ('double-credit',lambda x:x['observed'][2]['after'].__setitem__('balance','10')),
 ('failed-payment-retained',lambda x:x['observed'][3]['after'].__setitem__('balance','7')),
 ('changed-revert-code',lambda x:x['observed'][3]['revertBytes'].__setitem__(-1,17)),
 ('internal-abi-admitted',lambda x:x['internalOnlyAbi'].__setitem__('refused',False))]
 for label,mutate in mutations:
  x=copy.deepcopy(observed[0]);mutate(x)
  try:check_observations(x)
  except AssertionError:controls.append(dict(control=label,rejected=True,staticVerifierControl=True))
  else:raise AssertionError('verifier accepted corrupted evidence: '+label)
 return dict(valueEntryDiagnosticComplete=True,scope='Only this zero-argument imported-entry value diagnostic in both required pipelines; not whole-corpus,40-question attribution,universal proof,proof-search or generated-EVM completeness',pipelines=summary,matchingTransactions=16,helperAbiRefusals=2,unchangedScalarFalseOutputControls=2,allShared309SnapshotsUnchanged=True,all77OverlayOleansMatch=True,mutationControls=controls,historicalNativeValidationComplete='false remains unchanged in historical matrix',remainingLimits=['Environment spendable funding is an explicit assumption checked by the diagnostic, not enforced by Lifetime.','System.run returns no world on error; immutable prior World.atTime follows existing Step.rollback policy, not a concretely kernel-proved trace.','No generated-EVM or universal source/compiler dispatcher proof.','No nonzero-argument ABI decoding coverage is inferred.','Testing proof closure remains stale; no full/cold/warm build repeated.'])
def main():
 p=argparse.ArgumentParser();p.add_argument('base',type=Path);p.add_argument('--out',type=Path);a=p.parse_args();x=verify(a.base)
 if a.out:
  with a.out.open('x') as f:f.write(json.dumps(x,indent=2)+'\n')
 print(json.dumps(x))
if __name__=='__main__':main()
