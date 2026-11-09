#!/usr/bin/env python3
"""Run the additive v2 against an explicit frozen view; record blocked gates.
No v1 edit, baseline repin, owner approval or root/deletion certification follows.
Logs/receipts stay outside the code tree; the small result is checker input.
"""
import argparse,hashlib,json,os,pathlib,runpy,subprocess,time
HERE=pathlib.Path(__file__).resolve().parent
T=runpy.run_path(str(HERE/'trust_audit_v2.py'));Q=T['Q'];API=Q['API'];SHA=Q['SHA'];W=runpy.run_path(str(HERE/'warm_trust_v2.py'))
def main():
 p=argparse.ArgumentParser();p.add_argument('--source-root',type=pathlib.Path,required=True);p.add_argument('--view',type=pathlib.Path,required=True);p.add_argument('--capture',type=pathlib.Path,required=True);p.add_argument('--attempt',type=pathlib.Path,action='append',required=True);p.add_argument('--out',type=pathlib.Path,required=True);p.add_argument('--check',action='store_true');p.add_argument('--prior-warm-producer',action='append',default=[]);a=p.parse_args()
 for n in ('source_root','view','capture','out'):setattr(a,n,getattr(a,n).resolve())
 validated={}
 for path in a.attempt:
  path=path.resolve();assert path==path.parent/'receipt.json','Canonical warm receipt required';before=SHA(path);d=json.loads(path.read_text());log=path.parent/'capture.log';before_log=SHA(log)
  cmd=['python3','-I',str(HERE/'warm_trust_v2.py'),'--source-root',str(a.source_root),'--view',d['input_view'],'--out-view',d['output_view'],'--logs',str(path.parent),'--check']
  if '-DElab.async=false' in d['command']:cmd.append('--synchronous')
  if d['producers']['warm_trust_v2.py']!=SHA(HERE/'warm_trust_v2.py'):
   matches=[]
   for commit in a.prior_warm_producer:
    assert W['re'].fullmatch('[0-9a-f]{40}',commit)
    blob=subprocess.check_output(['git','show',commit+':docs/audits/direction-tools/declgraph/warm_trust_v2.py'],cwd=HERE.parents[3])
    if hashlib.sha256(blob).hexdigest()==d['producers']['warm_trust_v2.py']:matches.append(commit)
   assert len(matches)==1,'Explicit exact historical warm producer required'
   cmd+=['--capture-producer-commit',matches[0]]
  subprocess.run(cmd,check=True)
  assert SHA(path)==before and SHA(log)==before_log
  validated[str(path)]=before;validated[str(log)]=before_log
 with Q['writer_lease']():
  for protected in (a.source_root,a.view,HERE):
   assert not a.capture.is_relative_to(protected) and not protected.is_relative_to(a.capture),'Capture overlaps source/view/code'
  assert all(SHA(pathlib.Path(p))==h for p,h in validated.items())
  API['assert_sources'](a.source_root);v1=(a.source_root/'TrustAudit.lean').read_bytes();v2=T['TARGET'].read_bytes();T['verify'](v1,v2)
  target=a.source_root/'docs/audits/direction-tools/declgraph/v2/TrustAuditV2.lean';assert target.read_bytes()==v2
  version=subprocess.check_output(['lean','--version'],text=True).strip();assert 'version 4.24.0,' in version and '797c613' in version
  cmd=['lean','--tstack=131072','-j1','-M10000',str(target)];producers={n:SHA(HERE/n) for n in ('run_trust_v2.py','trust_audit_v2.py','warm_trust_v2.py','audit.py')};inputs={};attempts=[]
  for path in a.attempt:
   path=path.resolve();d=json.loads(path.read_text());assert d['base']==API['BASE'] and d['timeout_seconds']==600 and d['module']==W['MODULE']
   assert d['source_sha256']==SHA(a.source_root/pathlib.Path(W['MODULE'].replace('.','/')).with_suffix('.lean'))
   log=path.parent/'capture.log';assert SHA(log)==d['log_sha256'];W['verify_products'](pathlib.Path(d['output_view']),d['exit_code'],d['products'])
   inputs[str(path)]=SHA(path);inputs[str(log)]=SHA(log);attempts.append(dict(exit_code=d['exit_code'],timeout_seconds=600,synchronous='-DElab.async=false' in d['command']))
  fixed=dict(base=API['BASE'],command=cmd,source_root=str(a.source_root),view=str(a.view),lean=version,v1_sha256=hashlib.sha256(v1).hexdigest(),v2_sha256=hashlib.sha256(v2).hexdigest(),producers=producers,inputs=inputs)
  receipt=a.capture/'receipt.json';log=a.capture/'capture.log'
  if a.check:
   d=json.loads(receipt.read_text());assert all(d[k]==v for k,v in fixed.items()) and d['log_sha256']==SHA(log)
  else:
   assert not a.capture.exists();a.capture.mkdir(parents=True);start=time.monotonic()
   with log.open('w') as output:
    try:x=subprocess.run(cmd,cwd=a.source_root,env=dict(os.environ,LEAN_PATH=str(a.view),LEAN_NUM_THREADS='1'),stdout=output,stderr=subprocess.STDOUT,timeout=600);code=x.returncode
    except subprocess.TimeoutExpired:code=124;output.write('TRUST_V2_AUDIT_TIMEOUT600\n')
   d=dict(fixed,exit_code=code,seconds=time.monotonic()-start,log_sha256=SHA(log));Q['atomic_json'](receipt,d)
  text=log.read_text();missing="RowsNine.olean' of module Solidity.Examples.Tactics.OpenLoops.RowsNine does not exist" in text
  result=dict(base=API['BASE'],version='additive-v2',source='v2/TrustAuditV2.lean',status='pass' if d['exit_code']==0 else 'blocked',v1_byte_projection_preserved=True,original_import_order_preserved=True,v1_modified=False,dependency_attempts=attempts,audit_exit_code=d['exit_code'],missing_dependency_artifact=missing,owner_review='pending',adopted_for_deletion_verification=False,deletable_now_verified_lines=0,boundaries=['V2 is exactly one child import inserted after its original parent; removing it recovers every frozen v1 byte.','The original v1 failure remains a finding; v1 is never repaired or repinned here.','Failed dependency checks or missing artifacts cannot count as a successful audit.','Owner review and complete affected-root checks remain required before adoption or deletion certification.','Derived cache contents are externally trusted; this result does not attest source-to-artifact provenance.'])
  assert producers=={n:SHA(HERE/n) for n in producers};assert all(SHA(pathlib.Path(p))==h for p,h in inputs.items());API['assert_sources'](a.source_root);T['verify'](v1,T['TARGET'].read_bytes());assert target.read_bytes()==v2
  body=json.dumps(result,sort_keys=True,indent=2)+'\n'
  if a.check:assert a.out.read_text()==body,'Stale v2 result'
  else:Q['atomic_text'](a.out,body)
  print('TRUST_V2_AUDIT_RESULT',result['status'],d['exit_code'])
if __name__=='__main__':main()
