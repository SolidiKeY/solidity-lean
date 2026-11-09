#!/usr/bin/env python3
"""Recover only three named missing check modules from validated warm imports.
Use the repository writer lock, pinned Lean on PATH and no concurrent heavy job.
No library build or production source write occurs. Logs/receipts stay outside
this code directory; the small result reports build outcomes, not root liveness.
"""
import argparse,hashlib,json,os,pathlib,re,runpy,shutil,subprocess,time
HERE=pathlib.Path(__file__).resolve().parent
TARGETS=['Solidity.Examples.DecisionGaps','Solidity.Examples.Tactics.OpenLoops','Solidity.Examples.Tactics.RevertData']
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def quarantine(view,logs,module):
 relative=pathlib.Path(module.replace('.','/'))
 for suffix in ('.olean','.ilean','.olean.server','.olean.private'):
  source=view/relative.with_suffix(suffix)
  if source.exists():
   target=logs/'quarantine'/relative.with_suffix(suffix);target.parent.mkdir(parents=True,exist_ok=True)
   assert not target.exists(),'Quarantine destination already exists'
   shutil.move(str(source),str(target))

def build_command(a,module):
 relative=pathlib.Path(module.replace('.','/'))
 return ['lean','--tstack=131072','-j1','-M10000','--root='+str(a.source_root),'-o',str(a.out_view/relative.with_suffix('.olean')),'-i',str(a.out_view/relative.with_suffix('.ilean')),str(a.source_root/relative.with_suffix('.lean'))]

def verify_recovery(a,api,version):
 """Reuse actual checks bound to an immutable original producer/data commit."""
 assert a.producer_commit and re.fullmatch('[0-9a-f]{40}',a.producer_commit)
 receipt=json.loads(a.verify_receipt.read_text());root=HERE.parents[3];scope=HERE.relative_to(root)
 def committed(name):return subprocess.check_output(['git','show',a.producer_commit+':'+str(scope/name)],cwd=root)
 assert hashlib.sha256(committed('warm_checks.py')).hexdigest()==receipt['producer_sha256'],'Original producer differs'
 assert committed('warm-check-summary.json')==a.summary.read_bytes(),'Original result differs'
 assert pathlib.Path(receipt['source_root']).resolve()==a.source_root
 assert pathlib.Path(receipt['input_view']).resolve()==a.view and pathlib.Path(receipt['output_view']).resolve()==a.out_view
 data=json.loads(a.summary.read_text());assert data['base']==api['BASE'] and data['lean']==version
 assert [r['module'] for r in data['targets']]==TARGETS
 assert [r['module'] for r in receipt['builds']]==TARGETS
 assert data['recovered_modules']==sum(row['status']=='pass' for row in data['targets'])
 # The original input view is prepared/validated externally by prepare.py;
 # this verifies its unchanged hardlink identity in the derived consumer view.
 for source in a.view.rglob('*'):
  if source.is_file():assert os.path.samefile(source,a.out_view/source.relative_to(a.view)),'Input link changed'
 for row,built in zip(data['targets'],receipt['builds']):
  module=row['module'];relative=pathlib.Path(module.replace('.','/'));source=a.source_root/relative.with_suffix('.lean')
  assert row['source']==str(relative.with_suffix('.lean')) and row['source_sha256']==sha(source)
  assert built['command']==build_command(a,module),'Build flags or target paths differ'
  if row['status']=='pass':
   assert row['exit_code']==0
   for suffix in ('olean','ilean'):
    artifact=a.out_view/relative.with_suffix('.'+suffix);assert artifact.is_file() and sha(artifact)==built[suffix+'_sha256'],'Recovered artifact differs'
   assert json.loads((a.out_view/relative.with_suffix('.ilean')).read_text())['module']==module
  else:
   assert row['status']=='fail'
   assert all(not (a.out_view/relative.with_suffix(suffix)).exists() for suffix in ('.olean','.ilean','.olean.server','.olean.private')),'Failed target products must already be quarantined'
 api['assert_sources'](a.source_root)
 print('WARM_RECOVERY_VERIFIED',data['recovered_modules'],len(TARGETS))

def main():
 p=argparse.ArgumentParser();p.add_argument('--source-root',type=pathlib.Path,required=True);p.add_argument('--view',type=pathlib.Path,required=True);p.add_argument('--out-view',type=pathlib.Path,required=True);p.add_argument('--logs',type=pathlib.Path,required=True);p.add_argument('--summary',type=pathlib.Path,required=True);p.add_argument('--verify-receipt',type=pathlib.Path);p.add_argument('--producer-commit');a=p.parse_args();producer_start=sha(HERE/'warm_checks.py')
 api=runpy.run_path(str(HERE/'audit.py'));api['assert_sources'](a.source_root)
 a.source_root=a.source_root.resolve();a.view=a.view.resolve();a.out_view=a.out_view.resolve();a.logs=a.logs.resolve()
 assert a.view.is_dir() and not a.out_view.is_relative_to(a.view),'Output view must be outside input view'
 version=subprocess.check_output(['lean','--version'],text=True).strip();assert 'version 4.24.0,' in version and '797c613' in version
 if a.verify_receipt:
  verify_recovery(a,api,version);assert sha(HERE/'warm_checks.py')==producer_start,'Producer changed during verification';return
 assert not a.out_view.exists(),'Fresh output view required'
 a.out_view.mkdir(parents=True);a.logs.mkdir(parents=True,exist_ok=True)
 for src in sorted(a.view.rglob('*')):
  if src.is_file():
   dst=a.out_view/src.relative_to(a.view);dst.parent.mkdir(parents=True,exist_ok=True);os.link(src,dst)
 env=dict(os.environ,LEAN_PATH=str(a.out_view),LEAN_NUM_THREADS='1');rows=[];receipts=[]
 for module in TARGETS:
  relative=pathlib.Path(module.replace('.','/'));source=a.source_root/relative.with_suffix('.lean');olean=a.out_view/relative.with_suffix('.olean');ilean=a.out_view/relative.with_suffix('.ilean');assert not olean.exists() and not ilean.exists(),'Target already in cache view'
  olean.parent.mkdir(parents=True,exist_ok=True);cmd=build_command(a,module);started=time.monotonic()
  try:
   result=subprocess.run(cmd,cwd=a.source_root,env=env,text=True,capture_output=True,timeout=600);code=result.returncode;output=result.stdout+result.stderr
  except subprocess.TimeoutExpired as e:
   code=124;output='WARM_CHECK_TIMEOUT600\n'+str(e.stdout or '')+str(e.stderr or '')
  status='pass' if code==0 and olean.is_file() and ilean.is_file() else 'fail';log=a.logs/(module+'.log');log.write_text(output)
  if status=='fail':quarantine(a.out_view,a.logs,module)
  rows.append(dict(module=module,source=str(relative.with_suffix('.lean')),source_sha256=sha(source),status=status,exit_code=code))
  receipts.append(dict(module=module,command=cmd,seconds=time.monotonic()-started,log=str(log),olean_sha256=sha(olean) if olean.is_file() else None,ilean_sha256=sha(ilean) if ilean.is_file() else None));print('WARM_CHECK_'+status.upper(),module,flush=True)
 assert sha(HERE/'warm_checks.py')==producer_start,'Producer changed during checks'
 api['assert_sources'](a.source_root)
 data=dict(base=api['BASE'],lean=version,targets=rows,recovered_modules=sum(r['status']=='pass' for r in rows),boundaries=['Only these three modules are compiled individually against a warm import view.','The input view must already be source/dependency-validated by prepare.py; this helper trusts that preparation.', 'Failed target products are quarantined before consumer reuse.', 'Successful compilation recovers artifacts; it does not recover discarded check roots or certify deletion.'])
 a.summary.write_text(json.dumps(data,indent=2,sort_keys=True)+'\n');(a.logs/'receipt.json').write_text(json.dumps(dict(producer_sha256=producer_start,source_root=str(a.source_root),input_view=str(a.view),output_view=str(a.out_view),builds=receipts),indent=2)+'\n')
 print('WARM_CHECK_SUMMARY',data['recovered_modules'],len(rows))
if __name__=='__main__':main()
