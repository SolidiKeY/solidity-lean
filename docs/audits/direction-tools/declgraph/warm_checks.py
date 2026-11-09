#!/usr/bin/env python3
"""Recover only three named missing check modules from validated warm imports.
Use the repository writer lock, pinned Lean on PATH and no concurrent heavy job.
No library build or production source write occurs. Logs/receipts stay outside
this code directory; the small result reports build outcomes, not root liveness.
"""
import argparse,hashlib,json,os,pathlib,runpy,subprocess,time
HERE=pathlib.Path(__file__).resolve().parent
TARGETS=['Solidity.Examples.DecisionGaps','Solidity.Examples.Tactics.OpenLoops','Solidity.Examples.Tactics.RevertData']
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def main():
 p=argparse.ArgumentParser();p.add_argument('--source-root',type=pathlib.Path,required=True);p.add_argument('--view',type=pathlib.Path,required=True);p.add_argument('--out-view',type=pathlib.Path,required=True);p.add_argument('--logs',type=pathlib.Path,required=True);p.add_argument('--summary',type=pathlib.Path,required=True);a=p.parse_args()
 api=runpy.run_path(str(HERE/'audit.py'));api['assert_sources'](a.source_root)
 a.source_root=a.source_root.resolve();a.view=a.view.resolve();a.out_view=a.out_view.resolve();a.logs=a.logs.resolve()
 assert a.view.is_dir() and not a.out_view.exists(),'Fresh output view required'
 version=subprocess.check_output(['lean','--version'],text=True).strip();assert 'version 4.24.0,' in version and '797c613' in version
 a.out_view.mkdir(parents=True);a.logs.mkdir(parents=True,exist_ok=True)
 for src in sorted(a.view.rglob('*')):
  if src.is_file():
   dst=a.out_view/src.relative_to(a.view);dst.parent.mkdir(parents=True,exist_ok=True);os.link(src,dst)
 env=dict(os.environ,LEAN_PATH=str(a.out_view),LEAN_NUM_THREADS='1');rows=[];receipts=[]
 for module in TARGETS:
  relative=pathlib.Path(module.replace('.','/'));source=a.source_root/relative.with_suffix('.lean');olean=a.out_view/relative.with_suffix('.olean');ilean=a.out_view/relative.with_suffix('.ilean');assert not olean.exists() and not ilean.exists(),'Target already in cache view'
  olean.parent.mkdir(parents=True,exist_ok=True);cmd=['lean','--tstack=131072','-j1','-M10000','--root='+str(a.source_root),'-o',str(olean),'-i',str(ilean),str(source)];started=time.monotonic()
  try:
   result=subprocess.run(cmd,cwd=a.source_root,env=env,text=True,capture_output=True,timeout=600);code=result.returncode;output=result.stdout+result.stderr
  except subprocess.TimeoutExpired as e:
   code=124;output='WARM_CHECK_TIMEOUT600\n'+str(e.stdout or '')+str(e.stderr or '')
  status='pass' if code==0 and olean.is_file() and ilean.is_file() else 'fail';log=a.logs/(module+'.log');log.write_text(output)
  rows.append(dict(module=module,source=str(relative.with_suffix('.lean')),source_sha256=sha(source),status=status,exit_code=code))
  receipts.append(dict(module=module,command=cmd,seconds=time.monotonic()-started,log=str(log),olean_sha256=sha(olean) if olean.is_file() else None,ilean_sha256=sha(ilean) if ilean.is_file() else None));print('WARM_CHECK_'+status.upper(),module,flush=True)
 data=dict(base=api['BASE'],lean=version,targets=rows,recovered_modules=sum(r['status']=='pass' for r in rows),boundaries=['Only these three modules are compiled individually against a warm import view.','Successful compilation recovers artifacts; it does not recover discarded check roots or certify deletion.'])
 a.summary.write_text(json.dumps(data,indent=2,sort_keys=True)+'\n');(a.logs/'receipt.json').write_text(json.dumps(dict(producer_sha256=sha(HERE/'warm_checks.py'),source_root=str(a.source_root),input_view=str(a.view),output_view=str(a.out_view),builds=receipts),indent=2)+'\n')
 print('WARM_CHECK_SUMMARY',data['recovered_modules'],len(rows))
if __name__=='__main__':main()
