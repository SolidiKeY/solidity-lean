#!/usr/bin/env python3
"""Owner R1/R2/R4 refusal controls; no native Lean and no source mutations."""
import pathlib,runpy,subprocess,sys,tempfile
HERE=pathlib.Path(__file__).resolve().parent
R=runpy.run_path(str(HERE/'run_trust_v2.py'));W=runpy.run_path(str(HERE/'warm_trust_v2.py'))
def reject(fn):
 try:fn()
 except AssertionError:return
 raise AssertionError('Unsafe destination accepted')
def main():
 with tempfile.TemporaryDirectory() as directory:
  root=pathlib.Path(directory);source=root/'source';source.mkdir();view=root/'view';capture=root/'capture';logs=root/'logs';out=HERE/'trust-v2-summary.json';receipt=root/'attempt/receipt.json'
  protected=source/'TrustAudit.lean';protected.write_bytes(b'frozen fixture bytes\n');before=protected.read_bytes()
  R['safe_destinations'](source,view,capture,out,[receipt])
  for bad in (protected,receipt,root/'attempt/capture.log',view/'result.json',capture/'receipt.json',HERE/'run_trust_v2.py'):
   reject(lambda:R['safe_destinations'](source,view,capture,bad,[receipt]))
  for bad in (source/'new',view/'new',HERE/'new',HERE.parents[3]/'.lake/new'):
   reject(lambda:R['safe_destinations'](source,view,bad,out,[receipt]))
  W['safe_paths'](source,view,root/'products',logs)
  for bad in (source/'new-cache',HERE/'new-cache',HERE.parents[3]/'.lake/new-cache'):
   reject(lambda:W['safe_paths'](source,view,bad,logs))
  for bad in (source/'new-logs',HERE/'new-logs',HERE.parents[3]/'.lake/new-logs'):
   reject(lambda:W['safe_paths'](source,view,root/'products',bad))
  alias=root/'alias';alias.symlink_to(source,target_is_directory=True)
  reject(lambda:W['safe_paths'](source,view,alias/'new-cache',logs))
  reject(lambda:W['safe_paths'](source,view,root/'products',alias/'new-logs'))
  receipt.parent.mkdir();(receipt.parent/'capture.log').symlink_to(out)
  reject(lambda:R['safe_destinations'](source,view,capture,out,[receipt]))
  # Actual CLI must refuse BEFORE opening source inventory, attempts or captures.
  cmd=[sys.executable,'-I','-B',str(HERE/'run_trust_v2.py'),'--source-root',str(source),'--view',str(view),'--capture',str(capture),'--attempt',str(receipt),'--out',str(protected)]
  x=subprocess.run(cmd,text=True,capture_output=True);assert x.returncode!=0 and 'Only the designated checker summary' in x.stderr
  assert protected.read_bytes()==before and not capture.exists() and not receipt.exists()
 for name in ('trust_audit_v2.py','warm_trust_v2.py','run_trust_v2.py','owned_native.py','lease_lifecycle.py'):
  x=subprocess.run([sys.executable,'-I','-B','-O',str(HERE/name)],text=True,capture_output=True)
  assert x.returncode!=0 and 'OPTIMIZED_PYTHON_UNSUPPORTED' in x.stderr
 x=subprocess.run([sys.executable,'-I','-B','-O','-c',"import runpy; runpy.run_path("+repr(str(HERE/'trust_audit_v2.py'))+")['verify'](b'unrelated',b'invalid')"],text=True,capture_output=True)
 assert x.returncode!=0 and 'OPTIMIZED_PYTHON_UNSUPPORTED' in x.stderr
 print('TRUST_V2_INTEGRITY_PASS protected_output source_checkout_paths aliases before_mutation optimized_refusal')
if __name__=='__main__':main()
