#!/usr/bin/env python3
"""R5 private fixtures: mocked inventory/version/native outcome, no Lean.
Exercise real warm main, quarantine and post-publication refusal controls.
"""
import contextlib,fcntl,hashlib,json,os,signal,pathlib,runpy,sys,tempfile
HERE=pathlib.Path(__file__).resolve().parent;M=runpy.run_path(str(HERE/'warm_trust_v2.py'));G=M['main'].__globals__
def main():
 original_api=G['API']['assert_sources'];original_check=G['subprocess'].check_output;original_run=G['N']['run'];original_verify=G['verify_products'];original_quarantine=G['N']['L']['quarantine'];original_atomic=G['Q']['atomic_json'];original_sleep=G['time'].sleep;argv=sys.argv[:]
 with tempfile.TemporaryDirectory() as directory:
  root=pathlib.Path(directory);source=root/'source';view=root/'view';view.mkdir();(view/'Preserved.olean').write_bytes(b'input remains unchanged');relative=pathlib.Path(G['MODULE'].replace('.','/'));src=source/relative.with_suffix('.lean');src.parent.mkdir(parents=True);src.write_text('-- fixture only, never Lean executed\n');before={src:src.read_bytes(),view/'Preserved.olean':b'input remains unchanged'}
  G['API']['assert_sources']=lambda _:{};G['subprocess'].check_output=lambda *a,**k:'Lean (version 4.24.0, commit 797c613)'
  def setup(label):
   out=root/(label+'-products');logs=root/(label+'-logs');sys.argv=['warm_trust_v2.py','--source-root',str(source),'--view',str(view),'--out-view',str(out),'--logs',str(logs)];return out,logs
  def products(out,logs):
   values={}
   for suffix in ('.olean','.ilean','.olean.server','.olean.private'):
    f=out/relative.with_suffix(suffix);f.parent.mkdir(parents=True,exist_ok=True);body=json.dumps({'module':G['MODULE']}).encode() if suffix=='.ilean' else ('fixture'+suffix).encode();f.write_bytes(body);values[str(relative.with_suffix(suffix))]=body
   (logs/'receipt.json').write_bytes(b'partial fixture receipt');return values
  try:
   out,logs=setup('cancelled');expected={};interrupted=InterruptedError('fixture interruption after artifact write')
   def cancel(*a,**kw):
    assert kw['timeout']==600 and kw['cleanup_spec']['module']==G['MODULE'];expected.update(products(out,logs));raise interrupted
   G['N']['run']=cancel
   try:G['main']()
   except InterruptedError as exc:assert exc is interrupted
   else:raise AssertionError('Cancellation emitted success')
   assert not (logs/'receipt.json').exists()
   for relative_name,body in expected.items():
    assert not (out/relative_name).exists();matches=list(logs.glob('quarantine-exception-*/'+relative_name));assert len(matches)==1 and matches[0].read_bytes()==body
   assert list(logs.glob('quarantine-exception-*/receipt.json'))[0].read_bytes()==b'partial fixture receipt'
   out,logs=setup('post-publication');expected={}
   def success(*a,**kw):expected.update(products(out,logs));return 0
   def reject_products(*a,**kw):raise AssertionError('fixture post-publication integrity failure')
   G['N']['run']=success;G['verify_products']=reject_products
   try:G['main']()
   except AssertionError as exc:assert 'post-publication' in str(exc)
   else:raise AssertionError('Invalid published products accepted')
   assert not (logs/'receipt.json').exists() and list(logs.glob('quarantine-exception-*/receipt.json'))
   assert all(not (out/name).exists() for name in expected)
   G['verify_products']=original_verify;out,logs=setup('quarantine-failure');interrupted=InterruptedError('original exception preserved')
   def fail_move(*a,**kw):os.kill(os.getpid(),signal.SIGTERM);raise OSError('fixture quarantine failure')
   G['N']['run']=cancel;G['N']['L']['quarantine']=fail_move
   try:G['main']()
   except InterruptedError as exc:assert exc is interrupted and any('quarantine failed' in n for n in exc.__notes__)
   else:raise AssertionError('Cleanup error masked original')
   assert (logs/'quarantine-failed.json').exists();files={f:f.read_bytes() for base in (out,logs) for f in base.rglob('*') if f.is_file()}
   sys.argv.append('--check')
   try:G['main']()
   except AssertionError as exc:assert 'Unresolved interrupted-product cleanup' in str(exc)
   else:raise AssertionError('Unresolved cleanup receipt consumed')
   assert all(f.read_bytes()==b for f,b in files.items()) and all(f.read_bytes()==b for f,b in before.items())
   out,logs=setup('quarantine-and-marker-failure');attempts=[];interrupted=InterruptedError('double failure retains lease')
   def marker_fails_twice(path,data):
    with open(G['Q']['LOCK'],'a') as competitor:
     try:fcntl.flock(competitor,fcntl.LOCK_EX|fcntl.LOCK_NB)
     except BlockingIOError:pass
     else:raise AssertionError('Lease released before durable rejection')
    attempts.append(True)
    if len(attempts)<3:os.kill(os.getpid(),signal.SIGINT);raise OSError('fixture marker temporarily unavailable')
    return original_atomic(path,data)
   sleeps=[]
   def interrupted_delay(seconds):
    if seconds==.05:sleeps.append(True);raise KeyboardInterrupt('fixture interruption during retry delay')
    return original_sleep(seconds)
   G['time'].sleep=interrupted_delay;G['Q']['atomic_json']=marker_fails_twice
   try:G['main']()
   except InterruptedError as exc:assert exc is interrupted
   else:raise AssertionError('Double cleanup failure emitted success')
   assert len(attempts)==3 and len(sleeps)==2 and (logs/'quarantine-failed.json').exists()

  finally:
   G['API']['assert_sources']=original_api;G['subprocess'].check_output=original_check;G['N']['run']=original_run;G['verify_products']=original_verify;G['N']['L']['quarantine']=original_quarantine;G['Q']['atomic_json']=original_atomic;G['time'].sleep=original_sleep;sys.argv=argv
 print('WARM_INTERRUPTION_PASS four_artifacts receipt bytes_preserved original_exception post_publication double_cleanup_failure_retains_lease term_int_retry_delay_cancellation read_only_refusal input_unchanged fixture_only_no_Lean')
if __name__=='__main__':main()
