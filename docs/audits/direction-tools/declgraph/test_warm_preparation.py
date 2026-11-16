#!/usr/bin/env python3
"""Actual warm-main preparation refusal controls; no native invocation."""
import os,pathlib,runpy,sys,tempfile
HERE=pathlib.Path(__file__).resolve().parent
G=runpy.run_path(str(HERE/'warm_trust_v2.py'))['main'].__globals__
def main():
 saved=(G['API']['assert_sources'],G['subprocess'].check_output,G['N']['run'],G['N']['L']['quarantine'],os.link,sys.argv[:])
 native=[];cleanups=[]
 def forbidden(*a,**k):native.append(True);raise AssertionError('Native invocation forbidden in preparation fixtures')
 G['API']['assert_sources']=lambda _:{}
 G['subprocess'].check_output=lambda *a,**k:'Lean (version 4.24.0, commit 797c613)'
 G['N']['run']=forbidden
 original_quarantine=G['N']['L']['quarantine']
 def quarantine(spec):cleanups.append(dict(spec));return original_quarantine(spec)
 G['N']['L']['quarantine']=quarantine
 try:
  with tempfile.TemporaryDirectory() as directory:
   root=pathlib.Path(directory);source=root/'source';relative=pathlib.Path(G['MODULE'].replace('.','/'));src=source/relative.with_suffix('.lean');src.parent.mkdir(parents=True);src.write_bytes(b'-- fixture source only\n')
   def setup(label):
    view=root/(label+'-input');view.mkdir();out=root/(label+'-output');logs=root/(label+'-logs')
    sys.argv=['warm_trust_v2.py','--source-root',str(source),'--view',str(view),'--out-view',str(out),'--logs',str(logs)]
    return view,out,logs
   for index,suffix in enumerate(('.olean','.ilean','.olean.server','.olean.private')):
    view,out,logs=setup('target-'+str(index));target=view/relative.with_suffix(suffix);target.parent.mkdir(parents=True);target.write_bytes(b'protected input target');before=target.read_bytes();count=len(cleanups)
    try:G['main']()
    except AssertionError as exc:assert 'Input view already contains target artifact' in str(exc)
    else:raise AssertionError('Existing target accepted')
    assert not out.exists() and not logs.exists() and target.read_bytes()==before and len(cleanups)==count
   view,out,logs=setup('copy-failure');a=view/'A.olean';b=view/'B.olean';a.write_bytes(b'first input');b.write_bytes(b'second input');before={a:a.read_bytes(),b:b.read_bytes(),src:src.read_bytes()};links=[];error=OSError('injected second-copy failure');count=len(cleanups)
   def broken_link(source_path,target_path,*args,**kwargs):
    links.append((source_path,target_path))
    if len(links)==2:raise error
    return saved[4](source_path,target_path,*args,**kwargs)
   os.link=broken_link
   try:G['main']()
   except OSError as exc:assert exc is error
   else:raise AssertionError('Copy failure emitted success')
   finally:os.link=saved[4]
   assert len(links)==2 and len(cleanups)==count+1
   assert not (logs/'receipt.json').exists() and not (out/relative.with_suffix('.olean')).exists()
   assert os.path.samefile(links[0][0],links[0][1])
   assert all(f.read_bytes()==body for f,body in before.items()) and not native
 finally:
  G['API']['assert_sources'],G['subprocess'].check_output,G['N']['run'],G['N']['L']['quarantine'],os.link,sys.argv=saved
 print('WARM_PREPARATION_PASS four_target_suffixes_refused_before_mutation copy_failure_cleanup_armed input_hardlinks_preserved original_exception no_native')
if __name__=='__main__':main()
