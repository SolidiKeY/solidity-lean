#!/usr/bin/env python3
"""Warm the unchanged RowsNine dependency for additive TrustAudit v2.
Serial bounded Lean; preserve the pinned600s slow-example budget. All products,
logs and receipts belong outside the code directory. No production source edits.
"""
if not __debug__: raise SystemExit('OPTIMIZED_PYTHON_UNSUPPORTED')
import argparse,hashlib,json,re,os,pathlib,runpy,subprocess,time
HERE=pathlib.Path(__file__).resolve().parent
Q=runpy.run_path(str(HERE/'capture_cached_checks.py'));API=Q['API'];SHA=Q['SHA'];W=runpy.run_path(str(HERE/'warm_checks.py'))
N=runpy.run_path(str(HERE/'owned_native.py'))
MODULE='Solidity.Examples.Tactics.OpenLoops.RowsNine'
def safe_paths(source,view,out,logs,*,creation=True):
 source,view,out,logs=(pathlib.Path(x).resolve() for x in (source,view,out,logs))
 if creation:
  for product in (out,logs):
   for protected in (source,HERE.parents[3]):
    assert not product.is_relative_to(protected) and not protected.is_relative_to(product),'New artifacts/evidence overlap frozen source or checkout'
 for protected in (source,view,out):
  assert not logs.is_relative_to(protected) and not protected.is_relative_to(logs),'Log directory overlaps source/artifact trees'
 assert view!=out and not out.is_relative_to(view) and not view.is_relative_to(out),'Input/output view overlap'

def verify_products(view,code,products):
 rel=pathlib.Path(MODULE.replace('.','/'))
 if code==0:
  expected={str(view/rel.with_suffix(s)) for s in ('.olean','.ilean')}
  assert set(products)==expected,'Successful capture requires exactly both artifacts'
  assert all(pathlib.Path(p).is_file() and SHA(pathlib.Path(p))==h for p,h in products.items())
  assert json.loads((view/rel.with_suffix('.ilean')).read_text())['module']==MODULE
 else:
  assert products=={},'Failed capture cannot publish products'
  assert all(not (view/rel.with_suffix(s)).exists() for s in ('.olean','.ilean','.olean.server','.olean.private')),'Failed artifacts remain live'

def main():
 p=argparse.ArgumentParser();p.add_argument('--source-root',type=pathlib.Path,required=True);p.add_argument('--view',type=pathlib.Path,required=True);p.add_argument('--out-view',type=pathlib.Path,required=True);p.add_argument('--logs',type=pathlib.Path,required=True);p.add_argument('--check',action='store_true');p.add_argument('--capture-producer-commit');p.add_argument('--synchronous',action='store_true');a=p.parse_args()
 for n in ('source_root','view','out_view','logs'):setattr(a,n,getattr(a,n).resolve())
 with Q['writer_lease']() as lease:
  safe_paths(a.source_root,a.view,a.out_view,a.logs,creation=not a.check)
  API['assert_sources'](a.source_root);assert a.view.is_dir() and a.view!=a.out_view and not a.out_view.is_relative_to(a.view)
  version=subprocess.check_output(['lean','--version'],text=True).strip();assert 'version 4.24.0,' in version and '797c613' in version
  source=a.source_root/pathlib.Path(MODULE.replace('.','/')).with_suffix('.lean');cmd=W['build_command'](a,MODULE)
  if a.synchronous:cmd.insert(1,'-DElab.async=false')
  receipt=a.logs/'receipt.json';log=a.logs/'capture.log';producers={n:SHA(HERE/n) for n in ('warm_trust_v2.py','warm_checks.py','audit.py','capture_cached_checks.py','owned_native.py')}
  if a.capture_producer_commit:
   assert a.check and re.fullmatch('[0-9a-f]{40}',a.capture_producer_commit)
   subprocess.run(['git','merge-base','--is-ancestor',a.capture_producer_commit,'HEAD'],cwd=HERE.parents[3],check=True)
   blob=subprocess.check_output(['git','show',a.capture_producer_commit+':docs/audits/direction-tools/declgraph/warm_trust_v2.py'],cwd=HERE.parents[3])
   producers['warm_trust_v2.py']=hashlib.sha256(blob).hexdigest()
   # Prior receipts predate lease-aware execution; read-only verification does not retrofit that property.
   if b"owned_native.py" not in blob:producers.pop('owned_native.py')
  actual_producer=SHA(HERE/'warm_trust_v2.py')
  fixed=dict(base=API['BASE'],module=MODULE,command=cmd,source_sha256=SHA(source),source_root=str(a.source_root),input_view=str(a.view),output_view=str(a.out_view),lean=version,producers=producers,timeout_seconds=600)
  if a.check:
   d=json.loads(receipt.read_text());assert all(d[k]==v for k,v in fixed.items());assert d['log_sha256']==SHA(log)
  else:
   assert not a.out_view.exists() and not a.logs.exists(),'Fresh view/log directory required'
   a.out_view.mkdir(parents=True);a.logs.mkdir(parents=True)
   for f in a.view.rglob('*'):
    if f.is_file():
     to=a.out_view/f.relative_to(a.view);to.parent.mkdir(parents=True,exist_ok=True);os.link(f,to)
   rel=pathlib.Path(MODULE.replace('.','/'));(a.out_view/rel).parent.mkdir(parents=True,exist_ok=True)
   assert all(not (a.out_view/rel.with_suffix(s)).exists() for s in ('.olean','.ilean','.olean.server','.olean.private'))
   started=time.monotonic()
   with log.open('w') as output:
    code=N['run'](cmd,output,cwd=a.source_root,env=dict(os.environ,LEAN_PATH=str(a.out_view),LEAN_NUM_THREADS='1'),lease=lease,timeout=600)
   products={}
   if code==0:
    for suffix in ('.olean','.ilean'):
     f=a.out_view/rel.with_suffix(suffix);assert f.is_file();products[str(f)]=SHA(f)
    assert json.loads((a.out_view/rel.with_suffix('.ilean')).read_text())['module']==MODULE
   else:W['quarantine'](a.out_view,a.logs,MODULE)
   d=dict(fixed,exit_code=code,seconds=time.monotonic()-started,log_sha256=SHA(log),products=products);Q['atomic_json'](receipt,d)
  for f in a.view.rglob('*'):
   if f.is_file():assert os.path.samefile(f,a.out_view/f.relative_to(a.view)),'Input link changed'
  verify_products(a.out_view,d['exit_code'],d['products'])
  assert SHA(HERE/'warm_trust_v2.py')==actual_producer
  assert all(SHA(HERE/n)==h for n,h in producers.items() if n!='warm_trust_v2.py');API['assert_sources'](a.source_root)
  print('TRUST_V2_ROWS_'+('PASS' if d['exit_code']==0 else 'FAIL'),d['exit_code'])
if __name__=='__main__':main()
