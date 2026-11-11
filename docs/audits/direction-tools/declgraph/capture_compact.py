#!/usr/bin/env python3
"""One source's input-bound compact native root capture; serial warm imports.
The default legacy validator is reused after lossless record expansion.
"""
import argparse,hashlib,json,os,pathlib,runpy,subprocess
HERE=pathlib.Path(__file__).resolve().parent
API=runpy.run_path(str(HERE/'audit.py'));SHA=runpy.run_path(str(HERE/'module_graph.py'))['sha'];C=runpy.run_path(str(HERE/'compact_records.py'))
def main():
 p=argparse.ArgumentParser();p.add_argument('--source-root',type=pathlib.Path,required=True);p.add_argument('--view',type=pathlib.Path,required=True);p.add_argument('--capture',type=pathlib.Path,required=True);p.add_argument('--file',required=True);p.add_argument('--out',type=pathlib.Path,required=True);p.add_argument('--check',action='store_true');a=p.parse_args()
 for k in ('source_root','view','capture','out'):setattr(a,k,getattr(a,k).resolve())
 sources=API['assert_sources'](a.source_root);assert a.file in sources
 names=('CompactRoots.lean','compact_records.py','run_snapshot_roots.py','audit.py','modules.txt','capture_compact.py');producers={n:SHA(HERE/n) for n in names}
 source=a.source_root/a.file;ilean=a.view/pathlib.Path(a.file).with_suffix('.ilean');module=json.loads(ilean.read_text())['module'];gr=HERE.parents[3]/'.lake/refactor-cache/declgraph-module-native.jsonl.receipt.json';graph_receipt=json.loads(gr.read_text());assert pathlib.Path(graph_receipt['reference_view']).resolve()==a.view and graph_receipt['modules_sha256']==SHA(HERE/'modules.txt')
 version=subprocess.check_output(['lean','--version'],text=True).strip();assert 'version 4.24.0,' in version and '797c613' in version
 cmd=['lean','--tstack=131072','-j1','-M10000','--run',str(HERE/'CompactRoots.lean'),str(source),module,str(HERE/'modules.txt'),str(a.capture/'roots.jsonl')];fixed=dict(producers=producers,command=cmd,lean=version,source_sha256=SHA(source),module=module,view=str(a.view),graph_receipt_sha256=SHA(gr));receipt=a.capture/'receipt.json'
 if a.check:
  meta=json.loads(receipt.read_text());assert all(meta[k]==v for k,v in fixed.items()) and meta['exit_code']==0
  for n in ('roots.jsonl','capture.log'):assert meta['outputs'][n]==SHA(a.capture/n)
 else:
  assert not a.capture.exists();a.capture.mkdir(parents=True)
  with (a.capture/'capture.log').open('w') as log:x=subprocess.run(cmd,env=dict(os.environ,LEAN_PATH=str(a.view),LEAN_NUM_THREADS='1'),stdout=log,stderr=subprocess.STDOUT,timeout=600)
  assert x.returncode==0,'Compact capture failed; no measurement published'
  meta=dict(fixed,exit_code=0,outputs={n:SHA(a.capture/n) for n in ('roots.jsonl','capture.log')});receipt.write_text(json.dumps(meta,sort_keys=True,indent=2)+'\n')
 (metrics,imports,stage2),encoding=C['measure'](a.capture/'roots.jsonl',a.capture/'capture.log',a.file)
 data=dict(base=API['BASE'],status='partial',metrics=metrics,encoding=encoding,boundary='Actual saved-environment CI observations for this source only; compact pooling preserves every binding observation, not full root completeness or global liveness.')
 body=json.dumps(data,sort_keys=True,indent=2)+'\n';assert len(body.encode())<1000000
 assert producers=={n:SHA(HERE/n) for n in names};API['assert_sources'](a.source_root)
 if a.check:assert a.out.read_text()==body,'STALE compact capture result'
 else:a.out.write_text(body)
 print('COMPACT_CAPTURE_PASS',encoding['serialized_definitions'],encoding['binding_events'])
if __name__=='__main__':main()
