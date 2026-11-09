#!/usr/bin/env python3
"""Capture native pre-coalescing refs on one pinned alias-span counterexample.
Requires writer lock, prepared cache view and pinned Lean. --check reuses an
input/producer/output-bound capture. Comparison positions never supply use edges.
"""
import argparse,collections,hashlib,json,os,pathlib,re,runpy,subprocess
HERE=pathlib.Path(__file__).resolve().parent
API=runpy.run_path(str(HERE/'audit.py'));SHA=runpy.run_path(str(HERE/'module_graph.py'))['sha']
SOURCE='Solidity/Backend/InternalFlow/RuntimeFrameReference.lean'
TARGET='Solidity.Backend.InternalFlow.RuntimeFrame.Reference.headCode'

def utf16_slice(text,span):
 a,b,c,d=span;assert a==c
 return text.split('\n')[a].encode('utf-16-le')[2*b:2*d].decode('utf-16-le')

def measure(raw,ilean,source):
 rows=[json.loads(line) for line in raw.read_text().splitlines()];counts=collections.Counter(r['record'] for r in rows)
 assert set(counts)<={'identifier','command_info','command','coalescing_change'}
 refs=[r for r in rows if r['record']=='identifier'];commands=[r for r in rows if r['record']=='command'];changes=[r for r in rows if r['record']=='coalescing_change']
 assert commands and [r['command'] for r in commands]==list(range(len(commands)))
 assert all(r['unresolved_info_holes']==0 for r in commands),'Unresolved native info holes'
 assert all(r['name_key'] is not None for r in refs)
 cached=json.loads(ilean.read_text());matches=[value for key,value in cached['references'].items() if (ident:=json.loads(key)).get('c',{}).get('n')==TARGET]
 assert len(matches)==1;cached_range=matches[0]['definition'][:4]
 definitions=[r for r in refs if r['ident']['kind']=='const' and r['ident']['name']==TARGET and r['is_binder'] and r['origin']=='original']
 actual_ranges={tuple(r['range']) for r in definitions};assert len(actual_ranges)==1;actual=list(next(iter(actual_ranges)))
 at_cached=[r for r in refs if r['range']==cached_range and r['is_binder']]
 assert at_cached and all(r['ident']['kind']=='fvar' for r in at_cached)
 assert cached_range!=actual and utf16_slice(source,actual)=='headCode'
 promotions=sum(r['raw_ident']['kind']=='fvar' and r['combined_ident']['kind']=='const' for r in changes)
 return dict(base=API['BASE'],source=SOURCE,source_sha256=hashlib.sha256(source.encode()).hexdigest(),status='partial',counts=dict(sorted(counts.items())),native_original_identifier_events=sum(r['origin']=='original' for r in refs),native_other_origin_identifier_events=sum(r['origin']!='original' for r in refs),finished_diagnostic_snapshots=sum(r['finished_diagnostic_snapshots'] for r in commands),coalescing_fvar_to_const_diagnostics=promotions,comparison=dict(target=TARGET,cached_definition_lsp=cached_range,cached_definition_line=cached_range[0]+1,cached_definition_text=utf16_slice(source,cached_range),native_constant_binder_lsp=actual,native_definition_line=actual[0]+1,native_definition_text=utf16_slice(source,actual),raw_binders_at_cached_location=len(at_cached),raw_cached_location_kinds=sorted({r['ident']['kind'] for r in at_cached})),verdict='The cached editor definition range is not the declaration range. Fresh native info identifies local-variable binders there and the actual headCode constant binder at its own source location.',boundaries=['This measures observed native identifier infos; it does not certify exhaustive roots, runtime dependencies or deletions.', 'Prepared import-view contents are trusted externally; the receipt binds the view path and compared ilean, not every imported olean byte.', 'Module hints are first-owner metadata; typed names and const/fvar classes are retained without coalescing.', 'The module-wide coalescing comparison is diagnostic only. Promotions include legitimate aliases and are not counted as false dependency edges.', 'Fresh serial elaboration need not reproduce cached asynchronous alias decisions; the cached span and fresh native observations are compared separately.', 'Snapshot acceptance is limited to already-finished diagnostic-only trees; errors are propagated and unfinished/separate-info work is unsupported.'])

def main():
 p=argparse.ArgumentParser();p.add_argument('--source-root',type=pathlib.Path,required=True);p.add_argument('--view',type=pathlib.Path,required=True);p.add_argument('--raw',type=pathlib.Path,required=True);p.add_argument('--logs',type=pathlib.Path,required=True);p.add_argument('--out',type=pathlib.Path,required=True);p.add_argument('--check',action='store_true');a=p.parse_args();producers={name:SHA(HERE/name) for name in ('RawRefs.lean','raw_refs.py','audit.py')};src=API['assert_sources'](a.source_root)
 for name in ('source_root','view','raw','logs','out'):setattr(a,name,getattr(a,name).resolve())
 ilean=a.view/pathlib.Path(SOURCE).with_suffix('.ilean');module=json.loads(ilean.read_text())['module'];source=a.source_root/SOURCE;receipt_path=pathlib.Path(str(a.raw)+'.receipt.json');version=subprocess.check_output(['lean','--version'],text=True).strip();assert 'version 4.24.0,' in version and '797c613' in version
 command=['lean','--tstack=131072','-j1','-M10000','--run',str(HERE/'RawRefs.lean'),str(source),module,str(a.raw)]
 if a.check:
  receipt=json.loads(receipt_path.read_text());assert receipt['producers']==producers and receipt['lean']==version and receipt['exit_code']==0
  assert receipt['command']==command and receipt['view']==str(a.view)
  assert receipt['raw_sha256']==SHA(a.raw) and receipt['ilean_sha256']==SHA(ilean) and receipt['source_sha256']==SHA(source)
  assert receipt['log_sha256']==SHA(a.logs/'capture.log')
 else:
  assert not a.raw.exists() and not receipt_path.exists(),'Fresh capture outputs required';a.logs.mkdir(parents=True,exist_ok=True)
  env=dict(os.environ,LEAN_PATH=str(a.view),LEAN_NUM_THREADS='1');result=subprocess.run(command,env=env,text=True,capture_output=True,timeout=600);log=a.logs/'capture.log';log.write_text(result.stdout+result.stderr);assert result.returncode==0,result.stdout+result.stderr
  receipt=dict(producers=producers,lean=version,command=command,view=str(a.view),exit_code=result.returncode,raw_sha256=SHA(a.raw),ilean_sha256=SHA(ilean),source_sha256=SHA(source),log_sha256=SHA(log))
 data=measure(a.raw,ilean,src[SOURCE]);capture=(a.logs/'capture.log').read_text();m=re.search(r'RAW_REFS_CAPTURE_PASS (\d+) (\d+) (\d+)',capture);assert m
 assert tuple(map(int,m.groups()))==(data['counts']['command'],data['counts']['identifier']+data['counts']['command_info'],data['counts'].get('coalescing_change',0))
 assert producers=={name:SHA(HERE/name) for name in producers},'Producer changed';API['assert_sources'](a.source_root)
 body=json.dumps(data,indent=2,sort_keys=True)+'\n';assert len(body.encode())<1000000
 if a.check:assert a.out.read_text()==body,'STALE raw-reference summary'
 else:a.out.write_text(body);receipt_path.write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
 print('RAW_REFERENCE_SOURCE_PASS',data['counts']['identifier'],data['comparison']['cached_definition_line'],data['comparison']['native_definition_line'])
if __name__=='__main__':main()
