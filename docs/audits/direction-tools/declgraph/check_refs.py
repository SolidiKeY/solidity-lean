#!/usr/bin/env python3
"""Serial native captures for syntax-census candidate checks in four families.
The census selects files, not semantic edges. No negative liveness inference.
Imported cache view is externally trusted; each source/raw/log is hash-bound.
"""
import argparse,collections,json,os,pathlib,re,runpy,subprocess
HERE=pathlib.Path(__file__).resolve().parent
API=runpy.run_path(str(HERE/'audit.py'));SHA=runpy.run_path(str(HERE/'module_graph.py'))['sha']
FAMILIES=('Yul/Views','Backend/InternalFlow','SolcValidation','Frontend/SolcJson')

def measure(raw,log):
 rows=[json.loads(x) for x in raw.read_text().splitlines()]
 counts=collections.Counter(x['record'] for x in rows)
 assert set(counts)<={'command','command_info','identifier','coalescing_change'}
 assert all(x['name_key'] is not None for x in rows if x['record']=='identifier')
 marker=re.findall(r'RAW_REFS_CAPTURE_PASS (\d+) (\d+) (\d+)',log.read_text());assert len(marker)==1
 assert tuple(map(int,marker[0]))==(counts['command'],counts['identifier']+counts['command_info'],counts['coalescing_change'])
 commands=[x for x in rows if x['record']=='command']
 assert commands and [x['command'] for x in commands]==list(range(len(commands)))
 assert all(x['unresolved_info_holes']==0 for x in commands)
 checks=[x for x in rows if x['record']=='command_info' and x['check_kind']]
 refs=[x for x in rows if x['record']=='identifier' and x['check_kind'] and x['ident']['kind']=='const' and not x['is_binder']]
 # Deduplicate only identical native structural names; module hints remain hints.
 names={json.dumps(x['name_key'],separators=(',',':')):x['ident']['name'] for x in refs}
 return dict(top_commands=len(commands),check_info_events=len(checks),check_top_commands=len({x['command'] for x in checks}),check_reference_events=len(refs),observed_constants=[dict(name_key=json.loads(key),name=names[key]) for key in sorted(names)],finished_diagnostic_snapshots=sum(x['finished_diagnostic_snapshots'] for x in commands))

def main():
 p=argparse.ArgumentParser();p.add_argument('--source-root',type=pathlib.Path,required=True);p.add_argument('--view',type=pathlib.Path,required=True);p.add_argument('--captures',type=pathlib.Path,required=True);p.add_argument('--out',type=pathlib.Path,required=True);p.add_argument('--check',action='store_true');a=p.parse_args()
 for key in ('source_root','view','captures','out'):setattr(a,key,getattr(a,key).resolve())
 API['assert_sources'](a.source_root)
 producers={n:SHA(HERE/n) for n in ('check_refs.py','RawRefs.lean','audit.py','source-check-syntax.json')}
 paths=sorted({r['path'] for r in json.loads((HERE/'source-check-syntax.json').read_text()) if any(r['path'].startswith('Solidity/'+f+'/') for f in FAMILIES)})
 version=subprocess.check_output(['lean','--version'],text=True).strip();assert 'version 4.24.0,' in version and '797c613' in version
 if not a.check:assert not a.captures.exists(),'Fresh capture directory required';a.captures.mkdir(parents=True)
 results=[]
 for path in paths:
  module=path[:-5].replace('/','.');source=a.source_root/path;raw=a.captures/(module+'.jsonl');log=a.captures/(module+'.log');rp=a.captures/(module+'.receipt.json');cmd=['lean','--tstack=131072','-j1','-M10000','--run',str(HERE/'RawRefs.lean'),str(source),module,str(raw)]
  fixed=dict(producers=producers,source_sha256=SHA(source),command=cmd,view=str(a.view),lean=version)
  if a.check:
   receipt=json.loads(rp.read_text());assert all(receipt[k]==v for k,v in fixed.items());assert receipt['log_sha256']==SHA(log);assert receipt['raw_sha256']==(SHA(raw) if raw.exists() else None)
  else:
   try:
    run=subprocess.run(cmd,env=dict(os.environ,LEAN_PATH=str(a.view),LEAN_NUM_THREADS='1'),text=True,capture_output=True,timeout=600);log.write_text(run.stdout+run.stderr);code=run.returncode
   except subprocess.TimeoutExpired as exc:
    log.write_text('TIMEOUT 600s\n'+str(exc.stdout or '')+str(exc.stderr or ''));code=124
   receipt=dict(fixed,exit_code=code,log_sha256=SHA(log),raw_sha256=SHA(raw) if raw.exists() else None);rp.write_text(json.dumps(receipt,sort_keys=True)+'\n')
  item=dict(path=path,status='pass' if receipt['exit_code']==0 else 'unavailable',exit_code=receipt['exit_code'])
  if receipt['exit_code']==0:
   try:item.update(measure(raw,log))
   except (AssertionError,ValueError,KeyError,TypeError,FileNotFoundError) as exc:item.update(status='validation_failed',validation_error=type(exc).__name__+': '+str(exc))
  results.append(item);print(item['status'],path,flush=True)
 assert producers=={n:SHA(HERE/n) for n in producers};API['assert_sources'](a.source_root)
 data=dict(base=API['BASE'],status='partial',selection='Native syntax census selects candidate-family files containing explicit check syntax; macro-only files and external consumers are not covered.',files=results,verdict='Successful captures witness check references only. No file or declaration is certified unused or deletable.',boundaries=['Constant names are native pre-coalescing identities; module hints do not select imported proof bodies.','Check-info and reference events can repeat; counts are not unique successful root statements.','Unsuccessful files contribute no semantic roots; continue remaining files.','Imported cache artifacts are externally trusted; receipts bind source, producers, raw output and logs.'])
 body=json.dumps(data,indent=2,sort_keys=True)+'\n';assert len(body.encode())<1000000
 if a.check:assert a.out.read_text()==body
 else:a.out.write_text(body)
 print('CHECK_REFERENCE_BATCH_PASS',sum(x['status']=='pass' for x in results),len(results))
if __name__=='__main__':main()
