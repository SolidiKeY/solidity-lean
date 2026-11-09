#!/usr/bin/env python3
"""Real discarded-check CI and imported proof-version origin fixtures."""
import argparse,collections,hashlib,json,os,pathlib,re,subprocess,tempfile
HERE=pathlib.Path(__file__).resolve().parent

def main():
 p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args();cache=HERE.parents[3]/'.lake/refactor-cache';cache.mkdir(parents=True,exist_ok=True)
 with tempfile.TemporaryDirectory(prefix='declgraph-snapshot-fixture-',dir=cache) as directory:
  d=pathlib.Path(directory);env=dict(os.environ,LEAN_PATH=str(d),LEAN_NUM_THREADS='1')
  def run(args):
   x=subprocess.run(args,cwd=d,env=env,text=True,capture_output=True,timeout=120);assert x.returncode==0,x.stdout+x.stderr;return x
  for module,support in [('Left','leftSupport'),('Right','rightSupport')]:
   (d/(module+'.lean')).write_text(f'theorem {support} : True := True.intro\ntheorem shared : True := {support}\n');run(['lean','--tstack=131072','-j1','-M1000','--root='+str(d),'-o',module+'.olean','-i',module+'.ilean',module+'.lean'])
  source='import Left\nimport Right\nexample : True := shared\nexample : True := leftSupport\n#eval ``leftSupport\n';(d/'Fixture.lean').write_text(source);(d/'modules').write_text('Left\nRight\nFixture\n');raw=d/'raw.jsonl'
  x=run(['lean','--tstack=131072','-j1','-M2000','--run',str(HERE/'SnapshotRoots.lean'),str(d/'Fixture.lean'),'Fixture',str(d/'modules'),str(raw)])
  rows=[json.loads(line) for line in raw.read_text().splitlines()];counts=collections.Counter(r['record'] for r in rows);assert {'command','check_event','root_event','binding','snapshot_summary'}<=set(counts)<={'command','check_event','root_event','binding','snapshot_summary','missing_parent'}
  marker=re.findall(r'SNAPSHOT_ROOTS_PASS (\d+) (\d+) (\d+) (\d+) (\d+)',x.stdout);assert len(marker)==1;assert tuple(map(int,marker[0]))==tuple(counts[k] for k in ('command','check_event','root_event','snapshot_summary','binding'))
  checks={r['command']:r['check_kind'] for r in rows if r['record']=='check_event'};roots=[r for r in rows if r['record']=='root_event'];bindings=[r for r in rows if r['record']=='binding'];snapshots=[r for r in rows if r['record']=='snapshot_summary']
  assert len(checks)==3 and set(checks)=={r['command'] for r in roots},(checks,roots)
  shared=[r for r in bindings if r['name']=='shared'];assert shared
  for r in shared:
   assert r['imported_pointer_modules'] in (['Left'],['Right']) and not r['in_stage2'],r
   expected={'Left':'leftSupport','Right':'rightSupport'}[r['imported_pointer_modules'][0]];assert expected in [n['name'] for n in r['refs']]
  eval_ids={cmd for cmd,kind in checks.items() if kind=='eval'};assert len(eval_ids)==1
  assert not any(r['command'] in eval_ids and r['name']=='leftSupport' for r in bindings),'Quoted name must not become a value/body dependency'
  for snap in snapshots:assert not snap['missing_names'] and snap['unresolved_import_origins']==0,snap
  assert all(any(r['command']==cmd and r['in_stage2'] and r['is_root'] for r in bindings) for cmd in checks)
  result=dict(producer_sha256=hashlib.sha256((HERE/'SnapshotRoots.lean').read_bytes()).hexdigest(),source_sha256=hashlib.sha256(source.encode()).hexdigest(),counts=dict(sorted(counts.items())),observed_check_commands=len(checks),covered_check_commands=len({r['command'] for r in roots}),imported_shared_body_origins=sorted({m for r in shared for m in r['imported_pointer_modules']}),quote_is_not_body_use=True,missing_native_constants=0,unresolved_import_origins=0,boundary='Fixture only: native parent-declaration metadata covers these three checks; snapshot/event repetitions are not unique roots or general completeness.')
 body=json.dumps(result,sort_keys=True,indent=2)+'\n';out=HERE/'snapshot-root-fixtures.json'
 if a.check:assert out.read_text()==body,'STALE snapshot fixture result'
 else:out.write_text(body)
 print('SNAPSHOT_ROOT_FIXTURES_PASS discarded_ci imported_pointer_origin quote_not_body_use')
if __name__=='__main__':main()
