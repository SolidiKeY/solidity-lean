#!/usr/bin/env python3
"""Real dense/compact saved-check equivalence plus decoder corruption cases."""
import collections,copy,json,os,pathlib,runpy,subprocess,tempfile
HERE=pathlib.Path(__file__).resolve().parent;C=runpy.run_path(str(HERE/'compact_records.py'));L=runpy.run_path(str(HERE/'run_snapshot_roots.py'))
def main():
 cache=HERE.parents[3]/'.lake/refactor-cache';cache.mkdir(parents=True,exist_ok=True)
 with tempfile.TemporaryDirectory(prefix='declgraph-compact-fixture-',dir=cache) as directory:
  d=pathlib.Path(directory);env=dict(os.environ,LEAN_PATH=str(d),LEAN_NUM_THREADS='1')
  def run(args):
   x=subprocess.run(args,cwd=d,env=env,text=True,capture_output=True,timeout=120);assert x.returncode==0,x.stdout+x.stderr;return x
  for module,support in [('Left','leftSupport'),('Right','rightSupport')]:
   (d/(module+'.lean')).write_text(f'theorem {support} : True := True.intro\ntheorem shared : True := {support}\n');run(['lean','--tstack=131072','-j1','-M1000','--root='+str(d),'-o',module+'.olean',module+'.lean'])
  (d/'Fixture.lean').write_text('import Left\nimport Right\nexample : True := shared\nexample : True := leftSupport\n#eval ``leftSupport\n');(d/'modules').write_text('Left\nRight\nFixture\n')
  for label,producer in [('dense','SnapshotRoots.lean'),('compact','CompactRoots.lean')]:
   x=run(['lean','--tstack=131072','-j1','-M2000','--run',str(HERE/producer),str(d/'Fixture.lean'),'Fixture',str(d/'modules'),str(d/(label+'.jsonl'))]);(d/(label+'.log')).write_text(x.stdout+x.stderr)
  dense=[json.loads(x) for x in (d/'dense.jsonl').read_text().splitlines()];counts=C['footer'](d/'compact.log');expanded=list(C['expanded'](d/'compact.jsonl',counts[5]))
  canonical=lambda rows:collections.Counter(json.dumps(r,sort_keys=True,separators=(',',':')) for r in rows)
  assert canonical(dense)==canonical(expanded),'Compact expansion changed snapshot records'
  a=L['measure'](d/'dense.jsonl',d/'dense.log','Fixture.lean');b,encoding=C['measure'](d/'compact.jsonl',d/'compact.log','Fixture.lean');assert a==b
  assert encoding['serialized_definitions']<encoding['binding_events'],encoding
  rows=[json.loads(x) for x in (d/'compact.jsonl').read_text().splitlines()];bad=copy.deepcopy(rows)
  next(r for r in bad if r['record']=='binding_ref')['definition']=10**9
  wrong=d/'wrong.jsonl';wrong.write_text(''.join(json.dumps(r)+'\n' for r in bad))
  try:list(C['expanded'](wrong,counts[5]))
  except AssertionError:pass
  else:raise AssertionError('Broken definition reference accepted')
  bad=copy.deepcopy(rows);bad.append(next(r for r in bad if r['record']=='definition'));wrong.write_text(''.join(json.dumps(r)+'\n' for r in bad))
  try:list(C['expanded'](wrong,counts[5]))
  except AssertionError:pass
  else:raise AssertionError('Duplicate definition ID accepted')
 print('COMPACT_ROOT_FIXTURES_PASS dense_record_equivalence measurement_equivalence pooled_bodies corrupt_references')
if __name__=='__main__':main()
