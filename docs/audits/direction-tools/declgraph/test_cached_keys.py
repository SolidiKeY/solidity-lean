#!/usr/bin/env python3
"""Direct artifact native-key fixtures, including colliding printed names."""
import json,os,pathlib,subprocess,tempfile
HERE=pathlib.Path(__file__).resolve().parent

def main():
 cache=HERE.parents[3]/'.lake/refactor-cache';cache.mkdir(parents=True,exist_ok=True)
 with tempfile.TemporaryDirectory(prefix='declgraph-key-fixture-',dir=cache) as directory:
  d=pathlib.Path(directory);env=dict(os.environ,LEAN_PATH=str(d),LEAN_NUM_THREADS='1')
  (d/'Fixture.lean').write_text('def «#x.a» : Nat := 1\nnamespace «#x»\ndef a : Nat := 2\nend «#x»\n')
  x=subprocess.run(['lean','--tstack=131072','-j1','-M1000','--root='+str(d),'-o','Fixture.olean','Fixture.lean'],cwd=d,env=env,text=True,capture_output=True,timeout=120);assert x.returncode==0,x.stdout+x.stderr
  query=d/'query';out=d/'keys';query.write_text(json.dumps([dict(module='Fixture',artifacts=[str(d/'Fixture.olean')],names=['#x.a','notPresent'])]))
  cmd=['lean','--tstack=131072','-j1','-M1000','--run',str(HERE/'CachedKeys.lean'),str(query),str(out)];x=subprocess.run(cmd,cwd=d,env=env,text=True,capture_output=True,timeout=120);assert x.returncode==0,x.stdout+x.stderr
  rows=[json.loads(line) for line in out.read_text().splitlines()];keys=[r for r in rows if r['record']=='key'];assert len(keys)==2 and {r['name'] for r in keys}=={'#x.a'}
  expected={json.dumps(['str','anonymous','#x.a']),json.dumps(['str',['str','anonymous','#x'],'a'])};assert {json.dumps(r['name_key']) for r in keys}==expected
  assert [r for r in rows if r['record']=='module'][0]['missing_names']==['notPresent']
 print('CACHED_KEYS_FIXTURES_PASS native_structural_keys printed_collision explicit_missing')
if __name__=='__main__':main()
