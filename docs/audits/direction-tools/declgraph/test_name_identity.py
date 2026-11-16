#!/usr/bin/env python3
"""Native counterexample: pseudo-syntax names can share printed displays."""
import json,os,pathlib,subprocess,tempfile
HERE=pathlib.Path(__file__).resolve().parent

def main():
 cache=HERE.parents[3]/'.lake/refactor-cache';cache.mkdir(parents=True,exist_ok=True)
 with tempfile.TemporaryDirectory(prefix='declgraph-name-fixture-',dir=cache) as directory:
  d=pathlib.Path(directory);modules=d/'modules';modules.write_text('Init\n');obs=d/'observations';out=d/'identity'
  rows=[dict(name_key=['str','anonymous','#x.a'],name='#x.a'),dict(name_key=['str',['str','anonymous','#x'],'a'],name='#x.a')]
  def run():return subprocess.run(['lean','--tstack=131072','-j1','-M1000','--run',str(HERE/'NameIdentity.lean'),str(modules),str(obs),str(out)],env=dict(os.environ,LEAN_PATH=str(d),LEAN_NUM_THREADS='1'),text=True,capture_output=True,timeout=120)
  obs.write_text(json.dumps(rows));x=run();assert x.returncode==1,x.stdout+x.stderr;s=json.loads(out.read_text());assert len(s['collisions'])==1 and s['collisions'][0]['printed']=='#x.a'
  obs.write_text(json.dumps(rows[:1]*2));x=run();assert x.returncode==0,x.stdout+x.stderr;s=json.loads(out.read_text());assert not s['collisions'] and s['observation_rows']==2
  obs.write_text(json.dumps([dict(name_key=['str','anonymous','actual'],name='incorrect')]));x=run();assert x.returncode!=0 and 'display/key mismatch' in x.stdout+x.stderr
  modules.write_text('');obs.write_text('[]');x=run();assert x.returncode!=0 and 'Empty module universe' in x.stdout+x.stderr
 print('NATIVE_NAME_IDENTITY_FIXTURES_PASS real_display_collision duplicate_identity mismatch empty_universe')
if __name__=='__main__':main()
