#!/usr/bin/env python3
"""Compile real direct/higher-order/constructor/override IR fixtures."""
import json,os,pathlib,subprocess,tempfile
HERE=pathlib.Path(__file__).resolve().parent

def main():
 root=HERE.parents[3];cache=root/'.lake/refactor-cache';cache.mkdir(parents=True,exist_ok=True)
 with tempfile.TemporaryDirectory(prefix='declgraph-ir-test-',dir=cache) as d:
  d=pathlib.Path(d);env=dict(os.environ,LEAN_PATH=str(d),LEAN_NUM_THREADS='1')
  source='import Lean\nnamespace DeclgraphIRFixture\n@[noinline] unsafe def implementation (x : Nat) : Nat := x + 1\n@[implemented_by implementation, noinline] def wrapper (x : Nat) : Nat := x + 1\n@[noinline] def direct (x : Nat) : Nat := wrapper x\n@[noinline] def dynamicCall (f : Nat → Nat) (x : Nat) : Nat := f x\ninductive Flag where | off | on\n@[noinline] def branch (x : Flag) : Nat := match x with | .off => 1 | .on => 2\nend DeclgraphIRFixture\n'
  (d/'Fixture.lean').write_text(source)
  def run(args):
   r=subprocess.run(args,cwd=d,env=env,text=True,capture_output=True);assert r.returncode==0,r.stdout+r.stderr;return r.stdout
  run(['lean','-j1','-o','Fixture.olean','-i','Fixture.ilean','Fixture.lean'])
  modules=d/'modules.txt';modules.write_text('Fixture\n');out=d/'ir.jsonl'
  run(['lean','-j1','--run',str(HERE/'IRExport.lean'),str(modules),str(out)])
  rows=[json.loads(x) for x in out.read_text().splitlines()];functions=[r for r in rows if r['record']=='function'];attrs=[r for r in rows if r['record']=='implemented_by']
  assert any(r['name']=='DeclgraphIRFixture.wrapper' and r['implementation']=='DeclgraphIRFixture.implementation' and r['implementation_module']=='Fixture' for r in attrs),attrs
  direct=[r for r in functions if r['name']=='DeclgraphIRFixture.direct'];assert direct
  assert all('DeclgraphIRFixture.implementation' in r['functions'] for r in direct),direct
  dynamic=[r for r in functions if r['name']=='DeclgraphIRFixture.dynamicCall'];assert dynamic and all(r['dynamic_calls']>0 for r in dynamic),dynamic
  branches=[r for r in functions if r['name']=='DeclgraphIRFixture.branch'];assert branches and all(r['constructors'] for r in branches),branches
  for r in functions:
   assert len(r['functions'])==len(r['function_owners'])
   assert r['owner_module']=='Fixture',r
  versions={}
  for r in functions:
   versions.setdefault(r['name'],{})[r['phase']]={k:v for k,v in r.items() if k!='phase'}
  assert all(v['main']==v['ir'] for v in versions.values()),versions
 print('IR_FIXTURES_PASS static_calls dynamic_sites constructors native_owners module_overrides duplicate_views')
if __name__=='__main__':main()
