#!/usr/bin/env python3
"""Validate native serialization and namespace resolution against real Lean.
The duplicate theorem fixture distinguishes compile context from final-root
context and checks ConstantInfo bodies, not first-owner module metadata.
"""
import json,os,pathlib,runpy,subprocess,tempfile
HERE=pathlib.Path(__file__).resolve().parent
API=runpy.run_path(str(HERE/'module_graph.py'))

def run(cmd,cwd,env):
 r=subprocess.run(cmd,cwd=cwd,env=env,text=True,capture_output=True)
 assert r.returncode==0,r.stdout+r.stderr
 return r.stdout

def main():
 root=HERE.parents[3];cache=root/'.lake/refactor-cache';cache.mkdir(parents=True,exist_ok=True)
 with tempfile.TemporaryDirectory(prefix='declgraph-native-test-',dir=cache) as d:
  d=pathlib.Path(d);env=dict(os.environ,LEAN_PATH=str(d),LEAN_NUM_THREADS='1')
  sources={
   'DeclgraphB':'namespace DeclgraphFixture\ntheorem supportB : True := True.intro\ntheorem shared : True := supportB\nend DeclgraphFixture\n',
   'DeclgraphA':'import DeclgraphB\nnamespace DeclgraphFixture\ntheorem facade : True := shared\nend DeclgraphFixture\n',
   'DeclgraphC':'namespace DeclgraphFixture\n/-- Different body with exactly the same shared theorem type. -/\ntheorem supportC : True := Classical.choice ⟨True.intro⟩\ntheorem shared : True := supportC\nend DeclgraphFixture\n',
   'DeclgraphR':'import DeclgraphA\nimport DeclgraphC\nnamespace DeclgraphFixture\ntheorem root : True := facade\nend DeclgraphFixture\n'}
  for m,source in sources.items():
   (d/(m+'.lean')).write_text(source)
   run(['lean','-j1','-o',m+'.olean','-i',m+'.ilean',m+'.lean'],d,env)
  modules=d/'modules.txt';modules.write_text('\n'.join(sources)+'\n');output=d/'graph.jsonl'
  run(['lean','-j1','--run',str(HERE/'ModuleExport.lean'),str(modules),str(output)],d,env)
  g=API['load'](output,verify_receipt=False)
  b=('DeclgraphB','DeclgraphFixture.shared');c=('DeclgraphC','DeclgraphFixture.shared');rootkey=('DeclgraphR','DeclgraphFixture.root')
  assert b in g.nodes and c in g.nodes
  assert 'DeclgraphFixture.supportB' in g.nodes[b]['refs']
  assert 'DeclgraphFixture.supportC' in g.nodes[c]['refs']
  compiled=g.closure([rootkey]);semantic,boundary=g.root_closure('DeclgraphR',[rootkey[1]])
  assert b in compiled and c not in compiled
  assert c in semantic and b not in semantic
  assert any(n=='Classical.choice' for m,n in semantic)
  modules2={m:dict(r) for m,r in g.modules.items()};modules2['DeclgraphA']['selected']=False
  reentry=API['NativeGraph'](modules2,g.records,g.collisions)
  reached,reentry_boundary=reentry.root_closure('DeclgraphR',[rootkey[1]])
  assert ('DeclgraphA','DeclgraphFixture.facade') in reached and c in reached and b not in reached
  assert not reentry_boundary,reentry_boundary
  assert not {k:v for k,v in boundary.items() if k!='external_module'},boundary
  for key in (b,c):
   selection=g.nodes[key]['selection'];line=sources[key[0]].splitlines()[selection[0]]
   assert line[selection[1]:selection[3]]=='shared',selection
  selector='import Lean\nopen Lean\nunsafe def main (_args : List String) : IO UInt32 := do\n  initSearchPath (← findSysroot)\n  let env ← importModules #[{module := `DeclgraphR}] {} 0\n  let some ci := env.find? `DeclgraphFixture.shared | throw (IO.userError "missing shared")\n  let some value := ci.value? (allowOpaque := true) | throw (IO.userError "missing value")\n  let (_, state) := ((CollectAxioms.collect `DeclgraphFixture.root).run env).run {}\n  IO.println (Json.mkObj [(\"refs\", toJson (value.getUsedConstants.map Name.toString)),(\"axioms\", toJson (state.axioms.map Name.toString))]).compress\n  return 0\n'
  (d/'Select.lean').write_text(selector)
  selected=json.loads(run(['lean','-j1','--run','Select.lean'],d,env))
  assert 'DeclgraphFixture.supportC' in selected['refs'] and 'DeclgraphFixture.supportB' not in selected['refs'],selected
  assert set(selected['axioms'])=={n for m,n in semantic if g.records[(m,n)]['kind']=='axiom'}=={'Classical.choice'},selected
  assert not g.unresolved,g.unresolved
  try:API['NativeGraph']({'Modern':{'selected':True,'is_module':True,'imports':[],'names':[]}}, {}, {})
  except AssertionError:pass
  else:raise AssertionError('Unsupported module visibility accepted')
 print('NATIVE_GRAPH_FIXTURES_PASS duplicate_records native_ranges compile_context final_root_context actual_constant_info collect_axioms unselected_reentry unsupported_visibility')
if __name__=='__main__':main()
