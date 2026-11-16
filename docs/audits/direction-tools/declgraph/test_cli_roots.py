#!/usr/bin/env python3
"""Real incompatible-main fixtures for native append-only root contexts."""
import json,os,pathlib,runpy,subprocess,tempfile
HERE=pathlib.Path(__file__).resolve().parent
CLI=runpy.run_path(str(HERE/'cli_roots.py'));NATIVE=runpy.run_path(str(HERE/'module_graph.py'))
def main():
 cache=HERE.parents[3]/'.lake/refactor-cache';cache.mkdir(parents=True,exist_ok=True)
 with tempfile.TemporaryDirectory(prefix='declgraph-cli-fixture-',dir=cache) as directory:
  d=pathlib.Path(directory);env=dict(os.environ,LEAN_PATH=str(d),LEAN_NUM_THREADS='1')
  def run(args,good=True):
   result=subprocess.run(args,cwd=d,env=env,text=True,capture_output=True,timeout=120)
   if good:assert result.returncode==0,result.stdout+result.stderr
   return result
  for module,support,value in [('First','firstSupport',3),('Second','secondSupport',5)]:
   (d/(module+'.lean')).write_text(f'def {support} : UInt32 := {value}\ndef main (_ : List String) : IO UInt32 := pure {support}\ndef unused{module} : Nat := 7\n')
   run(['lean','--tstack=131072','-j1','-M10000','--root='+str(d),'-o',module+'.olean','-i',module+'.ilean',module+'.lean'])
  first=d/'first.txt';first.write_text('First\n');base=d/'base.jsonl'
  run(['lean','--tstack=131072','-j1','-M10000','--run',str(HERE/'ModuleExport.lean'),str(first),str(base)])
  graph=NATIVE['load'](base,verify_receipt=False)
  before,boundary=graph.root_closure('First',['main']);assert not boundary
  assert ('First','firstSupport') in before and ('First','unusedFirst') not in before
  modules=d/'modules.txt';modules.write_text('First\nSecond\n');out=d/'local.jsonl'
  run(['lean','--tstack=131072','-j1','-M10000','--run',str(HERE/'LocalExport.lean'),str(modules),str(out)])
  rows=[json.loads(line) for line in out.read_text().splitlines()];second=next(r for r in rows if r['record']=='module' and r['module']=='Second');constants=[r for r in rows if r['record']=='constant' and r['module']=='Second']
  CLI['extend_leaf'](graph,second,constants)
  after,boundary=graph.root_closure('First',['main']);assert not boundary and after==before
  other,boundary=graph.root_closure('Second',['main']);assert not boundary
  assert ('Second','secondSupport') in other and ('Second','unusedSecond') not in other
  assert ('First','main') in after and ('Second','main') not in after
  assert ('Second','main') in other and ('First','main') not in other
  assert 'Second' not in graph.visible['First'] and 'First' not in graph.visible['Second']
  assert graph.records['First','main']['refs']!=graph.records['Second','main']['refs']
  assert graph.resolve('First','main')==('First',None) and graph.resolve('Second','main')==('Second',None)
  (d/'Together.lean').write_text('import First\nimport Second\n')
  rejected=run(['lean','--tstack=131072','-j1','-M10000','Together.lean'],good=False)
  assert rejected.returncode!=0 and 'main' in rejected.stdout+rejected.stderr,rejected.stdout+rejected.stderr
 print('CLI_CONTEXT_FIXTURES_PASS distinct_main_bodies fixed_root_visibility old_cache_stability native_combined_import_rejected')
if __name__=='__main__':main()
