#!/usr/bin/env python3
"""Use Lake's current module artifact resolution; never trust old local traces.
Run with PATH containing pinned Lake, LEAN_NUM_THREADS=1 and LAKE_CACHE_DIR:
 python3 -I .../prepare.py --cache CACHE --view FRESH_VIEW --modules MODULES
Requires matching cache products. --no-build prohibits cold elaboration.
"""
import argparse,collections,json,os,pathlib,re,runpy,subprocess

def main():
 p=argparse.ArgumentParser();p.add_argument('--cache',type=pathlib.Path,required=True);p.add_argument('--view',type=pathlib.Path,required=True);p.add_argument('--modules',type=pathlib.Path,required=True);a=p.parse_args()
 api=runpy.run_path(str(pathlib.Path(__file__).with_name('audit.py')))
 pinned=api['assert_sources']()
 root=pathlib.Path(subprocess.check_output(['git','rev-parse','--show-toplevel'],text=True).strip());build=root/'.lake/build/lib/lean';tracked=subprocess.check_output(['git','ls-files','*.lean'],text=True).splitlines();mods=[]
 for f in build.rglob('*.ilean'):
  mods.append(json.loads(f.read_text())['module'])
 mods=sorted(set(mods));assert not a.view.exists(),'Fresh view required';a.view.mkdir(parents=True)
 excluded=[];logs=[]
 while True:
  run=subprocess.run(['lake','--no-build','--json','query']+['+'+m+':olean' for m in mods],text=True,capture_output=True)
  logs.append(run.stderr)
  a.modules.with_suffix('.lake.log').write_text('\n'.join(logs))
  if run.returncode==0:break
  failed=set(re.findall(r'Building ([A-Za-z0-9_.]+)\nerror: target is out-of-date',run.stderr))
  if not failed or not failed.issubset(set(mods)):raise RuntimeError('Unresolved cache-only dependency gap: '+run.stderr[-2000:])
  excluded.extend(sorted(failed));mods=[m for m in mods if m not in failed]
 a.modules.with_suffix('.excluded.json').write_text(json.dumps(excluded,indent=2)+'\n')
 paths=[pathlib.Path(json.loads(s)) for s in run.stdout.splitlines()];assert len(paths)==len(mods)
 table={}
 for f in (a.cache/'inputs').glob('*.jsonl'):
  for line in f.open():
   _,arts=json.loads(line)
   if isinstance(arts,dict):
    for h in arts.get('o',[]):
     if str(h) in table:assert table[str(h)]['i']==arts['i'], 'Ambiguous reference pair'
     table[str(h)]=arts
 # Hash local artifacts using the pinned Lean/Lake implementation.
 local=[str(f) for f in paths if not f.is_relative_to(a.cache/'artifacts')]
 hashes={}
 if local:
  listfile=a.modules.with_suffix('.locals.txt');listfile.write_text('\n'.join(local)+'\n')
  exporter=pathlib.Path(__file__).with_name('Export.lean')
  output=subprocess.check_output(['lean','-j1','--run',str(exporter),'binhash',str(listfile)],text=True)
  hashes=dict(s.split('\t',1) for s in output.splitlines())
 for m,f in zip(mods,paths):
  h=f.name.split('.',1)[0] if f.is_relative_to(a.cache/'artifacts') else hashes[str(f)]
  arts=table.get(h)
  if arts is None:raise RuntimeError('No matching reference artifact for '+m+' '+h)
  stem=a.view/pathlib.Path(m.replace('.','/'));stem.parent.mkdir(parents=True,exist_ok=True)
  os.link(f,stem.with_suffix('.olean'))
  src=a.cache/'artifacts'/(str(arts['i'])+'.ilean');os.link(src,stem.with_suffix('.ilean'))
  for suffix in ('olean.server','olean.private'):
   src=a.cache/'artifacts'/(h+'.'+suffix)
   if src.exists():os.link(src,stem.with_suffix('.'+suffix))
 a.modules.write_text('\n'.join(mods)+'\n');print('CURRENT_ARTIFACT_VIEW_PASS',len(mods))
if __name__=='__main__':main()
