#!/usr/bin/env python3
"""Use Lake's current module artifact resolution; never trust old local traces.
Run with PATH containing pinned Lake, LEAN_NUM_THREADS=1 and LAKE_CACHE_DIR:
 python3 -I .../prepare.py --cache CACHE --view FRESH_VIEW --modules MODULES
Requires matching cache products. --no-build prohibits cold elaboration.
"""
import argparse,collections,json,os,pathlib,re,runpy,subprocess

def recorded_artifacts(cache, arts):
 """Lake 4.24 ModuleOutputHashes: o[0]=main, o[1]=server, o[2]=private.
 Absent optional entries are allowed; a recorded artifact must exist.
 """
 hashes=arts['o']
 if not 1<=len(hashes)<=3:raise ValueError('Invalid Lake olean hash array')
 files={suffix:cache/'artifacts'/(str(h)+'.'+suffix)
        for suffix,h in zip(('olean','olean.server','olean.private'),hashes)}
 files['ilean']=cache/'artifacts'/(str(arts['i'])+'.ilean')
 for suffix,src in files.items():
  if not src.is_file():raise FileNotFoundError('Missing recorded '+suffix+' artifact: '+str(src))
 return files

def query_modules(mods,root,log):
 mods=sorted({m.strip() for m in mods if m.strip()})
 excluded=[];logs=[]
 while True:
  if not mods:raise RuntimeError('No cache-resolved modules; refusing Lake default targets')
  run=subprocess.run(['lake','--no-build','--json','query']+['+'+m+':olean' for m in mods],text=True,capture_output=True,cwd=root)
  logs.append(run.stderr)
  log.with_suffix('.lake.log').write_text('\n'.join(logs))
  if run.returncode==0:break
  failed=set(re.findall(r'Building ([A-Za-z0-9_.]+)\nerror: target is out-of-date',run.stderr))
  if not failed or not failed.issubset(set(mods)):raise RuntimeError('Unresolved cache-only dependency gap: '+run.stderr[-2000:])
  excluded.extend(sorted(failed));mods=[m for m in mods if m not in failed]
 return mods,run.stdout,excluded

def main():
 p=argparse.ArgumentParser();p.add_argument('--cache',type=pathlib.Path,required=True);p.add_argument('--view',type=pathlib.Path,required=True);p.add_argument('--modules',type=pathlib.Path,required=True);p.add_argument('--input-modules',type=pathlib.Path,help='Explicit native module universe, especially for a fresh frozen worktree');p.add_argument('--source-root',type=pathlib.Path,help='Explicit frozen-source checkout; default verifies this checkout');a=p.parse_args();a.cache=a.cache.resolve()
 api=runpy.run_path(str(pathlib.Path(__file__).with_name('audit.py')))
 pinned=api['assert_sources'](a.source_root)
 root=a.source_root.resolve() if a.source_root is not None else api['ROOT'];build=root/'.lake/build/lib/lean';tracked=subprocess.check_output(['git','ls-files','*.lean'],text=True).splitlines();mods=[]
 for f in build.rglob('*.ilean'):
  mods.append(json.loads(f.read_text())['module'])
 if a.input_modules:mods=a.input_modules.read_text().splitlines()
 mods=sorted(set(mods));assert mods,'No existing reference modules: supply --input-modules; refusing Lake default targets';assert not a.view.exists(),'Fresh view required';a.view.mkdir(parents=True)
 mods,stdout,excluded=query_modules(mods,root,a.modules)
 a.modules.with_suffix('.excluded.json').write_text(json.dumps(excluded,indent=2)+'\n')
 paths=[pathlib.Path(json.loads(s)) for s in stdout.splitlines()];paths=[f if f.is_absolute() else root/f for f in paths];assert len(paths)==len(mods)
 table={}
 for f in (a.cache/'inputs').glob('*.jsonl'):
  for line in f.open():
   _,arts=json.loads(line)
   if isinstance(arts,dict):
    hs=arts.get('o',[])
    if not hs:continue
    h=str(hs[0])
    if h in table:assert (table[h]['i'],table[h]['o'])==(arts['i'],arts['o']), 'Ambiguous module artifact pair'
    table[h]=arts
 # Hash local artifacts using the pinned Lean/Lake implementation.
 local=[str(f) for f in paths if not f.is_relative_to(a.cache/'artifacts')]
 hashes={}
 if local:
  listfile=a.modules.with_suffix('.locals.txt');listfile.write_text('\n'.join(local)+'\n')
  exporter=pathlib.Path(__file__).with_name('Export.lean')
  output=subprocess.check_output(['lean','-j1','--run',str(exporter.resolve()),'binhash',str(listfile.resolve())],text=True,cwd=root)
  hashes=dict(s.split('\t',1) for s in output.splitlines())
 for m,f in zip(mods,paths):
  h=f.name.split('.',1)[0] if f.is_relative_to(a.cache/'artifacts') else hashes[str(f)]
  arts=table.get(h)
  if arts is None:raise RuntimeError('No matching reference artifact for '+m+' '+h)
  stem=a.view/pathlib.Path(m.replace('.','/'));stem.parent.mkdir(parents=True,exist_ok=True)
  files=recorded_artifacts(a.cache,arts)
  # Lake's query is authoritative for the main object; optional sidecars and
  # references use their own recorded content hashes.
  files['olean']=f
  for suffix,src in files.items():os.link(src,stem.with_suffix('.'+suffix))
 a.modules.write_text('\n'.join(mods)+'\n');print('CURRENT_ARTIFACT_VIEW_PASS',len(mods))
if __name__=='__main__':main()
