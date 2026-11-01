#!/usr/bin/env python3
"""Actual Lake setup-file preparation; never a fresh proof timing result."""
import argparse,copy,fcntl,hashlib,importlib.util,json,os,shutil,subprocess
from pathlib import Path
from types import SimpleNamespace
ROOT=Path(__file__).resolve().parents[1]

def protocol():
 s=importlib.util.spec_from_file_location('setup_provenance',ROOT/'scripts/roadmap-v17-provenance.py');p=importlib.util.module_from_spec(s);s.loader.exec_module(p);return p

def capture(module,directory):
 p=protocol();p.e.require(module in p.setup_modules(),'not an original workload member')
 lake=Path(shutil.which('lake') or '').resolve();lean=Path(shutil.which('lean') or '').resolve()
 p.e.require(lake.is_file() and lean.is_file() and lake.parent==lean.parent,'Lean/Lake selection mismatch')
 env=os.environ.copy();env['PATH']=str(lake.parent)+os.pathsep+env.get('PATH','');env['LEAN_NUM_THREADS']='1'
 source=ROOT/(module.replace('.','/')+'.lean');command=[str(lake),'-f','roadmap-v17-runtime.lakefile.toml','setup-file',str(source)]
 (directory/'setup-command.json').write_text(json.dumps({'command':command,'selectedLake':str(lake),'selectedLean':str(lean),'childPath':env['PATH']}))
 with (directory/'lake-setup.stdout').open('wb') as stdout,(directory/'lake-setup.stderr').open('wb') as stderr:
  code=subprocess.run(command,cwd=ROOT,env=env,stdout=stdout,stderr=stderr).returncode
 if code:return code
 raw=(directory/'lake-setup.stdout').read_bytes();setup=p.e.loads(raw)
 p.e.require(setup['name']==module and type(setup['isModule']) is bool and isinstance(setup['importArts'],dict),'wrong actual Lake setup')
 target=ROOT/'.lake/build/ir'/(module.replace('.','/')+'.setup.json');target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(raw)
 print(json.dumps({'module':module,'setupSha256':p.e.digest(raw),'sourceSha256':p.resources.hash_file(source),'stage':'Lake imports/setup preparation only','releaseClosed':False}));return 0

def validate(manifest,directory,current,live=True):
 p=protocol();p.e.require(manifest['kind']=='actual-Lake-original24-setups' and manifest['sourceSnapshot']==current,'wrong setup source/revision')
 p.e.require(manifest.get('failure') is None and manifest['sourceAfter']==current and manifest['freshProofWorkloadPass'] is False and manifest['releaseClosed'] is False,'contradictory preparation status')
 p.e.require(manifest['expectedModules']==p.setup_modules() and len(manifest['stages'])==24,'incomplete setup preparation')
 p.e.require(set(manifest['setups'])==set(p.setup_modules()),'extra or missing restored setup')
 previous=None
 for i,row in enumerate(manifest['stages']):
  p.e.require(row['module']==p.setup_modules()[i],'reordered setup preparation')
  record_path=p.e.local_file(directory,row['path']);r=p.e.loads(p.read_bound(directory,row['path'],row['sha256']))
  p.e.require(p.validate(r,record_path.parent,current,f'derived17-setup-{i:02}',live_outputs=False) is True,'failed setup preparation')
  if previous is not None:p.e.require(previous['buildEnd']==r['buildStart'] and previous['cacheEnd']==r['cacheStart'],'setup-stage continuity mismatch')
  previous=r
  observed=r['setupOutput'];raw=p.read_bound(record_path.parent,observed['stdout']['path'],observed['stdout']['sha256'])
  if live:p.e.require(Path(observed['generatedSetup']).read_bytes()==raw,'current setup differs from actual captured Lake setup')
  for name,sha in observed['importArtifacts'].items():p.e.require(p.resources.hash_file(Path(name))==sha,'setup dependency artifact changed')
  p.e.require(manifest['setups'][row['module']]=={'path':observed['generatedSetup'],'sha256':observed['generatedSha256']},'wrong setup final binding')
 p.e.require(previous is not None and previous['installedAfter']==manifest['installedInputs'],'setup tool inputs disagree')
 expected=copy.deepcopy(previous['buildEnd'])
 for module,binding in manifest['setups'].items():expected['files']['ir/'+module.replace('.','/')+'.setup.json']=binding['sha256']
 p.e.require(manifest['finalBuild']==expected and manifest['finalCache']==previous['cacheEnd'],'unrecorded post-preparation build/cache mutation')
 if live:
  p.e.require(p.inventory(ROOT/'.lake/build')==manifest['finalBuild'],'setup build state changed')
  p.e.require(p.inventory(ROOT/'.lake/roadmap-v17-cache'/current['sourceToolchainKey'])==manifest['finalCache'],'setup cache state changed')
 return True

def prepare(directory,start):
 p=protocol();directory=directory.resolve();directory.mkdir(exist_ok=start>0)
 with open('/tmp/solidity-lean-feature-groups-20261025/writer.lock','a+') as lock:
  fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB);p.ensure_no_unresolved();current=p.e.snapshot(ROOT)
  path=directory/'preparation.json'
  if start:
   result=p.e.load(path);p.e.require(result['sourceSnapshot']==current and len(result['stages'])==start,'resume differs from completed preparation stages')
  else:result={'kind':'actual-Lake-original24-setups','sourceSnapshot':current,'expectedModules':p.setup_modules(),'stages':[],'setups':{},'freshProofWorkloadPass':False,'releaseClosed':False}
  for i,module in enumerate(p.setup_modules()[start:],start):
   out=directory/f'stage-{i:02}'
   try:code=p.collect(SimpleNamespace(gate=f'derived17-setup-{i:02}',out=out))
   except (ValueError,OSError,KeyError,TypeError,subprocess.SubprocessError) as error:
    result['failure']={'stage':i,'module':module,'error':str(error),'exit':2}
    if isinstance(error,p.resources.ResourceObservationError):result['failure']['resourceObservations']=error.observations
    path.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result['failure']));return 2
   if code:
    result['failure']={'stage':i,'module':module,'exit':code,'record':str(out/'provenance.json')};path.write_text(json.dumps(result,indent=2)+'\n');return code
   record=p.e.load(out/'provenance.json');observed=record['setupOutput']
   result['stages'].append({'module':module,'path':str((out/'provenance.json').relative_to(directory)),'sha256':p.resources.hash_file(out/'provenance.json')})
   result['setups'][module]={'path':observed['generatedSetup'],'sha256':observed['generatedSha256']}
   path.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'prepared':i+1,'module':module,'freshProofWorkloadPass':False}),flush=True)
  # Later import preparation may regenerate an earlier module's normal setup.
  # Restore ONLY the byte-exact actual Lake stdout retained for each member.
  for row in result['stages']:
   rp=directory/row['path'];record=p.e.load(rp);observed=record['setupOutput'];raw=p.read_bound(rp.parent,observed['stdout']['path'],observed['stdout']['sha256']);Path(observed['generatedSetup']).write_bytes(raw)
  result['installedInputs']=record['installedAfter'];result['finalBuild']=p.inventory(ROOT/'.lake/build');result['finalCache']=p.inventory(ROOT/'.lake/roadmap-v17-cache'/current['sourceToolchainKey']);result['sourceAfter']=p.e.snapshot(ROOT);p.e.require(result['sourceAfter']==current,'source changed during setup preparation')
  result.pop('failure',None);path.write_text(json.dumps(result,indent=2)+'\n');validate(result,directory,current);print('ACTUAL_LAKE_24_SETUPS_PREPARED_NOT_FRESH_PROOF_PASS');return 0

if __name__=='__main__':
 a=argparse.ArgumentParser(description=__doc__);a.add_argument('mode',choices=['capture','prepare']);a.add_argument('--module');a.add_argument('--directory',type=Path,required=True);a.add_argument('--start',type=int,default=0);args=a.parse_args()
 try:raise SystemExit(capture(args.module,args.directory) if args.mode=='capture' else prepare(args.directory,args.start))
 except (ValueError,OSError,KeyError,TypeError,subprocess.SubprocessError) as error:print(json.dumps({'error':str(error),'releaseClosed':False}));raise SystemExit(2)
