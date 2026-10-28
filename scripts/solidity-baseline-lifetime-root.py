#!/usr/bin/env python3
"""One bounded, private compilation of unchanged Lifetime; never calls Lake build."""
import argparse,hashlib,json,os,subprocess,time,resource,sys
from pathlib import Path
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 assert 0<int(Path('/sys/fs/cgroup/memory.max').read_text())<=12*1024**3 and int(Path('/sys/fs/cgroup/memory.swap.max').read_text())==0, 'hard12GiB/no-swap cgroup required'
 assert os.environ.get('LEAN_NUM_THREADS')=='1'
 p=argparse.ArgumentParser();p.add_argument('out',type=Path);args=p.parse_args();out=args.out.resolve()
 if out.exists():p.error('fresh private output required')
 out.mkdir(parents=True);(out/'logs').mkdir();overlay=out/'overlay';stem=overlay/'Solidity/Semantics/Lifetime';stem.parent.mkdir(parents=True)
 old=json.loads((ROOT/'tests/upstream/baseline-20261028/native-cache/cache-after.json').read_text());snap={}
 for r in old['checks']:
  paths={'source':ROOT/(r['module'].replace('.','/')+'.lean'),'olean':ROOT/'.lake/build/lib/lean'/(r['module'].replace('.','/')+'.olean'),'trace':ROOT/'.lake/build/lib/lean'/(r['module'].replace('.','/')+'.trace'),'setup':ROOT/'.lake/build/ir'/(r['module'].replace('.','/')+'.setup.json')}
  path=paths[r['kind']];assert sha(path)==r['sha256'],f'prior native cache drift: {path}';snap[str(path)]=sha(path)
 for path in [ROOT/'Solidity/Semantics/Lifetime.lean',ROOT/'.lake/build/lib/lean/Solidity/Semantics/Lifetime.olean',ROOT/'.lake/build/lib/lean/Solidity/Semantics/Lifetime.trace',ROOT/'.lake/build/ir/Solidity/Semantics/Lifetime.setup.json',ROOT/'lakefile.toml']:
  snap[str(path)]=sha(path)
 records=[]
 def call(name,command,seconds=120,env=None):
  start=time.monotonic();r=subprocess.run(['timeout','-k','10',str(seconds),*command],cwd=ROOT,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);log=out/'logs'/(name+'.log');log.write_bytes(r.stdout);record=dict(command=['timeout','-k','10',str(seconds),*command],exitCode=r.returncode,elapsedSeconds=time.monotonic()-start,maxChildRssKiB=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,log=str(log.relative_to(out)),sha256=sha(log),cgroupPeakBytes=int(Path('/sys/fs/cgroup/memory.peak').read_text()));records.append(record);(out/'commands.json').write_text(json.dumps(records,indent=2)+'\n');print(name,r.returncode,record['elapsedSeconds'],flush=True)
  shared=dict(allSharedArtifactsUnchanged=all(sha(Path(p))==h for p,h in snap.items()),checked=len(snap))
  (out/(name+'-shared-after.json')).write_text(json.dumps(shared,indent=2)+'\n')
  assert shared['allSharedArtifactsUnchanged'],'shared artifact drift'
  if r.returncode:raise SystemExit(r.returncode)
  return r.stdout
 env={**os.environ,'LEAN_NUM_THREADS':'1','LEAN_PATH':str(ROOT/'.lake/build/lib/lean')}
 call('versions',['bash','-c','lean --version; lake --version'],env=env)
 call('cache-audit',['python3','scripts/solidity-baseline-cache-audit.py','--out',str(out/'cache')],env=env)
 call('file-hashes',['lean','-j1','--run','tests/upstream/baseline-20261028/native-cache/FileHashes.lean',str(out/'cache/hash-jobs.json'),str(out/'cache/file-hashes.json')],env=env)
 call('cache-verify',['python3','scripts/solidity-baseline-cache-audit.py','--out',str(out/'cache'),'--hashes',str(out/'cache/file-hashes.json')],env=env)
 a=json.loads((out/'cache/audit.json').read_text());import importlib.util
 spec=importlib.util.spec_from_file_location('cache',ROOT/'scripts/solidity-baseline-cache-audit.py');cache=importlib.util.module_from_spec(spec);spec.loader.exec_module(cache);g=cache.graph(ROOT);deps=set()
 def walk(n):
  if n in deps:return
  deps.add(n)
  for d in g[n]:walk(d)
 walk('Solidity.Semantics.Lifetime');assert len(deps)==28 and deps-{'Solidity.Semantics.Lifetime'}<=set(a['targetClosures']['Solidity.Tools.Upstream'])
 (out/'before.json').write_text(json.dumps(dict(startingCommit=subprocess.check_output(['git','rev-parse','HEAD'],text=True,cwd=ROOT).strip(),sourceSha256=sha(ROOT/'Solidity/Semantics/Lifetime.lean'),snapshots=snap,currentDependencies=sorted(deps-{'Solidity.Semantics.Lifetime'}),LEAN_PATH=env['LEAN_PATH'],noLakeBuild=True),indent=2)+'\n')
 call('root-deps',['lean','-j1','--deps','Solidity/Semantics/Lifetime.lean'],env=env)
 call('root-compile',['lean','-j1','--tstack=131072','-o',str(stem.with_suffix('.olean')),'-i',str(stem.with_suffix('.ilean')),'-c',str(stem.with_suffix('.c')),'Solidity/Semantics/Lifetime.lean'],seconds=900,env=env)
 for module in a['targetClosures']['Solidity.Tools.Upstream']:
  target=overlay/(module.replace('.','/')+'.olean');target.parent.mkdir(parents=True,exist_ok=True)
  target.symlink_to(ROOT/'.lake/build/lib/lean'/(module.replace('.','/')+'.olean'))
 (out/'overlay-imports.json').write_text(json.dumps({str(p.relative_to(out)):dict(resolved=str(p.resolve()),sha256=sha(p),symlink=p.is_symlink()) for p in overlay.rglob('*.olean')},indent=2)+'\n')
 env['LEAN_PATH']=str(overlay)+':'+env['LEAN_PATH']
 preflight=out/'RootPreflight.lean';preflight.write_text('import Solidity.Tools.Upstream\nimport Solidity.Semantics.Lifetime\n#check Solidity.Lifetime.System.run\n#print axioms Solidity.Lifetime.System.run_ok\n#eval IO.println "LIFETIME_ROOT_NATIVE_IMPORT_PASS"\n')
 call('root-preflight',['lean','-j1','--tstack=131072',str(preflight)],env=env)
 assert all(sha(Path(p))==h for p,h in snap.items()),'shared artifacts changed'
 (out/'after.json').write_text(json.dumps(dict(allSharedArtifactsUnchanged=True,checked=len(snap),privateRootArtifacts={str(p.relative_to(out)):dict(sha256=sha(p),bytes=p.stat().st_size) for p in overlay.rglob('*') if p.is_file() and not p.is_symlink()},LEAN_PATH=env['LEAN_PATH'],cgroupPeakBytes=int(Path('/sys/fs/cgroup/memory.peak').read_text()),memoryMaxBytes=int(Path('/sys/fs/cgroup/memory.max').read_text()),swapMaxBytes=int(Path('/sys/fs/cgroup/memory.swap.max').read_text()),memoryEvents=Path('/sys/fs/cgroup/memory.events').read_text()),indent=2)+'\n')
if __name__=='__main__':main()
