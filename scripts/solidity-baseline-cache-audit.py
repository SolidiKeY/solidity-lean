#!/usr/bin/env python3
"""Read-only import/trace/artifact cache audit; this script never builds."""
import hashlib,json,re,argparse,datetime
from functools import lru_cache
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
TARGETS=['Solidity.Frontend.Import','Solidity.Tools.Upstream','Solidity.Frontend.Testing']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
@lru_cache(maxsize=None)
def info(p):
 if not p.exists():return {'path':str(p),'exists':False}
 return dict(path=str(p),exists=True,bytes=p.stat().st_size,sha256=sha(p),mtimeUtc=datetime.datetime.fromtimestamp(p.stat().st_mtime,datetime.timezone.utc).isoformat())
def graph(root):
 nodes={}
 for p in (root/'Solidity').rglob('*.lean'):
  nodes[str(p.relative_to(root).with_suffix('')).replace('/','.')]=[n for line in p.read_text().splitlines() if re.match(r'^import\s+',line) for n in line.split()[1:] if n.startswith('Solidity.')]
 return nodes

def audit(root):
 nodes=graph(root);closures={}
 def walk(n,s):
  if n in s:return
  s.add(n)
  for x in nodes.get(n,[]):walk(x,s)
 for t in TARGETS:
  s=set();walk(t,s);closures[t]=sorted(s)
 modules={};jobs={}
 for n in sorted(set().union(*(set(c) for c in closures.values()))):
  stem=n.replace('.','/');src=root/(stem+'.lean');tr=root/'.lake/build/lib/lean'/(stem+'.trace');ole=root/'.lake/build/lib/lean'/(stem+'.olean');setup=root/'.lake/build/ir'/(stem+'.setup.json')
  r=dict(source=info(src),trace=info(tr),olean=info(ole),setup=info(setup),directImports=nodes[n])
  if tr.exists():
   trace=json.loads(tr.read_text());r['traceOutputs']=trace['outputs'];r['traceSourceHash']=next((v for k,v in trace['inputs'] if k==str(src)),None);r['traceToolchain']=[i for i in trace['inputs'] if isinstance(i[0],str) and i[0].startswith('Lean ')]
   r['traceInputIdentitySha256']=hashlib.sha256(json.dumps(trace['inputs'],sort_keys=True).encode()).hexdigest()
  if setup.exists():
   d=json.loads(setup.read_text());checks=[]
   for imp,paths in sorted(d.get('importArts',{}).items()):
    local=root/'.lake/build/lib/lean'/(imp.replace('.','/')+'.olean')
    for path in paths:
     p=Path(path);item=dict(module=imp,cached=info(p),local=info(local));item['byteIdenticalToLocal']=p.exists() and local.exists() and item['cached']['sha256']==item['local']['sha256'];checks.append(item)
   r['importArtifactChecks']=checks
  modules[n]=r
 # Hash exactly the narrow adapter closure using Lake's own hash algorithm.
 for n in closures['Solidity.Tools.Upstream']:
  r=modules[n]
  jobs[(r['source']['path'],True)]={'path':r['source']['path'],'text':True}
  if r['olean']['exists']:jobs[(r['olean']['path'],False)]={'path':r['olean']['path'],'text':False}
 return dict(targetClosures=closures,modules=modules,hashJobs=list(jobs.values()),rootLakefile=info(root/'lakefile.toml'),retainedLakefile=info(root/'tests/upstream/baseline-20261028/probes/lakefile.toml'))
def verify(a,hashes):
 values={(r['path'],r['text']):r['lakeHash'] for r in hashes};failures=[]
 for n in a['targetClosures']['Solidity.Tools.Upstream']:
  r=a['modules'][n]
  if not all(r[k]['exists'] for k in ['source','trace','olean','setup']):failures.append([n,'required source/trace/olean/setup missing'])
  recorded={x['module'] for x in r.get('importArtifactChecks',[])}
  if not set(r['directImports'])<=recorded:failures.append([n,'current direct imports absent from saved setup'])
  if not any(x[0]=='Lean 4.24.0, commit 797c613eb9b6d4ec95db23e3e00af9ac6657f24b' for x in r.get('traceToolchain',[])):failures.append([n,'trace toolchain identity differs'])
  if values[(r['source']['path'],True)]!=r.get('traceSourceHash'):failures.append([n,'source hash differs from trace'])
  if values.get((r['olean']['path'],False)) not in r.get('traceOutputs',{}).get('o',[]):failures.append([n,'olean hash differs from trace'])
  if not all(x['byteIdenticalToLocal'] for x in r.get('importArtifactChecks',[])):failures.append([n,'recorded imports differ/missing'])
 root='Solidity.Tools.Upstream'
 if {root}|{x['module'] for x in a['modules'][root].get('importArtifactChecks',[])}!=set(a['targetClosures'][root]):failures.append([root,'source closure differs from saved complete import map'])
 return dict(narrowClosureSourceAndOleanChecksPass=not failures,failures=failures,checkedModules=len(a['targetClosures']['Solidity.Tools.Upstream']))
def main():
 p=argparse.ArgumentParser();p.add_argument('--out',type=Path,required=True);p.add_argument('--hashes',type=Path);a=p.parse_args();x=audit(ROOT)
 a.out.mkdir(parents=True,exist_ok=True)
 (a.out/'audit.json').write_text(json.dumps(x,indent=2)+'\n');(a.out/'hash-jobs.json').write_text(json.dumps(x['hashJobs'],indent=2)+'\n')
 if a.hashes:
  v=verify(x,json.loads(a.hashes.read_text()));(a.out/'hash-verification.json').write_text(json.dumps(v,indent=2)+'\n');print(json.dumps(v));
  if not v['narrowClosureSourceAndOleanChecksPass']:raise SystemExit(2)
 else:print(json.dumps({t:len(c) for t,c in x['targetClosures'].items()}))
if __name__=='__main__':main()
